Require Import Axioms.

Require Import sepcomp. Import SepComp.
Require Import semantics_lemmas.

Require Import pos.
Require Import stack. 
Require Import cast.

Require Import Program.
Require Import ssreflect Ssreflect.seq ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import AST.     (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Memory.
Require Import Integers.

Require Import ZArith.

Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation READ := 
  (EF_external 3%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).

Require Import compcert_linking.

(* (*move to other file*) *)
Class monad (mon : Type -> Type) :=
  {
    ret : forall {A : Type},  A -> mon A;
    bind : forall {A B : Type}, mon A -> (A -> mon B) -> mon B
  }.

Notation "x >>= f" := (bind x f) (at level 40, left associativity).
Notation "'do!' X <- A ; B" := (bind A (fun X => B))
                                 (at level 200, X ident, A at level 100, B at level 200).

Module OptionMonad.
  
  Instance optionMonad : monad option :=
    {
      ret A x := Some x;
      bind A B x f :=
        match x with
          | Some y => f y
          | None => None
        end
    }.

End OptionMonad.

Definition access_map := Maps.PMap.t (Z -> perm_kind -> option permission).

Module PermMap. Section PermMap.

Record t := mk
  { next : block
  ;  map : access_map 
  ;  max : forall (b : positive) (ofs : Z),
                 Mem.perm_order'' (Maps.PMap.get b map ofs Max)
                 (Maps.PMap.get b map ofs Cur)
  ; nextblock : forall (b : positive) (ofs : Z) (k : perm_kind),
                       ~ Coqlib.Plt b next -> Maps.PMap.get b map ofs k = None
  }. 

End PermMap. End PermMap.

Section permMapDefs.
 
  Definition empty_map : access_map :=
    (fun z p => None, Maps.PTree.empty (Z -> perm_kind -> option permission)).
  
  Lemma max_empty : forall b ofs, Mem.perm_order'' (Maps.PMap.get b empty_map ofs Max)
                                                   (Maps.PMap.get b empty_map ofs Cur).
  Proof.
    intros. unfold Maps.PMap.get. rewrite Maps.PTree.gempty. constructor.
  Qed.

  Lemma nextblock_empty : forall (b : positive) (ofs : Z) (k : perm_kind),
         ~ Coqlib.Plt b 1 -> Maps.PMap.get b empty_map ofs k = None.
  intros. unfold Maps.PMap.get. now rewrite Maps.PTree.gempty.
  Qed.

  Definition emptyPermMap :=
    {| PermMap.next := 1%positive;
       PermMap.map := empty_map;
       PermMap.max := max_empty;
       PermMap.nextblock := nextblock_empty |}.

  (* Some None represents the empty permission. None is used for
  permissions that conflict/race. *)
     
  Definition perm_union (p1 p2 : option permission) : option (option permission) :=
    match p1,p2 with
      | None, _ => Some p2
      | _, None => Some p1
      | Some p1', Some p2' =>
        match p1', p2' with
          | Nonempty, _ => Some p2
          | _, Nonempty => Some p1
          | Freeable, _ => None
          | _, Freeable => None
          | Writable, _ => None
          | _, Writable => None
          | Readable, Readable => Some (Some Readable)
        end
    end.

  Definition perm_max (p1 p2 : option permission) : option permission :=
    match p1,p2 with
      | Some Freeable, _ => p1
      | _, Some Freeable => p2
      | Some Writable, _ => p1
      | _, Some Writable => p2
      | Some Readable, _ => p1
      | _, Some Readable => p2
      | Some Nonempty, _ => p1
      | _, Some Nonempty => p2
      | None, None => None
    end.
      
  Definition updPermMap (m : mem) (p : PermMap.t) : option mem :=
    match positive_eq_dec (Mem.nextblock m) (PermMap.next p) with
      | left pf => 
        Some (Mem.mkmem 
                (Mem.mem_contents m) 
                (PermMap.map p) 
                (Mem.nextblock m)
                (PermMap.max p) 
                (eq_rect_r 
                   (fun n => forall (b : positive) (ofs : Z) (k : perm_kind),
                               ~ Coqlib.Plt b n ->
                               Maps.PMap.get b (PermMap.map p) ofs k = None)
                   (PermMap.nextblock p) pf)
                (Mem.contents_default m))
      | right _ => None
    end.

    Definition getPermMap (m : mem) :=
    {| PermMap.next := Mem.nextblock m;
       PermMap.map := Mem.mem_access m;
       PermMap.max := Mem.access_max m;
       PermMap.nextblock := Mem.nextblock_noaccess m
    |}.

    Lemma permOrder_union_max :
      forall (p1 p2 p3 p4 p : option permission),
        Mem.perm_order'' p1 p3 ->
        Mem.perm_order'' p2 p4 ->
        perm_union p3 p4 = Some p ->
        Mem.perm_order'' (perm_max p1 p2) p.
    Proof.
      (* intros ????? Hp13 Hp24 Hu34. *)
      (* destruct p1,p2,p3,p4; simpl in *; try congruence; *)
      (* inversion Hu34; subst; try econstructor(eauto). *)
      (* inversion Hp13. inversion Hp24. *)
      (* inversion Hp24. inversion Hp13. *)
      (* inversion Hp24. inversion Hp24. *)
      (* inversion Hp13. inversion Hp13. inversion Hp13. *)
      admit.
    Defined.

    Lemma mapOrd : forall pmap b ofs pm pc f,
                     Maps.PTree.get b (PermMap.map pmap).2 = Some f ->
                     (f ofs Max) = Some pm ->
                     (f ofs Cur) = Some pc ->
                     perm_order pm pc.
    Proof.
      intros ?????? Hget Hfm Hfc.
      destruct pmap; simpl in *.
      specialize (max b ofs).
      unfold Maps.PMap.get in max.
      rewrite Hget in max.
      rewrite Hfm Hfc in max. now simpl in max.
    Qed.
    
    Definition permMapsUnion (pmap1 pmap2 : PermMap.t)
               (Hget : forall b ofs k,
                       (exists p1,
                          Maps.PMap.get b (PermMap.map pmap1) ofs k = Some p1) <->
                       exists p2,
                         Maps.PMap.get b (PermMap.map pmap2) ofs k = Some p2)
    : option PermMap.t.
      refine
        (if eq_block (PermMap.next pmap1) (PermMap.next pmap2) then
           Some
             {| PermMap.next := PermMap.next pmap1;
                PermMap.map :=
                  (fun ofs kind =>
                     do! p1 <- (fst (PermMap.map pmap1)) ofs kind;
                     do! p2 <- (fst (PermMap.map pmap2)) ofs kind;
                     match kind with
                       | Max =>
                         Some (perm_max p1 p2)
                     | Cur => perm_union p1 p2
                     end,
                     Maps.PTree.combine
                       (fun of1 of2 =>
                          do! f1 <- of1;
                          do! f2 <- of2;
                          Some (fun ofs kind =>
                                  do! p1 <- f1 ofs kind;
                                  do! p2 <- f2 ofs kind;
                                  match kind with
                                    | Max =>
                                      Some (perm_max p1 p2)
                                    | Cur => perm_union p1 p2
                                  end))
                       (snd (PermMap.map pmap1)) (snd (PermMap.map pmap2)));
                PermMap.max := _;
                PermMap.nextblock := _ |}
         else None).
      Proof.
        intros b ofs. Focus 2. admit.
        unfold Maps.PMap.get.
        rewrite Maps.PTree.gcombine.
        simpl.
        repeat match goal with
                 | [ |- context[match ?Expr with _ => _ end]] =>
                   destruct Expr eqn:?
                | [H:context[match ?Expr with _ => _ end] |- _] =>
                  destruct Expr eqn:?
                | [H: Some _ = Some _ |- _] => inversion H; subst; clear H
               end; simpl; auto; try congruence; 
        repeat match goal with
                 | [ |- context[match ?Expr with _ => _ end]] =>
                   destruct Expr eqn:?
                 | [H:context[match ?Expr with _ => _ end] |- _] =>
                   destruct Expr eqn:?
               end; auto;
        subst;
        destruct pmap1 as [next1 map1 max1 nextblock1];
        destruct pmap2 as [next2 map2 max2 nextblock2]; simpl in *;
        specialize (max1 b ofs);
        specialize (max2 b ofs);
        specialize (Hget b ofs Max).
        Focus 7.
        destruct Hget as [Hget1 _].
        assert ( (exists p1 : permission, Maps.PMap.get b map1 ofs Max = Some p1) ).
        eexists; unfold Maps.PMap.get. rewrite Heqo4.
        eauto.
        apply Hget1 in H. destruct H as [p3 H].
        
        unfold Mem.perm_order'' in max2.
        rewrite H in max2.
        unfold Maps.PMap.get in max2. rewrite 
        rewrite H in max2. 
        
        

        
        
        unfold Maps.PMap.get in *;
        unfold Mem.perm_order'' in *;
                 
        repeat match goal with
          | [H : context[match ?Expr with _ => _ end], H1: ?Expr = _ |- _] =>
            rewrite H1 in H
               end.
        Focus 7. 
        specialize (Hget Max).
        destruct Hget as [Hget1 _].
        assert (Hex1: exists p3 : permission, map1.1 ofs Max = Some p3) by (eexists; eauto).
        apply Hget1 in Hex1. destruct Hex1 as [p3 Hget2].
        destruct (Maps.PTree.get b map2.2) eqn:?;
        repeat match goal with
                 | [H : context[match ?Expr with _ => _ end], H1: ?Expr = _ |- _] =>
                   rewrite H1 in H
               end.
        unfold Maps.PMap.get. rwrite 
        
       

        
        rewrite Heqo0 in max. rewrite Heqo in max. simpl in max.
        match goal with
          | [?F
        
        
        Focus 2. 
          

    Lemma permMapsUnionCorrect : forall pmap1 pmap2,
                                   eq_block (PermMap.next pmap1) (PermMap.next pmap2) ->
                                   match permMapsUnion pmap1 pmap2 with
                                     | Some pmap3 => 
                                       isUnionPermMaps pmap1 pmap2 pmap3
                                     | None => False
                                   end.


    Inductive isUnionPermMaps : PermMap.t -> PermMap.t -> PermMap.t -> Prop :=
    | PMapsUnion :
        forall pmap1 pmap2 pmap3
               (Hnext : (PermMap.next pmap1) = (PermMap.next pmap2)
                        /\ (PermMap.next pmap1) = (PermMap.next pmap3))
               (HmapCur: forall (b : positive) (ofs : Z) (p1 p2 : permission),
                           Maps.PMap.get b (PermMap.map pmap1) ofs Cur = Some p1 ->
                           Maps.PMap.get b (PermMap.map pmap2) ofs Cur = Some p2 ->
                           Maps.PMap.get b (PermMap.map pmap3) ofs Cur = perm_union p1 p2)
               (HmapCurNone: forall (b : positive) (ofs : Z) (p1 p2 : permission),
                           (Maps.PMap.get b (PermMap.map pmap1) ofs Cur = None \/
                           Maps.PMap.get b (PermMap.map pmap2) ofs Cur = None) ->
                           Maps.PMap.get b (PermMap.map pmap3) ofs Cur = None)
               (HmapMax: forall (b : positive) (ofs : Z) (p1 p2 : permission),
                           Maps.PMap.get b (PermMap.map pmap1) ofs Max = Some p1 ->
                           Maps.PMap.get b (PermMap.map pmap2) ofs Max = Some p2 ->
                           Maps.PMap.get b (PermMap.map pmap3) ofs Max = Some (perm_max p1 p2))
               (HmapMax: forall (b : positive) (ofs : Z) (p1 p2 : permission),
                           (Maps.PMap.get b (PermMap.map pmap1) ofs Max = None \/
                           Maps.PMap.get b (PermMap.map pmap2) ofs Max = None) ->
                           Maps.PMap.get b (PermMap.map pmap3) ofs Max = None),
          isUnionPermMaps pmap1 pmap2 pmap3.

      
End permMapDefs.

      
Module ThreadPool. Section ThreadPool.

  Variable sem : Modsem.t.

  Notation cT := (Modsem.C sem).

  Inductive ctl : Type :=
  | Krun : cT -> ctl
  | Kstage : external_function -> list val -> cT -> ctl.
  
  Record t := mk
                { num_threads : pos
                  ; pool :> 'I_num_threads -> ctl
                  ; perm_maps : 'I_num_threads -> PermMap.t
                  ; counter : nat
                }.

End ThreadPool. End ThreadPool.

Arguments ThreadPool.Krun [sem] _.
Arguments ThreadPool.Kstage [sem] _ _ _.

Notation pool := ThreadPool.t.

Section poolDefs.

Context {sem : Modsem.t} {next : block}.

Variable (tp : ThreadPool.t sem).

Import ThreadPool.

Notation cT := (Modsem.C sem).
Notation ctl := (ctl sem).
Notation num_threads := (num_threads tp).
Notation thread_pool := (t sem).

Definition addThread (c : ctl) (pmap : PermMap.t) : thread_pool :=
  let: new_num_threads := pos_incr num_threads in
  let: new_tid := ordinal_pos_incr num_threads in
  @mk sem new_num_threads
      (fun (n : 'I_new_num_threads) => 
         match unlift new_tid n with
           | None => c
           | Some n' => tp n'
         end)
      (fun (n : 'I_new_num_threads) => 
         match unlift new_tid n with
           | None => pmap
           | Some n' => (perm_maps tp) n'
         end)
      (counter tp).+1.

Definition updThreadC (tid : 'I_num_threads) (c' : ctl) : thread_pool :=
  @mk sem num_threads (fun (n : 'I_num_threads) =>
                         if n == tid then c' else tp n) (perm_maps tp) 
      (counter tp).

Definition updThreadP (tid : 'I_num_threads) (pmap : PermMap.t) : thread_pool :=
  @mk sem num_threads tp (fun (n : 'I_num_threads) =>
                            if n == tid then pmap else (perm_maps tp) n) 
      (counter tp).

Definition updThread (tid : 'I_num_threads) (c' : ctl) (pmap : PermMap.t) : thread_pool :=
  @mk sem num_threads
      (fun (n : 'I_num_threads) =>
                         if n == tid then c' else tp n)
      (fun (n : 'I_num_threads) =>
         if n == tid then pmap else (perm_maps tp) n) 
      (counter tp).

Definition schedNext : thread_pool :=
  @mk sem num_threads (pool tp) (perm_maps tp) (counter tp).+1.

Definition getThreadC (tid : 'I_num_threads) : ctl := tp tid.

Definition getThreadPerm (tid : 'I_num_threads) : PermMap.t := (perm_maps tp) tid.

Inductive permMapsInv : nat -> PermMap.t -> Prop :=
| perm0 : forall (pf : 0 < num_threads), permMapsInv 0 (perm_maps tp (Ordinal pf)) 
| permS : forall n (pf : n < num_threads) pprev punion,
            permMapsInv n pprev ->
            permMapsUnion pprev (perm_maps tp (Ordinal pf)) punion ->
            permMapsInv (S n) punion.
              
End poolDefs.

Section poolLemmas.

Context {sem : Modsem.t} {next : block} (tp : ThreadPool.t sem).

Import ThreadPool.

Lemma gssThreadCode (tid : 'I_(num_threads tp)) c' p' : 
  getThreadC (updThread tp tid c' p') tid = c'.
Proof. by rewrite /getThreadC /updThread /= eq_refl. Qed.

Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' p' :
  tid' != tid -> getThreadC (updThread tp tid c' p') tid' = getThreadC tp tid'.
Proof. by rewrite /getThreadC /updThread /=; case Heq: (tid' == tid). Qed.

Lemma getAddThread c pmap tid :
  tid = ordinal_pos_incr (num_threads tp) ->
  getThreadC (addThread tp c pmap) tid = c.
Proof. by rewrite /getThreadC /addThread /= => <-; rewrite unlift_none. Qed.

Lemma getUpdPermOrd tid p :
  'I_(num_threads tp) = 'I_(num_threads (updThreadP tp tid p)).
Proof.
    by [].
Qed.

Lemma permInvDet : forall n p1 p1',
                     permMapsInv tp n p1 ->
                     permMapsInv tp n p1' ->
                     p1 = p1'.
Proof.
  induction n.
  - intros. inversion H; inversion H0.
      by have->: pf = pf0 by apply:proof_irr.
  - intros p2 p2' Hp2 Hp2'.
    inversion Hp2 as [|? pf pprev punion Hinv Hunion2].
    inversion Hp2' as [|? pf' pprev' punion' Hinv' Hunion2']; subst.
    (have pfeq: pf = pf' by apply:proof_irr); subst.
    specialize (IHn _ _ Hinv Hinv'); subst.    
    eapply permMapsUnionDet; eauto.
Qed.
    

End poolLemmas.

Inductive Handled : external_function -> Prop :=
  | HandledLock : Handled LOCK
  | HandledUnlock : Handled UNLOCK
  | HandledCreate : Handled CREATE.
  (*...*)

Definition handled (ef : external_function) : bool :=
  match extfunct_eqdec ef LOCK with
    | left _ => true
    | right _ => 
      match extfunct_eqdec ef UNLOCK with
        | left _ => true
        | right _  => 
          match extfunct_eqdec ef CREATE with
            | left _ => true
            | right _  => false
          end
      end
  end.

Lemma extfunct_eqdec_refl ef : exists pf, extfunct_eqdec ef ef = left pf.
Proof. by case H: (extfunct_eqdec _ _)=> [pf|//]; exists pf. Qed.

Lemma handledP ef : reflect (Handled ef) (handled ef).
Proof.
case Hhdl: (handled ef); [apply: ReflectT|apply: ReflectF].
{ move: Hhdl; rewrite /handled; case: (extfunct_eqdec _ _).
   by move=> ->; constructor.
   move=> H; case: (extfunct_eqdec _ _)=> //.
   by move=> ->; constructor.
   move=> H2; case: (extfunct_eqdec _ _)=> //.
   by move=> ->; constructor.
}
{ inversion 1; subst; rewrite /handled in Hhdl. 
   by move: Hhdl; case: (extfunct_eqdec_refl LOCK)=> pf ->.
   by move: Hhdl; case: (extfunct_eqdec_refl UNLOCK)=> pf ->.   
   by move: Hhdl; case: (extfunct_eqdec_refl CREATE)=> pf ->.   
}
Qed.   

Definition cant_step {G C M} (sem : CoreSemantics G C M) c := 
  (exists pkg, semantics.at_external sem c = Some pkg)
  \/ exists v, semantics.halted sem c = Some v.

Lemma cant_step_step {G C M} (sem : CoreSemantics G C M) ge c m c' m' :
  cant_step sem c -> 
  ~ semantics.corestep sem ge c m c' m'.
Proof.
case.
{ case=> ? H H2.
  erewrite corestep_not_at_external in H; eauto.
  congruence.
}
case=> ? H H2.
erewrite corestep_not_halted in H; eauto.
congruence.
Qed.

Module Concur. Section Concur.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable aggelos : nat -> perm_map.
Variable schedule : nat -> nat.

Section Corestep.

Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).                
    
Inductive step : thread_pool -> mem -> thread_pool -> mem -> Prop :=
  | step_congr : 
      forall tp m c m' (c' : Modsem.C sem) n0,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
        let: tid := Ordinal tid0_lt_pf in
        getThreadC tp tid = Krun c ->
        corestepN the_sem the_ge (S n0) c m c' m' ->
        cant_step the_sem c' ->
        (* permMapsInv tp (num_threads tp) (getPermMap m) -> *)
        step tp m (updThreadC tp tid (Krun c')) m'

  | step_stage :
      forall tp m c ef args,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Krun c ->
      semantics.at_external the_sem c = Some (ef, ef_sig ef, args) ->
      handled ef ->
      (* permMapsInv tp (num_threads tp) (getPermMap m) -> *)
      step tp m (schedNext (updThreadC tp tid (Kstage ef args c))) m

  | step_lock :
      forall tp tp' m c m'' c' m' b ofs pnew,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Kstage LOCK (Vptr b ofs::nil) c ->
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one) ->
      Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      tp' = updThread tp tid (Krun c') (aggelos n) ->
      permMapsInv tp' (num_threads tp') pnew ->
      updPermMap m'' pnew = Some m' -> 
      step tp m tp' m'

  | step_unlock :
      forall tp tp' m c m'' c' m' b ofs pnew,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Kstage UNLOCK (Vptr b ofs::nil) c ->
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero) ->
      Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      tp' = updThread tp tid (Krun c') (aggelos n) ->
      permMapsInv tp' (num_threads tp') pnew ->
      updPermMap m'' pnew = Some m' -> 
      step tp m tp' m'

  | step_create :
      forall tp tp' m m' c c' c_new vf arg pnew,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Kstage CREATE (vf::arg::nil) c ->
      semantics.initial_core the_sem the_ge vf (arg::nil) = Some c_new ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      tp' = schedNext (addThread
                         (updThread tp tid (Krun c') (aggelos (n+1))) (Krun c_new) (aggelos n)) ->
      permMapsInv tp' (num_threads tp') pnew ->
      updPermMap m pnew = Some m' -> 
      step tp m tp' m'.
                           
End Corestep.

Lemma step_inv the_ge tp c m tp' m' ef sig args : 
  let: n := counter tp in
  let: tid0 := schedule n in
  forall (tid0_lt_pf :  tid0 < num_threads tp),
  let: tid := Ordinal tid0_lt_pf in
  getThreadC tp tid = Krun c ->
  semantics.at_external the_sem c = Some (ef, sig, args) -> 
  handled ef = false -> 
  ~ step the_ge tp m tp' m'.
Proof. 
  move=> pf get Hat; move/handledP=> Hhdl step.
  case: step pf get Hat Hhdl n. move {tp m tp' m'}.
{ move=> ?????? pf get step cant pf'; have ->: pf' = pf by apply: proof_irr.
  move: step=> /=; case=> x []y []? ?.
  by rewrite get; case=> <-; erewrite corestep_not_at_external; eauto.
}
{ move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
  rewrite get; case=> <-; rewrite Hat; case=> <- /= _ _ Contra _. 
  by apply: Contra; apply/handledP.
}
{ move=> ?????????? pf get Hat ????? pf'; have ->: pf' = pf by apply: proof_irr.
  by rewrite get.
}
{ move=> ?????????? pf get Hat ????? pf'; have ->: pf' = pf by apply: proof_irr.
  by rewrite get.
}
{ move=> ?????????? pf get init aft ??? pf'; have ->: pf' = pf by apply: proof_irr.
  by rewrite get.
}
Qed.

Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
Proof. by move/ltP. Qed.

Definition at_external (tp : thread_pool) 
  : option (external_function * signature * seq val) := 
  let: n := counter tp in
  let: tid0 := schedule n in
  match lt_dec tid0 (num_threads tp) with
    | left lt_pf => 
      let: tid := Ordinal (my_ltP lt_pf) in
      match getThreadC tp tid with 
        | Krun c => 
          match semantics.at_external the_sem c with
            | None => None
            | Some (ef, sg, args) => 
              if handled ef then None 
              else Some (ef, sg, args)
          end
        | Kstage _ _ _ => None
      end
    | right _ => None
  end.

Definition after_external (ov : option val) (tp : thread_pool) :=
  let: n := counter tp in
  let: tid0 := schedule n in
  match lt_dec tid0 (num_threads tp) with
    | left lt_pf => 
      let: tid := Ordinal (my_ltP lt_pf) in
      match getThreadC tp tid with 
        | Krun c => 
          match semantics.after_external the_sem ov c with
            | None => None
            | Some c' => Some (schedNext (updThreadC tp tid (Krun c')))
          end
        | Kstage _ _ _ => None
      end
    | right _ => None
  end.

Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

Section InitialCore.

  Variable ge : Genv.t (Modsem.F sem) (Modsem.V sem).

Definition initial_core (f : val) (args : list val) : option thread_pool :=
  match initial_core the_sem ge f args with
    | None => None
    | Some c => 
      Some (ThreadPool.mk 
              one_pos 
              (fun tid => if tid == ord0 then Krun c 
                          else Krun c (*bogus value; can't occur*))
              (fun tid => if tid == ord0 then emptyPermMap 
                          else emptyPermMap)
              0)
  end.

End InitialCore.

Definition halted (tp : thread_pool) : option val := None.

Program Definition semantics :
  CoreSemantics (Genv.t (Modsem.F sem) (Modsem.V sem)) thread_pool mem :=
  Build_CoreSemantics _ _ _
    initial_core
    at_external
    after_external
    halted
    step
    _ _ _.
Next Obligation.
rewrite /at_external.
case Hlt: (lt_dec _ _)=> //[a].
case Hget: (getThreadC _ _)=> //[c].
case Hat: (semantics.at_external _ _)=>[[[ef sg]  args]|//].
case Hhdl: (handled _)=> //.
elimtype False; apply: (step_inv (my_ltP a) Hget Hat Hhdl H).
Qed.
  
End Concur. End Concur.

(*MOVE to core/semantics_lemmas.v*)
Lemma corestepN_fun {G C M} {sem : CoreSemantics G C M} {c m c' m' c'' m'' n ge}
  (Hfun : corestep_fun sem) :
  corestepN sem ge n c m c' m' ->
  corestepN sem ge n c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
move: c m; elim: n=> /=.
{ by move=> c m; case=> <- <-; case=> <- <-. }
{ move=> n IH c m; case=> x []y []H H2 []z []w []H3 H4.
  case: (Hfun _ _ _ _ _ _ _ H H3)=> ??; subst.
  by case: (IH _ _ H2 H4)=> <- <-.
}
Qed.

Lemma corestepN_fun_cant {G C M} {sem : CoreSemantics G C M} 
      {c m c' m' c'' m'' ge}
      {n n' : nat}
      (Hfun : corestep_fun sem) :
  corestepN sem ge n c m c' m' ->
  corestepN sem ge n' c m c'' m'' -> 
  cant_step sem c' -> 
  cant_step sem c'' -> 
  c'=c'' /\ m'=m''.
Proof. 
move=> H H2 H3 H4. 
suff: n = n'.
by move=> ?; subst; apply: (corestepN_fun Hfun H H2).
elim: n n' c m H H2 H3 H4=> /=. 
{ move=> n' c m H H2 c1 c2.
case: n' H2=> n'; elim: n'=> //. 
case: H=> -> -> /=; case=> ? []? []H2 _.
by eapply cant_step_step in H2.
{ 
  case: H=> -> -> /= n H []c3 []m3 []H2 []c4 []m4 []H3 H4.
  clear - c1 H2; elimtype False.
  by eapply cant_step_step; eauto.
}
}
move=> n IH n' c m []c2 []m2 []H H2 H3 H4 H5.
case: n' H3.
{ 
  simpl; case=> ??; subst.
  by elimtype False; eapply cant_step_step; eauto.
}
move=> n' /= []c3 []m3 []H6 H7.
case: (Hfun _ _ _ _ _ _ _ H H6)=> ??; subst.
by move: (IH _ _ _ H2 H7 H4 H5)=> <-.
Qed.

Section ConcurLemmas.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable aggelos : nat -> perm_map.
Variable schedule : nat -> nat.

Notation thread_sem := (@Concur.semantics sem aggelos schedule).

Lemma thread_det :
  semantics_lemmas.corestep_fun the_sem ->
  semantics_lemmas.corestep_fun thread_sem.
Proof. 
move=> Hfun m m' m'' ge tp tp' tp''; case; move {tp tp' m m'}.
{ move=> tp m c m' c' n pf get cant step0 step.
  case: step pf get step0 cant; move {tp tp'' m''}.
  + move=> tp m'' c'' m''' c''' n' pf get step cant' pf'; move: get step.
    have ->: pf' = pf by apply: proof_irr.
    move=> -> step; case=> <- cant'' step'.
    by case: (corestepN_fun_cant Hfun step step')=> // <- <-; split.
  + move {m}=> tp m c'' b ofs pf get Hat Hhdl pf'.
    have ->: pf' = pf by apply: proof_irr.
    rewrite get; case=> <- cant step.
    simpl in step; case: step=> ? []? []step ?.
    by move: (corestep_not_at_external _ _ _ _ _ _ step); rewrite Hat.
  + move {m}=> tp tp' m c'' m'' c''' m''' b ofs pnew pf get load store aft upd inv updp pf'.
    have ->: pf' = pf by apply:proof_irr.
    by rewrite get.
  + move {m}=> tp tp' m c'' m'' c''' m''' b ofs pnew pf get load store aft upd inv updp pf'.
    have ->: pf' = pf by apply:proof_irr.
    by rewrite get.
  + move=> ?????????? pf get init aft ??? pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
}
{ move=> tp m c b ofs pf get Hat Hhdl step; 
  case: step pf get Hat Hhdl; move {tp m tp'' m''}.
  + move=> ?????? pf' get step cant pf; have <-: pf' = pf by apply: proof_irr.
    rewrite get; case=> <- H. 
    simpl in step; case: step=> ? []? []step.
    by erewrite corestep_not_at_external in H; eauto.
  + move=> ????? pf' get Hat Hhdl pf; have <-: pf' = pf by apply: proof_irr.
    by rewrite get; case=> <-; rewrite Hat; case=> -> _ -> _; split.
  + move=> ?????????? pf get ?????? pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ?????????? pf get ?????? pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ?????????? pf get init aft ??? pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
}
{ move=> tp tp' m c m''' c' m' b ofs pnew pf get load store aft upd inv updp step.
  case: step pf get upd inv updp load store; move {tp m tp'' m''}.
  + move=> ?????? pf get step0 cant pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ?????????? pf get load store aft' upd inv updp pf'. 
    have ->: pf' = pf by apply: proof_irr.
    rewrite get. case=> <- <- cs_eq upd' inv' updp' load'. rewrite store; case=> mem_eq; subst.
    by move: aft'; rewrite aft; case=> ->; move: upd'; rewrite upd; case=> ->; split.
  + move=> tp m c'' m'' c'''' m'''' b' ofs' pf get ? store aft' upd' pf'.
    have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ??????? pf get init aft' pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
}
{ move=> tp m c m''' c' m' b ofs pf get load store aft upd step. 
  case: step pf get load store aft upd; move {tp m tp'' m''}.
  + move=> ?????? pf get step cant pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ???????? pf get load store aft upd pf'. 
    have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ???????? pf get ? store aft upd pf'.
    have ->: pf' = pf by apply: proof_irr.
    rewrite get; case=> <- <- <- _; rewrite store; case=> <-.
    by rewrite aft; case=> <-; rewrite upd; split.
  + move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
}
{ move=> tp m c c' c_new vf arg pf get init aft step.
  case: step pf get init aft; move {tp m tp'' m''}.
  + move=> ?????? pf get ? cant pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ???????? pf get ? store aft upd pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ???????? pf get ? store aft upd pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get.
  + move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
    by rewrite get; case=> <- <- <-; rewrite init; case=> <-; rewrite aft; case=> <-.
}      
Qed.

End ConcurLemmas.

Module FineConcur. Section FineConcur.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable aggelos : nat -> perm_map.
Variable fschedule : nat -> nat.

Section Corestep.

Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).

Inductive fstep : thread_pool -> mem -> thread_pool -> mem -> Prop :=
  | fstep_congr : 
      forall tp m c m' (c' : Modsem.C sem),
      let: n := counter tp in
      let: tid0 := fschedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Krun c ->
      corestep the_sem the_ge c m c' m' ->
      fstep tp m (schedNext (updThread tp tid (Krun c'))) m'

  | fstep_stage :
      forall tp m c ef args,
      let: n := counter tp in
      let: tid0 := fschedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Krun c ->
      semantics.at_external the_sem c = Some (ef, ef_sig ef, args) ->
      handled ef ->
      fstep tp m (schedNext (updThread tp tid (Kstage ef args c))) m

  | fstep_lock :
      forall tp m c m'' c' m' b ofs,
      let: n := counter tp in
      let: tid0 := fschedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Kstage LOCK (Vptr b ofs::nil) c ->
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one) ->
      Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      updPermMap m'' (aggelos n) = Some m' -> 
      fstep tp m (updThread tp tid (Krun c')) m'

  | fstep_unlock :
      forall tp m c m'' c' m' b ofs,
      let: n := counter tp in
      let: tid0 := fschedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Kstage UNLOCK (Vptr b ofs::nil) c ->
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero) ->
      Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      updPermMap m'' (aggelos n) = Some m' -> 
      fstep tp m (updThread tp tid (Krun c')) m

  | fstep_create :
      forall tp m c c' c_new vf arg,
      let: n := counter tp in
      let: tid0 := fschedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThreadC tp tid = Kstage CREATE (vf::arg::nil) c ->
      semantics.initial_core the_sem the_ge vf (arg::nil) = Some c_new ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      fstep tp m (schedNext (addThread (updThread tp tid (Krun c')) (Krun c_new))) m.

End Corestep.

Lemma fstep_inv the_ge tp c m tp' m' ef sig args : 
  let: n := counter tp in
  let: tid0 := fschedule n in
  forall (tid0_lt_pf :  tid0 < num_threads tp),
  let: tid := Ordinal tid0_lt_pf in
  getThreadC tp tid = Krun c ->
  semantics.at_external the_sem c = Some (ef, sig, args) -> 
  handled ef = false -> 
  ~ fstep the_ge tp m tp' m'.
Proof. 
move=> pf get Hat; move/handledP=> Hhdl step. 
case: step pf get Hat Hhdl n; move {tp m tp' m'}.
{ move=> ????? pf get step pf'; have ->: pf' = pf by apply: proof_irr.
  intros get0 at_ext handl. rewrite get in get0. inversion get0; subst.
  
   erewrite corestep_not_at_external in at_ext; eauto. discriminate.
}
{ move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
  rewrite get; case=> <-; rewrite Hat; case=> <- /= _ _ Contra _. 
  by apply: Contra; apply/handledP.
}
{ move=> ???????? pf get Hat ??? pf'; have ->: pf' = pf by apply: proof_irr.
  by rewrite get.
}
{ move=> ???????? pf get Hat ??? pf'; have ->: pf' = pf by apply: proof_irr.
  by rewrite get.
}
{ move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
  by rewrite get.
}
Qed.

Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
Proof. by move/ltP. Qed.

Definition at_external (tp : thread_pool) 
  : option (external_function * signature * seq val) := 
  let: n := counter tp in
  let: tid0 := fschedule n in
  match lt_dec tid0 (num_threads tp) with
    | left lt_pf => 
      let: tid := Ordinal (my_ltP lt_pf) in
      match getThreadC tp tid with 
        | Krun c => 
          match semantics.at_external the_sem c with
            | None => None
            | Some (ef, sg, args) => 
              if handled ef then None 
              else Some (ef, sg, args)
          end
        | Kstage _ _ _ => None
      end
    | right _ => None
  end.

Definition after_external (ov : option val) (tp : thread_pool) :=
  let: n := counter tp in
  let: tid0 := fschedule n in
  match lt_dec tid0 (num_threads tp) with
    | left lt_pf => 
      let: tid := Ordinal (my_ltP lt_pf) in
      match getThreadC tp tid with 
        | Krun c => 
          match semantics.after_external the_sem ov c with
            | None => None
            | Some c' => Some (schedNext (updThread tp tid (Krun c')))
          end
        | Kstage _ _ _ => None
      end
    | right _ => None
  end.

Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

Section InitialCore.

Variable ge : Genv.t (Modsem.F sem) (Modsem.V sem).

Definition initial_core (f : val) (args : list val) : option thread_pool :=
  match initial_core the_sem ge f args with
    | None => None
    | Some c => 
      Some (ThreadPool.mk 
              one_pos 
              (fun tid => if tid == ord0 then Krun c 
                          else Krun c (*bogus value; can't occur*))
              0)
  end.

End InitialCore.

Definition halted (tp : thread_pool) : option val := None.

Program Definition semantics :
  CoreSemantics (Genv.t (Modsem.F sem) (Modsem.V sem)) thread_pool mem :=
  Build_CoreSemantics _ _ _
    initial_core 
    at_external
    after_external
    halted
    fstep
    _ _ _.
Next Obligation.
rewrite /at_external.
case Hlt: (lt_dec _ _)=> //[a].
case Hget: (getThreadC _ _)=> //[c].
case Hat: (semantics.at_external _ _)=>[[[ef sg]  args]|//].
case Hhdl: (handled _)=> //.
elimtype False; apply: (fstep_inv (my_ltP a) Hget Hat Hhdl H).
Qed.
  
End FineConcur.
End FineConcur.

(* Move to another file*)
Section In2.

Variable A : Type.

Variable x y : A.

Fixpoint In2 (l : seq A) {struct l} : Prop :=
  match l with
      | nil => False
      | a :: l' =>
        match l' with
          | nil => False
          | b :: l'' => (a = x /\ b = y) \/ (In2 l')
        end
  end.

Lemma in2_strengthen :
  forall zs ys,
    In2 zs ->
    In2 (ys ++ zs).
Proof.
  intros zs ys IN2.
  destruct zs. inversion IN2.
  induction ys. auto.
  destruct ys. simpl. right. assumption.
  simpl. right. auto.
Qed.

Lemma in2_trivial : forall xs ys,
  In2 (xs ++ x :: y :: ys).
Proof.
  intros xs ys. induction xs; intros. simpl; auto.
  simpl.
  destruct (xs ++ x :: y :: ys). inversion IHxs.
  right; assumption.
Qed.

Lemma In2_inv xs xmid xs' :
  In2 (xs ++ xmid :: xs') ->
  In2 (xs ++ [:: xmid]) \/
  In2 (xmid :: xs').
Proof.
  intros IN2.
  induction xs.
  - rewrite cat0s in IN2.
    right; trivial.
  - destruct xs.
    + destruct IN2 as [[E1 E2] | IN2].
      * subst.
        left; simpl; auto.
      * right; assumption.
    + destruct IN2 as [[E1 E2] | IN2].
      * subst. left; simpl; auto.
      * apply IHxs in IN2.
        destruct IN2 as [IN2 | IN2].
        { left. simpl; right; auto. }
        { right. trivial. }
Qed.

End In2.

Lemma In2_implies_In (A : eqType) (x y : A) xs :
  In2 x y xs ->
  x \in xs.
Proof.
  intros IN2.
  induction xs.
  - now destruct IN2.
  - destruct xs.
    + now destruct IN2.
    + destruct IN2 as [[? ?] | IN2]; subst.
      * by rewrite inE eqxx.
      * rewrite inE; apply/orP; right. apply IHxs; assumption.
Qed.

(* Simulation between fine and coarse grained semantics *)
Section ConcurEquiv.

  Import ThreadPool.
  Import FineConcur Concur.
  Context {sem : Modsem.t}.

  Notation thread_pool := (t sem).
  Notation the_sem := (Modsem.sem sem).
  Notation perm_map := PermMap.t.

  Variable aggelos : nat -> perm_map.

  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).


  (* Relating a fine grained and a coarse grained schedule*)
  Variable fsched : nat -> nat.
  
  Inductive schedType (n : nat) : Type :=
  | schedCore : ordinal n -> schedType n
  | schedExt : ordinal n -> schedType n.
  
  Fixpoint filter_core {m:nat} (n : ordinal m) (xs : seq (schedType m)) :=
    match xs with
      | nil => nil
      | x :: xs' =>
        match x with
          | schedCore k =>
            if beq_nat (nat_of_ord k) (nat_of_ord n) then
              filter_core n xs'
            else x :: (filter_core n xs')
          | schedExt k =>
            if beq_nat (nat_of_ord k) (nat_of_ord n) then
              xs
            else
              x :: (filter_core n xs')
        end
    end.

  Lemma length_filter_core :
    forall {m} n (xs : seq (schedType m)),
      size (filter_core n xs) <= (size xs).
  Proof.
    intros.
    induction xs as [|x xs']; simpl; auto.
    destruct x as [k | k];
      destruct (beq_nat k n); auto.
  Defined.
    
  Program Fixpoint buildSched {m} (fs : seq (schedType m))
          {measure (size fs)}:=
    match fs with
      | nil => nil
      | (schedCore n) :: fs' =>
        if has (fun x => match x with schedExt n => true | _ => false end) fs then
          (schedCore n) :: (buildSched (filter_core n fs'))
        else
          buildSched (filter_core n fs')
      | (schedExt n) :: fs' =>
        (schedExt n) :: buildSched fs'
    end.
  Solve All Obligations using
        (program_simpl;
         simpl in *;
           apply le_lt_n_Sm; apply/leP;
         apply length_filter_core).

  Definition trace :=
    {xs : seq (thread_pool * mem) |
     forall x y, In2 x y xs ->
                 fstep aggelos fsched the_ge (fst x) (snd x) (fst y) (snd y)}.

  Lemma pf1 : 1 < 5. auto. Defined.
  Lemma pf2 : 2 < 5. auto. Defined.
  
  Eval compute in buildSched ((schedCore (Ordinal pf1)) ::
                                                        (schedCore (Ordinal pf2)) ::
                                                        (schedCore (Ordinal pf1)) ::
                                              (schedCore (Ordinal pf2)) ::
                                              (schedExt (Ordinal pf1)) ::
                                              (schedExt (Ordinal pf2)) ::
                                              (schedCore (Ordinal pf2)) :: nil).
  
  Definition traceSched (xs : trace

  
  Require Import Coq.Relations.Relation_Operators.

  Definition multifine sched :=
    clos_trans _ (fun p1 p2 => fstep aggelos sched the_ge
                                     (fst p1) (snd p1) (fst p2) (snd p2)).

  Lemma csched_exists :
    forall {m} (pf: m > 0) (fs : seq (schedType m)) (counter : nat),
    exists (csched : nat -> nat),
      forall i,
        i < size (buildSched fs) ->
        csched (counter + i) =
        nth 0
            (map (fun (x : schedType m) => match x with
                        | schedCore n => nat_of_ord n
                        | schedExt n => nat_of_ord n
                                           end) (buildSched fs)) i.
  Proof.
    intros.
    generalize dependent (buildSched fs).
    apply last_ind.
    { simpl.
      exists (fun (n : nat) => 0).
      intros ? Hcontra.
      exfalso. by rewrite ltn0 in Hcontra. }
    { intros cs c IHcs.
      destruct IHcs as [csched IHcs].
      exists (fun n => if n == (counter0 + size cs) then
                         nat_of_ord (match c with
                                       | schedCore k => k
                                       | schedExt k => k end)
                       else csched n).
      intros i Hsize.
      rewrite size_rcons ltnS leq_eqVlt in Hsize.
      move/orP:Hsize => [/eqP Heq | Hprev].
      { subst. rewrite eq_refl.
        erewrite nth_map.
        erewrite nth_rcons. rewrite ltnn eq_refl.
        case c; auto.
          by rewrite size_rcons. }
      { rewrite ifN_eq.
        specialize (IHcs i Hprev).
        erewrite nth_map in *; auto.
        erewrite nth_rcons. rewrite Hprev. eauto.
        rewrite size_rcons. auto.
        apply contraNneq with (b:= false). auto. move/eqP => Hcontra. exfalso.
        rewrite eqn_add2l in Hcontra.
        move/eqP: Hcontra => Hcontra. subst. by rewrite ltnn in Hprev.
        auto.
        Grab Existential Variables. auto.
        auto. auto.
      }
    }
  Qed. 

End ConcurEquiv.