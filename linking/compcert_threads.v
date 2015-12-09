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

(* tactics to support Omega for ssrnats*)
Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [andb _ _] |- _ => let H0 := fresh in case/andP: H => H H0
    | H : context [orb _ _] |- _ => case/orP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?R] |- _ => move/ltP : H => H
    | H : context [?L == ?R] |- _ => move/eqP : H => H
    | H : context [addn ?L ?R] |- _ => rewrite -plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite -multE in H
    | H : context [subn ?L ?R] |- _ => rewrite -minusE in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  rewrite ?NatTrec.trecE -?plusE -?minusE -?multE -?leqNgt -?ltnNge;
  repeat match goal with
    | |- is_true (andb _ _) => apply/andP; split
    | |- is_true (orb _ _) => try apply/orP
    | |- is_true (_ <= _) => try apply/leP
    | |- is_true (_ < _) => try apply/ltP
  end.

Ltac ssromega :=
  repeat arith_hypo_ssrnat2coqnat;
  arith_goal_ssrnat2coqnat; simpl;
  omega.

Class monad (mon : Type -> Type) :=
  {
    ret : forall {A : Type},  A -> mon A;
    bind : forall {A B : Type}, mon A -> (A -> mon B) -> mon B
  }.

Notation "x >>= f" := (bind x f) (at level 40, left associativity).
Notation "'do!' X <- A ; B" := (bind A (fun X => B))
                                 (at level 200, X ident, A at level 100, B at level 200).
  
Global Instance optionMonad : monad option :=
  {
    ret A x := Some x;
    bind A B x f :=
        match x with
          | Some y => f y
          | None => None
        end
  }.

Definition access_map := Maps.PMap.t (Z -> perm_kind -> option permission).

Module PermMap. Section PermMap.
                  
(* Per-thread permission maps. Debatable whether we want a nextblock field *)
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

  Lemma perm_union_comm :
    forall p1 p2,
      perm_union p1 p2 = perm_union p2 p1.
  Proof.
    intros. destruct p1 as [p1|];
      destruct p2 as [p2|];
    try destruct p1, p2; simpl in *; reflexivity.
  Defined.

  Lemma perm_union_result : forall p1 p2 pu (Hunion: perm_union p1 p2 = Some pu),
                              pu = p1 \/ pu = p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1, p2; simpl in Hunion; try discriminate;
            try inversion Hunion; subst; auto.
  Defined.

  Lemma perm_union_ord : forall p1 p2 pu (Hunion: perm_union p1 p2 = Some pu),
                           Mem.perm_order'' pu p1 /\ Mem.perm_order'' pu p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1, p2; simpl in Hunion; try discriminate;
            try inversion Hunion; subst; unfold Mem.perm_order''; split; constructor.
  Defined.
    
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

  Lemma perm_max_comm :
    forall p1 p2,
      perm_max p1 p2 = perm_max p2 p1.
  Proof.
    intros. destruct p1 as [p1|];
      destruct p2 as [p2|];
    try destruct p1, p2; simpl in *; reflexivity.
  Defined.

  Lemma perm_max_result : forall p1 p2 pu (Hmax: perm_max p1 p2 = pu),
                            pu = p1 \/ pu = p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1, p2; simpl in Hmax; try rewrite Hmax; auto.
    destruct p1; auto. destruct p2; auto.
  Defined.

  Lemma perm_max_ord : forall p1 p2 pu (Hmax: perm_max p1 p2 = pu),
                           Mem.perm_order'' pu p1 /\ Mem.perm_order'' pu p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
    try destruct p1; try destruct p2; simpl in Hmax; try discriminate; subst; unfold Mem.perm_order'';
    split; constructor.
  Defined.

  Lemma permOrd_monotonic :
    forall p1c p1m p2c p2m pu
           (Hp1: Mem.perm_order'' p1m p1c)
           (Hp2: Mem.perm_order'' p2m p2c)
           (Hpu: perm_union p1c p2c = Some pu),
      Mem.perm_order'' (perm_max p1m p2m) pu.
  Admitted.

  (* Update the memory with a new permission map (of the same size) *)
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

    (* Currently unused definition of what it union of two permission maps means*)
    Inductive isUnionPermMaps : PermMap.t -> PermMap.t -> PermMap.t -> Prop :=
    | PMapsUnion :
        forall pmap1 pmap2 pmap3
               (Hnext:
                  (Coqlib.Plt (PermMap.next pmap1) (PermMap.next pmap2) ->
                   PermMap.next pmap3 = PermMap.next pmap1)
                  /\ (~ Coqlib.Plt (PermMap.next pmap1) (PermMap.next pmap2) ->
                      PermMap.next pmap3 = PermMap.next pmap2))
               (HmapCur: forall (b : positive) (ofs : Z) (p1 p2 : option permission),
                           Maps.PMap.get b (PermMap.map pmap1) ofs Cur = p1 ->
                           Maps.PMap.get b (PermMap.map pmap2) ofs Cur = p2 ->
                           exists p3, perm_union p1 p2 = Some p3 /\
                           Maps.PMap.get b (PermMap.map pmap3) ofs Cur = p3)
               (HmapMax: forall (b : positive) (ofs : Z) (p1 p2 : option permission),
                           Maps.PMap.get b (PermMap.map pmap1) ofs Max = p1 ->
                           Maps.PMap.get b (PermMap.map pmap2) ofs Max = p2 ->
                           Maps.PMap.get b (PermMap.map pmap3) ofs Max = perm_max p1 p2),
          isUnionPermMaps pmap1 pmap2 pmap3.
 
End permMapDefs.

Module ThreadPool. Section ThreadPool.

  Variable sem : Modsem.t.

  Notation cT := (Modsem.C sem).

  Inductive ctl : Type :=
  | Krun : cT -> ctl
  | Kstage : external_function -> list val -> cT -> ctl.

  (* Per-thread disjointness definition*)
  Definition permMapsDisjoint pmap1 pmap2 : Prop :=
    forall b ofs, exists pu,
      perm_union (Maps.PMap.get b (PermMap.map pmap1) ofs Cur)
                 (Maps.PMap.get b (PermMap.map pmap2) ofs Cur) = Some pu.
  
  Record t := mk
                { num_threads : pos
                  ; pool :> 'I_num_threads -> ctl
                  ; perm_maps : 'I_num_threads -> PermMap.t
                  ; schedule : list nat
                  ; counter : nat (* for angel *)
                  ; race_free : forall tid0 tid0' (Htid0 : tid0 < num_threads)
                                       (Htid0' : tid0' < num_threads) (Htid: tid0 <> tid0'),
                                  permMapsDisjoint (perm_maps (Ordinal Htid0))
                                                   (perm_maps (Ordinal Htid0'))
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
Notation num_threads := (@ThreadPool.num_threads sem tp).
Notation thread_pool := (t sem).
     
Definition newPermMap_wf pmap :=
  forall tid0  (Htid0 : tid0 < num_threads),
    permMapsDisjoint ((perm_maps tp) (Ordinal Htid0)) pmap.

Require Import fintype.

Lemma unlift_m_inv : forall tid (Htid : tid < num_threads.+1) ord
            (Hunlift: unlift (ordinal_pos_incr num_threads)
                             (Ordinal (n:=num_threads.+1) (m:=tid) Htid)
                      = Some ord),
       nat_of_ord ord = tid.
Proof.
Admitted.

Lemma permMapsDisjoint_comm :
  forall pmap1 pmap2
    (Hdis: permMapsDisjoint pmap1 pmap2),
    permMapsDisjoint pmap2 pmap1.
Proof.
  unfold permMapsDisjoint in *.
  intros. destruct (Hdis b ofs) as [pu Hpunion].
  rewrite perm_union_comm in Hpunion.
  eexists; eauto.
Qed.
  
Definition addThread (c : ctl) (pmap : {pmap | newPermMap_wf pmap}) : thread_pool.
  refine (let: new_num_threads := pos_incr num_threads in
          let: new_tid := ordinal_pos_incr num_threads in
          @mk sem new_num_threads
              (fun (n : 'I_new_num_threads) => 
                 match unlift new_tid n with
                   | None => c
                   | Some n' => tp n'
                 end)
              (fun (n : 'I_new_num_threads) => 
                 match unlift new_tid n with
                   | None => proj1_sig pmap
                   | Some n' => (perm_maps tp) n'
                 end)
              (schedule tp)
              ((counter tp).+1) _).
  Proof.
    intros.
    assert (Hrace := race_free tp).
    simpl in *.
    match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ord0|] eqn:Hget0
    end;
    match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ord1|] eqn:Hget1
    end; simpl in *. 
    - assert (Heq0: nat_of_ord ord0 =
                    nat_of_ord (Ordinal (n:=num_threads.+1) (m:=tid0) Htid0)).
      { simpl. 
        rewrite <- unlift_m_inv with (Htid := Htid0) (ord := ord0).
        reflexivity. auto.
      }
      assert (Heq1: nat_of_ord ord1 =
                    nat_of_ord (Ordinal (n:=num_threads.+1) (m:=tid0') Htid0')).
      { simpl. 
        rewrite <- unlift_m_inv with (Htid := Htid0') (ord := ord1).
        reflexivity. auto.
      }
      simpl in *. subst.
      destruct ord0, ord1; eapply Hrace; eauto.
    - destruct pmap as [pmap Hpmap_wf].
      unfold newPermMap_wf in Hpmap_wf.
      destruct ord0 as [ord0_tid ord0_pf].
      eapply Hpmap_wf.
    - destruct pmap as [pmap Hpmap_wf].
      unfold newPermMap_wf in Hpmap_wf.
      destruct ord1 as [ord1_tid ord1_pf].
      apply permMapsDisjoint_comm.
      eapply Hpmap_wf.
    - destruct (tid0 == num_threads) eqn:Heq0.
      + move/eqP:Heq0=>Heq0. subst.
        assert (Hcontra: (ordinal_pos_incr num_threads) !=
                            (Ordinal (n:=num_threads.+1) (m:=tid0') Htid0')).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra.
          inversion Hcontra; auto.
        }
        exfalso. apply unlift_some in Hcontra. rewrite Hget1 in Hcontra.
        destruct Hcontra. discriminate.
      + move/eqP:Heq0=>Heq0.
        assert (Hcontra: (ordinal_pos_incr num_threads) !=
                       (Ordinal (n:=num_threads.+1) (m:=tid0) Htid0)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra. inversion Hcontra. subst. auto. }
        exfalso. apply unlift_some in Hcontra. rewrite Hget0 in Hcontra. destruct Hcontra.
        discriminate.
  Defined.

Definition updThreadC (tid : 'I_num_threads) (c' : ctl) : thread_pool :=
  @mk sem num_threads (fun (n : 'I_num_threads) =>
                         if n == tid then c' else tp n) (perm_maps tp) 
      (schedule tp) (counter tp) (race_free tp).

Definition permMap_wf pmap tid :=
  forall tid0 (Htid0 : tid0 < num_threads) (Hneq: tid <> tid0),
    permMapsDisjoint ((perm_maps tp) (Ordinal Htid0)) pmap.
    
Definition updThreadP (tid : 'I_num_threads) (pmap : {pmap | permMap_wf pmap tid}) : thread_pool.
  refine( @mk sem num_threads tp (fun (n : 'I_num_threads) =>
                                    if n == tid then proj1_sig pmap else (perm_maps tp) n) 
              (schedule tp) (counter tp) _).
  Proof.
    intros.
    destruct (Ordinal (n:=num_threads) (m:=tid0) Htid0 == tid) eqn:Heq0,
              (Ordinal (n:=num_threads) (m:=tid0') Htid0' == tid) eqn:Heq0'.
    - move/eqP:Heq0 => Heq0. subst.
      move/eqP:Heq0' => Heq0'. inversion Heq0'. exfalso; auto.
    - destruct pmap as [pmap Hwf].
      move/eqP:Heq0=>Heq0. subst.
      apply permMapsDisjoint_comm.
      eapply Hwf. simpl; auto.
    - destruct pmap as [pmap Hwf].
      move/eqP:Heq0'=>Heq0'. subst.
      eapply Hwf. simpl; auto.
    - destruct pmap as [pmap Hwf].
      destruct tp as [? ? ? ? ? Hrace_free]; simpl in *. eapply Hrace_free; eauto.
  Defined.

  Definition updThread (tid : 'I_num_threads) (c' : ctl)
             (pmap : {pmap | permMap_wf pmap tid}) (counter' : nat) : thread_pool.
    refine (@mk sem num_threads
                (fun (n : 'I_num_threads) =>
                   if n == tid then c' else tp n)
                (fun (n : 'I_num_threads) =>
                   if n == tid then proj1_sig pmap else (perm_maps tp) n) 
                (schedule tp) (counter') _).
    Proof.
      intros.
      destruct (Ordinal (n:=num_threads) (m:=tid0) Htid0 == tid) eqn:Heq0,
                      (Ordinal (n:=num_threads) (m:=tid0') Htid0' == tid) eqn:Heq0'.
      - move/eqP:Heq0 => Heq0. subst.
        move/eqP:Heq0' => Heq0'. inversion Heq0'. exfalso; auto.
      - destruct pmap as [pmap Hwf].
        move/eqP:Heq0=>Heq0. subst.
        apply permMapsDisjoint_comm.
        eapply Hwf. simpl; auto.
      - destruct pmap as [pmap Hwf].
        move/eqP:Heq0'=>Heq0'. subst.
        eapply Hwf. simpl; auto.
      - destruct pmap as [pmap Hwf].
        destruct tp as [? ? ? ? ? Hrace_free]; simpl in *. eapply Hrace_free; eauto.
    Defined.

Definition schedNext : thread_pool :=
  @mk sem num_threads (pool tp) (perm_maps tp) (List.tl (schedule tp))
      (counter tp) (race_free tp).

Definition getThreadC (tid : 'I_num_threads) : ctl := tp tid.

Definition getThreadPerm (tid : 'I_num_threads) : PermMap.t := (perm_maps tp) tid.

Lemma no_race_wf : forall tid (pf: tid < num_threads),
                     permMap_wf (getThreadPerm (Ordinal pf)) tid.
  Proof.
    intros. unfold permMap_wf.
    assert (H:= race_free tp).
    intros. auto.
  Defined.

(*This definition is hard to use in proofs*)
Inductive permMapsInv' : nat -> PermMap.t -> Prop :=
| perm0 : forall (pf : 0 < num_threads), permMapsInv' 0 (perm_maps tp (Ordinal pf)) 
| permS : forall n (pf : n < num_threads) pprev punion,
            permMapsInv' n pprev ->
            isUnionPermMaps pprev (perm_maps tp (Ordinal pf)) punion ->
            permMapsInv' (S n) punion.

Import Maps.

Definition permMapsInv (pmap : PermMap.t) : Prop :=
  (forall tid, ~ Coqlib.Plt (PermMap.next pmap) (PermMap.next (getThreadPerm tid)))
  /\ (forall tid b ofs,
        Mem.perm_order'' (PMap.get b (PermMap.map pmap) ofs Cur)
                         (PMap.get b (PermMap.map (getThreadPerm tid)) ofs Cur))
  /\ (forall tid b ofs,
        Mem.perm_order''
          (Maps.PMap.get b (PermMap.map pmap) ofs Max)
          (Maps.PMap.get b (PermMap.map (getThreadPerm tid)) ofs Max))
  /\ (exists tid,
        PermMap.next pmap = PermMap.next (getThreadPerm tid))
  /\ (forall ofs b,
      exists tid,
        (PMap.get b (PermMap.map (perm_maps tp tid)) ofs Cur) =
        (PMap.get b (PermMap.map pmap) ofs Cur))
  /\ (forall ofs b,
      exists tid,
        (PMap.get b (PermMap.map (perm_maps tp tid)) ofs Max) =
        (PMap.get b (PermMap.map pmap) ofs Max)).

End poolDefs.

Arguments updThread {_} tp tid c' pmap counter'.
Arguments updThreadP {_} tp tid pmap.
Arguments addThread {_} tp c pmap.

Section CanonicalPMap.  
  (* Computation of a canonical form of permission maps where the default element is a function to the empty permission *)

  Import Maps.
  
  Fixpoint mkBlockList (n : nat) : list nat :=
  match n with
    | 0 => nil
    | S 0 => nil
    | S n => n :: (mkBlockList n)
  end.

Lemma mkBlockList_unfold : forall n (Hn: n > 1),
                             n :: (mkBlockList n) = mkBlockList (S n).
Proof.
  intros; simpl; destruct n. exfalso; auto.
  reflexivity.
Qed.

Lemma mkBlockList_unfold' : forall n,
                             (S n) :: (mkBlockList (S n)) = mkBlockList (S (S n)).
Proof.
  intros; reflexivity. 
Qed.
    
Lemma mkBlockList_include : forall n k (Hk: k > 0) (Hineq: k < (S (S n))),
                              List.In k (mkBlockList (S (S n))).
Proof.
  intros n. 
  induction n;
    intros.
  simpl. left. ssromega.
  rewrite <- mkBlockList_unfold'. simpl. simpl in IHn.
  destruct (beq_nat k (S (S n))) eqn:?. apply beq_nat_true in Heqb. subst.
  now left. right. apply IHn; auto;  clear IHn.
  apply beq_nat_false in Heqb. ssromega.
Qed.

Lemma mkBlockList_not_in : forall n m
                                  (Hge: m >= n)
                                  (HIn: List.In m (mkBlockList n)),
                             False.
Proof.
  intros.
  destruct n. auto.
  destruct n. auto. generalize dependent m.
  induction n; intros. simpl in HIn. destruct HIn; subst; auto.
  rewrite <- mkBlockList_unfold' in HIn.
  apply List.in_inv in HIn. destruct HIn as [? | HIn]; subst.
  rewrite ltnn in Hge. auto.
  eapply IHn. Focus 2. eauto.
  eapply leq_ltn_trans; eauto.
Qed.

Lemma mkBlockList_range:
  forall n k
         (HIn: List.In k (mkBlockList (S (S n)))),
      k < (S (S n)) /\ k > 0.
Proof.
  intro n. induction n; intros. simpl in HIn.
  destruct HIn; subst; auto.
  rewrite <- mkBlockList_unfold' in HIn.
  apply List.in_inv in HIn.
  destruct HIn as [? | HIn]; subst.
  auto. apply IHn in HIn. destruct HIn. auto.
Qed.

Fixpoint canonicalPList l m : list (positive * (Z -> perm_kind -> option permission)) :=
  match l with
    | nil => nil
    | x :: l =>
      (Pos.of_nat x, PMap.get (Pos.of_nat x) m) :: (canonicalPList l m)
  end.

Lemma canonicalPList_app : forall l m x,
                           (canonicalPList l m) ++ ((Pos.of_nat x,
                                                     PMap.get (Pos.of_nat x) m) :: nil) =
                           canonicalPList (l ++ (x :: nil)) m.
Proof.
  intro l. induction l; intros.
  reflexivity.
  simpl. apply f_equal.
  auto.
Qed.

Lemma canonicalPList_cons : forall l m x,
                           (Pos.of_nat x, PMap.get (Pos.of_nat x) m) :: (canonicalPList l m) =
                           canonicalPList (x :: l) m.
Proof.
  reflexivity.
Qed.

Lemma canonicalPList_correct : forall l m k v
                                      (HInl: List.In k l)
                                      (HInMap: List.In (Pos.of_nat k, v) (PTree.elements m.2)),
                                 List.In (Pos.of_nat k, v) (canonicalPList l m).
Proof.
  intros l m. induction l; intros; inversion HInl.
  - subst. simpl. apply PTree.elements_complete in HInMap.
    unfold PMap.get. rewrite HInMap. now left.
  - simpl. right. auto.
Qed.

Lemma canonicalPList_mkBlock_complete :
  forall k v m n
         (Hk: k > 0)
         (HIn1: List.In (Pos.of_nat k, v) (canonicalPList (mkBlockList n) m)),
    List.In k (mkBlockList n).
Proof.
  intros.
  induction n.
  simpl in *. auto.
  destruct n. simpl in HIn1. auto.
  rewrite <- mkBlockList_unfold' in HIn1.
  rewrite <- canonicalPList_cons in HIn1.
  apply List.in_inv in HIn1.
  destruct HIn1 as [Heq | HIn1].
  assert (Heqn: Pos.of_nat (S n) = Pos.of_nat k) by (inversion Heq; auto).
  apply Nat2Pos.inj_iff in Heqn.
  subst. simpl; auto.
  auto. intro Hcontra. subst. auto.
  rewrite <- mkBlockList_unfold'.
  right. auto.
Qed.
    
Lemma canonicalPList_mkBlock_det :
  forall n k v v' m
         (HIn1: List.In (Pos.of_nat k, v) (canonicalPList (mkBlockList n) m))
         (HIn2: List.In (Pos.of_nat k, v') (canonicalPList (mkBlockList n) m)),
    v = v'.
Proof.
  intros n. induction n.
  - simpl. intros. exfalso. auto.
  - intros.
    destruct n. simpl in HIn1. exfalso; auto.
    destruct n. simpl in HIn1, HIn2.
    destruct HIn1 as [HIn1 | HIn1];
      destruct HIn2 as [HIn2 | HIn2];
      inversion HIn1; inversion HIn2; now subst.
    rewrite <- mkBlockList_unfold' in HIn1, HIn2.
    rewrite <- canonicalPList_cons in HIn1, HIn2.
    apply List.in_inv in HIn1.
    apply List.in_inv in HIn2.
    destruct HIn1 as [Heq1 | HIn1].
    + destruct HIn2 as [Heq2 | HIn2].
      inversion Heq1; inversion Heq2. reflexivity.
      assert (Heq:Pos.of_nat (S (S n)) = Pos.of_nat k /\ m !! (Pos.of_nat (S (S n))) = v)
        by (inversion Heq1; auto).
      destruct Heq as [HEqk Hv].
      rewrite <- HEqk in HIn2.
      exfalso.
      clear Hv HEqk Heq1 IHn v k.
      apply canonicalPList_mkBlock_complete in HIn2.
      eapply mkBlockList_not_in in HIn2; eauto. auto.
    + destruct HIn2 as [Heq | HIn2].
      assert (Heq':Pos.of_nat (S (S n)) = Pos.of_nat k) by (inversion Heq; auto).
      rewrite <- Heq' in HIn1.
      apply canonicalPList_mkBlock_complete in HIn1; auto.
      apply mkBlockList_not_in in HIn1; auto. now exfalso.
      eauto.
Qed.
                               
Fixpoint canonicalPTree (l : list (positive * (Z -> perm_kind -> option permission))) :=
  match l with
    | nil => PTree.empty _
    | x :: l =>
      PTree.set (fst x) (snd x) (canonicalPTree l)
  end.

Lemma canonicalPTree_elements : forall l x
                                  (Hin: List.In x (PTree.elements (canonicalPTree l))),
                                  List.In x l.
Proof.
  intro l.
  induction l; intros; auto.
  simpl.
  simpl in Hin.
  unfold PTree.elements in Hin.
  destruct x as [p o].
  apply PTree.elements_complete in Hin.
  destruct (Pos.eq_dec a.1 p).
  - subst. rewrite PTree.gss in Hin. inversion Hin; subst.
    left.  destruct a; reflexivity.
  - rewrite PTree.gso in Hin; auto.
    apply PTree.elements_correct in Hin. right. auto.
Qed.

Lemma canonicalPTree_get_complete :
  forall l m k f
         (HGet: (canonicalPTree (canonicalPList l m)) ! k = Some f),
    List.In (k, f) (canonicalPList l m).
Proof.
  intro l. induction l.
  simpl. intros. rewrite PTree.gempty in HGet. discriminate.
  intros.
  rewrite <- canonicalPList_cons in HGet.
  apply PTree.elements_correct in HGet.
  apply canonicalPTree_elements in HGet.
  destruct (List.in_inv HGet) as [Heq | Hin].
  inversion Heq; subst. simpl; auto.
  auto.
Qed.
    
Lemma canonicalPTree_get_sound :
  forall n m k
         (Hk: k > 0)
         (Hn: n > 1)
         (HGet: (canonicalPTree (canonicalPList (mkBlockList n) m)) ! (Pos.of_nat k) = None),
    ~ List.In k (mkBlockList n).
Proof.
  intros.
  destruct n. simpl; auto.
  induction n. simpl; auto.
  intro HIn.
  rewrite <- mkBlockList_unfold' in HGet, HIn.
  destruct (List.in_inv HIn) as [? | HIn']; subst.
  rewrite <- canonicalPList_cons in HGet.
  unfold canonicalPTree in HGet. fold canonicalPTree in HGet.
  rewrite PTree.gss in HGet. discriminate.
  destruct n. simpl in *; auto.
  apply IHn. auto. rewrite <- canonicalPList_cons in HGet.
  unfold canonicalPTree in HGet. fold canonicalPTree in HGet.
  apply mkBlockList_range in HIn'.
  assert (k <> S (S n)). destruct HIn'. intros Hcontra; subst. auto. rewrite ltnn in H. auto.
  rewrite PTree.gso in HGet.
  assumption.
  intros HContra.
  unfold fst in HContra.
  apply Nat2Pos.inj_iff in HContra. auto. intros ?; subst; auto.
  intros ?; subst. discriminate.
  assumption.
Qed.
 
Definition canonicalPMap n m : access_map :=
  let l := mkBlockList n in
  (fun _ _ => None, canonicalPTree (canonicalPList l m)).

Lemma canonicalPMap_sound : forall k n m
                                     (Hk : k > 0)
                                     (Hkn : k < n),
                                m !! (Pos.of_nat k) = (canonicalPMap n m) !! (Pos.of_nat k).
Proof.
  intros.
  unfold PMap.get.
  destruct (((canonicalPMap n m).2) ! (Pos.of_nat k)) as [f|] eqn:HGet.
  - apply PTree.elements_correct in HGet.
    unfold canonicalPMap in HGet.  simpl in HGet.
    destruct ((m.2) ! (Pos.of_nat k)) eqn:HGet'.
    + apply PTree.elements_correct in HGet'.
      apply canonicalPTree_elements in HGet.
      apply canonicalPList_correct with (l := mkBlockList n) in HGet'.
      eapply canonicalPList_mkBlock_det; eauto.
      apply canonicalPList_mkBlock_complete in HGet. assumption.
      assumption.
    + apply PTree.elements_complete in HGet.
      apply canonicalPTree_get_complete in HGet.
      induction (mkBlockList n). simpl in HGet. by exfalso.
      simpl in HGet. destruct HGet as [Heq | Hin].
      inversion Heq; subst.
      unfold PMap.get. rewrite <- H0 in HGet'. rewrite HGet'. reflexivity.
      auto.
  - unfold canonicalPMap in HGet. simpl in HGet.
    apply canonicalPTree_get_sound in HGet.
    destruct n. exfalso. auto. destruct n. exfalso. ssromega.
    exfalso. apply HGet. apply mkBlockList_include; auto.
    assumption. clear HGet.
    eapply leq_ltn_trans; eauto.
Qed.

Lemma canonicalPMap_default : forall n k m
                                     (Hkn : k >= n),
                                (canonicalPMap n m) !! (Pos.of_nat k) = fun _ _ => None.
Proof.
  intro. induction n; intros. unfold canonicalPMap. simpl.
  unfold PMap.get.
  rewrite PTree.gempty. reflexivity.
  assert (Hkn': n <= k) by ssromega.
  unfold canonicalPMap.
  destruct n. simpl. unfold PMap.get. simpl. rewrite PTree.gempty. reflexivity.
  unfold PMap.get.
  rewrite <- mkBlockList_unfold'. rewrite <- canonicalPList_cons.
  unfold canonicalPTree.
  rewrite PTree.gso. fold canonicalPTree.
  specialize (IHn _ m Hkn').
  unfold canonicalPMap, PMap.get, snd in IHn.
  destruct ((canonicalPTree (canonicalPList (mkBlockList n.+1) m)) ! (Pos.of_nat k)); auto.
  unfold fst. intros HContra. apply Nat2Pos.inj_iff in HContra; subst; ssromega.
Qed.
    
Definition canonicalPermMap (p1 : PermMap.t) : PermMap.t.
  refine ({| PermMap.next := PermMap.next p1;
             PermMap.map := canonicalPMap (Pos.to_nat (PermMap.next p1)) (PermMap.map p1);
             PermMap.max := _;
             PermMap.nextblock := _
          |}).
  Proof.
    { intros.
      replace b with (Pos.of_nat (Pos.to_nat b)) by (rewrite Pos2Nat.id; done).
      destruct (leq (Pos.to_nat (PermMap.next p1)) (Pos.to_nat b)) eqn:Hbn.
        by rewrite canonicalPMap_default.
        erewrite <- canonicalPMap_sound. destruct p1. auto.
        apply/ltP/Pos2Nat.is_pos.
        ssromega. }
    { intros b ofs k H.
      replace b with (Pos.of_nat (Pos.to_nat b)) by (rewrite Pos2Nat.id; done).
      erewrite canonicalPMap_default. reflexivity.
      apply Pos.le_nlt in H.
      apply/leP.
      now apply Pos2Nat.inj_le.
    }
  Defined.

End CanonicalPMap.

Section PermMapConstruction.
  (* A constructive approach to computing the union of permission maps*)

  Import Maps.
  
  Definition pmap_union (pmap1 pmap2 : PermMap.t)
             (Hcanonical1: fst (PermMap.map pmap1) = fun _ _ => None)
             (Hcanonical2: fst (PermMap.map pmap2) = fun _ _ => None)
             (Hdisjoint : ThreadPool.permMapsDisjoint pmap1 pmap2) : PermMap.t.
   refine
     ({| PermMap.next := Pos.max (PermMap.next pmap1) (PermMap.next pmap2);
          PermMap.map :=
            (fun ofs kind => None,
             Maps.PTree.combine 
               (fun of1 of2 =>                  
                  let f1 := match of1 with
                              | Some f1 => f1
                              | None => (fst (PermMap.map pmap1))
                            end in
                  let f2 := match of2 with
                              | Some f2 => f2
                              | None => (fst (PermMap.map pmap2))
                            end in   
                  match of1, of2 with
                    | None, None => None
                    | _, _ => 
                      Some (fun ofs kind =>
                              let p1 := f1 ofs kind in
                              let p2 := f2 ofs kind in
                              match kind with
                                | Max =>
                                  perm_max p1 p2
                                | Cur =>
                                  match perm_union p1 p2 with
                                    | Some pu' => pu'
                                    | None => _
                                  end
                              end)
                  end)
               (snd (PermMap.map pmap1)) (snd (PermMap.map pmap2)));
          PermMap.max := _;
          PermMap.nextblock := _ |}).
   Proof.
     {
       unfold Maps.PMap.get. simpl. intros.
       rewrite PTree.gcombine.
       destruct (Hdisjoint b ofs) as [pu Hunion].
       unfold ThreadPool.permMapsDisjoint in Hdisjoint.
       destruct (((PermMap.map pmap1).2) ! b)
         as [f1|] eqn:Hget1, (((PermMap.map pmap2).2) ! b) as [f2|] eqn:Hget2.
       - unfold PMap.get in Hunion. rewrite Hget1 Hget2 in Hunion.
         rewrite Hunion.
         destruct pmap1, pmap2. simpl in *.
         unfold PMap.get in max, max0.
         eapply permOrd_monotonic; eauto.
         specialize (max b ofs). rewrite Hget1 in max. auto.
         specialize (max0 b ofs). rewrite Hget2 in max0. auto.
       - rewrite Hcanonical2. rewrite perm_max_comm.
         rewrite perm_union_comm. simpl.
         destruct pmap1. simpl in *.
         specialize (max b ofs). unfold PMap.get in max. rewrite Hget1 in max.
         destruct (f1 ofs Max) as [p|]; auto. destruct p; auto.
       - rewrite Hcanonical1. destruct pmap2. simpl in *.
         specialize (max b ofs). unfold PMap.get in max.
         rewrite Hget2 in max.  destruct (f2 ofs Max) as [p|]; auto.
       destruct p; auto.
       - constructor.
       - reflexivity.
     }
     { intros b ofs k Hnext. clear Hdisjoint.
       unfold PMap.get. rewrite PTree.gcombine.
       destruct pmap1 as [next map max nextblock],
                         pmap2 as [next2 map2 max2 nextblock2]; simpl in *.
       assert (Hnext1: ~ Coqlib.Plt b next).
       { apply Pos.le_nlt in Hnext.
         apply Pos.max_lub_l in Hnext.
         unfold Coqlib.Plt.  intro Hcontra.
         apply Pos.le_nlt in Hnext. auto.
       }
       assert (Hnext2: ~ Coqlib.Plt b next2).
       { apply Pos.le_nlt in Hnext.
         apply Pos.max_lub_r in Hnext.
         unfold Coqlib.Plt.  intro Hcontra.
         apply Pos.le_nlt in Hnext. auto.
       }
       specialize (nextblock b ofs k Hnext1).
       specialize (nextblock2 b ofs k Hnext2).
       unfold PMap.get in nextblock, nextblock2.
       destruct (map.2 ! b)
         as [f1|] eqn:Hget1, (map2.2 ! b) as [f2|] eqn:Hget2; auto;
       rewrite nextblock; rewrite nextblock2; simpl;
       destruct k; reflexivity.
       reflexivity.
       Grab Existential Variables. auto. auto.
     }
   Defined.

   Lemma pmap_union_result :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: fst (PermMap.map pmap1) = fun _ _ => None)
            (Hcanonical2: fst (PermMap.map pmap2) = fun _ _ => None)
            (Hdisjoint : ThreadPool.permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       PMap.get b (PermMap.map pmap12) ofs Cur = PMap.get b (PermMap.map pmap1) ofs Cur \/
       PMap.get b (PermMap.map pmap12) ofs Cur = PMap.get b (PermMap.map pmap2) ofs Cur.
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2;
     try match goal with
       | [H: perm_union ?Expr1 ?Expr2 = _ |- _] =>
         destruct (perm_union_result Expr1 Expr2 H) as [? | ?]; subst; rewrite H 
     end; auto. rewrite Hcanonical1. auto. reflexivity.
   Defined.

   Lemma pmap_union_result_union :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: fst (PermMap.map pmap1) = fun _ _ => None)
            (Hcanonical2: fst (PermMap.map pmap2) = fun _ _ => None)
            (Hdisjoint : ThreadPool.permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       Some (PMap.get b (PermMap.map pmap12) ofs Cur) =
       perm_union ((PermMap.map pmap1) !! b ofs Cur) ((PermMap.map pmap2) !! b ofs Cur). 
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2;
     try match goal with
       | [H: perm_union ?Expr1 ?Expr2 = _ |- _] =>
         destruct (perm_union_result Expr1 Expr2 H) as [? | ?]; subst; rewrite H 
         end; auto. rewrite Hcanonical1. reflexivity. rewrite Hcanonical2.  reflexivity.
     reflexivity.
   Defined.

   Lemma pmap_union_result_max :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: fst (PermMap.map pmap1) = fun _ _ => None)
            (Hcanonical2: fst (PermMap.map pmap2) = fun _ _ => None)
            (Hdisjoint : ThreadPool.permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       PMap.get b (PermMap.map pmap12) ofs Max =
       perm_max ((PermMap.map pmap1) !! b ofs Max) ((PermMap.map pmap2) !! b ofs Max). 
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2;
     try match goal with
       | [H: perm_union ?Expr1 ?Expr2 = _ |- _] =>
         destruct (perm_union_result Expr1 Expr2 H) as [? | ?]; subst; rewrite H 
         end; auto. rewrite Hcanonical1 Hcanonical2. reflexivity. reflexivity.
   Defined.

   Lemma pmap_union_ord :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: fst (PermMap.map pmap1) = fun _ _ => None)
            (Hcanonical2: fst (PermMap.map pmap2) = fun _ _ => None)
            (Hdisjoint : ThreadPool.permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs k,
       Mem.perm_order'' (PMap.get b (PermMap.map pmap12) ofs k)
                        (PMap.get b (PermMap.map pmap1) ofs k) /\
       Mem.perm_order'' (PMap.get b (PermMap.map pmap12) ofs k)
                        (PMap.get b (PermMap.map pmap2) ofs k).
   Proof.
     intros. unfold pmap_union in Hunion.
     rewrite <- Hunion. simpl. clear Hunion.  destruct (Hdisjoint b ofs) as [pu Hpu].
     unfold PMap.get in *. simpl. rewrite PTree.gcombine.
     destruct ((PermMap.map pmap1).2 ! b) as [f1|] eqn:Hget1;
       destruct ((PermMap.map pmap2).2 ! b) as [f2|] eqn:Hget2; destruct k;
       try rewrite Hpu;
       try match goal with
         | [|- context[Max]] => eapply perm_max_ord
         | [|- context[Cur]] => eapply perm_union_ord
       end; eauto.
     rewrite Hcanonical1 Hcanonical2. reflexivity.
     rewrite Hcanonical1 Hcanonical2. reflexivity.
     reflexivity.
   Defined.
   
   Lemma pmap_union_canonical :
     forall pmap1 pmap2 pmap12
            (Hcanonical1: fst (PermMap.map pmap1) = fun _ _ => None)
            (Hcanonical2: fst (PermMap.map pmap2) = fun _ _ => None)
            (Hdisjoint : ThreadPool.permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12),
       (PermMap.map pmap12).1 = fun _ _ => None.
     intros. rewrite <- Hunion. unfold pmap_union. simpl. reflexivity.
   Defined.
       
   Lemma pmap_union_inv :
     forall (pmap1 pmap2 pmap3 pu12 : PermMap.t)
            (Hcanonical1 : fst (PermMap.map pmap1) = fun _ _ => None)
            (Hcanonical2 : fst (PermMap.map pmap2) = fun _ _ => None)
            (Hcanonical3 : fst (PermMap.map pmap3) = fun _ _ => None)
            (Hdisjoint12: ThreadPool.permMapsDisjoint pmap1 pmap2)
            (Hdisjoint13: ThreadPool.permMapsDisjoint pmap1 pmap3)
            (Hdisjoint23: ThreadPool.permMapsDisjoint pmap2 pmap3)
            (Hunion12: pmap_union Hcanonical1 Hcanonical2 Hdisjoint12 =
                       pu12),
     exists pf pu, pmap_union (pmap_union_canonical Hunion12) Hcanonical3 pf = pu.
   Proof.
     intros.
     assert (pf : ThreadPool.permMapsDisjoint (pu12) (pmap3)).
     { unfold ThreadPool.permMapsDisjoint in *. intros b ofs.
       destruct (Hdisjoint12 b ofs) as [p12 Hp12],
                (Hdisjoint13 b ofs) as [p13 Hp13],
                                       (Hdisjoint23 b ofs) as [p23 Hp23].
       destruct (pmap_union_result Hunion12 b ofs) as [Hu12 | Hu12];
         rewrite Hu12; eexists; eauto.
     }
     exists pf.
     eexists. eauto.
   Defined.

   Context {sem : Modsem.t}.
   Variable (tp : ThreadPool.t sem).
   
   Import ThreadPool.
   
   Notation num_threads := (@ThreadPool.num_threads sem tp).

   Lemma permMapsUnion_oblig1:
     forall {A:Type} (l : seq A)
            (p : A) (l' : seq A) (Heq : p :: l' = l),
       List.In p l.
   Proof.
     intros. rewrite <- Heq. left. reflexivity.
   Defined.

   Lemma zero_numthreads : 0 < num_threads.
   Proof. destruct num_threads; ssromega. Defined.


   Require Import Coq.Sorting.Sorted.
   Definition ord_lt := fun (x y : 'I_num_threads)  => (nat_of_ord x) < (nat_of_ord y).

   Lemma ord_lt_trans : Relations_1.Transitive ord_lt.
   Proof.
     unfold Relations_1.Transitive. intros x y z Hxy Hyz.
     unfold ord_lt in *. ssromega.
   Defined.

   Definition ord_step := fun (x y : 'I_num_threads) => S (nat_of_ord x) = (nat_of_ord y).

   Definition base_pf : ((n num_threads)-1) < (n num_threads).
     destruct num_threads.
     ssromega.
   Defined.
   
   Inductive threadSeq : nat -> list 'I_num_threads -> Type :=
   | thrSeqN : forall pf,
       threadSeq ((n num_threads)-1) [:: @Ordinal num_threads ((n num_threads) -1) pf]
   | thrSeqS : forall thrSeq i pf
                  (Hseq: threadSeq (S i) thrSeq),
                  threadSeq i ((@Ordinal num_threads i pf) :: thrSeq).

   Definition threadSeq_ordpf {i l} (ts : threadSeq (S i) l) : is_true (i < (n num_threads)).
   Proof.
     inversion ts as [|? ? ? Hts']; subst; clear ts. destruct num_threads. ssromega.
          clear Hts'. destruct num_threads.  simpl in *. ssromega.
   Defined.

   Definition elim_eq_thr {a b l} (Ha: threadSeq a l) :
     forall (H: a == b), threadSeq b l.
     move/eqP=>H. by subst.
   Defined.
                        
   Definition threadsList : sigT (threadSeq 0).
     refine (let fix aux i acc (pf_acc: threadSeq i acc) :=
                 match i with
                   | 0 => fun (Heq : i == 0) =>
                            existT (threadSeq 0) acc _
                   | S n => fun (Heq : i == S n) =>
                              aux n ((@Ordinal
                                        num_threads n (threadSeq_ordpf (elim_eq_thr pf_acc Heq)))
                                       :: acc) _
                 end (eq_refl i)
             in aux ((n num_threads) - 1) [:: @Ordinal num_threads ((n num_threads)-1) base_pf]
                    (thrSeqN base_pf)).
     Proof.
       {move/eqP:Heq=>Heq; by subst. }
       { assert (i = S n) by (move/eqP:Heq; by subst).
         subst. constructor. assumption. }
     Defined.

     Lemma threadSeq_size_pos : forall n l (Hseq: threadSeq n l),
                              size l > 0.
     Proof.
       intros. inversion Hseq; simpl; auto.
     Defined.

     Lemma threadSeq_val : forall n x l (Hl: threadSeq n (x :: l)),
                             n = nat_of_ord x.
     Proof.
       intros. inversion Hl; subst; reflexivity.
     Defined.

     Lemma threadSeq_step : forall n l (Hl: threadSeq n l),
       Sorted ord_step l.
     Proof.
       intros n l. generalize dependent n. induction l as [|a l'].
       - intros. inversion Hl.
       - intros.
         destruct l'. constructor; auto.
         inversion Hl; subst. apply threadSeq_val in Hseq.
         inversion Hl as [|? ? ? Hseq0]; subst.
         constructor. eapply IHl'; eauto.
         constructor. unfold ord_step. rewrite <- Hseq. reflexivity.
     Defined.

     Lemma threadSeq_lt : forall n l (Hl: threadSeq n l),
       Sorted ord_lt l.
     Proof.
       intros n l. generalize dependent n. induction l as [|a l'].
       - intros. inversion Hl.
       - intros.
         destruct l'. constructor; auto.
         inversion Hl; subst. apply threadSeq_val in Hseq.
         inversion Hl as [|? ? ? Hseq0]; subst.
         constructor. eapply IHl'; eauto.
         constructor. unfold ord_lt. rewrite <- Hseq. simpl. ssromega.
     Defined.

     Lemma leq_pf_irr : forall n m (H1 : n < m) (H2: n < m), H1 = H2.
     Proof.
       intros. eapply Eqdep_dec.eq_proofs_unicity; intros x y; destruct x,y; auto.
     Defined.
     
     Lemma threadSeq_complete : forall tid i l (Hl: threadSeq i l) (Hle: i <= tid)
                                       (Hmax: tid <= num_threads -1),
                                exists (pf': tid < num_threads), List.In (Ordinal pf') l.
     Proof.
       intros tid i l. generalize dependent tid. generalize dependent i.
       induction l.
       - intros. inversion Hl.
       - intros. inversion Hl; subst.
         assert (H: tid = num_threads -1) by ssromega.
         rewrite H. exists pf. left. reflexivity.
         rewrite leq_eqVlt in Hle.
         move/orP:Hle=>[Heq | Hlt].
         + move/eqP:Heq=>Heq. subst. exists pf. left; auto.
         + specialize (IHl _ _ Hseq Hlt Hmax). destruct IHl as [pf' HIn].
           exists pf'. right. assumption.
     Defined.
         
     Definition subSeq {T:eqType} (s1 s2 : seq T) :=
       drop ((size s2)-(size s1)) s2 == s1.
     
     Lemma dropS:
       forall {T:Type} n (x:T) l l'
              (Hdrop: drop n l = x :: l'), drop n.+1 l = l'.
     Proof.
       intros. generalize dependent n.
       induction l; intros. simpl in *. discriminate.
       simpl in *. destruct n. inversion Hdrop; subst. apply drop0.
       eapply IHl; eassumption.
     Defined.

     Lemma drop_size_lt : forall {T : Type} (s s' : seq T) n
                                 (Hdrop: drop n s = s'),
                            size s >= size s'.
     Proof.
       intros T s. induction s; intros.
       destruct n; simpl in Hdrop; rewrite <- Hdrop; auto.
       simpl in *. destruct n. rewrite <- Hdrop. auto.
       eapply IHs in Hdrop. ssromega.
     Defined.

     Lemma subSeq_cons : forall {T:eqType} x (s' s : seq T) (Hneq: s' <> x :: s)
                                (Hsub: subSeq s' (x :: s)), subSeq s' s.
     Proof.
       unfold subSeq. intros.
       simpl in Hsub. destruct ((size s).+1 - size s') eqn:Hn.
       exfalso; move/eqP:Hsub=>Hsub. auto.
       replace (size s - size s') with n by ssromega.
       assumption.
     Defined.
      
     Lemma threadSeq_size : forall i l (Hseq: threadSeq i l), size l = ((n num_threads) - i).
     Proof.
       intros i l. generalize dependent i. induction l; intros.
       - inversion Hseq.
       - inversion Hseq as [|? ? ? Hseq']; subst.
         simpl. clear Hseq IHl. destruct num_threads. ssromega.
         simpl. eapply IHl in Hseq'.
         clear Hseq IHl. destruct num_threads.
         simpl in *. ssromega.
     Defined.
         
     Lemma threadSeq_subSeq : forall i l l' (Hseq: threadSeq i l) (Hsub: subSeq l' l)
                                      (Hl' : l' <> nil),
                                 threadSeq ((n num_threads) - (size l')) l'.
     Proof.
       intros. generalize dependent l'. generalize dependent i.
       induction l; intros.
       unfold subSeq in Hsub. simpl in Hsub. exfalso. move/eqP:Hsub. auto.
       inversion Hseq as [|? ? ? Hseq']; subst.
       - simpl in *.
         unfold subSeq in Hsub. simpl in Hsub.
         destruct (1- size l') as [|n] eqn:Hn. move/eqP:Hsub=>Hsub.
         rewrite <- Hsub. simpl. constructor.
         exfalso; move/eqP:Hsub=>Hsub; auto.
       - unfold subSeq in Hsub. move/eqP:Hsub=>Hsub.
         simpl in Hsub.
         destruct ((size l).+1 - size l') as [|n] eqn:Hn;
         rewrite Hn in Hsub.
         rewrite <- Hsub; simpl.
         erewrite threadSeq_size; eauto.
         replace (num_threads - (num_threads - i.+1).+1) with i by
             (clear Hsub Hseq Hseq' IHl; destruct num_threads; simpl in *; ssromega).
         assumption.
         eapply IHl; eauto.
         unfold subSeq.
         assert (Heq: size l - size l' = n)
           by (destruct l'; simpl in *; ssromega).
         rewrite Heq. by move/eqP:Hsub.
     Defined.

     Lemma subSeq_det : forall {T:eqType} (s s' s'' : seq T) (Hsize: size s' = size s'')
                               (Hsub': subSeq s' s) (Hsub'': subSeq s'' s),
                          s' = s''.
     Proof.
       intros T s. induction s; intros.
       - unfold subSeq in *. simpl in *. move/eqP:Hsub'=>Hsub'. subst. move/eqP:Hsub''; auto.
       - unfold subSeq in Hsub', Hsub''. simpl in Hsub', Hsub''.
         rewrite Hsize in Hsub'.
         destruct ((size s).+1 - size s'') eqn:Heq.
         move/eqP:Hsub''. move/eqP:Hsub'. intros. destruct s'; inversion Hsub'; subst.
         reflexivity.
         apply IHs. assumption.
         unfold subSeq.
         by replace n with (size s - size s') in Hsub' by ssromega.
           by replace n with (size s - size s'') in Hsub'' by ssromega.
     Defined.

     (* For the constructive version we assumed that all perm maps are canonical *)
     Hypothesis permMapsCanonical :
       forall tid, (PermMap.map (perm_maps tp tid)).1 = fun _ _ => None.                                   
     Lemma empty_disjoint : forall pmap,
                              permMapsDisjoint pmap emptyPermMap.
     Proof.
       unfold permMapsDisjoint. intros.
       unfold PMap.get. simpl. rewrite PTree.gempty.
       unfold perm_union. destruct ((PermMap.map pmap).2 !b) eqn:Hget;
       match goal with
         | [ |- context[match ?Expr with | _ => _ end]] => destruct Expr
       end; eexists; reflexivity.
     Defined.

     Lemma in_rcons : forall {T:Type} x y (s : seq T) (HIn: List.In x (rcons s y)),
                        x = y \/ List.In x s.
     Proof.
       intros. induction s.
       - simpl in HIn. destruct HIn; auto.
         simpl in HIn. destruct HIn as [|HIn]; subst.
         right. simpl. left. reflexivity.
         apply IHs in HIn. destruct HIn; subst; auto.
         right. simpl. auto.
     Defined.

     Lemma in_rcons_refl : forall {T:Type} x (s : seq T),
                             List.In x (rcons s x).
     Proof.
       intros. induction s. simpl. by left.
       simpl. by right.
     Defined.

     Lemma in_rcons_weaken:
       forall {T:Type} x y (s : seq T) (HIn: List.In x s),
         List.In x (rcons s y).
     Proof.
       intros. induction s.
       - inversion HIn.
       - inversion HIn; subst. simpl. by left.
         simpl. right. auto.
     Defined.
                             
     Definition permMapsUnion : {p : PermMap.t | permMapsInv tp p}.
       refine (let fix aux l
                       acc (Hl': forall x, List.In x l -> permMapsDisjoint (perm_maps tp x) acc)
                       (Hacc: (PermMap.map acc).1 = fun _ _ => None)
                       (Hsub: subSeq l (tag threadsList))
                       (Hnext: forall x lhd (Hlst: (tag threadsList) = lhd ++ l)
                                      (HIn: List.In x lhd),
                                 ~ Coqlib.Plt (PermMap.next acc) (PermMap.next (getThreadPerm tp x)))
                       (Hperm_ord: forall tid b ofs k lhd (Hlst: (tag threadsList) = lhd ++ l)
                               (HIn: List.In tid lhd),
                          Mem.perm_order'' ((PermMap.map acc) !! b ofs k)
                                           ((PermMap.map (getThreadPerm tp tid)) !! b ofs k))
                       (Hinit: tag threadsList = l -> acc = emptyPermMap)
                       (Hinv_eq: forall lhd (Hlhd: lhd <> [::]) (Hlst: (tag threadsList) = lhd ++ l),
                                  (exists tid, List.In tid lhd /\
                                               PermMap.next acc = PermMap.next (getThreadPerm tp tid))
                                  /\ (forall (ofs : Z) (b : positive),
                                      exists tid : 'I_num_threads, List.In tid lhd /\
                                        (PermMap.map (perm_maps tp tid)) !! b ofs Cur =
                                        (PermMap.map acc) !! b ofs Cur)
                                  /\ (forall (ofs : Z) (b : positive),
                                      exists tid : 'I_num_threads, List.In tid lhd /\
                                        (PermMap.map (perm_maps tp tid)) !! b ofs Max =
                                        (PermMap.map acc) !! b ofs Max))
                   :=
                   match l with
                     | nil => fun Heq =>
                                  exist (fun p => permMapsInv tp p) acc _
                     | tid :: l' =>
                       fun (Heq: tid :: l' = l) =>
                         let p := perm_maps tp tid in
                         aux l'
                             (@pmap_union p acc (permMapsCanonical tid)
                                          Hacc (Hl' tid (permMapsUnion_oblig1 Heq))) _ _ _ _ _ _ _
                   end (Logic.eq_refl l)
               in aux (tag threadsList) emptyPermMap _ _ _ _ _ _ _).
       Proof.
         { (* permMapsInv *)
           clear aux. subst. split; [idtac | split; [idtac | split]].
           - intros.
             destruct tid as [tid pf].
             destruct threadsList as [l Hl].
             assert (Hle: 0 <= tid) by ssromega.
             assert (Hmax: tid <= num_threads - 1) by ssromega.
             destruct (threadSeq_complete tid Hl Hle Hmax) as [pf' HIn].
             simpl in Hnext.
             specialize (Hnext (Ordinal pf') l).
             rewrite cats0 in Hnext. specialize (Hnext (Logic.eq_refl l) HIn).
             intros Hcontra.
             assert (Hget: getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf') =
                           getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf)).
             {
               unfold getThreadPerm.
               rewrite (leq_pf_irr _ _ pf pf'). reflexivity. }
             rewrite Hget in Hnext. apply Hnext. assumption. 
           - intros.
             destruct tid as [tid pf].
             destruct threadsList as [l Hl].
             assert (Hle: 0 <= tid) by ssromega.
             assert (Hmax: tid <= num_threads - 1) by ssromega.
             destruct (threadSeq_complete tid Hl Hle Hmax) as [pf' HIn].
             simpl in Hnext.
             specialize (Hperm_ord (Ordinal pf') b ofs Cur l).
             rewrite cats0 in Hperm_ord. specialize (Hperm_ord (Logic.eq_refl l) HIn).
             assert (Hget: getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf') =
                           getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf)).
             {
               unfold getThreadPerm.
               rewrite (leq_pf_irr _ _ pf pf'). reflexivity. }
             rewrite Hget in Hperm_ord.  assumption.
           - intros.
             destruct tid as [tid pf].
             destruct threadsList as [l Hl].
             assert (Hle: 0 <= tid) by ssromega.
             assert (Hmax: tid <= num_threads - 1) by ssromega.
             destruct (threadSeq_complete tid Hl Hle Hmax) as [pf' HIn].
             simpl in Hnext.
             specialize (Hperm_ord (Ordinal pf') b ofs Max l).
             rewrite cats0 in Hperm_ord. specialize (Hperm_ord (Logic.eq_refl l) HIn).
             assert (Hget: getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf') =
                           getThreadPerm tp (Ordinal (n:=num_threads) (m:=tid) pf)).
             {
               unfold getThreadPerm.
               rewrite (leq_pf_irr _ _ pf pf'). reflexivity. }
             rewrite Hget in Hperm_ord.  assumption.
           - clear Hnext Hperm_ord. specialize (Hinv_eq (tag threadsList)).
             destruct (threadsList) as [l Hl]. simpl in *.
             assert (Hempty: l <> [::]) by (inversion Hl; intro Hcontra; discriminate).
             rewrite cats0 in Hinv_eq.
             destruct (Hinv_eq Hempty (Logic.eq_refl _)) as [Hnext [Hcur Hmax]]; clear Hinv_eq.
             split; [idtac | split].
             + clear Hcur Hmax. destruct Hnext as [tid [Hin Hnext]].
               exists tid. assumption.
             + intros ofs b. destruct (Hcur ofs b) as [tid [_ ?]].
               eexists; eassumption.
             + intros ofs b. destruct (Hmax ofs b) as [tid [_ ?]].
               eexists; eassumption.
         }
         { (* l is race free*)
           clear aux.
           intros tid' Hin.
           assert (Hdis_tid'_acc: permMapsDisjoint acc (perm_maps tp tid')).
           { apply permMapsDisjoint_comm. eapply Hl'.
             rewrite <- Heq. right; assumption. }
           destruct threadsList as [threadsListV threadsListP].
           simpl in *.
           eapply threadSeq_subSeq in threadsListP; eauto.
           apply threadSeq_lt in threadsListP.
           assert (Hdis_tid'_tid: permMapsDisjoint (perm_maps tp tid) (perm_maps tp tid')).
           { rewrite <- Heq in threadsListP.
             apply Sorted_extends in threadsListP.
             eapply List.Forall_forall with (x:=tid') in threadsListP; eauto.
             assert (Hneq: nat_of_ord tid <> nat_of_ord tid').
             { intros Hcontra. subst. unfold ord_lt in threadsListP. ssromega. }
             assert (Hrace := race_free tp).
             destruct tid as [ntid pf_tid], tid' as [ntid' pf_tid'].
             eapply Hrace. intros Hcontra; subst. eapply Hneq. simpl. reflexivity.
             apply ord_lt_trans.
           }
           assert (Hdis_tid_acc: permMapsDisjoint (perm_maps tp tid) acc).
           { eapply Hl'. rewrite <-Heq. left; auto. }
           remember ((pmap_union (permMapsCanonical tid) Hacc
                                 (Hl' tid (permMapsUnion_oblig1 Heq)))) as pu.
           symmetry in Heqpu.
           destruct (pmap_union_inv (permMapsCanonical tid') Hdis_tid'_tid Hdis_tid'_acc Heqpu)
             as [pf ?].
           rewrite Heqpu. by apply permMapsDisjoint_comm.
           rewrite <- Heq. intro. discriminate.
         }
         { (* acc is canonical*) clear aux. reflexivity. }
         { (* l is a subSeq of threadsList*)
           unfold subSeq in *.
           rewrite <- Heq in Hsub.
           simpl in Hsub.
           move/eqP:Hsub=>Hsub.
           assert (Hlt: size (tid :: l') <= size (tag threadsList))
             by (eapply drop_size_lt; eapply Hsub).
           simpl in Hlt.
           assert (Hdrop: drop ((size (tag threadsList) - (size l').+1).+1) (tag threadsList) = l')
             by (eapply dropS; eauto).
           assert (Heq': (size (tag threadsList) - (size l').+1).+1 =
                         (size (tag threadsList) - size l')) by ssromega.
           rewrite Heq' in Hdrop. move/eqP:Hdrop; auto.
         }
         { (* Hnext_rec *)
           clear aux Hinv_eq Hinit Hperm_ord.
           intros. simpl.
           destruct l as [|o l]; inversion Heq. subst o. subst l'.
           destruct lhd as [|lhd tid'] using last_ind. by inversion HIn. clear IHlhd.
           rewrite <- cats1 in Hlst.
           rewrite <- catA in Hlst. simpl in Hlst.
           assert (Hsub': subSeq (tid' :: l) (tag threadsList)).
           { unfold subSeq. rewrite Hlst.
             simpl. rewrite size_cat. simpl.
             replace ((size lhd + (size l).+1 - (size l).+1)) with (size lhd) by ssromega.
             apply/eqP.
             apply drop_size_cat. reflexivity.
           }
           assert (Heq': tid' :: l = tid :: l)
             by (eapply subSeq_det; eauto).
           inversion Heq'; subst.
           eapply in_rcons in HIn.
           destruct HIn as [|HIn]; subst.
           assert (Hp: p = getThreadPerm tp tid) by auto. rewrite Hp.
           intros Hcontra.
           unfold Coqlib.Plt in Hcontra.
           apply Pos.max_lub_lt_iff in Hcontra.
           destruct Hcontra as [Hcontra _]. by apply Pos.lt_irrefl in Hcontra.
           specialize (Hnext _ _ Hlst HIn).
           unfold Coqlib.Plt in *. intros Hcontra.
           apply Pos.max_lub_lt_iff in Hcontra.
           destruct Hcontra as [_ Hcontra]. auto.
         }
         { (*Hperm_ord rec*)
           clear aux Hnext.
           intros tid0 b ofs k lhd Hlst HIn.
           destruct l as [|o l]; inversion Heq. subst o. subst l'.
           destruct lhd as [|lhd x] using last_ind. by inversion HIn. clear IHlhd.
           rewrite <- cats1 in Hlst.
           rewrite <- catA in Hlst. simpl in Hlst.
           assert (Hsub': subSeq (x :: l) (tag threadsList)).
           { unfold subSeq. rewrite Hlst.
             simpl. rewrite size_cat. simpl.
             replace ((size lhd + (size l).+1 - (size l).+1)) with (size lhd) by ssromega.
             apply/eqP.
             apply drop_size_cat. reflexivity.
           }
           assert (Heq': x :: l = tid :: l)
             by (eapply subSeq_det; eauto).
           inversion Heq'; subst.
           eapply in_rcons in HIn.
           destruct HIn as [|HIn]; subst.
         - remember (@pmap_union p acc (permMapsCanonical tid) Hacc
                                 (Hl' tid (@permMapsUnion_oblig1 'I_num_threads (tid :: l) tid l Heq)))
             as pu eqn:Hpu.
           symmetry in Hpu.
           eapply (pmap_union_ord Hpu).
         - specialize (Hperm_ord tid0 b ofs k lhd Hlst HIn).
           remember (@pmap_union p acc (permMapsCanonical tid) Hacc
                                 (Hl' tid (@permMapsUnion_oblig1 'I_num_threads (tid :: l) tid l Heq)))
             as pu eqn:Hpu.
           symmetry in Hpu.
           eapply pmap_union_ord with (b := b) (ofs := ofs) (k := k) in Hpu.
           destruct Hpu as [_ Hacc_ord].
           eapply po_trans; eauto. }
        { (*Hinit rec*)
         clear aux Hnext Hperm_ord Hinv_eq.
         intro Hlst. exfalso. rewrite Hlst in Hsub. rewrite <- Heq in Hsub.
         unfold subSeq in Hsub. simpl in Hsub.
         move/eqP:Hsub=>Hsub.
         assert (Hcontra := drop_size_lt _ _ Hsub).
         simpl in Hcontra. ssromega.
        }
        { (*Hinv_eq rec*)
          clear aux Hnext Hperm_ord. intros.
          destruct l as [|o l]; inversion Heq. subst o. subst l'.
          destruct lhd as [|lhd x] using last_ind.
          exfalso; auto.
          clear IHlhd.
          rewrite <- cats1 in Hlst.
          rewrite <- catA in Hlst. simpl in Hlst.
          assert (Hsub': subSeq (x :: l) (tag threadsList)).
          { unfold subSeq. rewrite Hlst.
            simpl. rewrite size_cat. simpl.
            replace ((size lhd + (size l).+1 - (size l).+1)) with (size lhd) by ssromega.
            apply/eqP.
            apply drop_size_cat. reflexivity.
          }
          assert (Heq': x :: l = tid :: l)
            by (eapply subSeq_det; eauto).
          inversion Heq'; subst.
          destruct lhd as [|tid' lhd].
          - apply Hinit in Hlst. subst.
            split; [idtac | split].
            { exists tid. split. simpl. by left.
              simpl. apply Pos.max_1_r. }
            { intros. exists tid. split. simpl. auto.
              remember ((pmap_union (permMapsCanonical tid) Hacc
                                    (Hl' tid (permMapsUnion_oblig1 Heq)))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_union Hpu).
              specialize (Hres b ofs).
              rewrite Hpu.
              assert (Hgoal: Some ((PermMap.map (perm_maps tp tid)) !! b ofs Cur) =
                             Some ((PermMap.map pu) !! b ofs Cur)).
              rewrite Hres. simpl. unfold PMap.get at 3. simpl.
              rewrite PTree.gempty. unfold perm_union.
              destruct ((PermMap.map (perm_maps tp tid)) !! b ofs Cur); reflexivity.
              inversion Hgoal. reflexivity. }
            { intros. exists tid. split. simpl. auto.
              remember ((pmap_union (permMapsCanonical tid) Hacc
                                    (Hl' tid (permMapsUnion_oblig1 Heq)))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_max Hpu).
              specialize (Hres b ofs).
              rewrite Hpu. rewrite Hres. simpl. unfold PMap.get at 3. simpl.
              rewrite PTree.gempty. unfold perm_max.
              destruct ((PermMap.map (perm_maps tp tid)) !! b ofs Max) as [p0|];
                [destruct p0 |]; reflexivity.
            }      
          - assert (Hlhd': tid' :: lhd <> [::]) by (intros; discriminate).
            destruct (Hinv_eq _ Hlhd' Hlst) as [Hnext [Hcur Hmax]];
              clear Hinv_eq. split; [idtac| split].
            { simpl.
              clear Hcur Hmax. destruct Hnext as [tid'' [HIn Hnext_acc]].
              apply List.in_inv in HIn. rewrite Hnext_acc.
              destruct (Pos.max_dec (PermMap.next p) (PermMap.next (getThreadPerm tp tid'')))
                as [Hmax | Hmax].
              + exists tid. split. right.
                apply in_rcons_refl.
                assumption.
              + exists tid''. split.
                destruct HIn as [? | HIn]; auto.
                right.
                  by apply in_rcons_weaken.
                  assumption.
            }
            { clear Hnext Hmax. intros.
              destruct (Hcur ofs b) as [tid'' [HIn Hacc_cur]].
              apply List.in_inv in HIn.
              remember (pmap_union (permMapsCanonical tid) Hacc
                                   (Hl' tid (permMapsUnion_oblig1 Heq))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_union Hpu).
              specialize (Hres b ofs).
              rewrite Hpu.
              symmetry in Hres.
              apply perm_union_result in Hres. destruct Hres as [Hres | Hres];
                rewrite Hres; eexists; split; eauto.
              apply in_rcons_refl.
              destruct HIn as [? | HIn]; subst.
              simpl; by left.
              simpl. right. by apply in_rcons_weaken.
            }
            { clear Hnext Hcur. intros.
              destruct (Hmax ofs b) as [tid'' [HIn Hacc_max]].
              apply List.in_inv in HIn.
              remember (pmap_union (permMapsCanonical tid) Hacc
                                   (Hl' tid (permMapsUnion_oblig1 Heq))) as pu eqn:Hpu.
              symmetry in Hpu.
              assert (Hres := pmap_union_result_max Hpu).
              specialize (Hres b ofs).
              rewrite Hpu.
              symmetry in Hres.
              apply perm_max_result in Hres. destruct Hres as [Hres | Hres].
              exists tid. split.
              apply in_rcons_refl. auto. 
              exists tid''. split.
              destruct HIn as [? | HIn]; subst.
              simpl; by left.
              simpl. right. by apply in_rcons_weaken.
              rewrite Hacc_max. rewrite Hres. reflexivity.
            }
        }
        { (* emptyPermMap is disjoint from all maps *)
          intros tid Hin. apply empty_disjoint. }
        { (* all maps are canonical *) reflexivity. }
        { unfold subSeq. rewrite subnn. by rewrite drop0. }
        { (* Hnext init*)
          intros. destruct lhd. inversion HIn.
          assert (H: size (tag threadsList) = size ((o :: lhd) ++ tag threadsList)) by
              (rewrite <- Hlst; reflexivity).
          simpl in H. rewrite size_cat in H. exfalso. ssromega. }
        {  (*Hperm_ord init*)
          intros. destruct lhd. inversion HIn.
          assert (H: size (tag threadsList) = size ((o :: lhd) ++ tag threadsList)) by
              (rewrite <- Hlst; reflexivity).
          simpl in H. rewrite size_cat in H. exfalso. ssromega. }
        { (*Hacc init*) reflexivity. }
        { (* Hinv_eq init*)
          intros. destruct lhd. exfalso; auto.
          assert (H: size (tag threadsList) = size ((o :: lhd) ++ tag threadsList)) by
              (rewrite <- Hlst; reflexivity).
          simpl in H. rewrite size_cat in H. exfalso. ssromega. }
       Defined.
   
End PermMapConstruction.

Section poolLemmas.

Context {sem : Modsem.t} {next : block} (tp : ThreadPool.t sem).

Import ThreadPool.

Lemma gssThreadCode (tid : 'I_(num_threads tp)) c' p' counter' : 
  getThreadC (updThread tp tid c' p' counter') tid = c'.
Proof. by rewrite /getThreadC /updThread /= eq_refl. Qed.

Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' p' counter':
  tid' != tid -> getThreadC (updThread tp tid c' p' counter') tid' = getThreadC tp tid'.
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

Definition restrPermMap (tid : 'I_(num_threads tp)) m
           (Hinv: permMapsInv tp (getPermMap m)) : mem.
Proof.
  refine ({|
             Mem.mem_contents := Mem.mem_contents m;
             Mem.mem_access := PermMap.map (getThreadPerm tp tid);
             Mem.nextblock := Mem.nextblock m;
             Mem.access_max := PermMap.max (getThreadPerm tp tid);
             Mem.nextblock_noaccess := _;
             Mem.contents_default := Mem.contents_default m |}).
  destruct Hinv as [Hnext [HorderCur [HorderMax [_ [Hcur Hmax]]]]].
  intros b ofs k Hlt.
  destruct k.
  - destruct (Hmax ofs b) as [tidm Hmax'].
    specialize (Hnext tidm). simpl in Hnext.
    unfold Coqlib.Plt in *.
    assert (Hle: (PermMap.next (getThreadPerm tp tidm) <= b)%positive).
    { apply Pos.le_nlt in Hlt. apply Pos.le_nlt in Hnext.
      eapply Pos.le_trans; eauto. }
    apply Pos.le_nlt in Hle.
    assert (Hnext_tid := PermMap.nextblock (getThreadPerm tp tidm)).
    specialize (Hnext_tid b ofs Max Hle). rewrite Hnext_tid in Hmax'.
    specialize (HorderMax tid b ofs).
    rewrite <- Hmax' in HorderMax. unfold Mem.perm_order'' in HorderMax.
    destruct (Maps.PMap.get b (PermMap.map (getThreadPerm tp tid)) ofs Max) eqn:HGet; [exfalso |]; auto.
  - destruct (Hcur ofs b) as [tidc Hcur'].
    specialize (Hnext tidc). simpl in Hnext.
    unfold Coqlib.Plt in *.
    assert (Hle: (PermMap.next (getThreadPerm tp tidc) <= b)%positive).
    { apply Pos.le_nlt in Hlt. apply Pos.le_nlt in Hnext.
      eapply Pos.le_trans; eauto. }
    apply Pos.le_nlt in Hle.
    assert (Hnext_tid := PermMap.nextblock (getThreadPerm tp tidc)).
    specialize (Hnext_tid b ofs Cur Hle). rewrite Hnext_tid in Hcur'.
    specialize (HorderCur tid b ofs).
    rewrite <- Hcur' in HorderCur. unfold Mem.perm_order'' in HorderCur.
    destruct (Maps.PMap.get b (PermMap.map (getThreadPerm tp tid)) ofs Cur) eqn:HGet; [exfalso |]; auto.
Defined.
       
End poolLemmas.

Arguments restrPermMap {_} {_} tid {_} Hinv. 

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

(* This is the same as Mem.load but does not obey the permissions map. It is intented
to be used for locks only. *)
Definition load_unsafe (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) :=
   decode_val chunk
              (Mem.getN (size_chunk_nat chunk) ofs
                        (Maps.PMap.get b (Mem.mem_contents m))).

Module Concur. Section Concur.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable aggelos : nat -> perm_map.

Section Corestep.

  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).

  Lemma restrPermMap_wf : forall (tp : thread_pool) (m m': mem) tid
                                 (Hinv: permMapsInv tp (getPermMap m))
                                 (Hrestrict: restrPermMap tid Hinv = m'),
                            permMap_wf tp (getPermMap m') (nat_of_ord tid).
  Proof.
    intros. rewrite <- Hrestrict.
    unfold restrPermMap, getPermMap. simpl.
    unfold permMap_wf. intros tid' Htid' Hneq.
    unfold permMapsDisjoint. simpl.
    assert (Hrace := race_free tp).
    assert (Hneq' : tid' <> tid) by auto.
    destruct tid as [tid Htid].
    specialize (Hrace tid' tid Htid' Htid Hneq').
    unfold permMapsDisjoint in Hrace.
    auto.
  Defined.
    
  Hypothesis permMapsCanonical :
    forall (tp : thread_pool) tid, (PermMap.map (perm_maps tp tid)).1 = fun _ _ => None.

  Hypothesis corestep_permMap_wf : forall tp tid (Htid: tid < num_threads tp) c m c' m' n
                                          (Hget : getThreadC tp (Ordinal Htid) = Krun c)
                                          (Hperm: permMap_wf tp (getPermMap m) tid)
                                          (Hcore: corestepN the_sem the_ge (S n) c m c' m'),
                                     permMap_wf tp (getPermMap m') tid.
        
Inductive step : thread_pool -> mem -> thread_pool -> mem -> Prop :=
  | step_congr : 
      forall tp tp' m m1 c m1' m' (c' : Modsem.C sem) pmap1 pnew n0,
        let: n := counter tp in
        forall tid0
          (Hsched: List.hd_error (schedule tp) = Some tid0)
          (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hinv: permMapsInv tp (getPermMap m))
            (Hthread: getThreadC tp tid = Krun c)
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (HcorestepN: corestepN the_sem the_ge (S n0) c m1 c' m1')
            (Hcant: cant_step the_sem c')
            (Htp': tp' =
                   updThread tp tid (Krun c')
                             (exist _ (getPermMap m1') (corestep_permMap_wf
                                                          Htid0_lt_pf Hthread (restrPermMap_wf Hrestrict_pmap)
                                                          HcorestepN)) n)
            (Hinv': permMapsUnion tp' (permMapsCanonical tp') = pnew)
            (Hupd_mem: updPermMap m1' (sval pnew) = Some m'),
            step tp m tp' m'

  | step_stage : (*should I say something about invariants on permission maps?*)
      forall tp m c ef args,
        let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Krun c)
            (Hat_external: semantics.at_external the_sem c = Some (ef, ef_sig ef, args))
            (Hhandled: handled ef),
            step tp m (schedNext (updThreadC tp tid (Kstage ef args c))) m

  | step_lock :
      forall tp tp' m m1 c m1' c' m' b ofs pmap1 pnew,
      let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage LOCK (Vptr b ofs::nil) c)
            (Hinv: permMapsInv tp (getPermMap m))
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m1')
            (Hat_external: semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Hangel_wf: permMap_wf tp (aggelos n) tid0)
            (Htp': tp' = updThread tp tid (Krun c') (exist _ (aggelos n) Hangel_wf) (n+1))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
            step tp m tp' m'
  
  | step_unlock :
      forall tp tp' m m1 c m1' c' m' b ofs pmap1 pnew,
      let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage UNLOCK (Vptr b ofs::nil) c)
            (Hinv: permMapsInv tp (getPermMap m))
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m1')
            (Hafter_external: semantics.after_external the_sem
                                                       (Some (Vint Int.zero)) c = Some c')
            (Hangel_wf: permMap_wf tp (aggelos n) tid0)
            (Htp': tp' = updThread tp tid (Krun c') (exist _ (aggelos n) Hangel_wf) (n+1))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
            step tp m tp' m'

  | step_create :
      forall tp tp_upd tp' m m' c c' c_new vf arg pnew,
        let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage CREATE (vf::arg::nil) c)
            (Hinitial: semantics.initial_core the_sem the_ge vf (arg::nil) = Some c_new)
            (Hafter_external: semantics.after_external the_sem
                                                       (Some (Vint Int.zero)) c = Some c')
            (Hangel_wf1: permMap_wf tp (aggelos n) tid0)
            (Htp_upd: tp_upd = updThread tp tid (Krun c') (exist _ (aggelos n) Hangel_wf1) (n.+2))
            (Hangel_wf2: newPermMap_wf tp_upd (aggelos (n.+1)))
            (Htp': tp' = schedNext (addThread tp_upd (Krun c_new) (exist _ (aggelos (n.+1)) Hangel_wf2)))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m pnew = Some m'),
            step tp m tp' m'

  | step_lockfail :
      forall tp m m1 c b ofs pmap1 tid0
             (Hsched: List.hd_error (schedule tp) = Some tid0)
             (Htid0_lt_pf :  tid0 < num_threads tp),
        let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage LOCK (Vptr b ofs::nil) c)
            (Hinv: permMapsInv tp (getPermMap m))
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (Htest: load_unsafe Mint32 m1 b (Int.intval ofs) = Vint Int.zero),
            step tp m (schedNext tp) m
                 
  | step_schedfail :
      forall tp m tid0
             (Hsched: List.hd_error (schedule tp) = Some tid0)
             (Htid0_lt_pf :  tid0 >= num_threads tp),
        step tp m (schedNext tp) m.
                           
End Corestep.


Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
Proof. by move/ltP. Qed.


Definition at_external (tp : thread_pool) 
  : option (external_function * signature * seq val) := 
  let: n := counter tp in
  @bind option _ _ _ 
        (List.hd_error (schedule tp))
        (fun tid0 => match lt_dec tid0 (num_threads tp) with
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
                     end).

Definition after_external (ov : option val) (tp : thread_pool) :=
  let: n := counter tp in
  @bind option _ _ _ 
        (List.hd_error (schedule tp))
        (fun tid0 => match lt_dec tid0 (num_threads tp) with
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
                     end).
  
End Concur. End Concur.

Module FineConcur. Section FineConcur.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable aggelos : nat -> perm_map.

Section Corestep.

  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).

  Inductive step : thread_pool -> mem -> thread_pool -> mem -> Prop :=
  | fstep_core : 
      forall tp tp' m m1 c m1' m' (c' : Modsem.C sem) pmap1 pnew,
        let: n := counter tp in
        forall tid0
          (Hsched: List.hd_error (schedule tp) = Some tid0)
          (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hinv: permMapsInv tp (getPermMap m))
            (Hthread: getThreadC tp tid = Krun c)
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (Hcorestep: corestep the_sem the_ge c m1 c' m1')
            (Htp': tp' = schedNext (updThread tp tid (Krun c') (getPermMap m1') n))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
            step tp m tp' m'

  | fstep_stage : (*should I say something about invariants on permission maps?*)
      forall tp m c ef args,
        let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Krun c)
            (Hat_external: semantics.at_external the_sem c = Some (ef, ef_sig ef, args))
            (Hhandled: handled ef),
            step tp m (schedNext (updThreadC tp tid (Kstage ef args c))) m

  | fstep_lock :
      forall tp tp' m m1 c m1' c' m' b ofs pmap1 pnew,
      let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage LOCK (Vptr b ofs::nil) c)
            (Hinv: permMapsInv tp (getPermMap m))
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (Hload: load_unsafe Mint32 m1 b (Int.intval ofs) = Vint Int.one)
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m1')
            (Hat_external: semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = schedNext (updThread tp tid (Krun c') (aggelos n) (n+1)))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
            step tp m tp' m'
  
  | fstep_unlock :
      forall tp tp' m m1 c m1' c' m' b ofs pmap1 pnew,
      let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage UNLOCK (Vptr b ofs::nil) c)
            (Hinv: permMapsInv tp (getPermMap m))
            (Hpmap: getThreadPerm tp tid = pmap1)
            (Hrestrict_pmap: restrPermMap tid Hinv = m1)
            (Hload: load_unsafe Mint32 m1 b (Int.intval ofs) = Vint Int.zero)
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m1')
            (Hafter_external: semantics.after_external the_sem
                                                       (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = schedNext (updThread tp tid (Krun c') (aggelos n) (n+1)))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
            step tp m tp' m'

  | fstep_create :
      forall tp tp' m m' c c' c_new vf arg pnew,
        let: n := counter tp in
        forall tid0
               (Hsched: List.hd_error (schedule tp) = Some tid0)
               (Htid0_lt_pf :  tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = Kstage CREATE (vf::arg::nil) c)
            (Hinitial: semantics.initial_core the_sem the_ge vf (arg::nil) = Some c_new)
            (Hafter_external: semantics.after_external the_sem
                                                       (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = schedNext (addThread (updThread tp tid (Krun c') (aggelos n) (n+2))
                                              (Krun c_new) (aggelos (n+1))))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m pnew = Some m'),
            step tp m tp' m'

  | step_lockfail :
      forall tp m m1 c b ofs pmap1 tid0
             (Hsched: List.hd_error (schedule tp) = Some tid0)
             (Htid0_lt_pf :  tid0 < num_threads tp),
        let: tid := Ordinal Htid0_lt_pf in
        forall
          (Hthread: getThreadC tp tid = Kstage LOCK (Vptr b ofs::nil) c)
          (Hinv: permMapsInv tp (getPermMap m))
          (Hpmap: getThreadPerm tp tid = pmap1)
          (Hrestrict_pmap: restrPermMap tid Hinv = m1)
          (Htest: load_unsafe Mint32 m1 b (Int.intval ofs) = Vint Int.zero),
          step tp m (schedNext tp) m
               
  | fstep_schedfail :
      forall tp m tid0
             (Hsched: List.hd_error (schedule tp) = Some tid0)
             (Htid0_lt_pf :  tid0 >= num_threads tp),
        step tp m (schedNext tp) m.
                 

End Corestep.

End FineConcur.
End FineConcur.

Module CoreLemmas.
Section CoreLemmas.
    
  Context {sem : Modsem.t}.

  Notation the_sem := (Modsem.sem sem).
  Notation perm_map := PermMap.t.

  Inductive mem_obs_eq (R : meminj) (m1 m2 : Mem.mem) : Prop :=
  | MEq : forall b1 b2 ofs chunk
                 (Hrenaming: R b1 =)
                 (Hload_eq: Mem.load chunk m1 b1 ofs = Mem.load chunk m2 b2 ofs),
            mem_obs_eq R m1 m2.

  (* also need some invariant for lock locations, probably requires a lock pool of some sort.*)
  
 
            
  
  Section CorePerm.

    Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).
    Hypothesis corestep_perm :
      forall c m c' m' (Hstep: corestep the_sem the_ge c m c' m'),
        (Mem.nextblock m = Mem.nextblock m' /\ Mem.mem_access m = Mem.mem_access m') \/
        (Coqlib.Plt (Mem.nextblock m) (Mem.nextblock m') /\
         forall b ofs, Coqlib.Plt b (Mem.nextblock m) ->
                       (Mem.mem_access m) b ofs k
        
    

(* Move to another file*)
Module In2.
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
  forall zs ys (HIn2: In2 zs),
    In2 (ys ++ zs).
Proof.
  intros.
  destruct zs; [inversion HIn2 | induction ys].
  auto.
  destruct ys; simpl; auto. 
Qed.

Lemma in2_trivial : forall xs ys,
  In2 (xs ++ x :: y :: ys).
Proof.
  intros. induction xs as [|? xs IHxs]; intros; simpl; auto.
  destruct (xs ++ x :: y :: ys). inversion IHxs.
  right; assumption.
Qed.

Lemma In2_inv xs xmid xs' (HIn2: In2 (xs ++ xmid :: xs')) :
  In2 (xs ++ [:: xmid]) \/ In2 (xmid :: xs').
Proof.
  induction xs.
  - rewrite cat0s in HIn2.
    right; trivial.
  - destruct xs.
    + destruct HIn2 as [[E1 E2] | HIn2].
      * subst.
        left; simpl; auto.
      * right; assumption.
    + destruct HIn2 as [[E1 E2] | HIn2].
      * subst. left; simpl; auto.
      * apply IHxs in HIn2.
        destruct HIn2; simpl; auto.
Qed.

End In2.

Lemma In2_implies_In (A : eqType) (x y : A) xs (HIn2: In2 x y xs):
  x \in xs.
Proof.
  induction xs.
  - now destruct HIn2.
  - destruct xs; [destruct HIn2 | destruct HIn2 as [[? ?] | HIn2]]; subst.
      by rewrite inE eqxx.
      rewrite inE; apply/orP; right; apply IHxs; assumption.
Qed.

End In2.

Module Similar.
Section CoreSimilar.

  Context {sem : Modsem.t}.
  Notation the_sem := (Modsem.sem sem).
  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).
  
  Class core_similar :=
    {
      mem_similar : mem -> mem -> Prop;
      step_similar : forall c m c' m' m''
                            (Hmem_sim: mem_similar m m'')
                            (Hstep: corestep the_sem the_ge c m c' m'),
                     exists m''', corestep the_sem the_ge c m'' c'  m''' /\ mem_similar m'' m'''
    }.

End CoreSimilar.

Section Similar.

  Import ThreadPool.
  Context {sem : Modsem.t}.

  Notation thread_pool := (t sem).
  Notation the_sem := (Modsem.sem sem).
  Notation perm_map := PermMap.t.

  Variable aggelos : nat -> perm_map.

  Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).

  Inductive tp_similar (tp tp' : thread_pool) : Prop :=
  | tp_sim : forall
               (Hnum_threads: num_threads tp = num_threads tp')
               (Hsim_pool : forall tid, (pool tp) tid = (pool tp') tid)
               (H

  
                            
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
  
   
  Definition trace (step : forall sem : Modsem.t,
                             (nat -> perm_map) ->
                             (nat -> nat) ->
                             Genv.t (Modsem.F sem) (Modsem.V sem) ->
                             Top.pool sem -> mem -> Top.pool sem -> mem -> Prop)
             (sched : nat -> nat) :=
    {xs : seq (thread_pool * mem) |
     forall x y, In2 x y xs ->
                 step _ aggelos sched the_ge (fst x) (snd x) (fst y) (snd y)}.
  
  Inductive obs (tp : thread_pool) : trace -> Prop :=
  | obs_chd : forall tr tp' m m',
                  

  Lemma pf1 : 1 < 5. auto. Defined.
  Lemma pf2 : 2 < 5. auto. Defined.
  
  Eval compute in buildSched ((schedCore (Ordinal pf1)) ::
                                                        (schedCore (Ordinal pf2)) ::
                                                        (schedCore (Ordinal pf1)) ::
                                              (schedCore (Ordinal pf2)) ::
                                              (schedExt (Ordinal pf1)) ::
                                              (schedExt (Ordinal pf2)) ::
                                              (schedCore (Ordinal pf2)) :: nil).
  
  
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