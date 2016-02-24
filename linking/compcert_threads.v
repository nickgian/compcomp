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

Require Import compcert_linking threads_lemmas permissions.

Ltac pf_cleanup :=
  repeat match goal with
           |[H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
            assert (H1 = H2) by (erewrite leq_pf_irr; eauto 2); subst H2
         end.

Global Instance optionMonad : monad option :=
  {
    ret A x := Some x;
    bind A B x f :=
        match x with
          | Some y => f y
          | None => None
        end
  }.

Module ThreadPool. Section ThreadPool.

  Variable cT : Type.
  
  Record t := mk
                { num_threads : pos
                  ; pool :> 'I_num_threads -> cT
                  ; perm_maps : 'I_num_threads -> access_map
                  ; counter : nat
                }.

End ThreadPool. End ThreadPool.

Notation pool := ThreadPool.t.
                  
Section poolDefs.

Variable cT : Type.

Variable (tp : ThreadPool.t cT).

Import ThreadPool.

Notation num_threads := (ThreadPool.num_threads tp).
Notation thread_pool := (t cT).

(* Per-thread disjointness definition*)
Definition race_free tp :=
  forall tid0 tid0' (Htid0 : tid0 < (@ThreadPool.num_threads cT tp))
         (Htid0' : tid0' < (@ThreadPool.num_threads cT tp)) (Htid: tid0 <> tid0'),
    permMapsDisjoint (perm_maps tp (Ordinal Htid0))
                     (perm_maps tp (Ordinal Htid0')).

Definition newPermMap_wf pmap :=
  forall tid0 (Htid0 : tid0 < num_threads),
    permMapsDisjoint ((perm_maps tp) (Ordinal Htid0)) pmap.

Require Import fintype.

Lemma unlift_m_inv : forall tid (Htid : tid < num_threads.+1) ord
            (Hunlift: unlift (ordinal_pos_incr num_threads)
                             (Ordinal (n:=num_threads.+1) (m:=tid) Htid)
                      = Some ord),
       nat_of_ord ord = tid.
Proof.
  intros.
  assert (Hcontra: unlift_spec (ordinal_pos_incr num_threads)
                               (Ordinal (n:=num_threads.+1) (m:=tid) Htid) (Some ord)).
  rewrite <- Hunlift.
  apply/unliftP.
  inversion Hcontra; subst.
  inversion H0.
  unfold bump.
  assert (pf: ord < num_threads)
    by (by rewrite ltn_ord).
  assert (H: num_threads <= ord = false).
  rewrite ltnNge in pf.
  rewrite <- Bool.negb_true_iff. auto.
  rewrite H. simpl. rewrite add0n. reflexivity.
Defined.
    
Definition addThread (c : cT) (pmap : access_map) : thread_pool :=
  let: new_num_threads := pos_incr num_threads in
          let: new_tid := ordinal_pos_incr num_threads in
          @mk cT new_num_threads
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
              ((counter tp).+1).

Lemma addThread_racefree :
  forall c p (Hwf: newPermMap_wf p) (Hrace: race_free tp),
    race_free (addThread c p).
  Proof.
    unfold race_free in *. intros.
    simpl.
    match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ord0|] eqn:Hget0
    end;
      match goal with
        | [ |- context[ match ?Expr with _ => _ end]] =>
          destruct Expr as [ord1|] eqn:Hget1
      end; simpl in *.
    - apply unlift_m_inv in Hget0.
      apply unlift_m_inv in Hget1. subst.
      destruct ord0 as [tid0 pf0], ord1 as [tid1 pf1]; simpl in Htid.
      eapply Hrace; eauto.
    - apply unlift_m_inv in Hget0.
      subst. unfold newPermMap_wf in Hwf.
      destruct ord0. eapply Hwf; eauto.
    - apply unlift_m_inv in Hget1.
      subst. unfold newPermMap_wf in Hwf.
      destruct ord1. apply permMapsDisjoint_comm. eapply Hwf; eauto.
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
    
Definition updThreadC (tid : 'I_num_threads) (c' : cT) : thread_pool :=
  @mk cT num_threads (fun (n : 'I_num_threads) =>
                         if n == tid then c' else tp n) (perm_maps tp)
      (counter tp).

Definition updThreadP (tid : 'I_num_threads) (pmap' : access_map) : thread_pool :=
  @mk cT num_threads (pool tp) (fun (n : 'I_num_threads) =>
                                   if n == tid then pmap' else (perm_maps tp) n)
      (counter tp).

Definition permMap_wf pmap tid :=
  forall tid0 (Htid0 : tid0 < num_threads) (Hneq: tid <> tid0),
    permMapsDisjoint ((perm_maps tp) (Ordinal Htid0)) pmap.
    
Definition updThread (tid : 'I_num_threads) (c' : cT)
           (pmap : access_map) (counter' : nat) : thread_pool :=
  @mk cT num_threads
      (fun (n : 'I_num_threads) =>
         if n == tid then c' else tp n)
      (fun (n : 'I_num_threads) =>
         if n == tid then pmap else (perm_maps tp) n) 
      counter'.

Lemma updThread_wf : forall tid (pf : tid < num_threads) pmap
                            (Hwf: permMap_wf pmap tid)
                            c'  counter'
                            (Hrace_free: race_free tp),
                       race_free (updThread (Ordinal pf) c' pmap counter').
  Proof.
    intros.
    unfold race_free. intros.
    simpl.
    destruct (Ordinal (n:=num_threads) (m:=tid0) Htid0 ==  Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0,
             (Ordinal (n:=num_threads) (m:=tid0') Htid0' == Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0'.
    - move/eqP:Heq0 => Heq0. subst.
      move/eqP:Heq0' => Heq0'. inversion Heq0'. inversion Heq0; subst. exfalso; auto.
    - move/eqP:Heq0=>Heq0. inversion Heq0. subst. 
      apply permMapsDisjoint_comm.
      eapply Hwf. simpl; auto.
    - move/eqP:Heq0'=>Heq0'. inversion Heq0'. subst.
      eapply Hwf. simpl; auto.
    - simpl in *. eapply Hrace_free; eauto.
  Defined.
  
  Definition getThreadC (tid : 'I_num_threads) : cT := tp tid.
  
  Definition getThreadPerm (tid : 'I_num_threads) : access_map := (perm_maps tp) tid.

  Import Maps.

  (* Definition permMapsInv (pmap : PermMap.t) : Prop := *)
  (*   (isCanonical pmap) *)
  (*   /\ (forall tid, ~ Coqlib.Plt (PermMap.next pmap) (PermMap.next (getThreadPerm tid))) *)
  (*   /\ (forall tid b ofs, *)
  (*         Mem.perm_order'' (PMap.get b (PermMap.map pmap) ofs Cur) *)
  (*                          (PMap.get b (PermMap.map (getThreadPerm tid)) ofs Cur)) *)
  (*   /\ (forall tid b ofs, *)
  (*         Mem.perm_order'' *)
  (*         (Maps.PMap.get b (PermMap.map pmap) ofs Max) *)
  (*         (Maps.PMap.get b (PermMap.map (getThreadPerm tid)) ofs Max)) *)
  (*   /\ (exists tid, *)
  (*         PermMap.next pmap = PermMap.next (getThreadPerm tid)) *)
  (*   /\ (forall ofs b, *)
  (*     exists tid, *)
  (*       (PMap.get b (PermMap.map (perm_maps tp tid)) ofs Cur) = *)
  (*       (PMap.get b (PermMap.map pmap) ofs Cur)) *)
  (*   /\ (forall ofs b, *)
  (*       exists tid, *)
  (*         (PMap.get b (PermMap.map (perm_maps tp tid)) ofs Max) = *)
  (*         (PMap.get b (PermMap.map pmap) ofs Max)). *)
  
Definition perm_compatible p :=
  forall tid (b : positive) (ofs : Z) ,
    Mem.perm_order'' (Maps.PMap.get b p ofs)
                     (Maps.PMap.get b (getThreadPerm tid) ofs).

Record mem_compatible m :=
  { perm_comp: perm_compatible (getMaxPerm m);
    mem_canonical: isCanonical (getMaxPerm m)
  }.

End poolDefs.

Arguments updThread {_} tp tid c' pmap counter'.
Arguments addThread {_} tp c pmap.

Section poolLemmas.

Context {cT : Type} (tp : ThreadPool.t cT).

Import ThreadPool.

Lemma gssThreadCode (tid : 'I_(num_threads tp)) c' p' counter' : 
  getThreadC (updThread tp tid c' p' counter') tid = c'.
Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' p' counter':
  tid' != tid -> getThreadC (updThread tp tid c' p' counter') tid' = getThreadC tp tid'.
Proof. by rewrite /getThreadC /updThread /=; case Heq: (tid' == tid). Defined.

Lemma gssThreadPerm (tid : 'I_(num_threads tp)) c' p' counter' : 
  getThreadPerm (updThread tp tid c' p' counter') tid = p'.
Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

Lemma gsoThreadPerm (tid tid' : 'I_(num_threads tp)) c' p' counter':
  tid' != tid -> getThreadPerm (updThread tp tid c' p' counter') tid' = getThreadPerm tp tid'.
Proof. by rewrite /getThreadPerm /updThread /=; case Heq: (tid' == tid). Defined.

Lemma getAddThread c pmap tid :
  tid = ordinal_pos_incr (num_threads tp) ->
  getThreadC (addThread tp c pmap) tid = c.
Proof. by rewrite /getThreadC /addThread /= => <-; rewrite unlift_none. Qed.

(* Lemma permMapsInv_lt : forall p (Hinv: permMapsInv tp p) tid, *)
(*                          permMapLt (getThreadPerm tp tid) p. *)
(* Proof. *)
(*   intros. destruct Hinv as [_ [Hnext [HorderCur [HorderMax [_ [Hcur Hmax]]]]]]. *)
(*   unfold permMapLt. auto. *)
(* Qed. *)

Lemma permMapsInv_lt : forall p (Hinv: perm_compatible tp p) tid,
                         permMapLt (getThreadPerm tp tid) p.
Proof.
  intros. 
  unfold permMapLt; auto.
Qed.

Definition restrPermMap p' m (Hlt: permMapLt p' (getMaxPerm m)) : mem.
Proof.
  refine ({|
             Mem.mem_contents := Mem.mem_contents m;
             Mem.mem_access :=
               (fun ofs k =>
                 match k with
                    | Cur => None
                    | Max => fst (Mem.mem_access m) ofs k
                  end, Maps.PTree.map (fun b f =>
                                         fun ofs k =>
                                           match k with
                                             | Cur =>
                                               (Maps.PMap.get b p') ofs
                                             | Max =>
                                               f ofs Max
                                           end) (Mem.mem_access m).2);
             Mem.nextblock := Mem.nextblock m;
             Mem.access_max := _;
             Mem.nextblock_noaccess := _;
             Mem.contents_default := Mem.contents_default m |}).
  - unfold permMapLt in Hlt.
    assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                               Maps.PMap.get b (Mem.mem_access m) ofs Max).
    { unfold getMaxPerm. intros.
      rewrite Maps.PMap.gmap. reflexivity. }
    intros.
    specialize (Hlt b ofs).
    specialize (Heq b ofs).
    unfold getMaxPerm in Hlt.
    unfold Maps.PMap.get in *. simpl in *.
    rewrite Maps.PTree.gmap; simpl.
    match goal with
      | [|- context[match Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
        destruct (Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
    end; auto; unfold Coqlib.option_map in Heqo.
    destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; try discriminate.
    + inversion Heqo; subst; clear Heqo.
      rewrite Heq in Hlt. auto.
    + unfold Mem.perm_order''. by destruct ((Mem.mem_access m).1 ofs Max).
  - intros b ofs k Hnext.
  - unfold permMapLt in Hlt.
    assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                               Maps.PMap.get b (Mem.mem_access m) ofs Max).
    { unfold getMaxPerm. intros.
      rewrite Maps.PMap.gmap. reflexivity. }
    specialize (Hlt b ofs).
    specialize (Heq b ofs).
    unfold Maps.PMap.get in *.
    simpl in *.
    rewrite Maps.PTree.gmap; simpl.
    assert (H := Mem.nextblock_noaccess m).
    specialize (H b). unfold Maps.PMap.get in H.
    match goal with
      | [|- context[match Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
        destruct (Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
    end; auto; unfold Coqlib.option_map in Heqo;
    destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:Heqo2; try discriminate.
    inversion Heqo. subst f. clear Heqo.
    destruct k; auto.
    rewrite Heq in Hlt.
    specialize (H ofs Max). rewrite H in Hlt; auto.
    unfold Mem.perm_order'' in Hlt. destruct (Maps.PTree.get b p'.2).
    destruct (o0 ofs); tauto.
    destruct (p'.1 ofs); tauto.
    rewrite H; auto. destruct k; auto.
Defined.
    
Lemma restrPermMap_nextblock :
  forall p' m (Hlt: permMapLt p' (getMaxPerm m)),
    Mem.nextblock (restrPermMap Hlt) = Mem.nextblock m.
Proof.
  intros. unfold restrPermMap. reflexivity.
Qed.

Lemma restrPermMap_irr : forall p' p'' m
                                (Hlt : permMapLt p' (getMaxPerm m))
                                (Hlt': permMapLt p'' (getMaxPerm m))
                                (Heq_new: p' = p''),
                           restrPermMap Hlt = restrPermMap Hlt'.
Proof.
  intros. subst.
  apply f_equal. by apply proof_irr.
Qed.

Lemma restrPermMap_disjoint_inv:
  forall (mi mj m : mem) (pi pj : access_map)
    (Hcan_m: isCanonical (getMaxPerm m))
    (Hltj: permMapLt pj (getMaxPerm m))
    (Hlti: permMapLt pi (getMaxPerm m))
    (Hdisjoint: permMapsDisjoint pi pj)
    (Hrestrj: restrPermMap Hltj = mj)
    (Hrestri: restrPermMap Hlti = mi),
    permMapsDisjoint (getCurPerm mi) (getCurPerm mj).
Proof.
  intros. rewrite <- Hrestri. rewrite <- Hrestrj.
  unfold restrPermMap, getCurPerm, permMapsDisjoint. simpl in *.
  intros b ofs.
  do 2 rewrite Maps.PMap.gmap.
  clear Hrestrj Hrestri.
  unfold permMapLt, Mem.perm_order'' in *.
  specialize (Hltj b ofs); specialize (Hlti b ofs).
  unfold getMaxPerm in *; simpl in *.
  rewrite Maps.PMap.gmap in Hlti, Hltj.
  unfold permMapsDisjoint, Maps.PMap.get in *; simpl in *.
  do 2 rewrite Maps.PTree.gmap. unfold Coqlib.option_map.
  specialize (Hdisjoint b ofs).
  assert (Hnone: (Mem.mem_access m).1 ofs Max = None)
    by (unfold isCanonical in Hcan_m; simpl in Hcan_m;
          by apply equal_f with (x:=ofs) in Hcan_m).
  destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; auto.
  rewrite Hnone in Hlti, Hltj;
  destruct (Maps.PTree.get b pi.2) as [f1 |] eqn:?;
  destruct (Maps.PTree.get b pj.2) as [f2|] eqn:?;
   repeat match goal with
     | [H: match ?Expr with _ => _ end |- _] => destruct Expr
   end; tauto.
Qed.
  
(* Lemma updPermMap_nextblock : *)
(*   forall (m : mem) (p : PermMap.t) m' *)
(*     (Hupd: updPermMap m p = Some m'), *)
(*     Mem.nextblock m = Mem.nextblock m'. *)
(* Proof. *)
(*   unfold updPermMap. intros. *)
(*   destruct (Pos.eq_dec (Mem.nextblock m) (PermMap.next p)) as [Heq | Heq]. *)
(*   inversion Hupd. simpl. by rewrite Heq. *)
(*   discriminate. *)
(* Qed. *)

(* Lemma updPermMap_contents: *)
(*   forall (m m' : mem) (pnew : PermMap.t) *)
(*          (Hupd: updPermMap m pnew = Some m'), *)
(*     Mem.mem_contents m = Mem.mem_contents m'. *)
(* Proof. *)
(*   intros. *)
(*   unfold updPermMap in Hupd. *)
(*   destruct (Pos.eq_dec (Mem.nextblock m) (PermMap.next pnew)). *)
(*   inversion Hupd. reflexivity. *)
(*   discriminate. *)
(* Qed. *)

(* Definition updPermMap_get pmap m m' *)
(*            (Hupd: updPermMap m pmap = Some m') : *)
(*   getPermMap m' = pmap. *)
(* Proof. *)
(*   intros. *)
(*   unfold updPermMap in Hupd. *)
(*   destruct (Pos.eq_dec (Mem.nextblock m) (PermMap.next pmap)) eqn:Heq. *)
(*   inversion Hupd; subst. *)
(*   unfold getPermMap.  *)
(*   destruct pmap. reflexivity. *)
(*   discriminate. *)
(* Qed. *)

Lemma no_race_wf : forall tid (pf: tid < (num_threads tp)) (Hrace: race_free tp),
                     permMap_wf tp (getThreadPerm tp (Ordinal pf)) tid.
Proof.
  intros. unfold permMap_wf; auto.
Defined.

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

Module Concur.
  Section Concur.
    
    Import ThreadPool.
    Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.

    Notation thread_pool := (t cT).
    Notation perm_map := access_map.

    Variable the_ge : G.
    Variable aggelos : nat -> perm_map.

    Lemma restrPermMap_wf :
      forall (tp : thread_pool) (m m': mem) tid
        (Hcanonical: isCanonical (perm_maps tp tid))
        (Hlt: permMapLt (perm_maps tp tid) (getMaxPerm m))
        (Hcompatible: mem_compatible tp m)
        (Hrestrict: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m')
        (Hrace : race_free tp),
        permMap_wf tp (getCurPerm m') (nat_of_ord tid).
    Proof.
      intros. subst.
      unfold restrPermMap, getCurPerm. simpl.
      unfold permMap_wf. intros tid' Htid' Hneq.
      unfold permMapsDisjoint. simpl.
      assert (Hneq' : tid' <> tid) by auto.
      destruct tid as [tid Htid].
      specialize (Hrace tid' tid Htid' Htid Hneq').
      unfold permMapsDisjoint in Hrace.
      destruct Hcompatible as [_ Hcan_mem].
      unfold isCanonical in Hcan_mem.
      unfold getMaxPerm in Hcan_mem. simpl in Hcan_mem.
      intros b ofs. specialize (Hrace b ofs).
      rewrite Maps.PMap.gmap. unfold getThreadPerm in *.
      
      unfold Maps.PMap.get in *. simpl.
      unfold isCanonical in Hcanonical. rewrite Hcanonical in Hrace.
      rewrite Maps.PTree.gmap. unfold Coqlib.option_map.
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?;
      destruct (Maps.PTree.get b
                               (perm_maps tp (Ordinal Htid)).2) eqn:?;
      try rewrite Hcanonical; auto.
      destruct (Maps.PTree.get b
                               (perm_maps tp (Ordinal Htid')).2) eqn:?; auto.
      unfold permMapLt in Hlt.
      unfold Maps.PMap.get in Hlt.
      specialize (Hlt b ofs).
      rewrite Heqo0 in Hlt.
      unfold getMaxPerm in Hlt. simpl in Hlt.
      rewrite Maps.PTree.gmap1 in Hlt. unfold Coqlib.option_map in Hlt.
      rewrite Heqo in Hlt.
      apply equal_f with (x := ofs) in Hcan_mem.
      rewrite Hcan_mem in Hlt.
      unfold Mem.perm_order'' in Hlt. destruct (o ofs); auto.
      exfalso. auto.
      rewrite perm_union_comm. apply not_racy_union. constructor.
    Defined.
    
    Lemma restrPermMap_can : forall (tp : thread_pool) (m m': mem) tid
                               (Hcanonical: isCanonical (perm_maps tp tid))
                               (Hlt: permMapLt (perm_maps tp tid) (getMaxPerm m))
                               (Hrestrict: restrPermMap Hlt = m'),
                               isCanonical (getCurPerm m').
    Proof.
      intros. subst.
      unfold restrPermMap, getCurPerm, isCanonical in *. simpl in *.
      auto.
    Defined.
    
    Hypothesis corestep_canonical_max :
      forall c m c' m' n
        (Hm_canon: isCanonical (getMaxPerm m))
        (Hcore: corestepN the_sem the_ge n c m c' m'),
        isCanonical (getMaxPerm m').

    Hypothesis corestep_canonical_cur :
      forall c m c' m' n
        (Hm_canon: isCanonical (getCurPerm m))
        (Hcore: corestepN the_sem the_ge n c m c' m'),
        isCanonical (getCurPerm m').

    Hypothesis corestep_permMap_wf : forall tp tid (Htid: tid < @num_threads cT tp) c m c' m' n
                                       (Hperm: permMap_wf tp (getCurPerm m) tid)
                                       (Hcore: corestepN the_sem the_ge n c m c' m'),
                                       permMap_wf tp (getCurPerm m') tid.

    Record invariant tp :=
      { canonical : forall tid, isCanonical (perm_maps tp tid);
        no_race : race_free tp;
        lock_pool : forall (pf : 0 < num_threads tp), exists c,
                      getThreadC tp (Ordinal pf) = c /\ halted the_sem c
      }.
    
    Lemma updThread_invariants :
      forall (tp tp' : thread_pool) c m m1 c' m1' n tid counter
        (Hinv: invariant tp)
        (Hcompatible: mem_compatible tp m)
        (Hthread: getThreadC tp tid = c)
        (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m1)
        (Hcore: corestepN the_sem the_ge (S n) c m1 c' m1')
        (Htp': tp' = updThread tp tid c' (getCurPerm m1') counter),
        invariant tp'.
    Proof.
      intros. destruct Hinv as [Hcanonical Hrace Hlp].
      destruct tid as [tid pf].
      assert (Hcontra: tid <> 0).
      { intros Hcontra. subst tp' tid.
        simpl in *.
        destruct (Hlp pf) as [c0' [Hthread' Hhalted]].
        rewrite Hthread in Hthread'; subst.
        destruct Hcore as [? [? [Hcontra _]]].
        apply corestep_not_halted in Hcontra. rewrite Hthread' in Hcontra.
        rewrite Hcontra in Hhalted. auto.
      }
      split.
      { intros tid'.
        destruct tid' as [tid' pf'].
        destruct (tid == tid') eqn:Heq'; move/eqP:Heq'=>Heq'; subst tp'; try subst tid'.
        - simpl in *.
          pf_cleanup.
          rewrite eq_refl.
          eapply corestep_canonical_cur with (c := c) (n := S n) (c' := c'); eauto.
          eapply restrPermMap_can; by eauto.
        - simpl in *.
          rewrite if_false.
          eapply Hcanonical.
          apply/eqP. intro Hcontra'. inversion Hcontra'; auto.
      }
      { unfold race_free in *.
        intros.
        destruct (tid == tid0) eqn:Heq0, (tid == tid0') eqn:Heq0'; move/eqP:Heq0=>Heq0;
          move/eqP:Heq0'=>Heq0'; simpl in *.
        - subst tid0 tid0'. exfalso; auto.
        - subst tid0. subst tp'. simpl in *.
          rewrite if_true.
          rewrite if_false.
          assert (Hwf := no_race_wf pf Hrace).
          apply restrPermMap_wf in Hrestrict_pmap; auto.
          assert (Hwf': permMap_wf tp (getCurPerm m1') tid).
          { eapply corestep_permMap_wf with (n := S n); eauto. }
          unfold permMap_wf in Hwf'.
          specialize (Hwf' _ Htid0' Heq0').
          apply permMapsDisjoint_comm. assumption.
          apply permMapsInv_lt. destruct Hcompatible; auto.
          apply/eqP. intro Hcontra'; inversion Hcontra'. auto.
          rewrite (leq_pf_irr _ _ Htid0 pf). apply eq_refl.
        - subst tid0' tp'; simpl in *.
          rewrite if_false. rewrite if_true.
          assert (Hwf := no_race_wf pf Hrace).
          apply restrPermMap_wf in Hrestrict_pmap; auto.
          assert (Hwf': permMap_wf tp (getCurPerm m1') tid).
          { eapply corestep_permMap_wf with (n := S n); eauto. }
          unfold permMap_wf in Hwf'.
          specialize (Hwf' _ Htid0 Heq0).
          assumption.
          apply permMapsInv_lt. destruct Hcompatible; auto.
          rewrite (leq_pf_irr _ _ Htid0' pf). apply eq_refl.
          apply/eqP. intro Hcontra'. inversion Hcontra'. auto.
        - subst tp'. simpl.
          rewrite if_false. rewrite if_false; simpl in *.
          eapply Hrace; eauto.
          apply/eqP. intro Hcontra'. inversion Hcontra'. auto.
          apply/eqP. intro Hcontra'. inversion Hcontra'. auto.
      }
      { subst tp'. simpl. intros pf0. destruct (Hlp pf0) as [c0 [Hcode Hhalted]].
        exists c0. split; auto.
        rewrite if_false; auto.
        apply/eqP. intro Hcontra'. inversion Hcontra'; auto.
      }     
    Defined.
    
    (* Semantics of the coarse-grained concurrent machine*)

    Inductive coarse_step : list nat -> thread_pool -> mem -> list nat -> thread_pool -> mem -> Prop :=
    | step_coarse:
        forall sched tp tp' m m1 c m' (c' : cT) n0 tid0
          (Htid0_lt_pf : tid0 < num_threads tp),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m1)
            (Hthread: getThreadC tp tid = c)
            (HcorestepN: corestepN the_sem the_ge (S n0) c m1 c' m')
            (Hcant: cant_step the_sem c')
            (Htp': tp' = updThread tp tid c' (getCurPerm m') n),
            coarse_step (tid0 :: sched) tp m sched tp' m'.
    
    Inductive fine_step : list nat -> thread_pool -> mem -> list nat -> thread_pool -> mem -> Prop :=
    | step_fine:
        forall sched tp tp' m m1 c m' (c' : cT) tid0
          (Htid0_lt_pf :  tid0 < num_threads tp),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m1)
            (Hthread: getThreadC tp tid = c)
            (HcorestepN: corestepN the_sem the_ge 1 c m1 c' m')
            (Htp': tp' = updThread tp tid c' (getCurPerm m') n),
            fine_step (tid0 :: sched) tp m sched tp' m'.

    (*missing lock-ranges*)
    Inductive ext_step : list nat -> thread_pool -> mem -> list nat -> thread_pool -> mem -> Prop :=
    | step_lock :
        forall sched tp tp' m m1 c c' m' b ofs tid0
          (Htid0_lt_pf : tid0 < num_threads tp)
          (pf_lp : 0 < num_threads tp),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          let: lp := Ordinal pf_lp in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hat_external: semantics.at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) lp) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hat_external: semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (Htp': tp' = updThread tp tid c' (aggelos n) (n+1)),
            ext_step (tid0 :: sched) tp m sched tp' m'
                       
    | step_unlock :
        forall sched tp tp' m m1 c c' m' b ofs tid0
          (Htid0_lt_pf : tid0 < num_threads tp)
          (pf_lp : 0 < num_threads tp),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          let: lp := Ordinal pf_lp in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hat_external: semantics.at_external the_sem c =
                           Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) lp) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
            (* what does the return value denote?*)
            (Hat_external: semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (Htp': tp' = updThread tp tid c' (aggelos n) (n+1)),
            ext_step (tid0 :: sched) tp m sched tp' m'
                       
    | step_create :
        forall sched tp tp_upd tp' m c c' c_new vf arg tid0
          (Htid0_lt_pf : tid0 < num_threads tp),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hat_external: semantics.at_external the_sem c =
                           Some (CREATE, ef_sig CREATE, vf::arg::nil))
            (Hinv: invariant tp)
            (Hinitial: semantics.initial_core the_sem the_ge vf (arg::nil) = Some c_new)
            (Hafter_external: semantics.after_external the_sem
                                                       (Some (Vint Int.zero)) c = Some c')
            (Htp': tp_upd = updThread tp tid c' (aggelos n) (n.+2))
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (* (Hangel_wf2: newPermMap_wf tp_upd (aggelos (n.+1))) *)
            (* (Hangel_canonical2: isCanonical (aggelos (n.+1))) *)
            (Htp': tp' = addThread tp_upd c_new (aggelos n.+1)),
            ext_step (tid0 :: sched) tp m sched tp' m
                       
    | step_mklock :
        forall sched tp tp' tp'' m m1 c c' m' b ofs pmap_tid' pmap_lp tid0
          (Htid0_lt_pf : tid0 < num_threads tp)
          (pf_lp : 0 < num_threads tp)
          (pf_lp' : 0 < num_threads tp'),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          let: lp := Ordinal pf_lp in
          let: lp' := Ordinal pf_lp' in
          let: pmap_tid := getThreadPerm tp tid in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hat_external: semantics.at_external the_sem c =
                           Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) tid) = m1)
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hdrop_perm:
               setPerm (Some Nonempty) b (Int.intval ofs) pmap_tid = pmap_tid')
            (Hlp_perm: setPerm (Some Writable) b (Int.intval ofs) (getThreadPerm tp lp) = pmap_lp)
            (Hat_external: semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread tp tid c' pmap_tid' (n+1))
            (Htp'': tp'' = updThreadP tp' lp' pmap_lp),
            ext_step (tid0 :: sched) tp m sched tp'' m'
                       
    | step_freelock :
        forall sched tp tp' tp'' m c c' b ofs pmap_lp' tid0
          (Htid0_lt_pf : tid0 < num_threads tp)
          (pf_lp : 0 < num_threads tp)
          (pf_lp' : 0 < num_threads tp'),
          let: n := counter tp in
          let: tid := Ordinal Htid0_lt_pf in
          let: lp := Ordinal pf_lp in
          let: lp' := Ordinal pf_lp' in
          let: pmap_lp := getThreadPerm tp lp in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hat_external: semantics.at_external the_sem c =
                           Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hdrop_perm:
               setPerm None b (Int.intval ofs) pmap_lp = pmap_lp')
            (Hat_external: semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (*the angel must provide the permissions for the thread - freeable or writeable *)
            (* (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
            (* (Hangel_canonical: isCanonical (aggelos n)) *)
            (Htp': tp' = updThread tp tid c' (aggelos n) (n+1))       
            (Htp'': tp'' = updThreadP tp' lp' pmap_lp'),
            ext_step (tid0 :: sched) tp m sched tp'' m
                       
    | step_lockfail :
        forall sched tp m c b ofs tid0 m1
          (Htid0_lt_pf : tid0 < num_threads tp)
          (pf_lp : 0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          let: lp := Ordinal pf_lp in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hat_external: semantics.at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hinv: invariant tp)
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap: restrPermMap (permMapsInv_lt (perm_comp Hcompatible) lp) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
            ext_step (tid0 :: sched) tp m sched tp m
                     
    | step_schedfail :
        forall sched tp m tid0
          (Htid0_lt_pf : tid0 >= num_threads tp),
          ext_step (tid0 :: sched) tp m sched tp m.

    Inductive step (t_step : list nat -> thread_pool -> mem -> list nat -> thread_pool -> mem -> Prop)
    : list nat -> thread_pool -> mem -> list nat -> thread_pool -> mem -> Prop :=
    | step_core:
        forall tid sched tp tp' m m'
          (Ht_step: t_step (tid :: sched) tp m sched tp' m'),
          step t_step (tid :: sched) tp m sched tp' m'
               
    | step_halted:
        forall sched tp m c tid0
          (Htid0_lt_pf : tid0 < num_threads tp),
          let: tid := Ordinal Htid0_lt_pf in
          forall
            (Hthread: getThreadC tp tid = c)
            (Hcant: halted the_sem c),
            step t_step (tid0 :: sched) tp m sched tp m
                 
    | step_ext:
        forall tid sched tp tp' m m'
          (Hext_step: ext_step (tid :: sched) tp m sched tp' m'),
          step t_step (tid :: sched) tp m sched tp' m'.
    
    Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
    Proof. by move/ltP. Qed.

    End Concur.
    Section InitialCore.

      Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.
      Import ThreadPool.

      Notation thread_pool := (t cT).
      Notation perm_map := access_map.
      
      Definition at_external (st : (list nat) * thread_pool)
      : option (external_function * signature * seq val) := None.

      Definition after_external (ov : option val) (st : list nat * thread_pool) :
        option (list nat * thread_pool) := None.

      Definition two_pos : pos := mkPos NPeano.Nat.lt_0_2.
      
      Definition ord1 := Ordinal (n := two_pos) (m := 1) (leqnn two_pos).

      (*not clear what the value of halted should be*)
      Definition halted (st : list nat * thread_pool) : option val := None.

      Variable compute_init_perm : G -> access_map.
      Variable sched : list nat.
      Variable lp_code : cT.
      Hypothesis lp_halted : semantics.halted the_sem lp_code = Some (Vint Int.zero). 

      Definition initial_core the_ge (f : val) (args : list val) : option (list nat * thread_pool) :=
        match initial_core the_sem the_ge f args with
          | None => None
          | Some c =>
            Some (sched, ThreadPool.mk
                           two_pos
                           (fun tid => if tid == ord0 then lp_code
                                       else if tid == ord1 then c
                                            else c (*bogus value; can't occur*))
                           (fun tid => if tid == ord0 then empty_map else
                                         if tid == ord1 then compute_init_perm the_ge
                                         else empty_map)
                           0)
        end.

      Variable aggelos : nat -> access_map.

      Definition cstep (the_ge : G) (st : list nat * thread_pool) m
                 (st' : list nat * thread_pool) m' :=
        @step cT G the_sem the_ge aggelos (@coarse_step cT G the_sem the_ge)
              (fst st) (snd st) m (fst st') (snd st') m'.

      Definition fstep (the_ge : G) (st : list nat * thread_pool) m
                 (st' : list nat * thread_pool) m' :=
        @step cT G the_sem the_ge aggelos (@fine_step cT G the_sem the_ge)
              (fst st) (snd st) m (fst st') (snd st') m'.
      
      Program Definition coarse_semantics :
        CoreSemantics G (list nat * thread_pool) mem :=
        Build_CoreSemantics _ _ _
                            initial_core
                            at_external
                            after_external
                            halted
                            cstep
                            _ _ _.

      Program Definition fine_semantics :
        CoreSemantics G (list nat * thread_pool) mem :=
        Build_CoreSemantics _ _ _
                            initial_core
                            at_external
                            after_external
                            halted
                            fstep
                            _ _ _.

    End InitialCore.
End Concur.

Module MemoryObs.
  
  Definition mem_func_eq (m m' : Mem.mem) :=
    Mem.mem_contents m = Mem.mem_contents m' /\
    Mem.mem_access m = Mem.mem_access m' /\
    Mem.nextblock m = Mem.nextblock m'.

  Notation "m1 '=~' m2" := (mem_func_eq m1 m2) (at level 50). 

  Require Import Coq.Relations.Relation_Definitions.
  
  Instance meq_Reflexive : RelationClasses.Reflexive mem_func_eq.
  Proof.
    unfold RelationClasses.Reflexive. intros m. destruct m. unfold mem_func_eq. simpl.
    auto.
  Defined.
  Instance meq_Symmetric : RelationClasses.Symmetric mem_func_eq.
  Proof.
    unfold RelationClasses.Symmetric, mem_func_eq. intros m m' [? [? ?]].
    auto.
  Defined.
  Instance meq_Transitive  : RelationClasses.Transitive mem_func_eq.
  Proof.
    unfold RelationClasses.Transitive, mem_func_eq.
    intros m m' m'' [Hcontents [Haccess Hblock]] [? [? ?]].
    rewrite Hcontents Haccess Hblock. auto.
  Defined.

  Hint Resolve meq_Reflexive : mem.
        
  Definition mem_obs_eq (f : block -> block) (m1 m2 : Mem.mem) : Prop :=
    forall b1 b2 ofs (Hrenaming: f b1 = b2),
      (Mem.perm m1 b1 ofs Cur Readable ->
       Maps.ZMap.get ofs (Maps.PMap.get b1 (Mem.mem_contents m1)) =
       Maps.ZMap.get ofs (Maps.PMap.get b2 (Mem.mem_contents m2))) /\
      (forall k,
         Maps.PMap.get b1 (Mem.mem_access m1) ofs k =
         Maps.PMap.get b2 (Mem.mem_access m2) ofs k).

  Lemma mem_obs_trans_comm :
    forall m1j m1'j m2j R
           (Hmem_1: mem_obs_eq R m1j m1'j)
           (Hmem_2: mem_obs_eq (fun b => b) m1j m2j),
      mem_obs_eq R m2j m1'j.
  Proof.
    intros.
    split.
    { intro Hperm.
      destruct (Hmem_1 b1 b2 ofs) as [Hval1 Hperm1]; auto.
      destruct (Hmem_2 b1 b1 ofs) as [Hval2 Hperm2]; auto.
      specialize (Hperm2 Cur). subst.
      assert (H: Mem.perm m1j b1 ofs Cur Readable).
      { unfold Mem.perm in *. rewrite Hperm2.
        assumption.
      }
      rewrite <- Hval2; auto.
    }
    { destruct (Hmem_1 b1 b2 ofs) as [Hval1 Hperm1]; auto.
      destruct (Hmem_2 b1 b1 ofs) as [Hval2 Hperm2]; auto.
      subst. intro k.
      rewrite <- Hperm1. auto.
    }
  Qed.

  Hint Resolve mem_obs_trans_comm : mem.

  Lemma mem_obs_trans :
    forall m1j m1'j m2'j R
      (Hmem_1: mem_obs_eq R m1j m1'j)
      (Hmem_2: mem_obs_eq (fun b => b) m1'j m2'j),
      mem_obs_eq R m1j m2'j.
  Proof.
    intros.
    unfold mem_obs_eq. intros.
    destruct (Hmem_1 b1 b2 ofs Hrenaming) as [Hval1 Hperm1].
    unfold mem_obs_eq in Hmem_2.
    destruct (Hmem_2 b2 b2 ofs (Logic.eq_refl b2)) as [Hval2 Hperm2].
    split.
    - intro Hperm.
      erewrite Hval1. eapply Hval2.
      unfold Mem.perm in *.
      erewrite <- Hperm1. eauto.
      assumption.
      intro k.
      erewrite Hperm1. eauto.
  Qed.

  Hint Resolve mem_obs_trans : mem.
  
  Lemma mem_func_obs_eq:
    forall (R : block -> block) (m1 m1' m1_eq m1'_eq : mem)
           (Hmeq: m1 =~ m1_eq)
           (Hmeq': m1' =~ m1'_eq)
           (Hobs_eq: mem_obs_eq R m1_eq m1'_eq),
      mem_obs_eq R m1 m1'.
  Proof.
    intros. inversion Hmeq; inversion Hmeq'.
    unfold Mem.perm, mem_func_eq in *;
      destruct Hmeq as [? [? ?]], Hmeq' as [? [? ?]];
      destruct m1, m1', m1_eq, m1'_eq; simpl in *; subst;
      econstructor; auto;
      destruct (Hobs_eq b1 b2 ofs Hrenaming) as [Hcontents Hperm];
      assumption.
  Qed.

  Hint Resolve mem_func_obs_eq : mem.

End MemoryObs.

Module SimDefs.
Section SimDefs.

  Import Concur.
  Import ThreadPool.
  Import MemoryObs.
  
  Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.
  
  Notation thread_pool := (t cT).
  Notation perm_map := access_map.
  Notation invariant := (@invariant cT G the_sem).
  
  Variable aggelos : nat -> perm_map.
  Variable the_ge : G.

  Variable rename_code : (block -> block) -> cT -> cT.

  Inductive tp_sim (tp tp' : thread_pool) (tid : nat) (R: block -> block) : Prop :=
  | Tp_sim : forall (pf: tid < num_threads tp)
               (pf': tid < num_threads tp')
               (Hnum: num_threads tp = num_threads tp')
               (Hcounter: counter tp = counter tp')
               (Hpool: rename_code R ((pool tp) (Ordinal pf)) = (pool tp') (Ordinal pf')),
               (* (Hperm: (perm_maps tp) (Ordinal pf) = (perm_maps tp') (Ordinal pf')), *)
               tp_sim tp tp' tid R.

  Inductive mem_sim (tp tp' : thread_pool) (m m' : Mem.mem) (tid : nat)
            (R : block -> block) : Prop :=
  | Mem_sim : forall (pf : tid < num_threads tp)
                (pf' : tid < num_threads tp') m_tid m'_tid m_tid_eq m'_tid_eq
                (Hinv: invariant tp)
                (Hinv': invariant tp')
                (Hcomp: mem_compatible tp m)
                (Hcomp': mem_compatible tp' m')
                (Hrestrict: restrPermMap
                              (permMapsInv_lt (perm_comp Hcomp) (Ordinal pf)) = m_tid)
                (Hrestrict': restrPermMap
                               (permMapsInv_lt (perm_comp Hcomp') (Ordinal pf')) = m'_tid)
                (Hmeq: m_tid =~ m_tid_eq)
                (Hmeq': m'_tid =~ m'_tid_eq)
                (Hobs: mem_obs_eq R m_tid_eq m'_tid_eq),
                mem_sim tp tp' m m' tid R.
End SimDefs.

Arguments tp_sim {cT} {rename_code} tp tp' tid R.
Arguments mem_sim {cT G the_sem} tp tp' m m' tid R.
End SimDefs.

Module FineStepLemmas.
Section FineStepLemmas.

  Import Concur ThreadPool MemoryObs SimDefs.

  Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.
  
  Notation thread_pool := (t cT).
  Notation perm_map := access_map.
  Notation invariant := (@invariant cT G the_sem).
  
  Variable aggelos : nat -> perm_map.
  Variable the_ge : G.
  Variable rename_code : (block -> block) -> cT -> cT.
  
  Hypothesis corestep_canonical_max :
    forall c m c' m' n
      (Hm_canon: isCanonical (getMaxPerm m))
      (Hcore: corestepN the_sem the_ge n c m c' m'),
      isCanonical (getMaxPerm m').

  Hypothesis corestep_canonical_cur :
    forall c m c' m' n
      (Hm_canon: isCanonical (getCurPerm m))
      (Hcore: corestepN the_sem the_ge n c m c' m'),
      isCanonical (getCurPerm m').

  Hypothesis corestep_permMap_wf : forall tp tid (Htid: tid < @num_threads cT tp) c m c' m' n
                                     (Hperm: permMap_wf tp (getCurPerm m) tid)
                                     (Hcore: corestepN the_sem the_ge n c m c' m'),
                                     permMap_wf tp (getCurPerm m') tid.

  Notation tp_sim := (@tp_sim cT rename_code).
  Notation fine_step := (@fine_step cT G the_sem the_ge).

  Hypothesis rename_code_at_ext :
    forall R c,
      semantics.at_external the_sem (rename_code R c) = None <->
      semantics.at_external the_sem c = None.

  Ltac pf_irr_clean :=
    repeat match goal with
             | [H1: invariant ?X, H2: invariant ?X |- _] =>
               assert (H1 = H2) by (by eapply proof_irr);
                 subst H2
             | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
               assert (H1 = H2) by (by eapply proof_irr);
                 subst H2
           end.
  
  (* Lemma corestep_mem_nextblock : *)
  (*   forall c1 c2 m1i m1j m2i m2j m1 m2 p1i p1j p2j pnew *)
  (*          (Hupd: updPermMap m2i pnew = Some m2) *)
  (*          (Hlt1j: permMapLt p1j (getPermMap m1)) *)
  (*          (Hlt1i: permMapLt p1i (getPermMap m1)) *)
  (*          (Hlt2j: permMapLt p2j (getPermMap m2)) *)
  (*          (Hrestr2j: restrPermMap Hlt2j = m2j) *)
  (*          (Hrestr1j: restrPermMap Hlt1j = m1j) *)
  (*          (Hrestr1i: restrPermMap Hlt1i = m1i) *)
  (*          (Hstep: corestep the_sem the_ge c1 m1i c2 m2i), *)
  (*     (Mem.nextblock m1j <= Mem.nextblock m2j)%positive. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply corestep_fwd in Hstep. *)
  (*   apply forward_nextblock in Hstep. *)
  (*   assert (H1i := restrPermMap_nextblock Hlt1i). *)
  (*   assert (H1j := restrPermMap_nextblock Hlt1j). *)
  (*   rewrite Hrestr1j in H1j. *)
  (*   rewrite Hrestr1i in H1i. rewrite H1j. rewrite <- H1i. *)
  (*   assert (H2j := restrPermMap_nextblock Hlt2j). *)
  (*   rewrite Hrestr2j in H2j. *)
  (*   rewrite H2j. *)
  (*   apply updPermMap_nextblock in Hupd. rewrite <- Hupd. *)
  (*   assumption. *)
  (* Qed. *)

  Hypothesis corestep_unchanged_on :
    forall c m c' m' b ofs
           (Hstep: corestep the_sem the_ge c m c' m')
           (Hstable: ~ Mem.perm m b ofs Cur Writable),
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).

  Lemma corestep_disjoint_mem_obs_id :
    forall c1 c2 m1i m1j m2j m1 m2 p1i p1j
      (Hcannical: isCanonical (getMaxPerm m1))
      (Hlt1j: permMapLt p1j (getMaxPerm m1))
      (Hlt1i: permMapLt p1i (getMaxPerm m1))
      (Hlt2j: permMapLt p1j (getMaxPerm m2))
      (Hrestr2j: restrPermMap Hlt2j = m2j)
      (Hrestr1j: restrPermMap Hlt1j = m1j)
      (Hrestr1i: restrPermMap Hlt1i = m1i)
      (Hdisjoint1: permMapsDisjoint p1i p1j)
      (Hstep: corestep the_sem the_ge c1 m1i c2 m2),
      mem_obs_eq (fun b => b) m1j m2j.
  Proof.
    intros.
    split; simpl in Hrenaming; subst b2.
    { intros Hperm; unfold Mem.perm in *. simpl in *.
      simpl.
      apply corestep_unchanged_on with (b := b1) (ofs := ofs) in Hstep.
      rewrite <- Hrestr1i in Hstep. simpl in Hstep.
      rewrite <- Hrestr1j. rewrite <- Hrestr2j. simpl. assumption.
      assert (Hdisjoint1': permMapsDisjoint (getCurPerm m1i) (getCurPerm m1j))
        by (eapply restrPermMap_disjoint_inv; eauto).
      intros Hpermi.
      eapply disjoint_norace; eauto.
    }
    { rewrite <- Hrestr1j. rewrite <- Hrestr2j. simpl. reflexivity. }
  Qed.

  Ltac step_absurd :=
    repeat
      (match goal with
         | [H1: List.hd_error ?Sched = Some ?Tid,
                H2: ?Sched = _ |- _] =>
           rewrite H2 in H1; simpl in H1; inversion H1;
         try (subst Tid; clear H1)
         | [H1: List.hd_error ?Sched = Some ?Tid1,
                H2: List.hd_error ?Sched = Some ?Tid2 |- _] =>
           rewrite H2 in H1; simpl in H1; inversion H1; subst Tid1; clear H1
         | [H1: getThreadC ?Tp (@Ordinal _ ?Tid ?Pf1) = _,
                H2: getThreadC ?Tp (@Ordinal _ ?Tid ?Pf2) = _ |- _] =>
           assert (Pf1 = Pf2) by (erewrite leq_pf_irr; reflexivity);
         subst Pf2
         | [H1: getThreadC ?Tp (Ordinal ?Pf) = _,
                H2: getThreadC ?Tp (Ordinal ?Pf) = Krun ?C2 |- _] =>   
           rewrite H2 in H1; inversion H1; try (subst C2; clear H1)
          | [H1: semantics.at_external _ ?C1 = None,
                 H2: semantics.at_external _ ?C1 = Some _ |- _] =>
           congruence
         | [H1: is_true (leq (n (num_threads ?Tp)) ?I),
                H2: is_true (leq (S ?I) (n (num_threads ?Tp))) |- _] =>
           clear - H1 H2;
         exfalso; ssromega
       end).

  Lemma corestep_sim_invariant_l :
    forall sched (tp1 tp1' tp2 : thread_pool) c (m1 m2 m1' : mem) (i j : nat)
           (R: block -> block)
           (Hneq: i <> j) (pfi : i < num_threads tp1)
           (Htp_sim: tp_sim tp1 tp1' j R)
           (Hmem_sim: mem_sim tp1 tp1' m1 m1' j R)
           (Hget: getThreadC tp1 (Ordinal pfi) = Krun c)
           (Hat_external: semantics.at_external the_sem c = None)
           (Hstep: fstep (i :: sched) tp1 m1 sched tp2 m2)
           (Hcompatible2: mem_compatible tp2 m2),
      tp_sim tp2 tp1' j R /\ mem_sim tp2 tp1' m2 m1' j R.
  Proof with (eauto 3 with mem).
    intros. inversion Hstep as [tsched tpt1 tpt2 mt1 m1i ct m2i m' c'| | | | | | | | ];
      [subst tpt1 tpt2 tsched mt1 m' | subst | subst | subst | subst | subst | subst | subst | subst];
      try step_absurd.
    { destruct Hcorestep as [c0 [m0 [Hcorestep Heq]]].
      inversion Heq; subst c0 m0; simpl in *.
      split.
      { subst. inversion Htp_sim.
        econstructor.
      - inversion Hnum. reflexivity.
      - inversion Hcounter. reflexivity.
      - simpl. rewrite if_false. eassumption.
        apply/eqP. intros Hcontra; inversion Hcontra; auto.
      }
      { inversion Hmem_sim as [pf1 pf1' m1j m1'j m1j_eq m1'j_eq].
        assert (pf2: j < num_threads tp2)
          by (subst; simpl; auto).
        assert (Hperm2: pnew = getPermMap m2)
          by (symmetry; eapply updPermMap_get; eauto).
        remember (restrPermMap (permMapsInv_lt Hcompatible2 (Ordinal pf2)))
          as m2j eqn:Hrestr2_j;
          symmetry in Hrestr2_j.
        eapply Mem_sim with (m_tid_eq := m2j) (m'_tid_eq := m1'j)...
        pf_cleanup.
        assert (HcorestepN: corestepN (Modsem.sem Sem) the_ge (S 0) c m1i c' m2i)
          by (unfold corestepN; eauto).
        eapply (updThread_invariants corestep_canonical corestep_permMap_wf Hinv0 Hrestrict_pmap Hthread HcorestepN Htp').
        assert (Hobs': mem_obs_eq id m1j m2j).
        { eapply corestep_disjoint_mem_obs_id
          with (m1j := m1j) (m2j := m2j) (m1i := m1i) (m2i := m2i)
                            (p1j := perm_maps tp1 (Ordinal pf1)).
          - eassumption.
          - simpl in Hrestr2_j. rewrite <- Hrestr2_j. eapply restrPermMap_irr.
            subst tp2. simpl.
            rewrite if_false. pf_cleanup. reflexivity.
            apply/eqP. intro Hcontra.
            inversion Hcontra. auto.
          - eapply Hrestrict.
          - eassumption.
          - destruct Hinv; auto.
          - eassumption.
        } 
        assert (mem_obs_eq R m1j m1'j)...
      }
    }
    Grab Existential Variables.
    clear -Htp' pf2 pf1 Hneq Hcompatible2.
    assert (Hperm_j: perm_maps tp1 (Ordinal (n:=num_threads tp1) (m:=j) pf1) =
                     perm_maps _ (Ordinal pf2)).
    { subst tp2; simpl. rewrite if_false. do 2 eapply f_equal. by erewrite leq_pf_irr.
      apply/eqP. intro Hcontra. inversion Hcontra; auto. }
    rewrite Hperm_j.
    eapply permMapsInv_lt; subst; auto. 
  Qed.

  Lemma corestep_sim_invariant_r :
    forall fsched (tp1 tp1' tp2' : thread_pool) c (m1 m1' m2' : mem) (i j : nat)
           (R: block -> block)
           (Hneq: i <> j) (pfi' : i < num_threads tp1')
           (Htp_sim: tp_sim tp1 tp1' j R)
           (Hmem_sim: mem_sim tp1 tp1' m1 m1' j R)
           (Hget: getThreadC tp1' (Ordinal pfi') = Krun c)
           (Hat_external: semantics.at_external the_sem c = None)
           (Hstep: fstep (i :: fsched) tp1' m1' fsched tp2' m2')
           (Hcompatible2: mem_compatible tp2' m2'),
      tp_sim tp1 tp2' j R /\ mem_sim tp1 tp2' m1 m2' j R.
  Proof with (eauto 3 with mem).
    intros;
    inversion Hstep as [tsched' tpt1' tpt2' mt1' m1i' ct' m2i' m'' c2'| | | | | | | | ];
      [subst tid0 tsched' tpt1' tpt2' mt1' m'' | subst | subst | subst | subst | subst | subst | subst | subst];
      try step_absurd.
    { clear Hstep.
      destruct Hcorestep as [? [? [Hcorestep Heq]]].
      inversion Heq; subst x x0; simpl in *.
      split.
      { inversion Htp_sim. rewrite Htp'.
        econstructor.
        - simpl; assumption.
        - simpl; assumption.
        - simpl. rewrite if_false. eassumption.
          apply/eqP. intros Hcontra; inversion Hcontra; auto.
      }
      { inversion Hmem_sim as [pf1 pf1' m1j m1'j].
        assert (pf2': j < num_threads tp2')
          by (subst; simpl; auto).
        assert (Hperm2': pnew = getPermMap m2')
          by (symmetry; eapply updPermMap_get; eauto).
        remember (restrPermMap (permMapsInv_lt Hcompatible2 (Ordinal pf2')))
          as m2'j eqn:Hrestr2_j;
          symmetry in Hrestr2_j.
        pf_cleanup.
        assert (HcorestepN: corestepN (Modsem.sem Sem) the_ge (S 0) c m1i' c2' m2i')
          by (unfold corestepN; eauto).
        eapply @Mem_sim with (m'_tid_eq := m2'j) (m_tid_eq := m1j)...
        eapply (updThread_invariants corestep_canonical corestep_permMap_wf Hinv' Hrestrict_pmap Hthread HcorestepN Htp').
        assert (Hobs_12j: mem_obs_eq id m1'j m2'j).
        {
          subst tp2'. simpl in Hrestr2_j.
          pf_irr_clean.
          eapply corestep_disjoint_mem_obs_id
          with (m1i := m1i') (m2i := m2i') (m2 := m2') 
                             (p1j := perm_maps tp1' (Ordinal pf1')).
          - eassumption.
          - rewrite <- Hrestr2_j. eapply restrPermMap_irr; eauto.
           rewrite if_false. unfold getThreadPerm.
           do 2 apply f_equal. erewrite leq_pf_irr; eauto.
           apply/eqP; intro Hcontra; inversion Hcontra; auto.
         - rewrite <- Hrestrict'.
           eapply restrPermMap_irr.
           apply f_equal. reflexivity.
         - eapply Hrestrict_pmap.
         - destruct Hinv. auto.
         - eassumption.
        }
        eapply mem_obs_trans...
      }
    } 
    Grab Existential Variables.
    clear -pf2' pf1' Hneq Hcompatible2.
    assert (Hperm_j: perm_maps tp1' (Ordinal (n:=num_threads tp1') (m:=j) pf1') =
                     perm_maps _ (Ordinal pf2')).
    { simpl in *. rewrite if_false. do 2 eapply f_equal. by erewrite leq_pf_irr.
      apply/eqP. intro Hcontra. inversion Hcontra; auto. }
    rewrite Hperm_j.
    eapply permMapsInv_lt; subst; auto.
    eapply permMapsInv_lt; eauto.
  Qed.

(* Lemma corestep_updPermMap : *)
(*       forall tp tp' m m1 c m1' (c' : Modsem.C Sem) pnew tid0 (Htid0_lt_pf  : tid0 < num_threads tp), *)
(*         let: n := counter tp in *)
(*         let: tid := Ordinal Htid0_lt_pf in *)
(*         forall *)
(*           (Hinv: invariant tp) *)
(*           (Hcompatible2: mem_compatible tp m), *)
(*           (Hthread: getThreadC tp tid = Krun c) *)
(*             (Hrestrict_pmap: restrPermMap *)
(*                                (permMapsInv_lt Hcompatible *)
(*                                                (Ordinal tid) = m1)  *)
(*           (Hcorestep: corestepN the_sem the_ge (S 0) c m1 c' m1') *)
(*           (Htp': tp' = updThread tp tid (Krun c') (getPermMap m1') n) *)
(*           (Hupd_mem: updPermMap m1' pnew = None), *)
(*               False. *)
(*     Proof. *)
(*       intros. *)
(*       unfold updPermMap in Hupd_mem. *)
(*       destruct (Pos.eq_dec (Mem.nextblock m1') (PermMap.next (sval pnew))). *)
(*       discriminate. *)
(*       clear Hupd_mem. *)
(*       assert (Hunion_inv := svalP (permMapsUnion (canonical Hinv) (no_race Hinv))). *)
(*       simpl in Hunion_inv. unfold permMapsInv in Hunion_inv. *)
(*       destruct Hunion_inv as [_ [Hgt [_ [_ [Hnext _]]]]]. *)
(*       destruct Hnext as [tid_max Hnext]. *)
(*       assert (Hnext_eq: Mem.nextblock m1 = *)
(*                         PermMap.next (sval (permMapsUnion (canonical Hinv) (no_race Hinv)))). *)
(*       { rewrite <- Hrestrict_pmap. unfold restrPermMap. simpl. *)
(*         rewrite Heq. reflexivity. } *)
(*       assert (Hnext_step: (Mem.nextblock m1 <= Mem.nextblock m1')%positive). *)
(*       { destruct Hcorestep as [c'' [m1'' [Hcorestep Hrefl]]]. *)
(*         unfold corestepN in Hrefl. inversion Hrefl; subst c'' m1''. *)
(*         clear Hinv'. *)
(*         apply corestep_fwd in Hcorestep. *)
(*           by apply forward_nextblock in Hcorestep. *)
(*       } *)
(*       rewrite Hnext_eq in Hnext_step. *)
(*       assert (pf': tid0 < num_threads tp') by (subst; simpl; assumption). *)
(*       assert (Hnext_m1' : Mem.nextblock m1' = PermMap.next (getThreadPerm tp' (Ordinal pf'))). *)
(*       { subst tp'. simpl. rewrite if_true. reflexivity. *)
(*         apply/eqP. apply f_equal. erewrite leq_pf_irr; eauto. } *)
(*       assert (Hgt_m1': forall tid, ~ Coqlib.Plt (Mem.nextblock m1') *)
(*                                 (PermMap.next (getThreadPerm tp' tid))). *)
(*       { intros tid' Hcontra. subst tp'. simpl in Hcontra. *)
(*         destruct ( tid' == *)
(*                    Ordinal (n:=num_threads tp) (m:=tid0) Htid0_lt_pf) eqn:Hguard; *)
(*           rewrite Hguard in Hcontra; simpl in Hcontra. *)
(*         - unfold Coqlib.Plt in Hcontra. eapply Pos.lt_irrefl; eassumption. *)
(*         - specialize (Hgt tid'). simpl in *. *)
(*           unfold Coqlib.Plt in Hcontra, Hgt. clear Hinv' Hcorestep. *)
(*           eapply Hgt. unfold getThreadPerm. *)
(*           eapply Pos.le_lt_trans. eapply Hnext_step. *)
(*           eassumption. *)
(*       } *)
(*       assert (Hnext_pnew : PermMap.next (sval pnew) = Mem.nextblock m1'). *)
(*       { assert (Hinv'' := svalP pnew). simpl in Hinv''. *)
(*         destruct Hinv'' as [_ [Hgt' [_ [_ [Hnext' _]]]]]. *)
(*         unfold getThreadPerm in Hgt_m1'. simpl in Hgt', Hgt_m1'. *)
(*         destruct Hnext' as [tid'' Hnext'']. *)
(*         specialize (Hgt_m1' tid''). *)
(*         unfold Coqlib.Plt in *. *)
(*         specialize (Hgt' (Ordinal (n:=num_threads tp') (m:=tid0) pf')). *)
(*         apply Pos.le_nlt in Hgt'. apply Pos.le_nlt in Hgt_m1'. *)
(*         simpl in Hnext''. rewrite <- Hnext'' in Hgt_m1'. *)
(*         unfold getThreadPerm in Hnext_m1'. simpl in *. rewrite <- Hnext_m1' in Hgt'. *)
(*         eapply Pos.le_antisym; eassumption. *)
(*       } *)
(*       auto. *)
(*     Qed. *)

  Hypothesis corestep_obs_eq :
    forall c1 c2 m1 m1' m2 R
      (Hsim: mem_obs_eq R m1 m1')
      (Hstep: corestep the_sem the_ge c1 m1 c2 m2),
    exists m2',
      corestep the_sem the_ge (rename_code R c1) m1' (rename_code R c2) m2'
      /\ mem_obs_eq R m2 m2'.

  Lemma corestep_sim_aux :
    forall fsched fsched' (tp1 tp2 tp1' : thread_pool) c1 (m1 m2 m1' : mem) R
      (i : nat) (pfi : i < num_threads tp1)
      (Hat_external1: semantics.at_external the_sem c1 = None)
      (Htp_simi: tp_sim tp1 tp1' i R)
      (Hmem_simi: mem_sim tp1 tp1' m1 m1' i R)
      (Hget1: getThreadC tp1 (Ordinal pfi) = Krun c1)
      (Hstep1: fstep (i :: fsched) tp1 m1 fsched tp2 m2),
    exists tp2' m2', fstep (i :: fsched') tp1' m1' fsched' tp2' m2' /\
                (forall tid, tp_sim tp1 tp1' tid R -> tp_sim tp2 tp2' tid R) /\
                (forall tid, mem_sim tp1 tp1' m1 m1' tid R ->
                          mem_sim tp2 tp2' m2 m2' tid R).
  Proof with (eauto 3 with mem).
    intros; inversion Hstep1 as [tsched tpt1 tpt2 mt1 m1i ct m2i m' c'| | | | | | | | ];
    [subst tid0 tpt1 tpt2 tsched mt1 m' | subst | subst | subst | subst | subst | subst | subst | subst];
    try step_absurd.
    inversion Hmem_simi as [pf_tid0 pf_tid0' m_tid0 m_tid0' m_tid0_eq m_tid0_eq'
                                    Hinv0 Hinv0'].
    pf_irr_clean; pf_cleanup.
    destruct Hcorestep as [c2 [m2it [Hcore Hrefl]]].
    unfold corestepN in Hrefl. inversion Hrefl; subst c' m2it.
    assert (Hm_eq: m_tid0 = m1i).
    { rewrite <- Hrestrict. rewrite <- Hrestrict_pmap.
      apply restrPermMap_irr. reflexivity. }
    subst m_tid0. rewrite Hm_eq in Hmeq.
    assert (Hobs_core: mem_obs_eq R m1i m_tid0')...
    destruct (corestep_obs_eq _ _ _ Hobs_core Hcore) as [m2i' [Hcore' Hobs']].
    assert (HcoreN': corestepN the_sem the_ge 1 (rename_code R c1) m_tid0' (rename_code R c2) m2i')
      by (unfold corestepN; eexists; eauto).
    inversion Htp_simi.
    unfold getThreadC in Hthread.
    pf_cleanup.
    rewrite Hthread in Hpool. simpl in Hpool.
    assert (Hget': getThreadC tp1' (Ordinal pf_tid0') = Krun (rename_code R c1))
           by (by unfold getThreadC).
    remember (updThread tp1' (Ordinal pf_tid0') (rename_core R (Krun c2))
                        (getPermMap m2i') (counter tp1')) as tp2' eqn:Htp2'.
    (* assert (Hrestrict_tid0': *)
    (*           restrPermMap Heq' (permMapsInv_lt Hcompatible' *)
    (*                                (Ordinal (n:=num_threads tp1') (m:=tid0) pf_tid0')) = m_tid0') *)
    (*   by (rewrite <- Hrestrict'; apply restrPermMap_irr; reflexivity). *)
    
    Hypothesis pmap_computable : forall fsched tp1 tp2 tp1' tid m1 m2 m1' p R,
                                   tp_sim tp1 tp1' tid R ->
                                   mem_sim tp1 tp1' m1 m1' tid R ->
                                   fstep (tid :: fsched) tp1 m1 fsched tp2 m2,
      exists 
                                         
    
    pose (Hupd_inv:= schedNext_inv (updThread_invariants
                                       corestep_canonical corestep_permMap_wf
                                      Hinv' 
                                      Hrestrict_tid0' Hget' HcoreN' Htp2')).
    remember (updPermMap m2i' (sval (permMapsUnion (canonical Hupd_inv) (no_race Hupd_inv))))
      as m2'o eqn:Hupd2';
      symmetry in Hupd2'.
    subst Hupd_inv.
    destruct m2'o as [m2'|]; [|exfalso; eapply corestep_updPermMap; eauto].
    exists (schedNext tp2'); exists m2'.
    split; [eapply fstep_core with (c:=rename_code R c1) (m' := m2'); eauto |].
    split.
    { intros tid Htp_sim.
      subst tpt2. subst tp2'.
      destruct (tid < num_threads (schedNext
                                     (updThread tp1 (Ordinal Htid0_lt_pf0)
                                                (Krun ci') (getPermMap m2i)
                                                (counter tp1)))) eqn:pf_tid;
        [|inversion Htp_sim; simpl in pf_tid; unfold is_true in *; congruence]. 
      assert (pf_tid':
                tid < num_threads
                        (schedNext
                           (updThread tp1' (Ordinal (n:=num_threads tp1') (m:=tid0) pf_tid0')
                                      (Krun (rename_code R ci')) (getPermMap m2i') 
                                      (counter tp1'))))
        by (simpl in *; rewrite <- Hnum; assumption).
      apply Tp_sim with (pf := pf_tid) (pf' := pf_tid'). simpl. assumption.
        by simpl.
        simpl.
        destruct (tid == tid0) eqn:Htid_eq;
          move/eqP:Htid_eq=>Htid_eq.
      + subst. pf_cleanup. rewrite if_true. rewrite if_true.
        reflexivity. apply/eqP. apply f_equal.
        reflexivity.
        apply/eqP. pf_cleanup. apply f_equal.
        erewrite leq_pf_irr; eauto.
      + rewrite if_false. rewrite if_false.
        inversion Htp_sim. simpl in pf_tid, pf_tid'. pf_cleanup.
        assert (pf = pf_tid) by (erewrite leq_pf_irr; eauto); subst pf.
        rewrite Hpool0.
        do 2 apply f_equal. reflexivity.
        apply/eqP. intro Hcontra. inversion Hcontra; auto.
        apply/eqP. intro Hcontra. inversion Hcontra; auto.
    }
    { intros tid Hmem_sim. subst tpt2 tp2'.
      inversion Hmem_sim as [pf_tid pf_tid' m_tid m_tid' m_tid_eq m_tid_eq'
                                    Hinv2 Hinv2'
                                    Heq2 Heq2' Hrestrict_tid Hrestrict_tid'
                                    Hmeq_tid Hmeq_tid' Hobs_tid].
      assert (pf2_tid: tid < num_threads (schedNext
                                      (updThread tp1 (Ordinal Htid0_lt_pf0)
                                                 (Krun ci') (getPermMap m2i) (counter tp1))))
        by (simpl in *; assumption).
      assert (pf2_tid':
                tid < num_threads
                        (schedNext
                           (updThread tp1' (Ordinal pf_tid0')
                                      (Krun (rename_code R ci')) (getPermMap m2i') 
                                      (counter tp1'))))
        by (simpl in *; assumption). pf_irr_clean.
      destruct (tid == tid0) eqn:Htid_eq; move/eqP:Htid_eq=>Htid_eq.
      + subst tid.
        assert (Heq2i: sval pnew = getPermMap m2)
          by (apply updPermMap_get in Hupd; symmetry; assumption).
        rewrite <- Hunion in Heq2i.             
        assert(restrPermMap Heq2i
                            (permMapsInv_lt (svalP _)
                                            (Ordinal pf2_tid)) =~ m2i).
        { simpl.
          assert (pf2_tid = Htid0_lt_pf0) by (erewrite leq_pf_irr; eauto).
          subst pf2_tid.
          unfold restrPermMap, mem_func_eq. simpl.
          rewrite if_true. simpl.
          split; [symmetry | split; symmetry]; eauto with permMaps.
            by apply/eqP.
        } 
        match goal with
          | [H: updPermMap m2i' ?Expr = Some _ |- _] =>
            remember Expr as pnew' eqn:Hpnew'
        end.
        assert (Heq2i': pnew' = getPermMap m2')
          by (apply updPermMap_get in Hupd2'; symmetry; assumption).
        subst pnew'.
        assert(restrPermMap Heq2i'
                            (permMapsInv_lt (svalP _)
                                            (Ordinal pf2_tid')) =~ m2i').
        { simpl.
          unfold restrPermMap, mem_func_eq. simpl.
          rewrite if_true. simpl.
          split; [symmetry | split; symmetry]; eauto with permMaps.
          apply/eqP; apply f_equal; erewrite leq_pf_irr; eauto.
        }
        econstructor; eauto.
      + assert (Heq2_tid: sval pnew = getPermMap m2)
          by (apply updPermMap_get in Hupd; symmetry; assumption).
        destruct pnew as [pnewV pnewP].
        assert (Hlt2_tid: permMapLt (perm_maps tp1 (Ordinal (n:=num_threads tp1) (m:=tid) pf_tid))
                          pnewV).
        { assert (Hperm_eq:
                    getThreadPerm tp1 (Ordinal pf_tid) =
                    getThreadPerm (updThread tp1
                                             (Ordinal Htid0_lt_pf0)
                                             (Krun c1)
                                             (getPermMap m2i) 
                                             (counter tp1)) (Ordinal pf2_tid)).
          { simpl. rewrite if_false. unfold getThreadPerm.
            pf_cleanup. reflexivity.
            apply/eqP; intro Hcontra; inversion Hcontra; auto.
          }
          unfold getThreadPerm in Hperm_eq.
          rewrite Hperm_eq.
          apply permMapsInv_lt. 
          apply pnewP.
        }
        remember (restrPermMap Heq2_tid Hlt2_tid) as m2_tid eqn:Hrestrict2_tid;
          symmetry in Hrestrict2_tid.
        assert (Hobs_eq2: mem_obs_eq id m_tid m2_tid).
        { eapply corestep_disjoint_mem_obs_id
          with (m1j := m_tid) (m2j := m2_tid) (m1i := m1i) (m2i := m2i) (m2 := m2)
                              (pnew := pnewV) (Heq2 := Heq2_tid)
                              (p1j := perm_maps tp1 (Ordinal pf_tid))
                              (Heq1 := Heq0)
                              (Hlt1j := (permMapsInv_lt
                                           (svalP (permMapsUnion (canonical Hinv0) (no_race Hinv0)))
                                           (Ordinal (n:=num_threads tp1) (m:=tid) pf_tid)))
                              (Hlt1i := (permMapsInv_lt
                                           (svalP (permMapsUnion (canonical Hinv0) (no_race Hinv0)))
                                                        (Ordinal Htid0_lt_pf0)))
                              (Hlt2j := Hlt2_tid).
          - assumption.
          - assumption.
          - rewrite <- Hrestrict_tid.
            reflexivity.
          - rewrite Hm_eq. reflexivity.
          - destruct Hinv0; auto.
          - eassumption.
        } 
        match goal with
          | [H: updPermMap m2i' ?Expr = Some _ |- _] =>
            pose Expr as pnew'
        end.
        assert (Heq2_tid': pnew' = getPermMap m2')
          by (apply updPermMap_get in Hupd2'; symmetry; assumption).
        assert (Hlt2_tid': permMapLt (perm_maps tp1' (Ordinal pf_tid'))
                                    pnew').
        { assert (Hperm_eq:
                    getThreadPerm tp1' (Ordinal pf_tid') =
                    getThreadPerm (updThread tp1'
                                             (Ordinal pf_tid0')
                                             (Krun (rename_code R ci'))
                                             (getPermMap m2i') 
                                             (counter tp1')) (Ordinal pf2_tid')).
        { simpl. rewrite if_false. unfold getThreadPerm.
          pf_cleanup. reflexivity.
          apply/eqP; intro Hcontra; inversion Hcontra; auto.
        } subst pnew'.
        unfold getThreadPerm in Hperm_eq.
        rewrite Hperm_eq.
        apply permMapsInv_lt. 
        match goal with
          | [ |- permMapsInv _ (sval ?X)] =>
            apply (svalP X)
        end.
        }
        remember (restrPermMap Heq2_tid' Hlt2_tid') as m2_tid' eqn:Hrestrict2_tid';
          symmetry in Hrestrict2_tid'.
        pf_irr_clean; pf_cleanup; simpl in *.
        assert (Hobs_eq2': mem_obs_eq id m_tid' m2_tid').
        { eapply corestep_disjoint_mem_obs_id
          with (m1j := m_tid') (m2j := m2_tid') (m1i := m_tid0') (m2i := m2i') (pnew := pnew')
                               (p1j := perm_maps tp1' (Ordinal pf_tid'))
                               (Heq2 := Heq2_tid') (Heq1 := Heq')
                               (Hlt1j := permMapsInv_lt
                                           (svalP (permMapsUnion (canonical Hinv') (no_race Hinv')))
                                                         (Ordinal pf_tid'))
                               (Hlt1i := permMapsInv_lt
                                           (svalP (permMapsUnion (canonical Hinv') (no_race Hinv')))
                                           (Ordinal pf_tid0'))
                               (Hlt2j := Hlt2_tid'). 
          - assumption.
          - assumption.
          - rewrite Hrestrict_tid'. reflexivity.
          - rewrite Hrestrict_tid0'. reflexivity.
          - destruct Hinv'; auto.
          - eassumption.
        }
        assert (Hobs_core2: mem_obs_eq R m2_tid m2_tid').
        { assert (mem_obs_eq R m_tid m2_tid').
          apply mem_obs_trans with (m1j := m_tid) (m1'j := m_tid').
          eapply mem_func_obs_eq; eauto. assumption.
          eapply mem_obs_trans_comm; eauto. }
        
        econstructor; eauto.
        simpl. rewrite <- Hrestrict2_tid.
        simpl. unfold mem_func_eq. split; eauto. split; eauto.
        simpl. rewrite if_false. reflexivity.
        apply/eqP; intros Hcontra; inversion Hcontra; auto.
        rewrite <- Hrestrict2_tid'. simpl. unfold mem_func_eq.
        split; eauto. split; eauto.
        simpl. rewrite if_false. reflexivity.
        apply/eqP; intros Hcontra; inversion Hcontra; auto.
    }
    Grab Existential Variables.
    - subst pnew'. eassumption.
    - rewrite Hunion. simpl. assumption.
    - simpl. intros. 
      match goal with
        | [H: permMapsUnion ?Pf1 ?Pf2 = exist _ _ _ |- _ ] =>
          assert (Hcanonical2 := Pf1);
            assert (Hrace2 := Pf2)
      end.
      split; auto.
      simpl.
      intros pf_lp.
      rewrite if_false. destruct Hinv0. auto.
      apply/eqP. intro Hcontra. inversion Hcontra as [Heq].
      clear -Hinv0 Hget1b Hcore Heq.
      subst.  destruct Hinv0 as [_ _ Hlp].
      destruct (Hlp Htid0_lt_pf0) as [c [Hget Hhalted]].
      unfold getThreadC in Hget. rewrite Hget1b in Hget. inversion Hget; subst.
      apply corestep_not_halted in Hcore. rewrite Hcore in Hhalted. auto.
  Qed.
      
  Lemma corestep_sim :
    forall (tp1 tp2 tp3 tp1' : thread_pool) c1 c2 (m1 m2 m3 m1' : mem) R
      (Hinv': invariant tp1')
      (Hsim: forall tid, tid < num_threads tp1 -> tp_sim tp1 tp1' tid R /\
                                            mem_sim tp1 tp1' m1 m1' tid R)
      (Heq': sval (permMapsUnion (canonical Hinv') (no_race Hinv')) = getPermMap m1')
      (i j : nat) (Hneq: i <> j) (pfi : i < num_threads tp1)
      (pfj : j < num_threads tp2) xs xs'
      (Hsched: schedule tp1 = i :: j :: xs)
      (Hsched': schedule tp1' = j :: i :: xs')
      (Hget1: getThreadC tp1 (Ordinal pfi) = Krun c1)
      (Hat_external1: semantics.at_external the_sem c1 = None)
      (Hstep1: fstep tp1 m1 tp2 m2)
      (Hget2: getThreadC tp2 (Ordinal pfj) = Krun c2)
      (Hat_external2: semantics.at_external the_sem c2 = None)
      (Hstep2: fstep tp2 m2 tp3 m3),
    exists tp2' m2' tp3' m3',
      fstep tp1' m1' tp2' m2' /\ fstep tp2' m2' tp3' m3' /\
      (forall tid, tid < num_threads tp3 -> tp_sim tp3 tp3' tid R /\
                                            mem_sim tp3 tp3' m3 m3' tid R).
  Proof.
    intros.
    (* j-simulation of tp2-tp1' *)
    assert (Hsimj_21': tp_sim tp2 tp1' j R /\ mem_sim tp2 tp1' m2 m1' j R).
    { inversion Hstep1; step_absurd; subst;
      try (clear Hupd_mem; step_absurd).
      simpl in pfj. destruct (Hsim _ pfj).
      eapply corestep_sim_invariant_l; eauto.
      rewrite Hsched. reflexivity.
    }
    destruct Hsimj_21' as [Htpsimj_21' Hmemsimj_21'].
    (* j-simulation of tp3-tp2' *)
    assert (Hsimj_32':
              exists tp2' m2',
                fstep tp1' m1' tp2' m2' /\
                (forall tid, tp_sim tp2 tp1' tid R -> tp_sim tp3 tp2' tid R) /\
                (forall tid,
                   mem_sim tp2 tp1' m2 m1' tid R -> mem_sim tp3 tp2' m3 m2' tid R)).
    { eapply corestep_sim_aux with (tp1 := tp2) (tp2 := tp3); eauto.
      - inversion Hstep1; step_absurd; subst; try (clear Hupd_mem; step_absurd).
        simpl. rewrite Hsched. reflexivity.
      - rewrite Hsched'. reflexivity.
    }
    destruct Hsimj_32' as [tp2' [m2' [Hstep1' [Htp_sim32' Hmem_sim32']]]].
    (* i-simulation of tp1-tp2' *)
    assert (Hsimi_12': tp_sim tp1 tp2' i R /\ mem_sim tp1 tp2' m1 m2' i R).
    { assert (pfj': j < num_threads tp1')
        by (inversion Htpsimj_21'; assumption).
      destruct (Hsim _ pfi).
      eapply corestep_sim_invariant_r with (pfi' := pfj') (c := rename_code R c2);
        eauto.
      rewrite Hsched'. reflexivity.
      inversion Htpsimj_21'. unfold getThreadC in *. pf_cleanup. rewrite <- Hpool.
      rewrite Hget2. reflexivity.
        by apply rename_code_at_ext.
    }
    destruct Hsimi_12' as [Htpsimi_12' Hmemsimi_12'].
    (* i-simulation of tp2-tp3' *)
    assert (Hsimi_23':
              exists tp3' m3',
                fstep tp2' m2' tp3' m3' /\
                (forall tid, tp_sim tp1 tp2' tid R -> tp_sim tp2 tp3' tid R) /\
                (forall tid,
                   mem_sim tp1 tp2' m1 m2' tid R -> mem_sim tp2 tp3' m2 m3' tid R)).
    { assert (Hget1': forall pfj',
                        getThreadC tp1' (Ordinal (m := j) pfj') = rename_core R (Krun c2)).
      { intros. inversion Htpsimj_21'. unfold getThreadC in *.
        rewrite <- Hget2. pf_cleanup. rewrite Hpool. reflexivity. }
      assert (Hat_external1': semantics.at_external the_sem (rename_code R c2) = None)
        by (by apply rename_code_at_ext).
      simpl in Hget1'.
      inversion Hstep1';
      repeat match goal with
        | [H1: List.hd_error (schedule ?Tp) = Some ?Tid,
               H2: schedule ?Tp = _ |- _] => rewrite H2 in H1; inversion H1;
                                             subst Tid
        | [pf: is_true (?Tid < n (num_threads tp1')) |- _] => specialize (Hget1' pf)
        | [H1: getThreadC tp1' _ = _, H2: getThreadC tp1' _ = Krun ?C |- _] =>
          rewrite H1 in H2; inversion H2; subst C
             end; step_absurd. subst m m' tp.
      - assert (Heq2': sval pnew = getPermMap m2')
          by (symmetry; eapply updPermMap_get; eauto).
        rewrite <- Hunion in Heq2'.
        eapply corestep_sim_aux with (tp1 := tp1) (tp2 := tp2) (c1 := c1); eauto.
        rewrite Hsched. simpl. reflexivity.
        subst tp'. simpl. rewrite Hsched'. reflexivity. rewrite H1.
        assumption.
        rewrite H1. assumption.
      - inversion Htpsimj_21'. exfalso. clear - Htid0_lt_pf pf'. ssromega.
    }
    destruct Hsimi_23' as [tp3' [m3' [Hstep2' [Htp_sim23' Hmem_sim23']]]].
    exists tp2' m2' tp3' m3'; split; auto; split; auto.
    intros tid pf3_tid.
    assert (Hnum_eq: num_threads tp3 = num_threads tp1).
    { specialize (Htp_sim32' _ Htpsimj_21'). inversion Htpsimi_12';
        inversion Htp_sim32'. rewrite Hnum. assumption. }
    destruct (i == tid) eqn:Htid; move/eqP:Htid=>Htid; subst.
    + eapply corestep_sim_invariant_l; eauto.
      inversion Hstep1; step_absurd; subst; try (clear Hupd_mem; step_absurd).
      simpl. rewrite Hsched. reflexivity.
    + assert (Hsimtid_21': tp_sim tp2 tp1' tid R /\ mem_sim tp2 tp1' m2 m1' tid R).
      { inversion Hstep1; step_absurd; subst; try (clear Hupd_mem; step_absurd).
        simpl in pf3_tid.
        rewrite Hnum_eq in pf3_tid.
        destruct (Hsim _ pf3_tid).
        eapply corestep_sim_invariant_l; eauto.
        rewrite Hsched. reflexivity.
      }
      destruct Hsimtid_21' as [Htpsimtid_21' Hmemsimtid_21'].
      assert (Hget1': forall pfj',
                        getThreadC tp1' (Ordinal (m := j) pfj') = rename_core R (Krun c2)).
      { intros. inversion Htpsimj_21'. unfold getThreadC in *.
        rewrite <- Hget2. pf_cleanup. rewrite Hpool. reflexivity. }
      assert (Hat_external1': semantics.at_external the_sem (rename_code R c2) = None)
        by (by apply rename_code_at_ext).
      simpl in Hget1'.
      inversion Htpsimj_21'.
      inversion Hstep1';
        repeat match goal with
                 | [H1: List.hd_error (schedule ?Tp) = Some ?Tid,
                        H2: schedule ?Tp = _ |- _] => rewrite H2 in H1; inversion H1;
                                                      subst Tid
                 | [pf: is_true (?Tid < n (num_threads tp1')) |- _] => specialize (Hget1' pf)
                 | [H1: getThreadC tp1' _ = _, H2: getThreadC tp1' _ = Krun ?C |- _] =>
                   rewrite H1 in H2; inversion H2; subst C
               end; step_absurd. subst m m' tp tp'.
      inversion  Htpsimi_12'. 
      eapply corestep_sim_invariant_r with
      (j := tid) (tp1' := tp2') (c := rename_code R c1) (pfi' := pf'0);
        eauto.
      subst tp2'.
      simpl. rewrite Hsched'. reflexivity.
      unfold getThreadC in *. 
      pf_cleanup. rewrite Hget1 in Hpool0. simpl in Hpool0. rewrite Hpool0. reflexivity.
        by apply rename_code_at_ext.
  Qed.

End CoreLemmas.
End CoreLemmas.


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


                
(*
(* Computing the union of permission maps*)
Section PermMapConstruction.

 Import Maps SeqLemmas.

 (* This cannot be partial because we do not know the domain of the functions on ofs*)
 Definition pmap_union (pmap1 pmap2 : PermMap.t)
             (Hcanonical1: isCanonical pmap1)
             (Hcanonical2: isCanonical pmap2)
             (Hdisjoint : permMapsDisjoint pmap1 pmap2) : PermMap.t.
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
       unfold Maps.PMap.get. unfold isCanonical in *. simpl. intros.
       rewrite PTree.gcombine.
       destruct (Hdisjoint b ofs) as [pu Hunion].
       unfold permMapsDisjoint in Hdisjoint.
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
     { intros b ofs k Hnext. clear Hdisjoint. unfold isCanonical in *.
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
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12)
            b ofs,
       PMap.get b (PermMap.map pmap12) ofs Cur = PMap.get b (PermMap.map pmap1) ofs Cur \/
       PMap.get b (PermMap.map pmap12) ofs Cur = PMap.get b (PermMap.map pmap2) ofs Cur.
   Proof.
     intros. unfold pmap_union in Hunion; unfold isCanonical in *.
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
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
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
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
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
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
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
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hdisjoint : permMapsDisjoint pmap1 pmap2) 
            (Hunion: pmap_union Hcanonical1 Hcanonical2 Hdisjoint = pmap12),
       (PermMap.map pmap12).1 = fun _ _ => None.
     intros. rewrite <- Hunion. unfold pmap_union. simpl. reflexivity.
   Defined.
       
   Lemma pmap_union_inv :
     forall (pmap1 pmap2 pmap3 pu12 : PermMap.t)
            (Hcanonical1: isCanonical pmap1)
            (Hcanonical2: isCanonical pmap2)
            (Hcanonical3: isCanonical pmap3)
            (Hdisjoint12: permMapsDisjoint pmap1 pmap2)
            (Hdisjoint13: permMapsDisjoint pmap1 pmap3)
            (Hdisjoint23: permMapsDisjoint pmap2 pmap3)
            (Hunion12: pmap_union Hcanonical1 Hcanonical2 Hdisjoint12 =
                       pu12),
     exists pf pu, pmap_union (pmap_union_canonical Hunion12) Hcanonical3 pf = pu.
   Proof.
     intros.
     assert (pf : permMapsDisjoint (pu12) (pmap3)).
     { unfold permMapsDisjoint in *. intros b ofs.
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

     
     Lemma threadSeq_complete :
       forall tid i l (Hl: threadSeq i l) (Hle: i <= tid)
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
         
      Lemma subSeq_cons : forall {T:eqType} x (s' s : seq T) (Hneq: s' <> x :: s)
                                (Hsub: subSeq s' (x :: s)), subSeq s' s.
     Proof.
       unfold subSeq. intros.
       simpl in Hsub. destruct ((size s).+1 - size s') eqn:Hn.
       exfalso; move/eqP:Hsub=>Hsub. auto.
       replace (size s - size s') with n by ssromega.
       assumption.
     Defined.
      
     Lemma threadSeq_size :
       forall i l (Hseq: threadSeq i l),
         size l = ((n num_threads) - i).
     Proof.
       intros i l. generalize dependent i. induction l; intros.
       - inversion Hseq.
       - inversion Hseq as [|? ? ? Hseq']; subst.
         simpl. clear Hseq IHl. destruct num_threads. ssromega.
         simpl. eapply IHl in Hseq'.
         clear Hseq IHl. destruct num_threads.
         simpl in *. ssromega.
     Defined.
         
     Lemma threadSeq_subSeq :
       forall i l l' (Hseq: threadSeq i l) (Hsub: subSeq l' l)
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

     (* For the constructive version we assumed that all perm maps are canonical,
        we can lift this assumption since we can compute a canonical version of a perm map.
        Let's use the hypothesis for now and instantiate it later*)
     Hypothesis permMapsCanonical :
       forall tid, isCanonical (perm_maps tp tid).                                   

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

     Hypothesis Hrace : race_free tp.
     
     Definition permMapsUnion : {p : PermMap.t | permMapsInv tp p}.
       refine (
           let fix aux l
                   acc (Hl': forall x, List.In x l -> permMapsDisjoint (perm_maps tp x) acc)
                   (Hacc: isCanonical acc)
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
                                   exists tid : 'I_num_threads,
                                     List.In tid lhd /\
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
           clear aux. subst. split; [idtac | split; [idtac | split; [idtac | split]]].
           - clear Hinv_eq Hinit Hperm_ord Hnext Hsub Hl'. assumption.
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
 *)

                    (* Lemma updThread_ext_invariants : *)
    (*   forall (tp tp' : thread_pool) c' tid0 (pf: tid0 < num_threads tp) *)
    (*     pmap counter *)
    (*     (Hinv: invariant tp) *)
    (*     (Hpmap_wf: permMap_wf tp pmap tid0) *)
    (*     (Hpmap_can: isCanonical pmap) *)
    (*     (Hthread: exists t, *)
    (*                 getThreadC tp (Ordinal pf) = Kstage t.1 t.2.1 t.2.2) *)
    (*     (Htp': tp' = updThread tp (Ordinal pf) (Krun c') pmap counter), *)
    (*     invariant tp'. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp Hlp_max]; split. *)
    (*   { intros tid'.  unfold isCanonical in *. *)
    (*     destruct tid' as [tid' pf']. *)
    (*     subst tp'. simpl in *. *)
    (*     destruct (tid' == tid0) eqn:Heq; move/eqP:Heq=>Heq; subst. *)
    (*     - rewrite if_true. auto. *)
    (*       pf_cleanup. apply eq_refl. *)
    (*     - rewrite if_false. auto. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; by subst. *)
    (*   } *)
    (*   { unfold race_free. intros. *)
    (*     destruct (tid0 == tid1) eqn:Heq0, (tid0 == tid0') eqn:Heq0'; *)
    (*       move/eqP:Heq0=>Heq0; move/eqP:Heq0'=>Heq0'; subst; simpl in *. *)
    (*     - exfalso. auto. *)
    (*     - rewrite if_true. rewrite if_false. *)
    (*       unfold permMap_wf in Hpmap_wf. *)
    (*       apply permMapsDisjoint_comm. *)
    (*       eapply Hpmap_wf; eauto. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; by subst. *)
    (*       apply/eqP. rewrite (leq_pf_irr _ _ Htid0 pf). reflexivity. *)
    (*     - rewrite if_false. rewrite if_true. *)
    (*       eapply Hpmap_wf; eauto. rewrite (leq_pf_irr _ _ Htid0' pf). apply eq_refl. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; by subst. *)
    (*     - rewrite if_false. rewrite if_false. eapply Hrace; eauto. *)
    (*       apply/eqP. intro Hcontra; inversion Hcontra; by subst. *)
    (*       apply/eqP. intro Hcontra; inversion Hcontra; by subst. *)
    (*   } *)
    (*   { intros. subst tp'; simpl in *. *)
    (*     destruct (Hlp pf0) as [c0 [Hthread0 Hhalted]]. *)
    (*     destruct (tid0 == 0) eqn:Htid0; move/eqP:Htid0=>Htid0. *)
    (*     - subst. pf_cleanup.  *)
    (*       destruct Hthread as [? Hthread]. rewrite Hthread0 in Hthread. *)
    (*       discriminate. *)
    (*       exists c0. rewrite if_false. *)
    (*       split; auto. *)
    (*       apply/eqP. intro Hcontra. inversion Hcontra; auto. *)
    (*   }    *)
    (* Defined. *)

    (* Lemma addThread_ext_invariants : *)
    (*   forall (tp tp' : thread_pool) c' pmap *)
    (*     (Hinv: invariant tp) *)
    (*     (Hpmap_wf: newPermMap_wf tp pmap) *)
    (*     (Hpmap_can: isCanonical pmap) *)
    (*     (Htp': tp' = addThread tp (Krun c') pmap), *)
    (*     invariant tp'. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp]; split. *)
    (*   { intros tid. unfold isCanonical in *. *)
    (*     destruct tid as [tid pf]. *)
    (*     subst tp'. simpl in *. *)
    (*     destruct ( unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                       (Ordinal (n:=(num_threads tp).+1) (m:=tid) pf)) eqn:Heqo; rewrite Heqo; auto. *)
    (*   } *)
    (*   { unfold race_free in *. intros. subst. simpl. *)
    (*     unfold newPermMap_wf in Hpmap_wf. *)
    (*     destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                      (Ordinal (n:=(num_threads tp).+1) (m:=tid0) Htid0)) as [o|] eqn:Heqo. *)
    (*     + rewrite Heqo. *)
    (*       apply unlift_m_inv in Heqo. subst. *)
    (*       destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                        (Ordinal (n:=(num_threads tp).+1) (m:=tid0') Htid0')) as [o'|] eqn:Heqo'. *)
    (*       * rewrite Heqo'. apply unlift_m_inv in Heqo'. subst. *)
    (*         unfold race_free in Hrace. *)
    (*         destruct o, o'. *)
    (*         eapply Hrace; eauto. *)
    (*       * rewrite Heqo'. unfold newPermMap_wf in Hpmap_wf. *)
    (*         destruct o. *)
    (*         eapply Hpmap_wf; eauto. *)
    (*     + rewrite Heqo. *)
    (*       destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                        (Ordinal (n:=(num_threads tp).+1) (m:=tid0') Htid0')) as [o'|] eqn:Heqo'. *)
    (*       * rewrite Heqo'. destruct o'. unfold newPermMap_wf in Hpmap_wf. *)
    (*         apply permMapsDisjoint_comm. *)
    (*         eapply Hpmap_wf. *)
    (*       * exfalso. *)
    (*         assert (Hcontra: unlift_spec (ordinal_pos_incr (num_threads tp)) *)
    (*                                      (Ordinal (n:=(num_threads tp).+1) (m:=tid0) Htid0) None) *)
    (*           by (rewrite <- Heqo; apply/unliftP). *)
    (*         inversion Hcontra as [|Hcontra']. *)
    (*         unfold ordinal_pos_incr in Hcontra'. inversion Hcontra'. subst. *)
    (*         assert (Hcontra2: unlift_spec (ordinal_pos_incr (num_threads tp)) *)
    (*                                       (Ordinal (n:=(num_threads tp).+1) (m:=tid0') Htid0') None) *)
    (*           by (rewrite <- Heqo'; apply/unliftP). *)
    (*         inversion Hcontra2 as [|Hcontra2']. *)
    (*         unfold ordinal_pos_incr in *. inversion Hcontra2'. subst. *)
    (*         ssromega. *)
    (*   } *)
    (*   { intros. subst tp'. simpl. *)
    (*     destruct (unlift (ordinal_pos_incr (num_threads tp)) *)
    (*                      (Ordinal (n:=(num_threads tp).+1) (m:=0) pf)) eqn:Hunlift. *)
    (*     - simpl in pf. *)
    (*       assert (pf0: 0 < num_threads tp) by (clear -pf; destruct num_threads; ssromega). *)
    (*       destruct (Hlp pf0) as [c0 [Hget Hhalted]]. destruct o.  *)
    (*       rewrite Hunlift.  *)
    (*       apply unlift_m_inv in Hunlift. simpl in *. subst.  pf_cleanup. exists c0. *)
    (*       auto. *)
    (*     - rewrite Hunlift. simpl in pf. *)
    (*       assert (pf0: 0 < num_threads tp) by (clear -pf; destruct num_threads; ssromega). *)
    (*       exfalso. *)
    (*       assert (Hun:= unliftP (ordinal_pos_incr (num_threads tp)) *)
    (*                             (Ordinal (n:=(num_threads tp).+1) (m:=0) pf)). *)
    (*       rewrite Hunlift in Hun. *)
    (*       inversion Hun. inversion H. ssromega. *)
    (*   } *)
    (* Defined. *)
    
    (* Lemma mklock_inv : *)
    (*   forall tp tp' tp'' m m1 b ofs m1' c' tid0 pmap_tid' pmap_lp *)
    (*     (Htid0_lt_pf : tid0 < num_threads tp) *)
    (*     (pf_lp : 0 < num_threads tp) *)
    (*     (pf_lp' : 0 < num_threads tp') counter, *)
    (*     let: tid := Ordinal Htid0_lt_pf in *)
    (*     let: lp := Ordinal pf_lp in *)
    (*     let: lp' := Ordinal pf_lp' in *)
    (*     let: pmap_tid := getThreadPerm tp tid in *)
    (*     forall *)
    (*       (Hinv: invariant tp) *)
    (*       (Hcompatible: mem_compatible tp m) *)
    (*       (Hrestrict_pmap: restrPermMap (permMapsInv_lt Hcompatible tid) = m1) *)
    (*       (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m1') *)
    (*       (Hdrop_perm: *)
    (*          setPerm (Some Nonempty) (getPerm b (Int.intval ofs) Max pmap_tid) *)
    (*                  (store_perm_order b ofs Hinv Hrestrict_pmap Hstore) *)
    (*                  b (Int.intval ofs) pmap_tid = pmap_tid') *)
    (*       (Hlp_perm: setPerm (Some Writable) (Some Freeable) (perm_F_any Writable) *)
    (*                          b (Int.intval ofs) (getThreadPerm tp lp) = pmap_lp) *)
    (*       (Hthread: exists t, *)
    (*                   getThreadC tp tid = Kstage (fst t) (fst (snd t)) (snd (snd t))) *)
    (*       (Htp': tp' = updThread tp tid (Krun c') pmap_tid' counter) *)
    (*       (Htp'': tp'' = updThreadP tp' lp' pmap_lp), *)
    (*       invariant tp''. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp]. subst tp'. subst tp''. *)
    (*   simpl in *. pf_cleanup. *)
    (*   assert (Hpmap: PermMap.map (getThreadPerm tp (Ordinal Htid0_lt_pf)) = *)
    (*                  Mem.mem_access m1). *)
    (*   { rewrite <- Hrestrict_pmap. *)
    (*     unfold restrPermMap. reflexivity. } *)
    (*   assert (Hcontra: tid0 <> 0). *)
    (*   { intros Hcontra. subst tid0. *)
    (*     simpl in *. *)
    (*     destruct (Hlp Htid0_lt_pf) as [c0' [Hthread' Hhalted]]. *)
    (*     destruct Hthread as [? Hthread]. *)
    (*     rewrite Hthread in Hthread'. inversion Hthread'. } *)
    (*   clear Hthread. *)
    (*   split. *)
    (*   { simpl. intros [tid tid_pf]. *)
    (*     repeat match goal with *)
    (*              | [|- context[if ?Expr then _ else _]] => destruct Expr eqn:? *)
    (*              | [H: _ == _ = _ |- _] => move/eqP:H=>H *)
    (*              | [H: @Ordinal _ _ _ = @Ordinal _ _ _ |- _] => inversion H; clear H *)
    (*            end; subst; auto; apply setPerm_canonical; auto. *)
    (*   } *)
    (*   { unfold race_free, updThreadP, updThread. simpl. *)
    (*     intros tid1 tid2 Htid1 Htid2 Hneq. *)
    (*     assert (Hracy_tid0: racy (getPerm b (Int.intval ofs) Cur *)
    (*                                       (getThreadPerm tp (Ordinal Htid0_lt_pf)))). *)
    (*     { clear - Hrestrict_pmap Hstore Hpmap. *)
    (*       apply Mem.store_valid_access_3 in Hstore. *)
    (*       apply Mem.valid_access_perm with (k := Cur) in Hstore. *)
    (*       unfold Mem.perm, Mem.perm_order' in *. unfold getPerm, getThreadPerm. *)
    (*       rewrite Hpmap. destruct (Maps.PMap.get b (Mem.mem_access m1) (Int.intval ofs) Cur); *)
    (*         inversion Hstore; subst; auto; constructor. *)
    (*     } *)
    (*     assert (Hnotracy: forall tid, nat_of_ord tid <> tid0 -> *)
    (*                              not_racy (getPerm b (Int.intval ofs) Cur *)
    (*                                                (getThreadPerm tp tid))). *)
    (*     { clear - Hrace Hracy_tid0. *)
    (*       intros tid Hneq. *)
    (*       eapply racy_disjoint; eauto. *)
    (*       unfold getThreadPerm; destruct tid. auto. *)
    (*     }  *)
    (*     assert (Hcur1_notracy: not_racy (Some Nonempty)) by constructor. *)
    (*     unfold getThreadPerm in *. *)
    (*     repeat match goal with *)
    (*              | [|- context[if ?Expr then _ else _]] => destruct Expr eqn:? *)
    (*              | [H: _ == _ = _ |- _] => move/eqP:H=>H *)
    (*              | [H: @Ordinal _ _ _ = @Ordinal _ _ _ |- _] => inversion H; clear H *)
    (*            end; subst; try (by (exfalso; auto)); auto; *)
    (*     try match goal with *)
    (*           | [|- permMapsDisjoint (setPerm (Some Writable) _ _ _ _ _) *)
    (*                                 (setPerm (Some Nonempty) _ _ _ _ _)] => *)
    (*             apply permMapsDisjoint_comm; apply setPerm_noracy1; auto *)
    (*           | [|- permMapsDisjoint (setPerm (Some Nonempty) _ _ _ _ _) *)
    (*                                 (setPerm (Some Writable) _ _ _ _ _)] => *)
    (*             apply setPerm_noracy1; auto *)
    (*           | [|- permMapsDisjoint (setPerm (Some Writable) _ _ _ _ _) (perm_maps _ _)] => *)
    (*             apply setPerm_noracy3; auto *)
    (*           | [|- permMapsDisjoint (perm_maps _ _) (setPerm (Some Writable) _ _ _ _ _)] => *)
    (*             apply permMapsDisjoint_comm; apply setPerm_noracy3; auto *)
    (*           | [|- permMapsDisjoint (setPerm (Some Nonempty) _ _ _ _ _) (perm_maps _ _)] => *)
    (*             apply setPerm_noracy2; auto *)
    (*           | [|- permMapsDisjoint (perm_maps _ _) (setPerm (Some Nonempty) _ _ _ _ _)] => *)
    (*             apply permMapsDisjoint_comm; apply setPerm_noracy2; auto *)
    (*         end; *)
    (*     apply Hnotracy; intros Hcontra';  *)
    (*     subst tid0; simpl in *; pf_cleanup; auto. *)
    (*   } *)
    (*   { simpl. intros. rewrite if_false. auto. *)
    (*     apply/eqP; intros Hcontra'. inversion Hcontra'; auto. *)
    (*   } *)
    (* Qed. *)

    (* Lemma freelock_inv : *)
    (*   forall tp tp' tp'' m m1 c' b ofs pmap_lp', *)
    (*     let: n := counter tp in *)
    (*     forall tid0 *)
    (*       (Htid0_lt_pf : tid0 < num_threads tp) *)
    (*       (pf_lp : 0 < num_threads tp) *)
    (*       (pf_lp' : 0 < num_threads tp'), *)
    (*       let: tid := Ordinal Htid0_lt_pf in *)
    (*       let: lp := Ordinal pf_lp in *)
    (*       let: lp' := Ordinal pf_lp' in *)
    (*       let: pmap_lp := getThreadPerm tp lp in *)
    (*       forall *)
    (*         (Hinv: invariant tp) *)
    (*         (Heq: sval (permMapsUnion (canonical Hinv) (no_race Hinv)) = getMaxPerm m) *)
    (*         (Hcompatible: mem_compatible tp m) *)
    (*         (Hrestrict_pmap: restrPermMap (permMapsInv_lt Hcompatible tid) = m1) *)
    (*         (Hdrop_perm: setPerm None (Some Freeable) I b (Int.intval ofs) pmap_lp = pmap_lp') *)
    (*         (Hangel_wf: permMap_wf tp (aggelos n) tid0) *)
    (*         (Hangel_canonical: isCanonical (aggelos n)) *)
    (*         (Hthread: exists t, *)
    (*                     getThreadC tp tid = Kstage (fst t) (fst (snd t)) (snd (snd t))) *)
    (*         (Htp': tp' = updThread tp tid (Krun c') (aggelos n) (n+1))             *)
    (*         (Htp'': tp'' = updThreadP tp' lp' pmap_lp'), *)
    (*         invariant tp''. *)
    (* Proof. *)
    (*   intros. destruct Hinv as [Hcanonical Hrace Hlp]. subst tp'. subst tp''. *)
    (*   simpl in *. pf_cleanup. *)
    (*   assert (Hpmap: PermMap.map (getThreadPerm tp (Ordinal Htid0_lt_pf)) = *)
    (*                  Mem.mem_access m1). *)
    (*   { rewrite <- Hrestrict_pmap. *)
    (*     unfold restrPermMap. reflexivity. } *)
    (*   assert (Hcontra: tid0 <> 0). *)
    (*   { intros Hcontra. subst tid0. *)
    (*     simpl in *. *)
    (*     destruct (Hlp Htid0_lt_pf) as [c0' [Hthread' Hhalted]]. *)
    (*     destruct Hthread as [? Hthread]. *)
    (*     rewrite Hthread in Hthread'. inversion Hthread'. } *)
    (*   split; simpl. *)
    (*   { intros. *)
    (*     destruct (tid == Ordinal (n:=num_threads tp) (m:=0) pf_lp); auto. *)
    (*     rewrite <- Hdrop_perm. *)
    (*     apply setPerm_canonical. auto. *)
    (*     destruct (tid == Ordinal (n:=num_threads tp) (m:=tid0) Htid0_lt_pf); auto. *)
    (*   } *)
    (*   { unfold race_free. simpl. intros tid1 tid2 Htid1 Htid2 Hneq. *)
    (*     unfold getThreadPerm in *. *)
    (*     unfold permMap_wf in Hangel_wf. *)
    (*     assert (Hnotracy: not_racy None) by constructor. *)
    (*     repeat match goal with *)
    (*              | [|- context[if ?Expr then _ else _]] => destruct Expr eqn:? *)
    (*              | [H: _ == _ = _ |- _] => move/eqP:H=>H *)
    (*              | [H: @Ordinal _ _ _ = @Ordinal _ _ _ |- _] => inversion H; clear H *)
    (*            end; subst; try (by (exfalso; auto)); auto; *)
    (*     try (apply setPerm_noracy2; auto); *)
    (*     try (apply permMapsDisjoint_comm; apply setPerm_noracy2; auto). *)
    (*     apply permMapsDisjoint_comm. auto. *)
    (*   } *)
    (*   { simpl. intros. rewrite if_false. auto. *)
    (*     apply/eqP; intros Hcontra'. inversion Hcontra'; auto. *)
    (*   } *)
    (* Defined. *)