Require Import Bool.

Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import core_semantics.
Require Import effect_semantics.
Require Import StructuredInjections.
Require Import reach.

Definition globals_separate {F V:Type} (ge: Genv.t F V) mu nu :=
    forall b1 b2 d, as_inj mu b1 = None ->
            as_inj nu b1 =Some(b2,d) -> 
            isGlobalBlock ge b2 = false.

Lemma meminj_preserves_globals_extern_incr_separate {F V:Type} (ge: Genv.t F V) mu nu: 
      forall (INC: extern_incr mu nu)
             (PG: meminj_preserves_globals ge (as_inj mu))
             (WDnu: SM_wd nu)
             (GSep: globals_separate ge mu nu),
      meminj_preserves_globals ge (as_inj nu).
Proof. intros. destruct PG as [PGa [PGb PGc]].
split; intros.
  apply PGa in H. eapply extern_incr_as_inj; eassumption.
split; intros.
  apply PGb in H. eapply extern_incr_as_inj; eassumption.
remember (as_inj mu b1) as q; apply eq_sym in Heqq.
  destruct q.
    destruct p.
    rewrite (extern_incr_as_inj _ _ INC WDnu _ _ _ Heqq) in H0.
    inv H0. apply (PGc _ _ _ _ H Heqq).
  specialize (GSep _ _ _ Heqq H0).
    rewrite (find_var_info_isGlobal _ _ _ H) in GSep; discriminate.
Qed.

Lemma intern_incr_globals_separate
      {F V:Type} (ge: Genv.t F V) mu nu: 
      forall (INC: intern_incr mu nu)
             (PG: meminj_preserves_globals ge (as_inj mu))
             (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)
             (WD: SM_wd mu) (WDnu: SM_wd nu), 
      globals_separate ge mu nu.
Proof. intros. red; intros. 
  remember (isGlobalBlock ge b2) as p; apply eq_sym in Heqp.
  destruct p; simpl; trivial.
  specialize (GF _ Heqp).
  destruct (frgnSrcAx _ WD _ GF) as [? [? [? ?]]].
  assert (EE: extern_of mu = extern_of nu) by eapply INC.
  destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [EXT LOC]]; clear H0.
    rewrite <- EE in EXT. 
    rewrite (extern_in_all _ _ _ _ EXT) in H; discriminate. 
  destruct (local_DomRng _ WDnu _ _ _ LOC) as [lS lT].
    assert (lT': locBlocksTgt nu b2 = false). 
      apply (meminj_preserves_globals_isGlobalBlock _ _ PG) in Heqp.
      rewrite (extern_in_all _ _ _ _ H1) in Heqp; inv Heqp.
      rewrite EE in H1.
      eapply extern_DomRng'; eassumption. 
    rewrite lT' in lT; discriminate. 
Qed.  

Lemma exter_incr_globals_separate
      {F V:Type} (ge: Genv.t F V) mu nu: 
      forall (EE: extern_of mu = extern_of nu)
             (PG: meminj_preserves_globals ge (as_inj mu))
             (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)
             (WD: SM_wd mu) (WDnu: SM_wd nu), 
      globals_separate ge mu nu.
Proof. intros. red; intros. 
  remember (isGlobalBlock ge b1) as p1; apply eq_sym in Heqp1.
  remember (isGlobalBlock ge b2) as p; apply eq_sym in Heqp.
  destruct p; simpl; trivial.
  destruct p1; simpl.
  specialize (GF _ Heqp1).
  destruct (frgnSrcAx _ WD _ GF) as [? [? [? ?]]].
  unfold as_inj, join in H.
  rewrite H1 in H; inversion H.
  (*eapply meminj_preserves_globals_isGlobalBlock in Heqp; eauto.*)

  specialize (GF _ Heqp).
  destruct (frgnSrcAx _ WD _ GF) as [? [? [? ?]]].
  destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [EXT LOC]]; clear H0.
    rewrite <- EE in EXT.
    rewrite (extern_in_all _ _ _ _ EXT) in H. discriminate. 
  destruct (local_DomRng _ WDnu _ _ _ LOC) as [lS lT].
    assert (lT': locBlocksTgt nu b2 = false). 
      apply (meminj_preserves_globals_isGlobalBlock _ _ PG) in Heqp.
      rewrite (extern_in_all _ _ _ _ H1) in Heqp; inv Heqp.
      rewrite EE in H1.
      eapply extern_DomRng'; eassumption. 
    rewrite lT' in lT; discriminate. 
Qed.  

Module SM_simulation. Section SharedMemory_simulation_inject. 

Context 
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record SM_simulation_inject := 
{ core_data : Type
; match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord

; match_sm_wd : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 -> SM_wd mu

; genvs_dom_eq : genvs_domain_eq ge1 ge2

; match_genv : 
    forall d mu c1 m1 c2 m2 (MC : match_state d mu c1 m1 c2 m2),
    meminj_preserves_globals ge1 (extern_of mu) /\
    (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)

; match_visible : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 -> 
    REACH_closed m1 (vis mu)

(*; match_restrict:
    forall d mu c1 m1 c2 m2,
      match_state d mu c1 m1 c2 m2 ->
      forall X, (forall b, vis mu b = true -> X b = true) ->
                REACH_closed m1 X ->
      (*forall m2', junk_inv_r (restrict_sm mu X) m1' m2 m2' ->
                  junk_inv_l (restrict_sm mu X) m1 m1' ->*)
      match_state d (restrict_sm mu X) c1 m1 c2 m2*)

(*match_junk_inv: 
    forall d mu c1 m1 c2 m2,
    match_state d mu c1 m1 c2 m2 -> 
    forall m2', junk_inv_r mu m1 m2 m2' ->
    (*forall m1', junk_inv_l mu m1 m1' ->*)
    match_state d mu c1 m1 c2 m2'

; match_restrict : 
    forall d mu c1 m1 c2 m2 X, 
    match_state d mu c1 m1 c2 m2 -> 
    (forall b, vis mu b = true -> X b = true) ->
    REACH_closed m1 X ->
    match_state d (restrict_sm mu X) c1 m1 c2 m2*)

; match_validblocks : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 ->
    sm_valid mu m1 m2


; core_initial : 
    forall v vals1 c1 m1 j vals2 m2 DomS DomT,
    initial_core Sem1 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j ->

    (*the next two conditions are required to guarantee initialSM_wd*)
    (forall b1 b2 d, j b1 = Some (b2, d) -> 
      DomS b1 = true /\ DomT b2 = true) ->
    (forall b, 
      REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b=true -> 
      DomT b = true) ->

    (*the next two conditions ensure the initialSM satisfies sm_valid*)
    (forall b, DomS b = true -> Mem.valid_block m1 b) ->
    (forall b, DomT b = true -> Mem.valid_block m2 b) ->

    exists cd, exists c2, 
    initial_core Sem2 ge2 v vals2 = Some c2 
    /\ match_state cd 
         (initial_SM DomS DomT 
           (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
           (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
         c1 m1 c2 m2

; effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
      intern_incr mu mu'
      /\ sm_locally_allocated mu mu' m1 m2 m1' m2' 
      /\ match_state cd' mu' st1' m1' st2' m2'
      /\ exists U2,              
          ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
            (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
             core_ord cd' cd)) /\
         forall 
           (UHyp: forall b1 z, U1 b1 z = true -> vis mu b1 = true)
           b ofs (Ub: U2 b ofs = true),
           visTgt mu b = true 
           /\ (locBlocksTgt mu b = false ->
               exists b1 delta1, 
                 foreign_of mu b1 = Some(b,delta1) 
                 /\ U1 b1 (ofs-delta1) = true 
                 /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty))

      
; core_halted : 
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists v2, 
    Mem.inject (as_inj mu) m1 m2 
    /\ val_inject (restrict (as_inj mu) (vis mu)) v1 v2 
    /\ halted Sem2 c2 = Some v2 


; core_at_external : 
    forall cd mu c1 m1 c2 m2 e vals1 ef_sig,
    match_state cd mu c1 m1 c2 m2 ->
    at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
    Mem.inject (as_inj mu) m1 m2 
    /\ exists vals2, 
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 
       /\ at_external Sem2 c2 = Some (e,ef_sig,vals2)

    /\ forall
       (pubSrc' pubTgt' : block -> bool)
       (pubSrcHyp : pubSrc' =
                  (fun b : block =>
                  locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgtHyp: pubTgt' =
                  (fun b : block =>
                  locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (Hnu: nu = (replace_locals mu pubSrc' pubTgt')),
       match_state cd nu c1 m1 c2 m2 
       /\ Mem.inject (shared_of nu) m1 m2

; eff_after_external: 
    forall cd mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu: Mem.inject (as_inj mu) m1 m2)
      (MatchMu: match_state cd mu st1 m1 st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals1))

        (* We include the clause AtExtTgt to ensure that vals2 is
         uniquely determined. We have e=e' and ef_sig=ef_sig' by the
         at_external clause, but omitting the hypothesis AtExtTgt
         would result in in 2 not necesssarily equal target argument
         lists in language 3 in the transitivity, as val_inject is not
         functional in the case where the left value is Vundef. (And
         we need to keep ValInjMu since vals2 occurs in pubTgtHyp) *)

      (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals2)) 
      (ValInjMu: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)  

      pubSrc' 
      (pubSrcHyp: 
         pubSrc' 
         = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
        
      pubTgt' 
      (pubTgtHyp: 
         pubTgt' 
         = fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b)

      nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),

      forall nu' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res (AST.ef_sig e)))
        (HasTy2: Val.has_type ret2 (proj_sig_res (AST.ef_sig e')))
        (INC: extern_incr nu nu') 
        (GSep: globals_separate ge2 nu nu')

        (WDnu': SM_wd nu') (SMvalNu': sm_valid nu' m1' m2')

        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')

        frgnSrc' 
        (frgnSrcHyp: 
           frgnSrc' 
           = fun b => DomSrc nu' b && 
                      (negb (locBlocksSrc nu' b) && 
                       REACH m1' (exportedSrc nu' (ret1::nil)) b))

        frgnTgt' 
        (frgnTgtHyp: 
           frgnTgt' 
           = fun b => DomTgt nu' b &&
                      (negb (locBlocksTgt nu' b) &&
                       REACH m2' (exportedTgt nu' (ret2::nil)) b))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
 
         (UnchPrivSrc: 
            Mem.unchanged_on (fun b ofs => 
              locBlocksSrc nu b = true /\ 
              pubBlocksSrc nu b = false) m1 m1') 

         (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' mu' st1' m1' st2' m2' }.

Require Import core_semantics_lemmas.

Lemma core_diagram (SMI: SM_simulation_inject):
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 mu m2,
        match_state SMI cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          intern_incr mu mu' /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
          match_state SMI cd' mu' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord SMI cd' cd).
Proof. intros. 
apply effax2 in H. destruct H as [U1 H]. 
exploit (effcore_diagram SMI); eauto.
intros [st2' [m2' [cd' [mu' [INC [LOCALLOC 
  [MST [U2 [STEP _]]]]]]]]].
exists st2', m2', cd', mu'.
split; try assumption.
split; try assumption.
split; try assumption.
destruct STEP as [[n STEP] | [[n STEP] CO]];
  apply effstepN_corestepN in STEP.
left. exists n. assumption.
right; split; trivial. exists n. assumption.
Qed.

End SharedMemory_simulation_inject. 

End SM_simulation.

