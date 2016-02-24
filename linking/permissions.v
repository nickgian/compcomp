Require Import ssreflect Ssreflect.seq ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Require Import Memory.
Require Import Values. (*for val*)
Require Import Integers.
Require Import ZArith.
Require Import threads_lemmas.

Definition access_map := Maps.PMap.t (Z -> option permission).

Section permMapDefs.
 
  Definition empty_map : access_map :=
    (fun z => None, Maps.PTree.empty (Z -> option permission)).
 
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

  Inductive not_racy : option permission -> Prop :=
  | non_empty : not_racy (Some Nonempty)
  | empty : not_racy None.

  Inductive racy : option permission -> Prop :=
  | writable : racy (Some Writable)
  | freeable : racy (Some Freeable).

  Lemma not_racy_union :
    forall p1 p2 (Hnot_racy: not_racy p1),
    exists pu, perm_union p1 p2 = Some pu.
  Proof. intros. destruct p2 as [o |]; [destruct o|]; inversion Hnot_racy; subst; 
                 simpl; eexists; reflexivity.
  Qed.

  Lemma no_race_racy : forall p1 p2 (Hracy: racy p1)
                              (Hnorace: exists pu, perm_union p1 p2 = Some pu),
                         not_racy p2.
  Proof.
    intros.
    destruct p2 as [o|]; [destruct o|];
    inversion Hracy; subst;
    simpl in *; inversion Hnorace;
    (discriminate || constructor).
  Qed.
    
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

  Definition getMaxPerm (m : mem) : access_map :=
    Maps.PMap.map (fun f => fun ofs => f ofs Max) (Mem.mem_access m).

  Definition getCurPerm (m : mem) : access_map :=
    Maps.PMap.map (fun f => fun ofs => f ofs Cur) (Mem.mem_access m).

  Definition getPermMap (m : mem) : Maps.PMap.t (Z -> perm_kind -> option permission) :=
    Mem.mem_access m.
  
  Definition permMapsDisjoint (pmap1 pmap2 : access_map) : Prop :=
    forall b ofs, exists pu,
      perm_union ((Maps.PMap.get b pmap1) ofs)
                 ((Maps.PMap.get b pmap2) ofs) = Some pu.
  
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

  Lemma disjoint_norace:
    forall (mi mj : mem) (b : block) (ofs : Z)
      (Hdisjoint: permMapsDisjoint (getCurPerm mi) (getCurPerm mj))
      (Hpermj: Mem.perm mj b ofs Cur Readable)
      (Hpermi: Mem.perm mi b ofs Cur Writable),
      False.
  Proof.
    intros.
    unfold Mem.perm, Mem.perm_order' in *.
    unfold permMapsDisjoint, getCurPerm in Hdisjoint. simpl in Hdisjoint.
    destruct (Hdisjoint b ofs) as [pu Hunion].
    clear Hdisjoint.
    do 2 rewrite Maps.PMap.gmap in Hunion.
    destruct (Maps.PMap.get b (Mem.mem_access mj) ofs Cur) as [pj|] eqn:Hpj;
      auto.
    destruct (Maps.PMap.get b (Mem.mem_access mi) ofs Cur) as [pi|] eqn:Hpi;
      auto.
    inversion Hpermi; inversion Hpermj; subst; simpl in Hunion;
    discriminate.
  Qed.

  Definition isCanonical (pmap : access_map) := pmap.1 = fun _ => None.
  
  Definition permMapLt (pmap1 pmap2 : access_map) : Prop :=
    forall b ofs,
      Mem.perm_order'' (Maps.PMap.get b pmap2 ofs)
                       (Maps.PMap.get b pmap1 ofs).
  
  Definition setPerm (p : option permission) (b : block)
             (ofs : Z) (pmap : access_map) : access_map :=
    Maps.PMap.set b (fun ofs' => if Coqlib.zeq ofs ofs' then
                                p
                              else
                                Maps.PMap.get b pmap ofs')
                  pmap.

  (*Inductive SetPerm b ofs : PermMap.t -> PermMap.t -> Prop :=
  | set: forall pmap1 pmap2 b' ofs' k,
           b <> b' \/ (b = b' /\ ofs <> ofs') ->
           Maps.PMap.get b' (PermMap.map pmap1) ofs' k =
           Maps.PMap.get b' (PermMap.map pmap2) ofs' k ->
           SetPerm b ofs pmap1 pmap2.

  Lemma setPerm_correct :
    forall p_cur p_max (Hord: Mem.perm_order'' p_max p_cur) b ofs
           pmap b' ofs' k,
           b <> b' \/ (b = b' /\ ofs <> ofs') ->
           Maps.PMap.get b' (PermMap.map pmap) ofs' k =
           Maps.PMap.get b' (PermMap.map (setPerm p_cur p_max Hord b ofs pmap))
                         ofs' k.
  Proof.
    intros. unfold setPerm. simpl.
      destruct H. rewrite Maps.PMap.gso. reflexivity. auto.
      destruct H. subst. unfold Coqlib.zeq.
      rewrite Maps.PMap.gss.
      destruct (Z.eq_dec ofs ofs'). exfalso; auto.
      simpl.
      destruct k; auto.
  Qed.
   
  Lemma setPerm_canonical :
    forall p_cur p_max (Hord: Mem.perm_order'' p_max p_cur) b ofs
           pmap (Hpmap_can: isCanonical pmap),
      isCanonical (setPerm p_cur p_max Hord b ofs pmap).
  Proof.
    intros. unfold setPerm, isCanonical in *. simpl.
    assumption.
  Qed.

  Lemma setPerm_noracy1 :
    forall p_cur1 p_cur2 p_max1 p_max2
           (Hord1: Mem.perm_order'' p_max1 p_cur1)
           (Hord2: Mem.perm_order'' p_max2 p_cur2)
           b ofs pmap1 pmap2
           (Hrace: permMapsDisjoint pmap1 pmap2)
           (Hnot_racy: not_racy p_cur1),
      permMapsDisjoint (setPerm p_cur1 p_max1 Hord1 b ofs pmap1)
                       (setPerm p_cur2 p_max2 Hord2 b ofs pmap2).
  Proof.
    intros.
    unfold permMapsDisjoint, setPerm. simpl.
    intros b' ofs'.
    destruct (Pos.eq_dec b b') as [Hblock_eq | Hblock_neq].
    - subst.
      destruct (Z.eq_dec ofs ofs') as [Hofs_eq | Hofs_neq] eqn:Hofs;
        subst; unfold Coqlib.zeq;
        do 2 rewrite Maps.PMap.gss; rewrite Hofs; simpl;
        [apply not_racy_union|]; auto. 
    - rewrite Maps.PMap.gso; auto.
      rewrite Maps.PMap.gso; auto.
  Qed.
    
  Definition getPerm b ofs k (pmap : PermMap.t) :=
    (Maps.PMap.get b (PermMap.map pmap)) ofs k.
  
  Lemma setPerm_noracy2 :
    forall p_cur1 p_max1
           (Hord1: Mem.perm_order'' p_max1 p_cur1)
           b ofs pmap1 pmap2
           (Hrace12: permMapsDisjoint pmap1 pmap2)
           (Hnot_racy: not_racy p_cur1),
      permMapsDisjoint (setPerm p_cur1 p_max1 Hord1 b ofs pmap1) pmap2.
  Proof.
    intros.
    unfold permMapsDisjoint, setPerm. simpl.
    intros b' ofs'.
    destruct (Pos.eq_dec b b') as [Hblock_eq | Hblock_neq].
    - subst.
      destruct (Z.eq_dec ofs ofs') as [Hofs_eq | Hofs_neq] eqn:Hofs;
        subst; unfold Coqlib.zeq;
        rewrite Maps.PMap.gss; rewrite Hofs; simpl;
        [apply not_racy_union|]; auto. 
    - rewrite Maps.PMap.gso; auto.
  Qed.

  Lemma racy_disjoint :
    forall b ofs pmap1
           (Hracy: racy (getPerm b ofs Cur pmap1)),
      (forall pmap, permMapsDisjoint pmap1 pmap ->
                    not_racy (getPerm b ofs Cur pmap)).
  Proof.
    intros b ofs pmap1 Hracy pmap Hdisjoint.
    unfold permMapsDisjoint in *.
    specialize (Hdisjoint b ofs). destruct Hdisjoint as [pu Hpu].
    unfold getPerm in *.
    inversion Hracy as [Hp1 | Hp1]; rewrite <- Hp1 in Hpu;
    simpl in Hpu; destruct (Maps.PMap.get b (PermMap.map pmap) ofs Cur) as [p|];
    try destruct p; inversion Hpu; constructor.
  Qed.

  Lemma setPerm_noracy3 :
    forall p_cur1 p_max1
           (Hord1: Mem.perm_order'' p_max1 p_cur1)
           b ofs pmap1 pmap2
           (Hrace12: permMapsDisjoint pmap1 pmap2)
           (Hnot_racy: not_racy (getPerm b ofs Cur pmap2)),      
      permMapsDisjoint (setPerm p_cur1 p_max1 Hord1 b ofs pmap1) pmap2.
  Proof.
    intros.
    unfold permMapsDisjoint, setPerm. simpl.
    intros b' ofs'.
    destruct (Pos.eq_dec b b') as [Hblock_eq | Hblock_neq].
    - subst.
      destruct (Z.eq_dec ofs ofs') as [Hofs_eq | Hofs_neq] eqn:Hofs;
        subst; unfold Coqlib.zeq;
        rewrite Maps.PMap.gss; rewrite Hofs; simpl;
        [rewrite perm_union_comm; apply not_racy_union|]; auto. 
    - rewrite Maps.PMap.gso; auto.
  Qed.
*)
  (* Lemma setPerm_noracy2 : *)
  (*   forall p_cur1 p_cur2 p_max1 p_max2 *)
  (*          (Hord1: Mem.perm_order'' p_max1 p_cur1) *)
  (*          (Hord2: Mem.perm_order'' p_max2 p_cur2) *)
  (*          b ofs pmap1 pmap2 pmap3 *)
  (*          (Hrace12: permMapsDisjoint pmap1 pmap2) *)
  (*          (Hrace13: permMapsDisjoint pmap1 pmap3) *)
  (*          (Hrace23: permMapsDisjoint pmap2 pmap3) *)
  (*          (Hnot_racy: not_racy p_cur1) *)
  (*          (Hracy: racy (getPerm b ofs Cur pmap1)), *)
  (*     permMapsDisjoint (setPerm p_cur1 p_max1 Hord1 b ofs pmap1) pmap3 *)
  (*     /\ permMapsDisjoint (setPerm p_cur2 p_max2 Hord2 b ofs pmap2) pmap3. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold permMapsDisjoint in *. *)
  (*   split. *)
  (*   { intros b' ofs'. *)
  (*     apply not_racy_union with (p2 := getPerm b' ofs' Cur pmap3) in Hnot_racy. *)
  (*     simpl. rewrite Maps.PMap.gsspec. *)
  (*     destruct (Coqlib.peq b' b); auto. *)
  (*     subst. destruct (Coqlib.zeq ofs ofs'); simpl; auto. *)
  (*   } *)
  (*   { intros b' ofs'. *)
  (*     destruct (Pos.eq_dec b b'). *)
  (*     - subst.  *)
  (*       destruct (Z.eq_dec ofs ofs'). *)
  (*       + subst. *)
  (*         assert (Hnot_racy3: not_racy (getPerm b' ofs' Cur pmap3)). *)
  (*         { eapply no_race_racy. eapply Hracy. *)
  (*           unfold getPerm. auto. *)
  (*         } *)
  (*         rewrite perm_union_comm. apply not_racy_union. *)
  (*         unfold getPerm in *.  auto. *)
  (*       + rewrite <- setPerm_correct; auto. *)
  (*     - rewrite <- setPerm_correct; auto. *)
  (*   } *)
  (* Qed. *)
        
End permMapDefs.

(* Computation of a canonical form of permission maps where the
     default element is a function to the empty permission *)
(*
Section CanonicalPMap.

  Import Maps BlockList.
  
  Fixpoint canonicalPList l m : list (positive * (Z -> perm_kind -> option permission)) :=
    match l with
      | nil => nil
      | x :: l =>
        (Pos.of_nat x, PMap.get (Pos.of_nat x) m) :: (canonicalPList l m)
  end.
  
  Lemma canonicalPList_app :
    forall l m x,
      (canonicalPList l m) ++ ((Pos.of_nat x,
                                PMap.get (Pos.of_nat x) m) :: nil) =
      canonicalPList (l ++ (x :: nil)) m.
  Proof.
    intro l. induction l; intros.
    reflexivity.
    simpl. apply f_equal.
    auto.
  Qed.

  Lemma canonicalPList_cons :
    forall l m x,
      (Pos.of_nat x, PMap.get (Pos.of_nat x) m) :: (canonicalPList l m) =
      canonicalPList (x :: l) m.
  Proof.
    reflexivity.
  Qed.

  Lemma canonicalPList_correct :
    forall l m k v
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

  Lemma canonicalPTree_elements :
    forall l x
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

  Lemma canonicalPMap_sound :
    forall k n m
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

  Lemma canonicalPMap_default :
    forall n k m
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
               PermMap.map := canonicalPMap
                                (Pos.to_nat (PermMap.next p1)) (PermMap.map p1);
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

End CanonicalPMap. *)