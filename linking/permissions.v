Require Import ssreflect Ssreflect.seq ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Require Import Memory.
Require Import Values. (*for val*)
Require Import Integers.
Require Import ZArith.
Require Import threads_lemmas.

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
  Definition updPermMap (m : mem) (p : PermMap.t) : option mem.
    refine (match positive_eq_dec (Mem.nextblock m) (PermMap.next p) with
      | left pf => 
        Some (Mem.mkmem 
                (Mem.mem_contents m) 
                (PermMap.map p) 
                (PermMap.next p)
                (PermMap.max p) 
                (PermMap.nextblock p)
                (Mem.contents_default m))
      | right _ => None
            end).
    Defined.

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
 
Definition permMapsDisjoint pmap1 pmap2 : Prop :=
  forall b ofs, exists pu,
    perm_union (Maps.PMap.get b (PermMap.map pmap1) ofs Cur)
               (Maps.PMap.get b (PermMap.map pmap2) ofs Cur) = Some pu.

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
         (Hdisjoint: permMapsDisjoint (getPermMap mi) (getPermMap mj))
         (Hpermj: Mem.perm mj b ofs Cur Readable)
         (Hpermi: Mem.perm mi b ofs Cur Writable),
    False.
Proof.
  intros.
  unfold Mem.perm, Mem.perm_order' in *.
  unfold permMapsDisjoint, getPermMap in Hdisjoint. simpl in Hdisjoint.
  destruct (Hdisjoint b ofs) as [pu Hunion].
  clear Hdisjoint.
  destruct (Maps.PMap.get b (Mem.mem_access mj) ofs Cur) as [pj|] eqn:Hpj;
    auto.
  destruct (Maps.PMap.get b (Mem.mem_access mi) ofs Cur) as [pi|] eqn:Hpi;
    auto.
  inversion Hpermi; inversion Hpermj; subst; simpl in Hunion;
  discriminate.
Qed.

Definition isCanonical pmap := (PermMap.map pmap).1 = fun _ _ => None.

Definition permMapLt pmap1 pmap2 : Prop :=
  ~ Coqlib.Plt (PermMap.next pmap2) (PermMap.next pmap1)
  /\ (forall b ofs,
        Mem.perm_order'' (Maps.PMap.get b (PermMap.map pmap2) ofs Cur)
                         (Maps.PMap.get b (PermMap.map pmap1) ofs Cur))
  /\ (forall b ofs,
        Mem.perm_order''
          (Maps.PMap.get b (PermMap.map pmap2) ofs Max)
          (Maps.PMap.get b (PermMap.map pmap1) ofs Max)).

Definition setPerm p b ofs pmap :=
  Maps.PMap.set b
                (fun ofs' k =>
                   match k with
                     | Max => Maps.PMap.get b (PermMap.map pmap) ofs k
                     | Cur =>
                       if Coqlib.zeq ofs ofs' then
                         Some p
                       else Maps.PMap.get b (PermMap.map pmap) ofs k
                   end)
                (PermMap.map pmap).

Definition getPerm b ofs k (pmap : PermMap.t) :=
  (Maps.PMap.get b (PermMap.map pmap)) ofs k.

End permMapDefs.

(* Computation of a canonical form of permission maps where the
     default element is a function to the empty permission *)
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

End CanonicalPMap.