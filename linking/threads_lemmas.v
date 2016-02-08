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
Notation "'do!' X <- A ; B" := (bind A (fun X => B)) (at level 40).

Lemma leq_pf_irr : forall n m (H1 : n < m) (H2: n < m), H1 = H2.
Proof.
  intros. eapply Eqdep_dec.eq_proofs_unicity; intros x y; destruct x,y; auto.
Defined.

Lemma if_true : forall {A : Type} b (x y : A)
                  (Htrue: is_true b),
                  (if b then x else y) = x.
Proof.
  intros.  by rewrite Htrue.
Defined.

Lemma if_false : forall {A : Type} b (x y : A)
                   (Hfalse: is_true (~~b)),
                   (if b then x else y) = y.
Proof.
  intros. rewrite <- Bool.if_negb. by rewrite Hfalse.
Defined.

Module SeqLemmas.

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
  
End SeqLemmas.

Module BlockList.
  
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

End BlockList.


