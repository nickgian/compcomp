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


    (* Should there be an axiom Hnext :
         next pmap1 > next pmap2 -> next pmap3 = next pmap1
        /\ next pmap1 <= next pmap2 -> next pmap3 = next pmap2 ?*)
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
  
  Record t := mk
                { num_threads : pos
                  ; pool :> 'I_num_threads -> ctl
                  ; perm_maps : 'I_num_threads -> PermMap.t
                  ; schedule : list pos
                  ; counter : nat (* for angel *)
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
      (schedule tp)
      (counter tp).+1.

Definition updThreadC (tid : 'I_num_threads) (c' : ctl) : thread_pool :=
  @mk sem num_threads (fun (n : 'I_num_threads) =>
                         if n == tid then c' else tp n) (perm_maps tp) 
      (schedule tp) (counter tp).

Definition updThreadP (tid : 'I_num_threads) (pmap : PermMap.t) : thread_pool :=
  @mk sem num_threads tp (fun (n : 'I_num_threads) =>
                            if n == tid then pmap else (perm_maps tp) n) 
      (schedule tp) (counter tp).

Definition updThread (tid : 'I_num_threads) (c' : ctl)
           (pmap : PermMap.t) (counter' : nat) : thread_pool :=
  @mk sem num_threads
      (fun (n : 'I_num_threads) =>
                         if n == tid then c' else tp n)
      (fun (n : 'I_num_threads) =>
         if n == tid then pmap else (perm_maps tp) n) 
      (schedule tp) (counter').

Definition schedNext : thread_pool :=
  @mk sem num_threads (pool tp) (perm_maps tp) (List.tl (schedule tp)) (counter tp).

Definition getThreadC (tid : 'I_num_threads) : ctl := tp tid.

Definition getThreadPerm (tid : 'I_num_threads) : PermMap.t := (perm_maps tp) tid.

(*This definition is hard to use in proofs*)
Inductive permMapsInv' : nat -> PermMap.t -> Prop :=
| perm0 : forall (pf : 0 < num_threads), permMapsInv' 0 (perm_maps tp (Ordinal pf)) 
| permS : forall n (pf : n < num_threads) pprev punion,
            permMapsInv' n pprev ->
            isUnionPermMaps pprev (perm_maps tp (Ordinal pf)) punion ->
            permMapsInv' (S n) punion.

Import Maps.

Definition permMapsInv (pmap : PermMap.t) : Prop :=
  (forall tid0 tid0' (Htid0 : tid0 < num_threads) (Htid0' : tid0' < num_threads)
         b ofs (pcur pmax : option permission)
         (Htid: tid0 <> tid0'),
    perm_union (PMap.get b (PermMap.map
                              (getThreadPerm (Ordinal Htid0))) ofs Cur)
               (PMap.get b (PermMap.map
                              (getThreadPerm (Ordinal Htid0'))) ofs Cur) = Some pcur
    /\ Mem.perm_order'' (PMap.get b (PermMap.map pmap) ofs Cur) pcur
    /\ perm_max (PMap.get b (PermMap.map
                               (getThreadPerm (Ordinal Htid0))) ofs Max)
                (PMap.get b (PermMap.map
                               (getThreadPerm (Ordinal Htid0'))) ofs Max) = pmax
    /\ Mem.perm_order'' (PMap.get b (PermMap.map pmap) ofs Max) pmax
    /\ exists tid'',
         (PMap.get b (PermMap.map (perm_maps tp tid'')) ofs Cur) =
         (PMap.get b (PermMap.map pmap) ofs Cur) /\
         (PMap.get b (PermMap.map (perm_maps tp tid'')) ofs Max) =
         (PMap.get b (PermMap.map pmap) ofs Max))
  /\
  (forall tid, ~ Coqlib.plt (PermMap.next pmap) (PermMap.next (getThreadPerm tid)))
  /\ (forall tid b ofs,
        (Mem.perm_order'' (PMap.get b (PermMap.map pmap) ofs Cur)
                          (PMap.get b (PermMap.map (getThreadPerm tid)) ofs Cur))
        /\ ( Mem.perm_order'' (PMap.get b (PermMap.map pmap) ofs Max)
                              (PMap.get b (PermMap.map (getThreadPerm tid)) ofs Max)))
  /\ exists tid',
       PermMap.next pmap = PermMap.next (getThreadPerm tid').

End poolDefs.

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
  destruct Hinv as [_ [Hnext [Horders _]]].
  specialize (Hnext tid). intros b ofs k Hmem_next.
  destruct (Horders tid b ofs) as [HCur HMax].
  assert (Hb: ~Coqlib.Plt b (PermMap.next (getPermMap m))).
  { clear Horders HCur HMax.
    destruct m; simpl in *; trivial. }  
  assert (Hget: Maps.PMap.get b (PermMap.map (getPermMap m)) ofs k = None).
  { remember (getPermMap m) as pmap eqn:Heq.
    destruct pmap; simpl in *. clear Heq. auto. }
  destruct k; [rewrite Hget in HMax | rewrite Hget in HCur]; subst;
  simpl in *; match goal with
                | [H: match ?Expr with _ => _ end |- _] => destruct Expr
              end; tauto.
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
Definition load_unafe (chunk : memory_chunk) (m : mem) (b : block) (ofs : Z) :=
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
            (Htp': tp' = updThread tp tid (Krun c') (getPermMap m1') n)
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
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
            (Htp': tp' = updThread tp tid (Krun c') (aggelos n) (n+1))
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
            (Htp': tp' = updThread tp tid (Krun c') (aggelos n) (n+1))
            (Hinv': permMapsInv tp' pnew)
            (Hupd_mem: updPermMap m1' pnew = Some m'),
            step tp m tp' m'

  | step_create :
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
            (Htest: load_unafe Mint32 m1 b (Int.intval ofs) = Vint Int.zero),
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
Variable fschedule : nat -> nat.

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
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
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
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
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
          (Htest: load_unafe Mint32 m1 b (Int.intval ofs) = Vint Int.zero),
          step tp m (schedNext tp) m
               
  | fstep_schedfail :
      forall tp m tid0
             (Hsched: List.hd_error (schedule tp) = Some tid0)
             (Htid0_lt_pf :  tid0 >= num_threads tp),
        step tp m (schedNext tp) m.
                 

End Corestep.

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