Require Import Coq.Strings.String.
Require Coq.Vectors.Vector.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import ListUtil.
Require Import Coq.MSets.MSets.
Require Import Coq.FSets.FMaps.
Require Import Coq.Program.Basics.
Require Import Coq.Structures.Equalities.

Definition var := nat.

(* Module Map := FMapWeakList.Make(Nat). *)
Search "empty".

Inductive expr : Type :=
| eunit : expr
| etrue : expr
| efalse : expr
| evar : var -> expr
| elet : var -> expr -> expr -> expr
| eapp : forall {k}, var -> Vector.t var k -> expr
| eif : var -> expr -> expr -> expr
| epair : var -> var -> expr
| epair_match : var -> var * var -> expr -> expr
| esum_inl : var -> expr
| esum_inr : var -> expr
| esum_match : var -> var * expr -> var * expr -> expr
| esum_match_elim : var -> var * expr -> var * expr -> expr
| elist_nil : expr
| elist_cons : var -> var -> expr
| elist_match : var -> expr -> var * var * expr -> expr
| elist_match_elim : var -> expr -> var * var * expr -> expr.

(* TODO: Wrong definition of substitution!!! *)
Fixpoint subst (p : var * expr) (e : expr) :=
match p, e with
| (x, xe), eunit => eunit
| (x, xe), etrue => etrue
| (x, xe), efalse => efalse
| (x, xe), evar y => if Nat.eqb x y then xe else evar y
| (x, xe), elet y e1 e2 => elet y e1 e2 (* TODO: Fix *)
| (x, xe), eapp f xs => eapp f xs       (* TODO: Fix *)
| (x, xe), eif b et ef => eif b et ef   (* TODO: Fix *)
| (x, xe), epair x1 x2 => epair x1 x2   (* TODO: Fix *)
| (x, xe), epair_match y (x1, x2) e => epair_match y (x1, x2) e (* TODO: Fix *)
| (x, xe), esum_inl y => esum_inl y     (* TODO: Fix *)
| (x, xe), esum_inr y => esum_inr y     (* TODO: Fix *)
| (x, xe), esum_match y (y1, e1) (y2, e2) => esum_match y (y1, e1) (y2, e2)
  (* TODO: Fix *)
| (x, xe), esum_match_elim y (y1, e1) (y2, e2) =>
  esum_match_elim y (y1, e1) (y2, e2) (* TODO: Fix *)
| (x, xe), elist_nil => elist_nil
| (x, xe), elist_cons yh yt => elist_cons yh yt (* TODO: Fix *)
| (x, xe), elist_match y e1 (yh, yt, e2) => elist_match y e1 (yh, yt, e2)
| (x, xe), elist_match_elim y e1 (yh, yt, e2) =>
  elist_match_elim y e1 (yh, yt, e2)
end.

Inductive type0 : Type :=
| tunit : type0
| tbool : type0
| tpair : type0 -> type0 -> type0
| tsum  : type0 -> type0 -> type0
| tlist : type0 -> type0.

Inductive type1 : Type :=
| tfun : forall {k}, Vector.t type0 k -> type0 -> type1.



Module Context := FMapWeakList.Make Nat.
Module ContextFacts := Facts Context.
Module ContextProperties := Properties Context.

Definition context := Context.t type0.

Arguments Context.empty {elt}.

Definition context_add (Gamma : context) (p : var * type0) : context :=
  let (v, t) := p in Context.add v t Gamma.
Definition context_join (Gamma1 Gamma2 : context) : context :=
  Context.fold (@Context.add type0) Gamma2 Gamma1.

Definition context_is_disjoint (c c' : context) : Prop := forall x,
  (Context.In x c  -> ~ Context.In x c') /\
  (Context.In x c' -> ~ Context.In x c).

Definition prog_sig := var -> option type1.
Definition prog_sig_empty : prog_sig := fun _ => None.
Definition prog_sig_add (Sigma : prog_sig) (p : var * type1) : prog_sig :=
  fun x => let (y, t) := p in if Nat.eqb x y then Some t else Sigma x.

(* Definition 4.2 *)
Inductive share : type0 -> type0 * type0 -> Prop :=
| share_base : forall A, share A (A, A).

(* Definition 4.1 *)
Inductive has_type : prog_sig -> context -> expr -> type0 -> Prop :=
| has_type_unit :
    has_type prog_sig_empty Context.empty eunit tunit

| has_type_bool_true :
    has_type prog_sig_empty Context.empty etrue tbool

| has_type_bool_false :
    has_type prog_sig_empty Context.empty efalse tbool

| has_type_var : forall x C,
    has_type prog_sig_empty (context_add Context.empty (x, C)) (evar x) C

| has_type_let : forall Sigma Gamma1 Gamma2 x e1 e2 A C,
    has_type Sigma Gamma1 e1 A ->
    has_type Sigma (context_add Gamma2 (x, A)) e2 C ->
    has_type Sigma (context_join Gamma1 Gamma2) (elet x e1 e2) C

| has_type_fun : forall Sigma Gamma
    (k : nat) (xs : Vector.t var k) (As : Vector.t type0 k) f C,
    Gamma = Vector.fold_left context_add Context.empty (Vector.map2 pair xs As) ->
    Sigma f = Some (tfun As C) ->
    has_type Sigma Gamma (eapp f xs) C

| has_type_if : forall Sigma Gamma x et ef C,
    ~ Context.In x Gamma ->
    has_type Sigma Gamma et C ->
    has_type Sigma Gamma ef C ->
    has_type Sigma (context_add Gamma (x, tbool)) (eif x et ef) C

| has_type_pair : forall Sigma x1 x2 A B,
    x1 <> x2 ->
    let Gamma := context_add (context_add Context.empty (x1, A)) (x2, B) in
    has_type Sigma Gamma (epair x1 x2) (tpair A B)

| has_type_pair_match : forall Sigma Gamma x x1 x2 e A B C,
    has_type Sigma (context_add (context_add Gamma (x1, A)) (x2, B)) e C ->
    has_type Sigma (context_add Gamma (x, tpair A B)) (epair_match x (x1, x2) e) C

| has_type_sum_inl : forall Sigma x A B,
    has_type Sigma (context_add Context.empty (x, A)) (esum_inl x) (tsum A B)

| has_type_sum_inr : forall Sigma x A B,
    has_type Sigma (context_add Context.empty (x, B)) (esum_inr x) (tsum A B)

| has_type_sum_match : forall Sigma Gamma x y z el er A B C,
    has_type Sigma (context_add Gamma (y, A)) el C ->
    has_type Sigma (context_add Gamma (z, B)) er C ->
    has_type Sigma (context_add Gamma (x, tsum A B))
      (esum_match x (y, el) (z, er)) C

| has_type_sum_match_elim : forall Sigma Gamma x y z el er A B C,
    has_type Sigma (context_add Gamma (y, A)) el C ->
    has_type Sigma (context_add Gamma (z, B)) er C ->
    has_type Sigma (context_add Gamma (x, tsum A B))
      (esum_match_elim x (y, el) (z, er)) C

| has_type_list_nil : forall Sigma A,
    has_type Sigma Context.empty elist_nil (tlist A)

| has_type_list_const : forall Sigma xh xt A,
    let Gamma := context_add (context_add Context.empty (xh, A)) (xt, tlist A) in
    has_type Sigma Gamma (elist_cons xh xt)  (tlist A)

| has_type_list_match : forall Sigma Gamma x xh xt e1 e2 A C,
    has_type Sigma Gamma e1 C ->
    has_type Sigma (context_add (context_add Gamma (xh, A)) (xt, tlist A)) e2 C ->
    has_type Sigma (context_add Gamma (x, tlist A))
      (elist_match x e1 (xh, xt, e2)) C

| has_type_list_match_elim : forall Sigma Gamma x xh xt e1 e2 A C,
    has_type Sigma Gamma e1 C ->
    has_type Sigma (context_add (context_add Gamma (xh, A)) (xt, tlist A)) e2 C ->
    has_type Sigma (context_add Gamma (x, tlist A))
      (elist_match x e1 (xh, xt, e2)) C

(* Structural Rules *)

| has_type_weak : forall Sigma Gamma x e A C,
    ~ Context.In x Gamma ->
    has_type Sigma Gamma e C ->
    has_type Sigma (context_add Gamma (x, A)) e C

| has_type_share : forall Sigma Gamma x y z e A A1 A2 C,
    has_type Sigma (context_add (context_add Gamma (x, A1)) (y, A2)) e C ->
    share A (A1, A2) ->
    has_type Sigma (context_add Gamma (z, A))
      (subst (z, evar x) (subst (z, evar y) e)) C
.


(* Definition 4.4 *)
Definition program := var -> list var * expr.

Definition loc := nat.
Module Loc := Nat.
Module LocSet := MSetWeakList.Make Loc.
Print MSetWeakList.Make.

Inductive val : Type :=
| vunit : val
| vtt : val
| vff : val
| vpair : val -> val -> val
| vloc : loc -> val
| vnull : val
| vbad : val.

(* Module LocVal : DecidableType. *)
Module LocVal : DecidableType.
  Definition t : Set := loc * val.
  Definition eq (p1 p2 : t) : Prop :=
    let (l1, v1) := p1 in
    let (l2, v2) := p2 in
    l1 = l2 /\ v1 = v2.

  Instance eq_reflexive : Reflexive eq.
    intros [x1 x2]. simpl. auto.
  Qed.

  Instance eq_symmetric : Symmetric eq.
    intros [x1 x2] [y1 y2] [H1 H2]. simpl. auto.
  Qed.

  Instance eq_transitive : Transitive eq.
    intros [x1 x2] [y1 y2] [z1 z2] [H1 H2] [H3 H4]. simpl. eauto using eq_trans.
  Qed.

  Instance eq_equiv : Equivalence eq.
    split.
    - exact eq_reflexive.
    - exact eq_symmetric.
    - exact eq_transitive.
  Qed.

  Theorem eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    intros [x1 x2] [y1 y2].
    simpl.
  Admitted.

End LocVal.

(* Definition 4.6 *)
Module Var := Nat.
Module Stack := FMapWeakList.Make Var.
Module StackFacts := Facts Stack.
Module StackProperties := Properties Stack.

Arguments Stack.empty {elt}.
Arguments Stack.find {elt}.

Module Heap := FMapWeakList.Make Loc.
Module HeapFacts := Facts Heap.
Module HeapProperties := Properties Heap.

Arguments Heap.empty {elt}.
Arguments Heap.remove {elt}.

Definition stack := Stack.t val.
Definition heap := Heap.t val.

Definition stack_empty : stack := Stack.empty.
Definition heap_empty : heap := Heap.empty.

Definition stack_add (s : stack) (p : var * option val) :=
  match p with
  | (_, None) => s
  | (x, Some v) => Stack.add x v s
  end.

Definition heap_add (h : heap) (p : loc * val) :=
  let (x, v) := p in Heap.add x v h.

Definition alloc (h : heap) (l : loc) (v : val) := Heap.add l v h.
Definition dealloc (l : loc) (h : heap) := Heap.add l vbad h.

Definition heap_remove (h : heap) (l : loc) := Heap.remove l h.


Inductive eval : program -> stack -> heap -> expr -> val -> heap -> Prop :=
| eval_unit :  forall p s h,
    eval p s h eunit vunit h

| eval_true :  forall p s h,
    eval p s h etrue vtt h

| eval_false : forall p s h,
    eval p s h efalse vff h

| eval_var : forall p s h x v,
    Stack.find x s = Some v ->
    eval p s h (evar x) v h

| eval_let : forall p s h h0 h' x v0 v e1 e2,
    eval p s h e1 v0 h0 -> eval p (stack_add s (x, Some v0)) h0 e2 v h' ->
    eval p s h (elet x e1 e2) v h'

| eval_fun : forall (p : program) (s : stack) (h h' : heap) (f : var)
    (ys : list var) (ef : expr) (xs : Vector.t var (List.length ys)) (v : val),
    p f = (ys, ef) ->
    let vs := Vector.map (flip Stack.find s) xs in
    let yvs := Vector.map2 pair (Vector.of_list ys) vs in
    let s' := Vector.fold_left stack_add stack_empty yvs in
    eval p s' h ef v h' ->
    eval p s h (eapp f xs) v h'

| eval_if_true : forall p s h h' x et ef v,
    Stack.find x s = Some vtt ->
    eval p s h et v h' ->
    eval p s h (eif x et ef) v h'

| eval_if_false : forall p s h h' x et ef v,
    Stack.find x s = Some vff ->
    eval p s h ef v h' ->
    eval p s h (eif x et ef) v h'

| eval_pair : forall p s h x1 x2 v1 v2,
    Stack.find x1 s = Some v1 ->
    Stack.find x2 s = Some v2 ->
    eval p s h (epair x1 x2) (vpair v1 v2) h

| eval_pair_match : forall p s h h' x x1 x2 v1 v2 e v,
    Stack.find x s = Some (vpair v1 v2) ->
    let s' := Stack.add x1 v1 (Stack.add x2 v2 s) in
    eval p s' h e v h' ->
    eval p s h (epair_match x  (x1, x2) e) v  h'

| eval_sum_inl : forall p s h x w l v,
    Stack.find x s = Some v ->
    w = vpair vtt v ->
    Heap.find l h = None ->
    eval p s h (esum_inl x) (vloc l) (alloc h l w)

| eval_sum_inr : forall p s h x w l v,
    Stack.find x s = Some v ->
    w = vpair vff v ->
    Heap.find l h = None ->
    eval p s h (esum_inr x) (vloc l) (alloc h l w)

| eval_sum_match_inl : forall p s h h' l x y z w w' el er v,
    Stack.find x s = Some (vloc l) ->
    Heap.find l h = Some w ->
    w = vpair vtt w' ->
    eval p (stack_add s (y, Some w')) h el v h' ->
    eval p s h (esum_match x (y, el) (z, er)) v h'

| eval_sum_match_elim_inl : forall p s h h' l x y z w w' el er v,
    Stack.find x s = Some (vloc l) ->
    Heap.find l h = Some w ->
    w = vpair vtt w' ->
    eval p (stack_add s (y, Some w')) (dealloc l h) el v h' ->
    eval p s h (esum_match_elim x (y, el) (z, er)) v h'

| eval_sum_match_inr : forall p s h h' l x y z w w' el er v,
    Stack.find x s = Some (vloc l) ->
    Heap.find l h = Some w ->
    w = vpair vff w' ->
    eval p (stack_add s (z, Some w')) h er v h' ->
    eval p s h (esum_match x (y, el) (z, er)) v h'

| eval_sum_match_elim_inr : forall p s h h' l x y z w w' el er v,
    Stack.find x s = Some (vloc l) ->
    Heap.find l h = Some w ->
    w = vpair vff w' ->
    eval p (stack_add s (z, Some w')) (dealloc l h) er v h' ->
    eval p s h (esum_match_elim x (y, el) (z, er)) v h'

| eval_list_nil : forall p s h,
    eval p s h elist_nil vnull h

| eval_list_cons : forall p s h l w xh xt vh vt,
    Stack.find xh s = Some vh ->
    Stack.find xt s = Some vt ->
    w = vpair vh vt ->
    Heap.find l h = None ->
    eval p s h (elist_cons xh xt) (vloc l) (heap_add h (l, w))

| eval_list_match_nil : forall p s h h' x xh xt e1 e2 v,
    Stack.find x s = Some vnull ->
    eval p s h e1 v h' ->
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'

| eval_list_match_elim_nil : forall p s h h' x xh xt e1 e2 v,
    Stack.find x s = Some vnull ->
    eval p s h e1 v h' -> 
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'

| eval_list_match_cons : forall (p : program) (s : stack) (h h' : heap)
    (l : loc) (x xh xt : var) (w wh wt : val) (e1 e2 : expr) (v : val),
    Stack.find x s = Some (vloc l) ->
    Heap.find l h = Some w ->
    w = (vpair wh wt) ->
    eval p (stack_add (stack_add s (xh, Some wh)) (xt, Some wt)) h e2 v h' ->
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'

| eval_list_match_elim_cons : forall (p : program) (s s' : stack) (h h' : heap)
    (l : loc) (x xh xt : var) (w wh wt : val) (e1 e2 : expr) (v : val),
    Stack.find x s = Some (vloc l) ->
    Heap.find l h = Some w ->
    w = (vpair wh wt) ->
    s' = stack_add (stack_add s (xh, Some wh)) (xt, Some wt) ->
    eval p s' (heap_add h (l, vbad)) e2 v h' ->
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'
.

Definition heap_is_subset (h h' : heap) : Prop :=
  forall x v, Heap.find x h = Some v -> Heap.find x h' = Some v.

Lemma heap_is_subset_refl : forall (h : heap),
  heap_is_subset h h.
Proof.
  unfold heap_is_subset. trivial.
Qed.

Lemma heap_is_subset_trans : forall (h1 h2 h3 : heap),
  heap_is_subset h1 h2 -> heap_is_subset h2 h3 -> heap_is_subset h1 h3.
Proof.
  unfold heap_is_subset. auto.
Qed.

Lemma heap_add_lookup_refl : forall (h : heap) (l : loc) (x : val),
  Heap.find l (heap_add h (l, x)) = Some x.
Proof.
  simpl. auto using HeapFacts.add_eq_o.
Qed.

Lemma Some_implies_not_None : forall (A : Set) (o : option A) (x : A),
  o = Some x -> o <> None.
Proof. congruence. Qed.

Lemma not_None_implies_Some : forall (A : Set) (o : option A),
  o <> None -> exists (x : A), o = Some x.
Proof.
  intros A o H.
  destruct o.
  - exists a. reflexivity.
  - congruence.
Qed.

Lemma new_heap_lookup_diff : forall (h : heap) (l l' : loc) (x : val),
   l' <> l ->
   Heap.In l h ->
   Heap.find l (Heap.add l' x h) = Heap.find l h.
Proof.
  intros h l l' x  H1 H2.
  apply HeapFacts.in_find_iff in H2.
  apply not_None_implies_Some in H2 as [x' H2].
  assert (H3 := Heap.find_2 H2).
  assert (H4 := HeapFacts.add_neq_mapsto_iff h x x' H1).
  apply proj2 in H4.
  eauto using eq_trans, Heap.find_1.
Qed.

Lemma in_if_find_some : forall (h : heap) (l : loc) (x : val),
  Heap.find l h = Some x -> Heap.In l h.
Proof.
  intros l h x H.
  apply Some_implies_not_None in H.
  apply HeapFacts.in_find_iff in H.
  assumption.
Qed.

Lemma in_add_if_in : forall (h : heap) (l l' : loc) (x : val),
  Heap.In l h -> Heap.In l (Heap.add l' x h).
Proof.
  intros h l l' x H.
  apply HeapFacts.add_in_iff.
  auto.
Qed.


Lemma in_add_neq_iff : forall (h : heap) (l l' : loc) (x : val),
  l <> l' -> Heap.In l h <-> Heap.In l (Heap.add l' x h).
Proof.
  intros h l l' x H1.
  split.
  - apply in_add_if_in.
  - intros H2.
    apply HeapFacts.add_in_iff in H2.
    destruct H2 as [H2 | H2]; congruence.
Qed.

(* Lemma 4.8 *)
Lemma heap_stability : forall p s h e v h',
  eval p s h e v h' ->
  forall l,
  Heap.In l h ->
  Heap.find l h' = Heap.find l h \/ Heap.find l h' = Some vbad.
Proof.
  intros p s h e v h' H1. induction H1; try assumption; try (left; reflexivity).
  - (* eval_let *)
    intros l H2. destruct (IHeval1 _ H2) as [H3 | H3]; rewrite <- H3 in *.
    + apply HeapFacts.in_find_iff in H2.
      apply not_None_implies_Some in H2 as [x' H2].
      rewrite H2 in *.
      apply in_if_find_some in H3.
      destruct (IHeval2 _ H3) as [H5 | H5]; rewrite H5 in *; auto.
    + apply Some_implies_not_None in H3.
      apply HeapFacts.in_find_iff in H3.
      destruct (IHeval2 _ H3) as [H5 | H5]; rewrite H5 in *; auto.
  - (* eval_sum_inl *)
    intros l' H2. left. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb. rewrite Heqb in *.
      apply HeapFacts.in_find_iff in H2.
      congruence.
    + rewrite Nat.eqb_neq in Heqb.
      unfold alloc.
      auto using new_heap_lookup_diff.
  - (* eval_sum_inr *)
    intros l' H2. left. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb. rewrite Heqb in *.
      apply HeapFacts.in_find_iff in H2.
      congruence.
    + rewrite Nat.eqb_neq in Heqb.
      unfold alloc.
      auto using new_heap_lookup_diff.
  - (* eval_sum_match_inl *)
    intros l' HEAP_DOM. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb; rewrite Heqb in *.
      assert (H3 := heap_add_lookup_refl h l' vbad).
      apply in_if_find_some in H3.
      destruct (IHeval l' H3) as [H4 | H4];
        rewrite H4; eauto using HeapFacts.add_eq_o.
    + apply Nat.eqb_neq in Heqb.
      eapply in_add_if_in in HEAP_DOM.
      specialize (IHeval l' HEAP_DOM).
      destruct IHeval as [IHeval | IHeval].
      * rewrite IHeval. left.
        eapply new_heap_lookup_diff; try assumption.
        eapply in_add_neq_iff with (l':=l); eauto.
      * auto.
  - (* eval_sum_match_inr *)
    intros l' HEAP_DOM.
    specialize (IHeval _ (in_add_if_in _ _ l vbad HEAP_DOM)).
    destruct (Nat.eqb l l') eqn:Heqn.
    + rewrite Nat.eqb_eq in Heqn; subst.
      destruct IHeval as [IHeval | IHeval];
        rewrite IHeval; eauto using HeapFacts.add_eq_o.
    + rewrite Nat.eqb_neq in Heqn.
      unfold dealloc in IHeval.
      destruct IHeval as [IHeval | IHeval];
        rewrite IHeval; auto using new_heap_lookup_diff.
  - (* eval_list_cons *)
    intros l' HEAP_DOM. destruct (Nat.eqb l l') eqn:Heqn.
    + rewrite Nat.eqb_eq in Heqn. subst.
      apply HeapFacts.in_find_iff in HEAP_DOM. congruence.
    + rewrite Nat.eqb_neq in Heqn.
      eauto using new_heap_lookup_diff.
  - (* eval_list_match_cons *)
    intros l' HEAP_DOM.
    specialize (IHeval _ (in_add_if_in _ _ l vbad HEAP_DOM)).
    destruct (Nat.eqb l l') eqn:Heqn.
    + rewrite Nat.eqb_eq in Heqn; subst.
      destruct IHeval as [IHeval | IHeval];
        rewrite IHeval; eauto using HeapFacts.add_eq_o.
    + rewrite Nat.eqb_neq in Heqn.
      destruct IHeval as [IHeval | IHeval];
        rewrite IHeval; eauto using new_heap_lookup_diff.
Qed.

Check @LocSet.fold.

Lemma heap_stability2 : forall p s h e v h',
  eval p s h e v h' ->
  exists (s1 :  (s2 : LocSet.t),
  h' = LocSet.fold dealloc s2 h.
Proof.

Lemma heap_stability_domain : forall p s h e v h',
  eval p s h e v h' ->
  forall l x, h l = Some x -> exists x', h' l = Some x'.
Proof.
  intros p s h e v h' EVAL l x H.
  eapply heap_stability in EVAL; try eassumption.
  destruct EVAL as [H2 | H2].
  - rewrite H2. exists x. assumption.
  - rewrite H2. exists vbad. reflexivity.
Qed.

Lemma heap_stability_domain' : forall p s h e v h',
  eval p s h e v h' ->
  forall l, h l <> None -> h' l <> None.
Proof.
  intros p s h e v h' EVAL l H.
  apply not_None_implies_Some in H.
  destruct H as [x H].
  eapply heap_stability in EVAL as [H1 | H2].
  - rewrite H1. eauto using Some_implies_not_None.
  - eauto using Some_implies_not_None.
  - eassumption.
Qed.

Definition heap_is_in_dom (h : heap) (l : loc) : Prop := h l <> None.
Definition heap_is_not_in_dom (h : heap) (l : loc) : Prop := h l = None.
Definition is_dealloc (h : heap) (l : loc) : Prop := h l = Some vbad.
Definition dealloc (h : heap) (l : loc) : heap := heap_add h (l, vbad).

Lemma heap_stability_list_deallocations : forall p s h e v h',
  eval p s h e v h' ->
  exists (ls : list loc),
  Forall (heap_is_in_dom h) ls /\ Forall (is_dealloc h') ls.
Proof.
  intros p s h e v h' EVAL.
  exists nil.
  auto.
Qed.

(* Definition 4.9 *)

Inductive mem_consistant : heap -> val -> type0 -> Prop :=
| mem_cons_unit : forall h,
    mem_consistant h vunit tunit

| mem_cons_true : forall h,
    mem_consistant h vtt tbool

| mem_cons_false : forall h,
    mem_consistant h vff tbool

| mem_cons_pair : forall h v w A B,
    mem_consistant h v A ->
    mem_consistant h w B ->
    mem_consistant h (vpair v w) (tpair A B)

| mem_cons_sum_inl : forall h l v A B,
    h l = Some (vpair vtt v) ->
    mem_consistant (heap_remove h l) v A ->
    mem_consistant h (vloc l) (tsum A B)

| mem_cons_sum_inr : forall h l v A B,
    h l = Some (vpair vff v) ->
    mem_consistant (heap_remove h l) v B ->
    mem_consistant h (vloc l) (tsum A B)

| mem_cons_sum_bad : forall h l A B,
    h l = Some vbad ->
    mem_consistant h (vloc l) (tsum A B)

| mem_cons_list_nil : forall h A,
    mem_consistant h vnull (tlist A)

| mem_cons_list_cons : forall h l A v,
    h l = Some v ->
    mem_consistant (heap_remove h l) v (tpair A (tlist A)) ->
    mem_consistant h (vloc l) (tlist A)

| mem_cons_list_bad : forall h l A,
    h l = Some vbad ->
    mem_consistant h (vloc l) (tlist A)
.

Definition mem_consistant_stack (h : heap) (s : stack) (Gamma : context) :=
  forall x t, Context.find x Gamma = Some t -> exists v, s x = Some v /\ mem_consistant h v t.

Definition context_is_subset (c c' : context) : Prop :=
  forall x v, Context.find x c = Some v -> Context.find x c' = Some v.

Lemma context_is_subset_refl : forall (c : context),
  context_is_subset c c.
Proof.
  unfold context_is_subset. trivial.
Qed.

Lemma context_is_subset_add : forall (c : context) (x : var) (t : type0),
  ~ Context.In x c -> context_is_subset c (context_add c (x, t)).
Proof.
  intros.
  unfold context_is_subset.
  intros x0 v CONTEXT_DOM.
  unfold context_add.
  apply ContextFacts.not_find_in_iff in H.
  destruct (Nat.eqb x0 x) eqn:Eqn.
  - rewrite Nat.eqb_eq in Eqn; subst.
    congruence.
  - rewrite Loc.eqb_sym in Eqn.
    rewrite Loc.eqb_neq in Eqn.
    rewrite (ContextFacts.add_neq_o _ _ Eqn).
    assumption.
Qed.

Definition stack_is_subset (s s' : stack) : Prop :=
  forall x v, s x = Some v -> s' x = Some v.

Lemma stack_is_subset_refl : forall (s : stack),
  stack_is_subset s s.
Proof.
  unfold stack_is_subset. trivial.
Qed.

Lemma stack_is_subset_trans : forall (s1 s2 s3 : stack),
  stack_is_subset s1 s2 -> stack_is_subset s2 s3 -> stack_is_subset s1 s3.
Proof.
  unfold stack_is_subset. auto.
Qed.

Lemma stack_is_subset_add : forall s x v,
  s x = None -> stack_is_subset s (stack_add s (x, Some v)).
Proof.
  intros.
  unfold stack_is_subset.
  intros x0 v0 STACK_DOM.
  simpl.
  destruct (Nat.eqb x x0) eqn:Eqn.
  - rewrite Nat.eqb_eq in Eqn. congruence.
  - assumption.
Qed.

Lemma heap_is_subset_remove : forall (h h' : heap) (l : loc),
  heap_is_subset h h' ->
  heap_is_subset (heap_remove h l) (heap_remove h' l).
Proof.
  unfold heap_is_subset.
  unfold heap_remove.
  intros h h' l HEAP_SUBSET x.
  destruct (Nat.eqb l x); auto.
Qed.

Lemma mem_consistancy_heap : forall (h h' : heap) (v : val) (t : type0),
  heap_is_subset h h' -> mem_consistant h v t -> mem_consistant h' v t.
Proof.
  intros h h' v t HEAP_SUBSET MEM_CONS. generalize dependent h'.
  induction MEM_CONS; intros; eauto using mem_consistant, heap_is_subset_remove.
Qed.

Lemma mem_consistancy_stack : forall (h: heap) (s s' : stack) (Gamma : context),
  stack_is_subset s s' ->
  mem_consistant_stack h s Gamma ->
  mem_consistant_stack h s' Gamma.
Proof.
  intros h s s' Gamma STACK_SUBSET MEM_CONS.
  unfold mem_consistant_stack in *.
  intros x t Hcontext.
  apply MEM_CONS in Hcontext as [v [H1 H2]].
  eauto.
Qed.

(* Lemma 4.10 *)
Lemma mem_consistancy_closure : forall h h' s s' Delta Gamma,
  heap_is_subset h h' ->
  stack_is_subset s s' ->
  context_is_subset Delta Gamma ->
  mem_consistant_stack h s Gamma ->
  mem_consistant_stack h' s' Delta.
Proof.
  intros h h' s s' Delta Gamma HEAP_SUBSET STACK_SUBSET CONTEXT_SUBSET MEM_CONS.
  unfold mem_consistant_stack.
  intros x t Hcontext.
  apply CONTEXT_SUBSET in Hcontext.
  eapply MEM_CONS in Hcontext as [v [H1 H2]].
  eauto using mem_consistancy_heap.
Qed.

Definition stack_is_disjoint (s s' : stack) : Prop := forall x v,
  (s  x = Some v -> s' x = None) /\
  (s' x = Some v -> s  x = None).

Print stack.
Print var.

Definition stack_join (s s' : stack) : stack := fun x =>
  match s x with
  | None => s' x
  | Some y => Some y
  end.

(* Lemma 4.11 *)
Lemma join_consistency :
  forall (h : heap) (s s' : stack) (Delta Gamma : context),
  stack_is_disjoint s s' ->
  context_is_disjoint Delta Gamma ->
  mem_consistant_stack h s Gamma ->
  mem_consistant_stack h s' Delta ->
  mem_consistant_stack h (stack_join s s') (context_join Gamma Delta).
Proof.
  intros h s s' Delta Gamma STACK_DISJOINT _ MEM_CONS1 MEM_CONS2.
  unfold mem_consistant_stack in *. intros x t H.
  unfold context_join in H.
  destruct (Context.find x Gamma) eqn:GammaX.
  - rewrite H in GammaX.
    apply MEM_CONS1 in GammaX as [v [H1 H2]].
    unfold stack_join.
    rewrite H1. eauto.
  - apply MEM_CONS2 in H as [v [H1 H2]].
    unfold stack_join.
    rewrite H1.
    unfold stack_is_disjoint in STACK_DISJOINT.
    edestruct STACK_DISJOINT as [SD1 SD2].
    apply SD2 in H1.
    rewrite H1.
    eauto.
Qed.

Lemma heap_remove_add_swap : forall h l l' v,
  l <> l' ->
  heap_remove (heap_add h (l, v)) l' = heap_add (heap_remove h l') (l, v).
Proof.
  intros h l l' v H.
  extensionality x. unfold heap_add, heap_remove.
  destruct (Nat.eqb l x) eqn:Eqn1, (Nat.eqb l' x) eqn:Eqn2; try reflexivity.
  - apply beq_nat_true in Eqn1; subst.
    apply beq_nat_true in Eqn2; subst.
    congruence.
Qed.

Print context.

(* Lemma 4.12 *)
Lemma deallocation_consistency :
  forall (h : heap) (s : stack) (Gamma : context) (l : loc) (x : val),
  mem_consistant_stack h s Gamma ->
  h l = Some x ->
  mem_consistant_stack (heap_add h (l, vbad)) s Gamma.
Proof.
  unfold mem_consistant_stack in *.
  intros h s Gamma l x' MEM_CONS HEAP_DOM x t CONTEXT_DOM.
  apply MEM_CONS in CONTEXT_DOM as [v' [STACK_DOM MEM_CONS2]].
  exists v'.
  split; try assumption.
  clear MEM_CONS. clear Gamma. clear STACK_DOM.
  induction MEM_CONS2.
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - destruct (Nat.eqb l l0) eqn:Eqn.
    + apply beq_nat_true in Eqn. subst.
      apply mem_cons_sum_bad.
      unfold heap_add. rewrite Nat.eqb_refl. reflexivity.
    + apply mem_cons_sum_inl with (v:=v).
      * unfold heap_add. rewrite Eqn. assumption.
      * rewrite heap_remove_add_swap.
        { apply IHMEM_CONS2.
          unfold heap_remove.
          rewrite Nat.eqb_sym.
          rewrite Eqn.
          assumption. }
        { apply beq_nat_false. assumption. }
  - destruct (Nat.eqb l l0) eqn:Eqn.
    + apply beq_nat_true in Eqn. subst.
      apply mem_cons_sum_bad.
      unfold heap_add. rewrite Nat.eqb_refl. reflexivity.
    + apply mem_cons_sum_inr with (v:=v).
      * unfold heap_add. rewrite Eqn. assumption.
      * rewrite heap_remove_add_swap.
        { apply IHMEM_CONS2.
          unfold heap_remove.
          rewrite Nat.eqb_sym.
          rewrite Eqn.
          assumption. }
        { apply beq_nat_false. assumption. }
  - apply mem_cons_sum_bad.
    unfold heap_add.
    destruct (Nat.eqb l l0).
    + reflexivity.
    + assumption.
  - constructor.
  - destruct (Nat.eqb l l0) eqn:Eqn.
    + apply beq_nat_true in Eqn. subst.
      apply mem_cons_list_bad.
      unfold heap_add. rewrite Nat.eqb_refl. reflexivity.
    + apply mem_cons_list_cons with (v:=v).
      * unfold heap_add. rewrite Eqn. assumption.
      * rewrite heap_remove_add_swap.
        { apply IHMEM_CONS2.
          unfold heap_remove.
          rewrite Nat.eqb_sym.
          rewrite Eqn.
          apply HEAP_DOM. }
        { apply beq_nat_false. assumption. }
  - apply mem_cons_list_bad.
    unfold heap_add.
    destruct (Nat.eqb l l0).
    + reflexivity.
    + assumption.
Qed.

Check   List.fold_left.

Lemma deallocation_consistency_ind :
  forall (h : heap) (s : stack) (Gamma : context),
  mem_consistant_stack h s Gamma ->
  forall (ls : list loc),
  Forall (heap_is_in_dom h) ls ->
  let h' := List.fold_left (fun h l => heap_add h (l, vbad)) ls h in
  mem_consistant_stack h' s Gamma.
Proof.
Admitted.

Lemma deallocation_consistency' :
  forall (h : heap) (s : stack) (Gamma : context),
  mem_consistant_stack h s Gamma ->
  forall (l : loc),
  h l <> None ->
  mem_consistant_stack (heap_add h (l, vbad)) s Gamma.
Proof.
  intros h s Gamma MEM_CONS l H.
  apply not_None_implies_Some in H.
  destruct H.
  eauto using deallocation_consistency.
Qed.

Lemma heap_add_remove_new_loc : forall h l v,
  h l = None -> heap_remove (heap_add h (l, v)) l = h.
Proof.
  intros.
  unfold heap_remove, heap_add.
  extensionality y.
  destruct (Nat.eqb l y) eqn:Eqn.
  - rewrite Nat.eqb_eq in *. subst. auto.
  - reflexivity.
Qed.

Lemma context_add_lookup : forall (Gamma : context) (x : var) (t : type0),
  Context.find x (context_add Gamma (x, t)) = Some t.
Proof.
  intros. simpl. rewrite ContextFacts.add_eq_o; reflexivity.
Qed.

Definition heap_add_all (h : heap) (xs : list (loc * val)) : heap :=
  List.fold_left heap_add xs h.
Definition heap_dealloc_all (h : heap) (xs : list loc) : heap :=
  List.fold_left dealloc xs h.
Definition heap_fresh_location (h : heap) (lv : loc * val) :=
  let (l, v) := lv in ~heap_is_in_dom h l.
Definition heap_existing_location (h : heap) (lv : loc * val) :=
  let (l, v) := lv in heap_is_in_dom h l.

Lemma heap_add_lookup_distinct' : forall l x,
  l <> x ->
  forall h v,
  heap_add h (l, v) x = h x.
Proof.
  intros l x DISTINCT h v.
  simpl.
  rewrite <- Nat.eqb_neq in DISTINCT.
  rewrite DISTINCT.
  reflexivity.
Qed.

Lemma heap_add_all_lookup_distinct' : forall x ls,
  Forall (fun l => l <> x) ls ->
  forall vs zs,
  Zip ls vs zs ->
  forall h,
  heap_add_all h zs x = h x.
Proof.
  intros x ls ALL_DISTINCT.
  induction ALL_DISTINCT; intros vs zs ZIP h.
  - inversion ZIP; subst.
    reflexivity.
  - inversion ZIP; subst.
    simpl.
    erewrite IHALL_DISTINCT; try eassumption.
    apply heap_add_lookup_distinct'.
    assumption.
Qed.

Lemma heap_add_lookup_distinct'' :
  forall x xs, ~In x xs ->
  forall ys zs, Zip xs ys zs ->
  forall h, heap_add_all h zs x = h x.
Proof.
  intros x xs H1 ys zs ZIP.
  induction ZIP.
  - reflexivity.
  - intros h. simpl in *. rewrite IHZIP.
    + simpl. destruct (Nat.eqb x0 x) eqn:Heqn.
      * apply Nat.eqb_eq in Heqn.
        exfalso. auto.
      * reflexivity.
    + auto.
Qed.

Lemma heap_add_all_add' : forall (h : heap) ls,
  Forall (fun l => ~heap_is_in_dom h l) ls ->
  forall vs zs,
  Zip ls vs zs ->
  forall l,
  ~heap_is_in_dom h l ->
  Forall (fun x => x <> l) ls ->
  forall v,
  heap_add_all (heap_add h (l, v)) zs = heap_add (heap_add_all h zs) (l, v).
Proof.
  intros h ls ALL_FRESH.
  induction ALL_FRESH; intros vs zs ZIP; inversion ZIP; subst; clear ZIP.
  - reflexivity.
  - intros l0 FRESH ALL_DISTINCT v.
    inversion ALL_DISTINCT; subst; clear ALL_DISTINCT.
    simpl.
    extensionality a.
    simpl.
    destruct (Nat.eqb l0 a) eqn:Heqn1.
    + apply Nat.eqb_eq in Heqn1; subst.
      rewrite (heap_add_all_lookup_distinct' _ _ H3 _ _ H4).
      rewrite (heap_add_lookup_distinct' _ _ H2).
      apply heap_add_lookup_refl.
    + destruct (in_dec Nat.eq_dec a l).
      * specialize (IHALL_FRESH _ _ H4 _ FRESH H3).
        assert (FOO :
          forall x xs, In x xs ->
          forall ys zs, Zip xs ys zs ->
          forall h1 h2, heap_add_all h1 zs x = heap_add_all h2 zs x). {
          clear.
          intros x xs.
          induction xs; intros H ys zs ZIP h1 h2.
          - exfalso. assumption.
          - inversion ZIP; subst; clear ZIP.
            simpl in *. destruct H as [H | H].
            + subst.
              assert (DISTINCT : ~ In x xs). admit.
              repeat erewrite heap_add_lookup_distinct''; try eassumption.
              repeat rewrite heap_add_lookup_refl.
              reflexivity.
            + eapply IHxs; try eassumption.
        }
        eapply FOO; eauto.
      * repeat rewrite (heap_add_lookup_distinct'' _ _ n _ _ H4).
        simpl. rewrite Heqn1. reflexivity.
Admitted.

Lemma heap_is_subset_add_all_fresh : forall h xs,
    Forall (fun x => ~ heap_is_in_dom h x) xs ->
    forall ys zs, Zip xs ys zs ->
    heap_is_subset h (heap_add_all h zs).
Proof.
  intros h xs ALL_FRESH.
  induction xs; intros ys zs ZIP.
  - inversion ZIP; subst; clear ZIP.
    auto using heap_is_subset_refl.
  - inversion ZIP; subst; clear ZIP.
    inversion ALL_FRESH; subst; clear ALL_FRESH.
    specialize (IHxs H2 _ _ H3).
    intros x v HEAP_DOM.
    simpl.
    specialize (IHxs _ _ HEAP_DOM).
    Check heap_add_all_add'.
    erewrite heap_add_all_add'; try eassumption.
    + unfold heap_add.
      rewrite IHxs.
      destruct (Nat.eqb a x) eqn:Heqn.
      * apply Nat.eqb_eq in Heqn.
        subst. unfold heap_is_in_dom in H1.
        apply Some_implies_not_None in HEAP_DOM.
        exfalso.
        auto.
      * reflexivity.
    + admit. (* True if the elements of the list are unique *)
Admitted.

Lemma mem_consistant_stack_heap_add_all : forall h s G,
  mem_consistant_stack h s G ->
  forall xs, Forall (fun x => ~ heap_is_in_dom h x) xs ->
  forall ys zs, Zip xs ys zs ->
  mem_consistant_stack (heap_add_all h zs) s G.
Proof.
  intros h s G MEM_CONS xs ALL_FRESH ys zs ZIP.
  eapply mem_consistancy_closure;
    eauto using
      heap_is_subset_add_all_fresh,
      stack_is_subset_refl,
      context_is_subset_refl.
Qed.

Lemma mem_consistant_stack_heap_dealloc_all :
  forall h s G, mem_consistant_stack h s G ->
  forall xs, Forall (heap_is_in_dom h) xs ->
  mem_consistant_stack (heap_dealloc_all h xs) s G.
Proof.
  intros h s G MEM_CONS xs DOM.
  generalize dependent h.
  induction xs.
  - intros. assumption.
  - intros h MEM_CONS DOM. simpl.
    inversion DOM; subst; clear DOM.
    apply IHxs.
    + eauto using deallocation_consistency'.
    + admit. (* True if the elements of the list are unique. *)
Admitted.

Lemma heap_is_in_dom_after_dealloc : forall x h l,
  heap_is_in_dom h x ->
  heap_is_in_dom h l ->
  heap_is_in_dom (dealloc h l) x.
Proof.
  intros x h b H1 H2.
  unfold heap_is_in_dom, dealloc in *.
  simpl.
  destruct (Nat.eqb b x); congruence.
Qed.

Lemma heap_is_in_dom_forall_after_dealloc : forall xs h l,
  Forall (heap_is_in_dom h) xs ->
  heap_is_in_dom h l ->
  Forall (heap_is_in_dom (dealloc h l)) xs.
Proof.
  induction xs; intros h b H1 H2.
  - constructor.
  - inversion H1; clear H1; subst.
    auto using heap_is_in_dom_after_dealloc.
Qed.

Lemma heap_is_not_in_dom_after_dealloc : forall x h l,
  ~ heap_is_in_dom h x ->
  heap_is_in_dom h l ->
  ~heap_is_in_dom (dealloc h l) x.
Proof.
  intros x h b H1 H2.
  unfold heap_is_in_dom, dealloc in *.
  simpl.
  destruct (Nat.eqb b x) eqn:Heqn.
  - intro H3.
    apply Nat.eqb_eq in Heqn.
    subst.
    auto.
  - assumption.
Qed.

Lemma heap_is_not_in_dom_after_dealloc_all : forall ys h x,
  Forall (heap_is_in_dom h) ys ->
  ~ heap_is_in_dom h x ->
  ~ heap_is_in_dom (heap_dealloc_all h ys) x.
Proof.
  induction ys; simpl; intros h x H1 H2.
  - assumption.
  - inversion H1; subst; clear H1.
    apply IHys.
    + auto using heap_is_in_dom_forall_after_dealloc.
    + auto using heap_is_not_in_dom_after_dealloc.
Qed.

Lemma heap_is_not_in_dom_forall_after_dealloc_all : forall h xs ys,
  Forall (fun x => ~ heap_is_in_dom h x) xs ->
  Forall (heap_is_in_dom h) ys ->
  Forall (fun x => ~ heap_is_in_dom (heap_dealloc_all h ys) x) xs.
Proof.
  intros h xs. generalize dependent h.
  induction xs; intros h ys ALL_FRESH H1.
  - constructor.
  - inversion ALL_FRESH; subst; clear ALL_FRESH.
    auto using heap_is_not_in_dom_after_dealloc_all.
Qed.

(* Lemma 4.13 *)
Lemma preservation : forall (l : loc) (Sigma : prog_sig) (Gamma : context) (p : program)
  (s : stack) (h h' : heap) (e : expr) (c : type0) (v : val),
  (* 4.1 *) has_type Sigma Gamma e c ->
  (* 4.2 *) eval p s h e v h' ->
  (* 4.3 *) mem_consistant_stack h s Gamma ->
  (* 4.a *) mem_consistant h' v c /\ (* 4.b *) mem_consistant_stack h' s Gamma.
Proof.
  intros l Sigma Gamma p s h h' e c v WELL_TYPED EVAL. split.
  - generalize dependent s.
    generalize dependent h'.
    generalize dependent h.
    generalize dependent v.
    generalize dependent p.
    induction WELL_TYPED; intros p v h h' s EVAL MEM_CONS.
    + inversion EVAL; subst. apply mem_cons_unit.
    + inversion EVAL; subst. apply mem_cons_true.
    + inversion EVAL; subst. apply mem_cons_false.
    + inversion EVAL; subst. unfold mem_consistant_stack in MEM_CONS.
      specialize (MEM_CONS x C (context_add_lookup _ _ _)).
      destruct MEM_CONS as [v' [H1 H2]]. congruence.
    + (* let x = e1 in e2 *)
      assert (H1 := heap_is_subset_refl h).
      assert (H2 := stack_is_subset_refl s).
      assert (H3 : context_is_subset Gamma1 (context_join Gamma1 Gamma2)).
      { unfold context_is_subset, context_join. intros. rewrite H. reflexivity. }
      assert (H4 : context_is_subset Gamma2 (context_join Gamma1 Gamma2)).
      { admit.
      (* redefine context_join as a relation with hypothesis for disjoinct
         domain *) }
      assert (MEM_CONS_Gamma1 := mem_consistancy_closure _ _ _ _ _ _ H1 H2 H3 MEM_CONS).
      assert (MEM_CONS_Gamma2 := mem_consistancy_closure _ _ _ _ _ _ H1 H2 H4 MEM_CONS).
      inversion EVAL; subst; clear EVAL.
      specialize (IHWELL_TYPED1 _ _ _ _ _ H11 MEM_CONS_Gamma1).
      (* with inductive version of lemma 4.8 and 4.12 *)
      admit.
    + admit.
    + inversion EVAL; subst.
      * eapply IHWELL_TYPED1;
          eauto using
            mem_consistancy_closure,
            heap_is_subset_refl,
            stack_is_subset_refl,
            context_is_subset_add.
      * eapply IHWELL_TYPED2;
          eauto using mem_consistancy_closure,
            heap_is_subset_refl,
            stack_is_subset_refl,
            context_is_subset_add.
    + inversion EVAL; subst.
      unfold mem_consistant_stack in MEM_CONS.
      subst Gamma.
      apply mem_cons_pair.
      * specialize (MEM_CONS x1 A); simpl in MEM_CONS.
        Search (Nat.eqb _ _ = false).
        rewrite <- Nat.eqb_neq in H.
        rewrite H in MEM_CONS.
        rewrite Nat.eqb_refl in MEM_CONS.
        specialize (MEM_CONS eq_refl).
        destruct MEM_CONS as [v [STACK_DOM MEM_CONS]].
        rewrite STACK_DOM in H5.
        injection H5; intros; subst.
        assumption.
      * specialize (MEM_CONS x2 B); simpl in MEM_CONS.
        rewrite <- Nat.eqb_neq in H.
        rewrite Nat.eqb_sym in H.
        rewrite H in MEM_CONS.
        rewrite Nat.eqb_refl in MEM_CONS.
        specialize (MEM_CONS eq_refl).
        destruct MEM_CONS as [v [STACK_DOM MEM_CONS]].
        rewrite STACK_DOM in H8.
        injection H8; intros; subst.
        assumption.
    + inversion EVAL; subst.
      eapply IHWELL_TYPED.
      * apply H9.
      * assert (H1 : s x1 = None). admit.
        assert (H2 : stack_add s (x1, Some v1) x2 = None). admit.
        assert (H3 := stack_is_subset_add s x1 v1 H1).
        assert (H4 := stack_is_subset_add (stack_add s (x1, Some v1)) x2 v2 H2).
        assert (STACK_SUBSET := stack_is_subset_trans _ _ _ H3 H4).
        admit.
    + inversion EVAL; subst.
      eapply mem_cons_sum_inl.
      * rewrite heap_add_lookup_refl. reflexivity.
      * rewrite (heap_add_remove_new_loc _ _ _ H5).
        unfold mem_consistant_stack in *.
        specialize (MEM_CONS x A).
        simpl in MEM_CONS. rewrite Nat.eqb_refl in *.
        specialize (MEM_CONS eq_refl).
        destruct MEM_CONS as [v [STACK_DOM MEM_CONS]].
        rewrite STACK_DOM in *.
        injection H0. intros; subst.
        assumption.
    + inversion EVAL; subst.
      eapply mem_cons_sum_inr.
      * rewrite heap_add_lookup_refl. reflexivity.
      * rewrite (heap_add_remove_new_loc _ _ _ H5).
        unfold mem_consistant_stack in *.
        specialize (MEM_CONS x B).
        simpl in MEM_CONS. rewrite Nat.eqb_refl in *.
        specialize (MEM_CONS eq_refl).
        destruct MEM_CONS as [v [STACK_DOM MEM_CONS]].
        rewrite STACK_DOM in *.
        injection H0. intros; subst.
        assumption.
    + admit.
    + admit.
    + inversion EVAL; subst.
      apply mem_cons_list_nil.
    + admit.
    + inversion EVAL; subst.
      * eapply IHWELL_TYPED1.
        { apply H10. }
        { admit. }
      * eapply IHWELL_TYPED1.
        { apply H10. }
        { admit. }
      * eapply IHWELL_TYPED2.
        { apply H12. }
        { admit. }
      * eapply IHWELL_TYPED2.
        { apply H13. }
        { admit. }
    + admit.
    + eapply IHWELL_TYPED.
      * apply EVAL.
      * Check mem_consistancy_closure.
        assert (HEAP_SUBSET := heap_is_subset_refl h).
        assert (STACK_SUBSET := stack_is_subset_refl s).
        assert (DOM_SUBSET := context_is_subset_add Gamma x A H).
        eauto using mem_consistancy_closure, heap_is_subset_refl,
        stack_is_subset_refl, context_is_subset_add.
    + admit.
(*
heap_stability
     : forall (p : program) (s : stack) (h : heap) (e : expr) (v : val)
         (h' : heap) (l : loc),
       eval p s h e v h' ->
       forall x : val, h l = Some x -> h' l = h l \/ h' l = Some vbad

heap_stability_domain
     : forall (p : program) (s : stack) (h : heap) (e : expr) (v : val)
         (h' : heap),
       eval p s h e v h' ->
       forall (l : loc) (x : val),
       h l = Some x -> exists x' : val, h' l = Some x'

deallocation_consistency'
     : forall (h : heap) (s : stack) (Gamma : context),
       mem_consistant_stack h s Gamma ->
       forall (l : loc) (x : val),
       h l = Some x -> mem_consistant_stack (heap_add h (l, vbad)) s Gamma

deallocation_consistency_ind
     : forall (h : heap) (s : stack) (Gamma : context),
       mem_consistant_stack h s Gamma ->
       forall (ls : list loc) (xs : list val),
       Forall2 (fun (l : loc) (x : val) => h l = Some x) ls xs ->
       let h' :=
         fold_left (fun (h0 : heap) (l : loc) => heap_add h0 (l, vbad)) ls h
         in
       mem_consistant_stack h' s Gamma


*)
  - (* assert (H2 := heap_stability_list_deallocations _ _ _ _ _ _ EVAL).
    destruct H2 as [ls [IN_HEAP WAS_DEALLOC]]. *)
(*     assert (H2 := heap_stability _ _ _ _ _ _ EVAL). *)
    
    assert (H3 := deallocation_consistency' _ _ _ H).
    
    assert (BAZ : forall p s h e v h',
      eval p s h e v h' ->
      exists ps ws,
      LocSet.For_all (compose (heap_is_not_in_dom h) fst) ps /\
      LocSet.For_all (heap_is_in_dom h) ws /\
      h' = heap_add_all (heap_dealloc_all h ws) zs). admit.
    
    destruct (BAZ _ _ _ _ _ _ EVAL)
      as [xs [ys [zs [ws [ZIP [FRESH [OLD H'DEF]]]]]]].
    subst.
    eapply mem_consistant_stack_heap_add_all.
    + apply mem_consistant_stack_heap_dealloc_all; assumption.
    + apply heap_is_not_in_dom_forall_after_dealloc_all; eassumption.
    + apply ZIP.
    (* from H2 we show that there is a list of deallocated locations
       from H3 we show the context with deallocated locations is memory consistant.
       from mem_consistancy_closure we show that any allocated location is irrelevant.
    *)
Admitted.



(* Definition 4.14 *)
Fixpoint size (v : val) : nat :=
match v with
| vunit => 1
| vtt => 1
| vff => 1
| vpair v1 v2 => size v1 + size v2
| vloc _ => 1
| vnull => 1
| vbad => 0
end.

(* Definition 4.15 *)
Fixpoint typ_size (t : type0) : nat :=
match t with
| tunit => 1
| tbool => 1
| tpair a b => typ_size a + typ_size b
| tsum _ _ => 1
| tlist _ => 1
end.

Check mem_consistant.

(* Lemma 4.16 *)
Lemma size_correspondance : forall (h: heap) (v : val) (a : type0),
  mem_consistant h v a -> size v = typ_size a.
Proof.
  intros h v a MEM_CONS. induction MEM_CONS; try reflexivity.
  - simpl. rewrite IHMEM_CONS1. rewrite IHMEM_CONS2. reflexivity.
Qed.

(* Definition 4.17 *)
Inductive evalR : program -> stack -> heap -> nat -> nat -> expr -> val ->
  heap -> Prop :=
| evalR_unit :  forall (p : program) (s : stack) (h : heap) (m : nat),
    evalR p s h m m eunit vunit h

| evalR_true :  forall (p : program) (s : stack) (h : heap) (m : nat),
    evalR p s h m m etrue vtt h

| evalR_false : forall (p : program) (s : stack) (h : heap) (m : nat),
    evalR p s h m m efalse vff h

| evalR_var : forall (p : program) (s : stack) (h : heap) (m : nat) x v,
    s x = Some v ->
    evalR p s h m m (evar x) v h

| evalR_let : forall (p : program) (s : stack) (h h0 h' : heap) (m m0 m' : nat)
    (x : var) (e1 e2 : expr) (v0 v : val),
    evalR p s h m m0 e1 v0 h0 ->
    evalR p (stack_add s (x, Some v0)) h0 m0 m' e2 v h' ->
    evalR p s h m m' (elet x e1 e2) v h'

| evalR_fun : forall (p : program) (s s' : stack) (h h' : heap) (f : var)
    (ys : list var) (ef : expr)
    (xs : Vector.t var (List.length ys))
    (vs : Vector.t (option val) (List.length ys))
    (v : val) (m m' : nat),
    vs = Vector.map s xs ->
    p f = (ys, ef) ->
    s' = Vector.fold_left stack_add stack_empty
      (Vector.map2 pair (Vector.of_list ys) vs) ->
    evalR p s' h m m' ef v h' ->
    evalR p s h m m' (eapp f xs) v h'

| evalR_if_true : forall (p : program) (s : stack) (h h' : heap) (x : var)
    (et ef : expr) (v : val) (m m' : nat),
    s x = Some vtt ->
    evalR p s h m m' et v h' ->
    evalR p s h m m' (eif x et ef) v h'

| evalR_if_false : forall (p : program) (s : stack) (h h' : heap) (x : var)
    (et ef : expr) (v : val) (m m' : nat),
    s x = Some vff ->
    evalR p s h m m' ef v h' ->
    evalR p s h m m' (eif x et ef) v h'

| evalR_pair : forall (p : program) (s : stack) (h : heap) (x1 x2 : var)
    (v1 v2 : val) (m : nat),
    s x1 = Some v1 ->
    s x2 = Some v2 ->
    evalR p s h m m (epair x1 x2) (vpair v1 v2) h

| evalR_pair_match : forall (p : program) (s s' : stack) (h h' : heap)
    (x x1 x2 : var) (v1 v2 v : val) (e : expr) (m m' : nat),
    s x = Some (vpair v1 v2) ->
    s' = stack_add (stack_add s (x1, Some v1)) (x2, Some v2) ->
    evalR p s' h m m' e v h' ->
    evalR p s h m m' (epair_match x  (x1, x2) e) v  h'

| evalR_sum_inl : forall (p : program) (s : stack) (h : heap) (x : var)
    (w : val) (l : loc) (v : val) (m' : nat),
    s x = Some v ->
    w = vpair vtt v ->
    h l = None ->
    evalR p s h (m' + size w) m' (esum_inl x) (vloc l) (heap_add h (l, w))

| evalR_sum_inr : forall (p : program) (s : stack) (h : heap) (x : var)
    (w : val) (l : loc) (v : val) (m' : nat),
    s x = Some v ->
    w = vpair vff v ->
    h l = None ->
    evalR p s h (m' + size w) m' (esum_inr x) (vloc l) (heap_add h (l, w))

| evalR_sum_match_inl : forall (p : program) (s : stack) (h h' : heap) (l : loc)
    (x y z : var) (w w' : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some w ->
    w = vpair vtt w' ->
    evalR p (stack_add s (y, Some w')) h m m' el v h' ->
    evalR p s h m m' (esum_match x (y, el) (z, er)) v h'

| evalR_sum_match_elim_inl : forall (p : program) (s : stack) (h h' : heap)
    (l : loc) (x y z : var) (w w' : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some w ->
    w = vpair vtt w' ->
    evalR p (stack_add s (y, Some w')) (heap_add h (l, vbad)) (m + size w) m' el v h' ->
    evalR p s h m m' (esum_match_elim x (y, el) (z, er)) v h'

| evalR_sum_match_inr : forall (p : program) (s : stack) (h h' : heap) (l : loc)
    (x y z : var) (w w' : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some w ->
    w = vpair vff w' ->
    evalR p (stack_add s (z, Some w')) h m m' er v h' ->
    evalR p s h m m' (esum_match x (y, el) (z, er)) v h'

| evalR_sum_match_elim_inr : forall (p : program) (s : stack) (h h' : heap)
    (l : loc) (x y z : var) (w w' : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some w ->
    w = vpair vff w' ->
    evalR p (stack_add s (z, Some w')) (heap_add h (l, vbad)) (m + size w) m' er v h' ->
    evalR p s h m m' (esum_match_elim x (y, el) (z, er)) v h'

| evalR_list_nil : forall (p : program) (s : stack) (h : heap) (m : nat),
    evalR p s h m m elist_nil vnull h

| evalR_list_cons : forall (p : program) (s : stack) (h : heap) (l : loc)
    (w : val) (xh xt : var) (vh vt : val) (m' : nat),
    s xh = Some vh ->
    s xt = Some vt ->
    w = vpair vh vt ->
    h l = None ->
    evalR p s h (m' + size w) m' (elist_cons xh xt) (vloc l) (heap_add h (l, w))

| evalR_list_match_nil : forall (p : program) (s : stack) (h h' : heap)
    (x xh xt : var) (e1 e2 : expr) (v : val) (m m' : nat),
    s x = Some vnull ->
    evalR p s h m m' e1 v h' ->
    evalR p s h m m' (elist_match x e1 (xh, xt, e2)) v h'

| evalR_list_match_elim_nil : forall (p : program) (s : stack) (h h' : heap)
    (x xh xt : var) (e1 e2 : expr) (v : val) (m m' : nat),
    s x = Some vnull ->
    evalR p s h m m' e1 v h' -> 
    evalR p s h m m' (elist_match x e1 (xh, xt, e2)) v h'

| evalR_list_match_cons : forall (p : program) (s : stack) (h h' : heap)
    (l : loc) (x xh xt : var) (w wh wt : val) (e1 e2 : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some w ->
    w = (vpair wh wt) ->
    evalR p (stack_add (stack_add s (xh, Some wh)) (xt, Some wt)) h m m' e2 v h' ->
    evalR p s h m m' (elist_match x e1 (xh, xt, e2)) v h'

| evalR_list_match_elim_cons : forall (p : program) (s s' : stack) (h h' : heap)
    (l : loc) (x xh xt : var) (w wh wt : val) (e1 e2 : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some w ->
    w = (vpair wh wt) ->
    s' = stack_add (stack_add s (xh, Some wh)) (xt, Some wt) ->
    evalR p s' (heap_add h (l, vbad)) (m + size w) m' e2 v h' ->
    evalR p s h m m' (elist_match x e1 (xh, xt, e2)) v h'
.

(* Lemma 4.18 *)
Lemma additional_memory : forall (p : program) (s : stack) (h h' : heap)
  (m m' : nat) (e : expr) (v : val),
  evalR p s h m m' e v h' ->
  forall (k : nat), evalR p s h (m + k) (m' + k) e v h'.
Proof.
  assert (PLUS : forall a b c, a + b + c = (a + c) + b). { intros. omega. }
  intros p s h h' m m' e v EVAL k.
  induction EVAL; try rewrite PLUS in *; try eauto using evalR.
Qed.


(* Lemma 4.19 *)
Lemma cost_counting_inviolacy : forall (p : program) (s : stack) (h h' : heap)
  (m m' : nat) (e : expr) (v : val),
  evalR p s h m m' e v h' ->
  eval p s h e v h'.
Proof.
  intros p s h h' m m' e v EVAL.
  induction EVAL; subst; try eauto using eval.
Qed.


(* Lemma 4.20 *)
Lemma finite_evaluation_cost : forall (p : program) (s : stack) (h h' : heap)
  (e : expr) (v : val),
  eval p s h e v h' ->
  exists (m m' : nat), evalR p s h m m' e v h'.
Proof.
  assert (plus_n_minus_n : forall a b, a >= b -> a - b + b = a).
  { clear. intros. omega. }
  intros p s h h' e v EVAL.
  induction EVAL; try destruct IHEVAL as [m [m' IHEVAL]]; try eauto using evalR.
  - destruct IHEVAL1 as [m1 [m2 IHEVAL1]].
    destruct IHEVAL2 as [m3 [m4 IHEVAL2]].
    apply additional_memory with (k := m3) in IHEVAL1.
    apply additional_memory with (k := m2) in IHEVAL2.
    rewrite Nat.add_comm in IHEVAL2.
    eauto using evalR_let.
  - (* We must define the size of the heap, and |h| + m is the total amount of
       potention we have *)
    exists m, m'.
    eapply evalR_sum_match_elim_inl; try eassumption.
    rewrite (plus_n_O m').
    eapply additional_memory.
    rewrite plus_n_minus_n; try assumption.
    admit.
  - exists (m - size w), m'.
    eapply evalR_sum_match_elim_inr; try eassumption.
    rewrite plus_n_minus_n; try assumption.
    admit.
  - exists (m - size w), m'.
    eapply evalR_list_match_elim_cons; try eassumption.
    rewrite plus_n_minus_n; try assumption.
    admit.
Admitted.
