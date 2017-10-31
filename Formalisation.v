Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
(* Require Import Coq.FSets.FMaps. *)

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

Definition context := var -> option type0.
Definition context_empty : context := fun _ => None.
Definition context_add (Gamma : context) (p : var * type0) : context :=
  fun x => let (y, t) := p in if Nat.eqb x y then Some t else Gamma x.
Definition context_union (Gamma1 Gamma2 : context) : context :=
  fun x => match Gamma1 x with
  | Some t => Some t
  | None => Gamma2 x
  end.

Definition context_is_disjoint (c c' : context) : Prop := forall x v,
  (c  x = Some v -> c' x = None) /\
  (c' x = Some v -> c  x = None).

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
    has_type prog_sig_empty context_empty eunit tunit

| has_type_bool_true :
    has_type prog_sig_empty context_empty etrue tbool

| has_type_bool_false :
    has_type prog_sig_empty context_empty efalse tbool

| has_type_var : forall x C,
    has_type prog_sig_empty (context_add context_empty (x, C)) (evar x) C

| has_type_let : forall Sigma Gamma1 Gamma2 x e1 e2 A C,
    has_type Sigma Gamma1 e1 A ->
    has_type Sigma (context_add Gamma2 (x, A)) e2 C ->
    has_type Sigma (context_union Gamma1 Gamma2) (elet x e1 e2) C

| has_type_fun : forall Sigma Gamma
    (k : nat) (xs : Vector.t var k) (As : Vector.t type0 k) f C,
    Gamma = Vector.fold_left context_add context_empty (Vector.map2 pair xs As) ->
    Sigma f = Some (tfun As C) ->
    has_type Sigma Gamma (eapp f xs) C

| has_type_if : forall Sigma Gamma x et ef C,
    has_type Sigma Gamma et C ->
    has_type Sigma Gamma ef C ->
    has_type Sigma (context_add Gamma (x, tbool)) (eif x et ef) C

| has_type_pair : forall Sigma x1 x2 A B,
    let Gamma := context_add (context_add context_empty (x1, A)) (x2, B) in
    has_type Sigma Gamma (epair x1 x2) (tpair A B)

| has_type_pair_match : forall Sigma Gamma x x1 x2 e A B C,
    has_type Sigma (context_add (context_add Gamma (x1, A)) (x2, B)) e C ->
    has_type Sigma (context_add Gamma (x, tpair A B)) (epair_match x (x1, x2) e) C

| has_type_sum_inl : forall Sigma x A B,
    has_type Sigma (context_add context_empty (x, A)) (esum_inl x) (tsum A B)

| has_type_sum_inr : forall Sigma x A B,
    has_type Sigma (context_add context_empty (x, B)) (esum_inl x) (tsum A B)

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
    has_type Sigma context_empty elist_nil (tlist A)

| has_type_list_const : forall Sigma xh xt A,
    let Gamma := context_add (context_add context_empty (xh, A)) (xt, tlist A) in
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

Inductive val : Type :=
| vunit : val
| vtt : val
| vff : val
| vpair : val -> val -> val
| vloc : loc -> val
| vnull : val
| vbad : val.

(* Definition 4.6 *)
Definition stack := var -> option val.
Definition heap := loc -> option val.

Definition stack_empty : stack := fun _ => None.
Definition heap_empty : heap := fun _ => None.

Definition stack_add (s : stack) (p : var * option val) :=
  fun y => match p with
  | (_, None) => s y
  | (x, Some v) => if Nat.eqb x y then Some v else s y
  end.

Definition heap_add (h : heap) (p : loc * val) :=
  fun y => let (x, v) := p in if Nat.eqb x y then Some v else h y.

Definition heap_remove (h : heap) (l : loc) :=
  fun y => if Nat.eqb l y then None else h y.


Inductive eval : program -> stack -> heap -> expr -> val -> heap -> Prop :=
| eval_unit :  forall p s h,
    eval p s h eunit vunit h

| eval_true :  forall p s h,
    eval p s h etrue vtt h

| eval_false : forall p s h,
    eval p s h efalse vff h

| eval_var : forall p s h x v,
    s x = Some v ->
    eval p s h (evar x) v h

| eval_let : forall p s h h0 h' x v0 v e1 e2,
    eval p s h e1 v0 h0 -> eval p (stack_add s (x, Some v0)) h0 e2 v h' ->
    eval p s h (elet x e1 e2) v h'

| eval_fun : forall (p : program) (s : stack) (h h' : heap) (f : var)
    (ys : list var) (ef : expr) (xs : Vector.t var (List.length ys)) (v : val),
    p f = (ys, ef) ->
    let vs := Vector.map s xs in
    let yvs := Vector.map2 pair (Vector.of_list ys) vs in
    let s' := Vector.fold_left stack_add stack_empty yvs in
    eval p s' h ef v h' ->
    eval p s h (eapp f xs) v h'

| eval_if_true : forall p s h h' x et ef v,
    s x = Some vtt ->
    eval p s h et v h' ->
    eval p s h (eif x et ef) v h'

| eval_if_false : forall p s h h' x et ef v,
    s x = Some vff ->
    eval p s h ef v h' ->
    eval p s h (eif x et ef) v h'

| eval_pair : forall p s h x1 x2 v1 v2,
    s x1 = Some v1 ->
    s x2 = Some v2 ->
    eval p s h (epair x1 x2) (vpair v1 v2) h

| eval_pair_match : forall p s h h' x x1 x2 v1 v2 e v,
    s x = Some (vpair v1 v2) ->
    let s' := stack_add (stack_add s (x1, Some v1)) (x2, Some v2) in
    eval p s' h e v h' ->
    eval p s h (epair_match x  (x1, x2) e) v  h'

| eval_sum_inl : forall p s h x w l v,
    s x = Some v ->
    w = vpair vtt v ->
    h l = None ->
    eval p s h (esum_inl x) (vloc l) (heap_add h (l, w))

| eval_sum_inr : forall p s h x w l v,
    s x = Some v ->
    w = vpair vff v ->
    h l = None ->
    eval p s h (esum_inr x) (vloc l) (heap_add h (l, w))

| eval_sum_match_inl : forall p s h h' l x y z w el er v,
    s x = Some (vloc l) ->
    h l = Some (vpair vtt w) ->
    eval p (stack_add s (y, Some w)) h el v h' ->
    eval p s h (esum_match x (y, el) (z, er)) v h'

| eval_sum_match_elim_inl : forall p s h h' l x y z w el er v,
    s x = Some (vloc l) ->
    h l = Some (vpair vtt w) ->
    eval p (stack_add s (y, Some w)) (heap_add h (l, vbad)) el v h' ->
    eval p s h (esum_match_elim x (y, el) (z, er)) v h'

| eval_sum_match_inr : forall p s h h' l x y z w el er v,
    s x = Some (vloc l) ->
    h l = Some (vpair vff w) ->
    eval p (stack_add s (z, Some w)) h er v h' ->
    eval p s h (esum_match x (y, el) (z, er)) v h'

| eval_sum_match_elim_inr : forall p s h h' l x y z w el er v,
    s x = Some (vloc l) ->
    h l = Some (vpair vff w) ->
    eval p (stack_add s (z, Some w)) (heap_add h (l, vbad)) er v h' ->
    eval p s h (esum_match_elim x (y, el) (z, er)) v h'

| eval_list_nil : forall p s h,
    eval p s h elist_nil vnull h

| eval_list_cons : forall p s h l w xh xt vh vt,
    s xh = Some vh ->
    s xt = Some vt ->
    w = vpair vh vt ->
    h l = None ->
    eval p s h (elist_cons xh xt) (vloc l) (heap_add h (l, w))

| eval_list_match_nil : forall p s h h' x xh xt e1 e2 v,
    s x = Some vnull ->
    eval p s h e1 v h' ->
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'

| eval_list_match_elim_nil : forall p s h h' x xh xt e1 e2 v,
    s x = Some vnull ->
    eval p s h e1 v h' -> 
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'

| eval_list_match_cons : forall p s h h' l x xh xt wh wt e1 e2 v,
    s x = Some (vloc l) ->
    h l = Some (vpair wh wt) ->
    eval p (stack_add (stack_add s (xh, Some wh)) (xt, Some wt)) h e2 v h' ->
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'

| eval_list_match_elim_cons : forall p s h h' l x xh xt wh wt e1 e2 v,
    s x = Some (vloc l) ->
    h l = Some (vpair wh wt) ->
    let s' := stack_add (stack_add s (xh, Some wh)) (xt, Some wt) in
    eval p s' (heap_add h (l, vbad)) e2 v h' ->
    eval p s h (elist_match x e1 (xh, xt, e2)) v h'
.

Definition heap_is_subset (h h' : heap) : Prop :=
  forall x v, h x = Some v -> h' x = Some v.

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
  heap_add h (l, x) l = Some x.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma new_heap_lookup_diff : forall (h : heap) (l l' : loc) (x x' : val),
   Nat.eqb l' l = false -> h l = Some x -> heap_add h (l', x') l = Some x.
Proof.
  intros h l' l x x' H1 H2.
  simpl. rewrite H1. assumption.
Qed.

Lemma new_heap_lookup : forall (h h' : heap) (l : loc) (x : val),
  h l = heap_add h' (l, x) l -> h l = Some x.
Proof.
  intros. rewrite heap_add_lookup_refl in *. assumption.
Qed.

Lemma new_heap_lookup2 : forall h h' l l' x,
  Nat.eqb l' l = false -> h l = heap_add h' (l', x) l -> h l = h' l.
Proof.
  intros h h' l l' x H1 H2.
  rewrite H2.
  simpl.
(*   rewrite Nat.eqb_sym. *)
  rewrite H1.
  reflexivity.
Qed.

(* Lemma 4.8 *)
Lemma heap_stability : forall p s h e v h',
  eval p s h e v h' ->
  forall l x,
  h l = Some x ->
  h' l = h l \/ h' l = Some vbad.
Proof.
  intros p s h e v h' H1. induction H1; try assumption; try (left; reflexivity).
  - (* eval_let *)
    intros l x' H2. destruct (IHeval1 _ _ H2) as [H3 | H3].
    + rewrite <- H3 in *. eauto.
    + destruct (IHeval2 _ _ H3) as [H4 | H4]; rewrite <- H4 in *; eauto.
  - (* eval_sum_inl *)
    intros l' x' H2. left. simpl. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb. congruence.
    + reflexivity.
  - (* eval_sum_inr *)
    intros l' x' H2. left. simpl. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb. congruence.
    + reflexivity.
  - (* eval_sum_match_inl *)
    intros l' x' H2. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb; subst.
      destruct (IHeval _ _ (heap_add_lookup_refl h l' vbad));
        eauto using new_heap_lookup.
    + destruct (IHeval _ _ (new_heap_lookup_diff h l' l x' vbad Heqb H2));
        eauto using new_heap_lookup2.
  - (* eval_sum_match_inr *)
    intros l' x' H2. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb; subst.
      destruct (IHeval _ _ (heap_add_lookup_refl h l' vbad));
        eauto using new_heap_lookup.
    + destruct (IHeval _ _ (new_heap_lookup_diff h l' l x' vbad Heqb H2));
        eauto using new_heap_lookup2.
  - (* eval_list_cons *)
    intros l' x' H3. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb. congruence.
    + simpl. rewrite Heqb. auto.
  - (* eval_list_match_cons *)
    intros l' x' H3. destruct (Nat.eqb l l') eqn:Heqb.
    + rewrite Nat.eqb_eq in Heqb; subst.
      destruct (IHeval _ _ (heap_add_lookup_refl h l' vbad));
        eauto using new_heap_lookup.
    + destruct (IHeval _ _ (new_heap_lookup_diff h l' l x' vbad Heqb H3));
        eauto using new_heap_lookup2.
Qed.

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

Lemma Some_implies_not_None : forall {A : Set} (o : option A) (x : A),
  o = Some x -> o <> None.
Proof. congruence. Qed.

Lemma not_None_implies_Some : forall {A : Set} (o : option A),
  o <> None -> exists (x : A), o = Some x.
Proof.
  intros A o H.
  destruct o.
  - exists a. reflexivity.
  - congruence.
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
  forall x t, Gamma x = Some t -> exists v, s x = Some v /\ mem_consistant h v t.

Definition context_is_subset (c c' : context) : Prop :=
  forall x v, c x = Some v -> c' x = Some v.

Definition stack_is_subset (s s' : stack) : Prop :=
  forall x v, s x = Some v -> s' x = Some v.

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

Definition context_join (c c' : context) : context := fun x =>
  match c x with
  | None => c' x
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
  destruct (Gamma x) eqn:GammaX.
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
Lemma deallocation_consistency' :
  forall (h : heap) (s : stack) (Gamma : context),
  mem_consistant_stack h s Gamma ->
  forall (l : loc) (x : val),
  h l = Some x ->
  mem_consistant_stack (heap_add h (l, vbad)) s Gamma.
Proof.
  intros h s Gamma MEM_CONS l x.
  eauto using deallocation_consistency.
Qed.

(* Lemma 4.13 *)
Lemma preservation : forall (Sigma : prog_sig) (Gamma : context) (p : program)
  (s : stack) (h h' : heap) (e : expr) (c : type0) (v : val),
  (* 4.1 *) has_type Sigma Gamma e c ->
  (* 4.2 *) eval p s h e v h' ->
  (* 4.3 *) mem_consistant_stack h s Gamma ->
  (* 4.a *) mem_consistant h' v c /\ (* 4.b *) mem_consistant_stack h' s Gamma.
Proof.
  intros Sigma Gamma p s h h' e c v WELL_TYPED EVAL. split.
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
      (* Here, the instanciation with x0:=x and t:=C leads to a trivial
         hypothesis Some C = Some C.
         Is there a way to get rid of this hypothesis without the following
         assertion? *)
      assert (H : context_add context_empty (x, C) x = Some C).
      { simpl. rewrite Nat.eqb_refl. reflexivity. }
      apply MEM_CONS in H as [v' [H1 H2]]. congruence.
    + (* let x = e1 in e2 *)
      assert (H1 : heap_is_subset h h). { unfold heap_is_subset. trivial. }
      assert (H2 : stack_is_subset s s). { unfold stack_is_subset. trivial. }
      assert (H3 : context_is_subset Gamma1 (context_union Gamma1 Gamma2)).
      { unfold context_is_subset, context_union. intros. rewrite H. reflexivity. }
      assert (MEM_CONS_Gamma1 := mem_consistancy_closure _ _ _ _ _ _ H1 H2 H3 MEM_CONS).
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
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

*)
  - assert (H2 := heap_stability _ _ _ _ _ _ EVAL).
    assert (H3 := deallocation_consistency' _ _ _ H).
    unfold mem_consistant_stack in *.
    intros x t H4.
    apply H in H4.
    destruct H4 as [v' [H4 H5]].
    exists v'.
    split.
    + assumption.
    + admit.
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
    (x y z : var) (w : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some (vpair vtt w) ->
    evalR p (stack_add s (y, Some w)) h m m' el v h' ->
    evalR p s h m m' (esum_match x (y, el) (z, er)) v h'

| evalR_sum_match_elim_inl : forall (p : program) (s : stack) (h h' : heap)
    (l : loc) (x y z : var) (w : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some (vpair vtt w) ->
    evalR p (stack_add s (y, Some w)) (heap_add h (l, vbad)) (m + size w) m' el v h' ->
    evalR p s h m m' (esum_match_elim x (y, el) (z, er)) v h'

| evalR_sum_match_inr : forall (p : program) (s : stack) (h h' : heap) (l : loc)
    (x y z : var) (w : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some (vpair vff w) ->
    evalR p (stack_add s (z, Some w)) h m m' er v h' ->
    evalR p s h m m' (esum_match x (y, el) (z, er)) v h'

| evalR_sum_match_elim_inr : forall (p : program) (s : stack) (h h' : heap)
    (l : loc) (x y z : var) (w : val) (el er : expr) (v : val) (m m' : nat),
    s x = Some (vloc l) ->
    h l = Some (vpair vff w) ->
    evalR p (stack_add s (z, Some w)) (heap_add h (l, vbad)) (m + size w) m' er v h' ->
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
