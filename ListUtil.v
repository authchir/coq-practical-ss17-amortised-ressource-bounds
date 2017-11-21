Require Import Coq.Lists.List.

Import ListNotations.

Theorem Forall_app : forall (A : Type) (P : A -> Prop) (xs ys : list A),
  Forall P xs ->
  Forall P ys ->
  Forall P (xs ++ ys).
Proof.
  intros A P xs ys H1.
  generalize dependent ys.
  induction H1; intros ys H2.
  - assumption.
  - simpl.
    auto using Forall_cons.
Qed.

Inductive Zip {A B : Type} : list A -> list B -> list (A * B) -> Prop :=
| Zip_nil : Zip [] [] []
| Zip_cons : forall x y xs ys zs,
    Zip xs ys zs -> Zip (x :: xs) (y :: ys) ((x, y) :: zs).

Theorem Zip_app : forall (A B : Type) (xs1 xs2 : list A) (ys1 ys2 : list B)
  (zs1 zs2 : list (A * B)),
  Zip xs1 ys1 zs1 ->
  Zip xs2 ys2 zs2 ->
  Zip (xs1 ++ xs2) (ys1 ++ ys2) (zs1 ++ zs2).
Proof.
  intros A B xs1 xs2 ys1 ys2 zs1 zs2 HZip1.
  generalize dependent zs2.
  generalize dependent ys2.
  generalize dependent xs2.
  induction HZip1; intros xs2 ys2 zs2 HZip2; simpl; auto using Zip_cons.
Qed.