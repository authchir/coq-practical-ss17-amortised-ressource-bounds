Require Import LF.
Require Import Map.

Inductive type0 : Type :=
| tunit : type0
| tbool : type0
| tpair : type0 -> type0 -> type0
| tsum  : type0 * nat -> type0 * nat -> type0
| tlist : type0 -> nat -> type0.

Inductive type1 : Type :=
| tfun : nat -> nat -> list type0 -> type0 -> type1.

Module VarEq <: EQ_TYPE.

  Definition t := nat.

  Definition eq := Nat.eqb.

  Theorem eq_refl : forall x,
    true = eq x x.
  Proof.
    intros. unfold eq. Search (Nat.eqb _ _).
    apply beq_nat_refl.
  Qed.

End NatEq.

Module NatMap := Make(NatEq).

(* Definition context := var -> option type0. *)
Definition context := NatMap.t type0.

Print context.
Definition context_empty : context := fun _ => None.
Definition context_add (Gamma : context) (p : var * type0) : context :=
  fun x => let (y, t) := p in if Nat.eqb x y then Some t else Gamma x.
Definition context_union (Gamma1 Gamma2 : context) : context :=
  fun x => match Gamma1 x with
  | Some t => Some t
  | None => Gamma2 x
  end.


(* Definition 5.1 *)
Fixpoint erase0 (t : type0) : LF.type0 :=
  match t with
  | tunit => LF.tunit
  | tbool => LF.tbool
  | tpair t1 t2 => LF.tpair (erase0 t1) (erase0 t2)
  | tsum (t1, _) (t2, _) => LF.tsum (erase0 t1) (erase0 t2)
  | tlist t1 _ => LF.tlist (erase0 t1)
  end.

Fixpoint erase1 (t : type1) : LF.type1 :=
  let (_, _, t1s, t2) := t in
  LF.tfun (Vector.of_list (List.map erase0 t1s)) (erase0 t2).