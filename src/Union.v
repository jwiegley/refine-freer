Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Lists.List.

Import ListNotations.

Generalizable All Variables.

Inductive UnionF (a : Type) : list (Type -> Type) -> Type :=
  | UThis : forall t r, t a -> UnionF a (t :: r)
  | UThat : forall t r, UnionF a r -> UnionF a (t :: r).

Arguments UThis {a t r} _.
Arguments UThat {a t r} _.

Definition Union (r : list (Type -> Type)) (a : Type) := UnionF a r.

Lemma Union_empty : forall a, Union [] a -> False.
Proof. inversion 1. Qed.

(* A notation for natural transformations. *)
Notation "f ~> g" := (forall x, f x -> g x) (at level 90).

Import EqNotations.

Program Definition decomp `(u : Union (t :: r) v) : t v + Union r v :=
  match u in UnionF _ xs
        return (t :: r)%list = xs -> t v + Union r v with
  | UThis x => fun _ => inl (_ x)
  | UThat x => fun _ => inr x
  end eq_refl.

Definition decomp_rev `(u : Union (r ++ [t]) v) : Union r v + t v.
Proof.
  induction r; simpl in u.
    inversion u; subst.
      exact (inr X).
    inversion X.
  inversion u; subst.
    exact (inl (UThis X)).
  destruct (IHr X).
    exact (inl (UThat u0)).
  exact (inr t0).
Defined.

Program Definition extract `(u : Union [t] v) : t v :=
  match decomp u with | inl x => x | inr x => ! end.
Next Obligation. inversion x. Qed.

Definition weaken {t} `(u : Union r v) : Union (t :: r) v := UThat u.

Fixpoint inject_last  (t : Type -> Type) (r : list (Type -> Type))
         `(x : t a) : Union (r ++ [t]) a :=
  match r with
  | [] => UThis x
  | _ :: xs => UThat (inject_last t xs x)
  end.
