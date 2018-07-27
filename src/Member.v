Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Lists.List.

Require Export
  Freer
  Union.

Import ListNotations.

Generalizable All Variables.

Inductive FindElem (t : Type -> Type) : list (Type -> Type) -> Type :=
  | Here : forall xs, FindElem t (t :: xs)
  | Next : forall t' xs, FindElem t xs -> FindElem t (t' :: xs).

Class Member (t : Type -> Type) (r : list (Type -> Type)) := {
  inj : forall v, t v -> Union r v;
  prj : forall v, Union r v -> option (t v);
  hasElem : FindElem t r
}.

Arguments inj {t r _ v} _.
Arguments prj {t r _ v} _.

Program Instance Member_Here (t : Type -> Type) (r : list (Type -> Type)) :
  Member t (t :: r) | 1 := {
  inj := fun _ x => UThis x;
  prj := fun _ u =>
    match decomp u with
    | inl x => Some x
    | inr _ => None
    end;
  hasElem := Here _ _
}.

Program Instance Member_Next (t t' : Type -> Type) (r : list (Type -> Type)) :
  Member t r -> Member t (t' :: r) | 2 := {
  inj := fun _ x => UThat (inj x);
  prj := fun _ u =>
    match decomp u with
    | inl _ => None
    | inr u => prj u
    end;
  hasElem := Next _ _ _ hasElem
}.

Fixpoint FindElem_last  (t : Type -> Type) (r : list (Type -> Type)) :
  FindElem t (r ++ [t]) :=
  match r with
  | [] => Here _ _
  | _ :: xs => Next _ _ _ (FindElem_last t xs)
  end.

Program Instance Member_Last (t : Type -> Type) (r : list (Type -> Type)) :
  Member t (r ++ [t]) | 2 := {
  inj := fun _ x => inject_last t r x;
  prj := fun _ u =>
    match decomp_rev u with
    | inl _ => None
    | inr x => Some x
    end;
  hasElem := FindElem_last t r
}.

Fixpoint injF `{Member eff r} `(f : Freer eff a) : Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure f k => Impure (inj f) (fun x => injF (k x))
  end.
