Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Hask.Control.Monad.

Require Import ExtLib.Data.HList.

Generalizable All Variables.

Inductive rFreer (f : list Type -> Type -> Type) (a : Type) : Type :=
| rPure : a -> rFreer f a
| rImpure : forall x ts, f ts x -> (hlist (fun _ => rFreer f a) ts) -> (x -> rFreer f a) -> rFreer f a.

Arguments rPure {f a} _.
Arguments rImpure {f a x ts} _ _ _.

Fixpoint rFreer_map {r} `(f : a -> b) (x : rFreer r a) : rFreer r b :=
  match x with
  | rPure v => rPure (f v)
  | rImpure u l k => rImpure u (hlist_map (fun _ => rFreer_map f) l) (fun x => rFreer_map f (k x))
  end.

Program Instance rFreer_Functor (f : list Type -> Type -> Type) : Functor (rFreer f) := {
  fmap := @rFreer_map _
}.

