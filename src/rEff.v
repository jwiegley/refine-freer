Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Hask.Control.Monad
  Coq.Init.Datatypes.

Require Import ExtLib.Data.HList.

Import EqNotations.

Generalizable All Variables.
Set Printing Universes.

Inductive rFreer (f : ((list Type): Type) -> Type -> Type) (a : Type) : Type :=
| rPure : a -> rFreer f a
| rImpure : forall (x: Type) (ts: (list Type): Type), f ts x -> (hlist (rFreer f) ts) -> (x -> rFreer f a) -> rFreer f a.

Arguments rPure {f a} _.
Arguments rImpure {f a x ts} _ _ _.

Program Fixpoint rFreer_fmap {r} `(f : a -> b) (x : rFreer r a) : rFreer r b :=
  match x with
  | rPure v => rPure (f v)
  | rImpure u l k => rImpure u l (fun x => rFreer_fmap f (k x))
  end.

Program Instance rFreer_Functor (f : list Type -> Type -> Type) : Functor (rFreer f) := {
  fmap := @rFreer_fmap f
}.

Fixpoint rFreer_ap {r} `(f : rFreer r (a -> b)) (x : rFreer r a) : rFreer r b :=
  match f, x with
  | rPure f, rPure v       => rPure (f v)
  | rPure f, rImpure u l k => rImpure u l (fun x' => rFreer_fmap f (k x'))
  | rImpure u l k, m       => rImpure u l (fun x' => rFreer_ap (k x') m)
  end.

Program Instance rFreer_Applicative (f : list Type -> Type -> Type) : Applicative (rFreer f) := {
  pure := fun _ => rPure;
  ap := fun _ _ => rFreer_ap
}.

Polymorphic Fixpoint rFreer_join {r: list Type -> Type -> Type} {a} (f : rFreer r (rFreer r a)) : rFreer r a :=
  match f with
  | Pure v     => v
  | Impure u l k => Impure u l (fun x => rFreer_join (k x))
  end.

Program Instance Freer_Monad (f : Type -> Type) : Monad (Freer f) := {
  join := @Freer_join _
}.