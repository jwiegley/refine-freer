Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Hask.Control.Monad
  Coq.Init.Datatypes.

Import EqNotations.

Generalizable All Variables.
Set Printing Universes.

Polymorphic Inductive rFreer (f : Type -> Type -> Type) (a: Type): Type :=
| rPure : a -> rFreer f a
| rImpure : forall (x: Type) (b: Type), f b x -> rFreer f b -> (b -> x -> rFreer f a) -> rFreer f a.

Arguments rPure {f a} _.
Arguments rImpure {f a x b} _ _ _.

Program Fixpoint rFreer_fmap {r} `(f : a -> b) (t : rFreer r a) : rFreer r b :=
  match t with
  | rPure v => rPure (f v)
  | rImpure u t' k => rImpure u t' (fun b x => rFreer_fmap f (k b x))
  end.

Program Instance rFreer_Functor (f : Type -> Type -> Type) : Functor (rFreer f) := {
  fmap := @rFreer_fmap f
}.

Fixpoint rFreer_ap {r} `(ta : rFreer r (a -> b)) (t : rFreer r a) : rFreer r b :=
  match ta, t with
  | rPure f, rPure v       => rPure (f v)
  | rPure f, rImpure u t' k => rImpure u t' (fun b x => rFreer_fmap f (k b x))
  | rImpure u ta' k, m       => rImpure u ta' (fun b x => rFreer_ap (k b x) m)
  end.

Program Instance rFreer_Applicative (f : Type -> Type -> Type) : Applicative (rFreer f) := {
  pure := fun _ => rPure;
  ap := fun _ _ => rFreer_ap
}.

Polymorphic Program Fixpoint rFreer_bind {r} `(f : t -> rFreer r u) (i : rFreer r t) : rFreer r u :=
  match i with
  | rPure x => f x
  | rImpure u t' k => rImpure u t' (fun b x => rFreer_bind f (k b x))
  end.

Polymorphic Fixpoint rFreer_join {r: Type -> Type -> Type} {a} (f: rFreer r (rFreer r a))  : rFreer r a :=
  match f with
  | rPure x =>  x
  | rImpure u l k => rImpure u l (fun b' x => rFreer_join (k b' x))
  end.

Program Instance Freer_Monad (f : Type -> Type -> Type) : Monad (rFreer f) := {
  join := @rFreer_join _
}.
