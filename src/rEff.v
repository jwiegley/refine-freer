Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Hask.Control.Monad
  Coq.Init.Datatypes.

Require Export
  Member.

Import EqNotations.

Generalizable All Variables.

Polymorphic Inductive rFreer (f : option Type -> Type -> Type) (a: Type): Type :=
| rPure : a -> rFreer f a
| rImpureBranch : forall (x y: Type),
    f (Some y) x -> (x -> rFreer f y) -> (y -> x -> rFreer f a) -> rFreer f a
| rImpureNoBranch : forall (x : Type),
    f None x -> (x -> rFreer f a) -> rFreer f a.

Arguments rPure {f a} _.
Arguments rImpureBranch  {f a x y} _ _ _.
Arguments rImpureNoBranch  {f a x} _ _.

Program Fixpoint rFreer_fmap {r} `(f : a -> b) (t : rFreer r a) : rFreer r b :=
  match t with
  | rPure v => rPure (f v)
  | rImpureBranch eff k' k =>
    let kont := (fun x y => rFreer_fmap f (k x y)) in
    rImpureBranch eff k' kont
  | rImpureNoBranch x k =>
    let kont := (fun x => rFreer_fmap f (k x)) in
    rImpureNoBranch x kont
  end.

Program Instance rFreer_Functor (f : option Type -> Type -> Type) : Functor (rFreer f) := {
  fmap := @rFreer_fmap f
}.

Fixpoint rFreer_ap {r} `(ta : rFreer r (a -> b)) (t : rFreer r a) : rFreer r b :=
  match ta, t with
  | rPure f, rPure v         => rPure (f v)
  | rPure f, rImpureBranch eff t' k  => rImpureBranch eff t' (fun x y => rFreer_fmap f (k x y))
  | rPure f, rImpureNoBranch eff k  => rImpureNoBranch eff  (fun x => rFreer_fmap f (k x))
  | rImpureBranch eff ta' k, m       => rImpureBranch eff ta' (fun x y => rFreer_ap (k x y) m)
  | rImpureNoBranch ta' k, m       => rImpureNoBranch ta' (fun x => rFreer_ap (k x) m)
  end.

Program Instance rFreer_Applicative
        (f : option Type -> Type -> Type) : Applicative (rFreer f) :=
  {
    pure := fun _ => rPure;
    ap := fun _ _ => rFreer_ap
  }.

Polymorphic Fixpoint rFreer_join {f : option Type -> Type -> Type}
            {a}
            (t: rFreer f (rFreer f a))  : rFreer f a :=
  match t with
  | rPure x =>  x
  | rImpureBranch eff k' k => rImpureBranch eff k' (fun x y => rFreer_join (k x y))
  | rImpureNoBranch eff  k => rImpureNoBranch eff (fun x => rFreer_join (k x))
  end.

Program Instance Freer_Monad (f : option Type -> Type -> Type) : Monad (rFreer f) := {
  join := @rFreer_join _
}.
(*
Inductive UnionF (a b: Type)
  : list (Type -> Type -> Type) -> Type :=
| UThis : forall t r, t a b -> UnionF a b (t :: r)
| UThat : forall t r, UnionF a b r -> UnionF a b (t :: r).

Arguments UThis {a b t r} _.
Arguments UThat {a b t r} _.

Definition Union (r : list (Type -> Type -> Type)) (a b: Type) : Type := UnionF a b r.

Polymorphic Definition rEff (effs : list (Type -> option Type -> Type -> Type)) (a: Type) : Type :=
  rFreer (Union effs) a.

Inductive FindElem (t : Type -> Type -> Type) : list (Type -> Type -> Type) -> Type :=
  | Here : forall xs, FindElem t (t :: xs)
  | Next : forall t' xs, FindElem t xs -> FindElem t (t' :: xs).

Class Member (t : Type -> Type -> Type) (r : list (Type -> Type -> Type)) := {
  inj : forall a b, t a b -> Union r a b;
  prj : forall a b, Union r a b -> option (t a b);
  hasElem : FindElem t r
}.

Arguments inj {t r _ a b} _.
Arguments prj {t r _ a b} _.

Program Definition decomp `(u : Union (t :: r) a b) : t a b + Union r a b :=
  match u in UnionF _ _ xs
        return (t :: r)%list = xs -> t a b + Union r a b with
  | UThis x => fun _ => inl (_ x)
  | UThat x => fun _ => inr x
  end eq_refl.

Program Instance Member_Here (t : Type -> Type -> Type) (r : list (Type -> Type -> Type)) :
  Member t (t :: r) | 1 := {
  inj := fun _ x => UThis;
  prj := fun _ _ u =>
    match decomp u with
    | inl x => Some x
    | inr _ => None
    end;
  hasElem := Here _ _
}.

Program Instance Member_Next (t t' : Type -> Type -> Type) (r : list (Type -> Type -> Type)) :
  Member t r -> Member t (t' :: r) | 2 := {
  inj := fun _ _ x => UThat (inj x);
  prj := fun _ _ u =>
    match decomp u with
    | inl _ => None
    | inr u => prj u
    end;
  hasElem := Next _ _ _ hasElem
}.
*)

(*
Definition rEff (effs : list (Type -> Type)) (a: Type) : Type :=
  rFreer (Union effs) a.

Definition send `{Member eff effs} `(t : eff a) : rEff effs a :=
  rImpure (inj t) None rPure. *)

Inductive IVar (a: Type): Type :=
  | ivar: IVar a.

Arguments ivar {_}.

Inductive Par (s : Type) : option Type -> Type -> Type :=
  | new : Par s None (IVar s)
  | get : IVar s -> Par s None s
  | put : IVar s -> s -> Par s None unit
  | fork: Par s (Some (unit : Type)) unit.

Arguments new {_}.
Arguments get {_} _.
Arguments put {_} _ _.
Arguments fork {_}.

Lemma ivar_unit: forall v, IVar v.
Proof.
  constructor.
Qed.

Set Printing All.

Definition put_ex : rFreer (Par nat) nat :=
  rImpureNoBranch new
          (fun i => rImpureBranch fork
                                  (fun u => rImpureNoBranch (put i 3)
                                                   (fun x => rPure tt))
                         (fun u u' => rImpureNoBranch (get i)
                                                      (fun x => rPure (x + 2)))).
