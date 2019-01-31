Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Hask.Control.Monad
  Coq.Init.Datatypes.

Require Export
  Member.

Import EqNotations.

Generalizable All Variables.

Polymorphic Inductive rFreer (f : Type -> Type) (a: Type): Type :=
| rPure : a -> rFreer f a
| rImpure : forall (x: Type), f x -> option (x -> rFreer f a) -> (x -> rFreer f a) -> rFreer f a.

Arguments rPure {f a} _.
Arguments rImpure {f a x} _ _ _.


Program Fixpoint rFreer_fmap {r} `(f : a -> b) (t : rFreer r a) : rFreer r b :=
  match t with
  | rPure v => rPure (f v)
  | rImpure x o k =>
    let kont := (fun x => rFreer_fmap f (k x)) in
                     match o with
                     | Some t' => rImpure x (Some (fun x => rFreer_fmap f (t' x))) kont
                     | None => rImpure x None kont
                     end
  end.

Program Instance rFreer_Functor (f : Type -> Type) : Functor (rFreer f) := {
  fmap := @rFreer_fmap f
}.

(*
Fixpoint rFreer_ap {r} `(ta : rFreer r (a -> b)) (t : rFreer r a) : rFreer r b :=
  match ta, t with
  | rPure f, rPure v         => rPure (f v)
  | rPure f, rImpure u t' k  => rImpure u t' (fun e => rFreer_fmap f (k e))
  | rImpure u ta' k, m       => rImpure u ta' (fun e => rFreer_ap (k e) m)
  end.

Program Instance rFreer_Applicative (f : Type -> Type) : Applicative (rFreer f) := {
  pure := fun _ => rPure;
  ap := fun _ _ => rFreer_ap
}.

Polymorphic Program Fixpoint rFreer_bind {r} `(f : t -> rFreer r u) (i : rFreer r t) : rFreer r u :=
  match i with
  | rPure x => f x
  | rImpure u t' k => rImpure u t' (fun e => rFreer_bind f (k e))
  end.

Polymorphic Fixpoint rFreer_join {r: Type -> Type} {a} (f: rFreer r (rFreer r a))  : rFreer r a :=
  match f with
  | rPure x =>  x
  | rImpure u l k => rImpure u l (fun e => rFreer_join (k e))
  end.

Program Instance Freer_Monad (f :  Type -> Type) : Monad (rFreer f) := {
  join := @rFreer_join _
}.

Inductive UnionF (a b: Type) : list (Type -> Type -> Type) -> Type :=
  | UThis : forall t r, t a b -> UnionF a b (t :: r)
  | UThat : forall t r, UnionF a b r -> UnionF a b (t :: r).

Arguments UThis {a b t r} _.
Arguments UThat {a b t r} _.

Definition Union (r : list (Type -> Type -> Type)) (a b: Type) : Type := UnionF a b r.

Polymorphic Definition rEff (effs : list (Type -> Type -> Type)) (a: Type) : Type :=
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

Definition rEff (effs : list (Type -> Type)) (a: Type) : Type :=
  rFreer (Union effs) a.

Definition send `{Member eff effs} `(t : eff a) : rEff effs a :=
  rImpure (inj t) None rPure.

Inductive IVar (a: Type): Type :=
  | ivar: IVar a.

Arguments ivar {_}.

Inductive Par (s : Type) : Type -> Type :=
  | new : Par s (IVar s)
  | get : IVar s -> Par s s
  | put : IVar s -> s -> Par s unit
  | fork: Par s unit.

Arguments new {_}.
Arguments get {_} _.
Arguments put {_} _ _.
Arguments fork {_}.

Lemma ivar_unit: forall v, IVar v.
Proof.
  constructor.
Qed.

Definition send_get: Par () () :=
  get ivar.

Definition put_ex : rFreer (Par nat) _ :=
  rImpure (new) None
          (fun i => rImpure fork
                         (Some (fun _ => rImpure (put i 3) None
                                              (fun _ => rImpure (get i) None
                                                             (fun x => rPure x))))
                         (fun _ => rImpure (put i 4) None
                                        (fun _ => rImpure (get i) None
                                                       (fun x => rPure x)))).

Program Definition put_ex' : Eff [Par nat] nat :=
    (i <- send new;
     send (put i 3);;
     x <- send (get i);
     pure x).
