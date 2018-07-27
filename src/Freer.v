Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Hask.Control.Monad.

Generalizable All Variables.

Inductive Fix (f : Type -> Type) : Type :=
  | mkFix : forall x, f x -> (x -> Fix f) -> Fix f.

Arguments mkFix {f x} _ _.

Definition Freer' (f : Type -> Type) (a : Type) : Type :=
  Fix (fun t => a + f t)%type.

Inductive Freer (f : Type -> Type) (a : Type) : Type :=
  | Pure : a -> Freer f a
  | Impure : forall x, f x -> (x -> Freer f a) -> Freer f a.

Arguments Pure {f a} _.
Arguments Impure {f a x} _ _.

Fixpoint toFreer `(x : Freer' f a) : Freer f a :=
  match x with
  | mkFix (inl a) _ => Pure a
  | mkFix (inr u) k => Impure u (toFreer ∘ k)
  end.

Fixpoint fromFreer `(x : Freer f a) : Freer' f a :=
  match x with
  | Pure a     => mkFix (x:=False) (inl a) (False_rect _)
  | Impure u k => mkFix (inr u) (fromFreer ∘ k)
  end.

Theorem fromFreer_toFreer `(x : Freer' f a) : fromFreer (toFreer x) = x.
Proof.
  induction x; simpl in *.
  destruct f0; simpl.
    (* [Freer] is "bigger" than [Freer'], since it contains information about
       the existential type (and a mapping from it) even in the terminating
       case. *)
    assert (x = False) by admit.
    subst.
    f_equal.
    extensionality z.
    contradiction.
  f_equal.
  unfold compose.
  extensionality z.
  apply H.
Admitted.

Theorem toFreer_fromFreer `(x : Freer f a) : toFreer (fromFreer x) = x.
Proof.
  induction x; simpl in *; auto.
  f_equal.
  unfold compose.
  extensionality z.
  apply H.
Qed.

Fixpoint Freer_map {r} `(f : a -> b) (x : Freer r a) : Freer r b :=
  match x with
  | Pure v => Pure (f v)
  | Impure u k => Impure u (fun x => Freer_map f (k x))
  end.

Program Instance Freer_Functor (f : Type -> Type) : Functor (Freer f) := {
  fmap := @Freer_map _
}.

Fixpoint Freer_ap {r} `(f : Freer r (a -> b)) (x : Freer r a) : Freer r b :=
  match f, x with
  | Pure f, Pure v     => Pure (f v)
  | Pure f, Impure u k => Impure u (fun x => Freer_map f (k x))
  | Impure u k, m      => Impure u (fun x => Freer_ap (k x) m)
  end.

Program Instance Freer_Applicative (f : Type -> Type) : Applicative (Freer f) := {
  pure := fun _ => Pure;
  ap := fun _ _ => Freer_ap
}.

Fixpoint Freer_join {r} `(f : Freer r (Freer r a)) : Freer r a :=
  match f with
  | Pure v     => v
  | Impure u k => Impure u (fun x => Freer_join (k x))
  end.

Program Instance Freer_Monad (f : Type -> Type) : Monad (Freer f) := {
  join := @Freer_join _
}.

Module FreerLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Program Instance Freer_FunctorLaws (f : Type -> Type) : FunctorLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold id.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold comp.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.

Program Instance Freer_ApplicativeLaws (f : Type -> Type) : ApplicativeLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  specialize (H y).
  destruct (f1 y); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction u, v, w; simpl; auto;
  f_equal;
  extensionality y; simpl;
  try (specialize (H y);
       destruct (f1 y); auto).
  - induction (f1 y); auto.
    f_equal.
    extensionality z; simpl.
    specialize (H z).
    destruct (f3 z); auto.
  - induction (f1 y); auto.
    f_equal.
    extensionality z; simpl.
    specialize (H z).
    destruct (f3 z); auto.
  - induction (f1 y); auto.
      f_equal.
      extensionality z; simpl.
      induction (f3 z); auto.
      f_equal.
      extensionality w; simpl.
      specialize (H w).
      destruct (f5 w); auto.
    f_equal.
    extensionality z; simpl.
    specialize (H z).
    destruct (f5 z); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction u; auto.
  f_equal.
  extensionality x0.
  specialize (H x0).
  destruct (f1 x0); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  extensionality x0.
  destruct x0; auto.
Qed.

Program Instance Freer_MonadLaws (f : Type -> Type) : MonadLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.

End FreerLaws.

Fixpoint iter `{Functor f} `(phi : f a -> a) (fr : Freer f a) : a :=
  match fr with
    | Pure x => x
    | Impure h g => phi (fmap (iter phi \o g) h)
  end.

Definition liftF {f : Type -> Type} {a : Type} : f a -> Freer f a :=
  fun x => Impure x Pure.

Definition uniter `{Functor f} `(psi : Freer f a -> a) : f a -> a :=
  psi \o liftF.

Fixpoint retract `{Monad f} `(fr : Freer f a) : f a :=
  match fr with
    | Pure x => pure x
    | Impure h g => h >>= (retract \o g)
  end.

Fixpoint hoistFree `(n : forall a, f a -> g a) `(fr : Freer f b) : Freer g b :=
  match fr with
  | Pure x => Pure x
  | Impure h g => Impure (n _ h) (hoistFree n \o g)
  end.

Fixpoint foldFree `{Monad m} `(n : forall x, f x -> m x) `(fr : Freer f a) :
  m a :=
  match fr with
  | Pure x => pure x
  | Impure h g => join (fmap (foldFree n \o g) (n _ h))
  end.

Fixpoint cutoff (n : nat) `(fr : Freer f a) : Freer f (option a) :=
  match n with
  | O => Pure None
  | S n' =>
    match fr with
    | Pure x => Pure (Some x)
    | Impure h g => Impure h (cutoff n \o g)
    end
  end.
