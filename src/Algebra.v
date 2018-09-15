(** An example of using Coq to work through the algebraic homomorphisms
    of a denotation. *)

Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Open Scope nat_scope.

Generalizable All Variables.

Notation "f ≈ g" := (equiv f g) (at level 79).

(** Specification of a stream *)

Definition StreamS (a : Type) := nat -> a.

Program Instance Function_Setoid `{Setoid b} : Setoid (a -> b) := {
  equiv := fun f g => forall i, f i ≈ g i
}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now (transitivity (y i)).
Qed.

(** An algebra of streams *)

Definition cons `(x : a) (s : StreamS a) : StreamS a :=
  fun i => if i =? 0 then x else s (pred i).

Definition uncons `(s : StreamS a) : a * StreamS a :=
  (s 0, fun i => s (succ i)).

Definition zip `(s : StreamS a) `(t : StreamS b) : StreamS (a * b) :=
  fun i => (s i, t i).

Definition replicate `(x : a) : StreamS a := fun _ => x.

(* etc... *)

(** Streams, by their shape also express many other algebras:

    Functor
    Representable Functor
    Applicative
    Monad
    Monoid, if a is a Monoid
    etc.
*)

(** We want to denote some object that represents streams, but what is
    sufficient to capture our use of them? *)

Program Definition denote' {a} (d : _ a) : StreamS a :=
  fun i => _.
Admit Obligations.

(** If the type of the specification alone is not enough of a guide,
    we can try out a data type as an idea. *)

CoInductive Stream (a : Type) := Cons : a -> Stream a -> Stream a.

Arguments Cons {a} _ _.

CoInductive stream_equiv `{Setoid a} : Stream a -> Stream a -> Prop :=
  | Stream_equiv : forall h h' t1 t2,
      stream_equiv t1 t2
        -> h ≈ h'
        -> stream_equiv (Cons h t1) (Cons h' t2).

Definition frob `(s : Stream a) : Stream a :=
  match s with Cons h t => Cons h t end.

Theorem frob_eq : forall `(s : Stream a), s = frob s.
  destruct s; reflexivity.
Qed.

Definition hd `(s : Stream a) : a :=
  match s with Cons x _ => x end.

Definition tl `(s : Stream a) : Stream a :=
  match s with Cons _ xs => xs end.

Theorem stream_equiv_coind `{Setoid a} `(R : Stream a -> Stream a -> Prop) :
  (forall s1 s2, R s1 s2 -> hd s1 ≈ hd s2) ->
  (forall s1 s2, R s1 s2 -> R (tl s1) (tl s2)) ->
  forall s1 s2, R s1 s2 -> stream_equiv s1 s2.
Proof.
  intros Cons_case_hd Cons_case_tl.
  cofix; destruct s1; destruct s2; intro.
  generalize (Cons_case_hd _ _ H0); intros.
  simpl in H1.
  constructor; auto.
  apply stream_equiv_coind.
  apply (Cons_case_tl _ _ H0).
Qed.

Program Instance stream_equiv_Equivalence `{Setoid a} :
  Equivalence (@stream_equiv a _).
Next Obligation.
  repeat intro.
  apply stream_equiv_coind with (R:=fun s1 s2 => s1 = s2); intros; subst; auto.
  reflexivity.
Qed.
Next Obligation.
  repeat intro.
  eapply stream_equiv_coind
    with (R := fun s1 s2 => stream_equiv s2 s1); eauto; clear;
    intros s1 s2 H0.
  destruct H0; simpl; symmetry; eassumption.
  destruct H0; simpl; eassumption.
Qed.
Next Obligation.
  repeat intro.
  eapply stream_equiv_coind
    with (R := fun s1 s2 => exists s3, stream_equiv s1 s3 /\ stream_equiv s3 s2);
    eauto; clear; intros ? ? [s3 [H0 H1] ].
  - destruct H0; inversion H1; subst; simpl; etransitivity; eauto.
  - destruct H0; inversion H1; subst; simpl; eexists; eauto.
Qed.

Instance Stream_Setoid `{Setoid a} : Setoid (Stream a) := {
  equiv := stream_equiv;
  setoid_equiv := stream_equiv_Equivalence
}.

Program Instance Cons_Proper `{Setoid a} : Proper (equiv ==> equiv ==> equiv) Cons.
Next Obligation.
  repeat intro.
  cofix.
  simpl.
  now constructor.
Qed.

(* Program Fixpoint denote `(d : Stream a) : StreamS a *)
Fixpoint denote `(d : Stream a) (i : nat) : a :=
  match i, d with
  | O,    Cons x _  => x
  | S i', Cons _ xs => denote xs i'
  end.

(** Now we may show that this denotation is an algebra homomorphism
    for all algebras of interest. *)

Require Import FunctionalExtensionality.

Theorem denote_cons :
  forall a (x : a) s, denote (Cons x s) = cons x (denote s).
Proof.
  intros.
  extensionality i.
  now induction i.
Qed.

Theorem denote_uncons :
  forall a (x : a) s, (x, denote s) = uncons (denote (Cons x s)).
Proof.
  intros.
  unfold uncons; simpl.
  f_equal.
Qed.

Reserved Infix "⨂" (at level 12, right associativity).

Class Monoid (a : Type) `{Setoid a} := {
  mempty : a;
  mappend : a -> a -> a where "x ⨂ y" := (mappend x y);
  mempty_left : forall x, mempty ⨂ x ≈ x;
  mempty_right : forall x, x ⨂ mempty ≈ x;
  mappend_assoc : forall x y z, x ⨂ (y ⨂ z) ≈ (x ⨂ y) ⨂ z
}.

Infix "⨂" := mappend (at level 12, right associativity).

Program Instance Function_Monoid {a b} `{Monoid b} : Monoid (a -> b) := {
  mempty  := fun _ => mempty;
  mappend := fun x y a => x a ⨂ y a;
}.
Next Obligation. now rewrite mempty_left. Qed.
Next Obligation. now rewrite mempty_right. Qed.
Next Obligation. now rewrite mappend_assoc. Qed.

CoFixpoint empty_stream `{Monoid a} : Stream a := Cons mempty empty_stream.

CoFixpoint append_streams `{Monoid a} (x y : Stream a) : Stream a :=
  match x, y with
  | Cons x' xs, Cons y' ys => Cons (x' ⨂ y') (append_streams xs ys)
  end.

Lemma append_streams_empty_Cons `{Monoid a} (x : a) xs :
  append_streams empty_stream (Cons x xs) ≈ Cons x (append_streams empty_stream xs).
Proof.
  simpl.
  cofix.
  rewrite (frob_eq (append_streams _ _)).
  rewrite (frob_eq (Cons _ (append_streams _ _))).
  simpl.
  constructor.
    reflexivity.
  apply mempty_left.
Qed.

Lemma append_streams_mempty_left `{Monoid a} x:
  append_streams empty_stream x ≈ Cons (hd x) (append_streams empty_stream (tl x)).
Proof.
  simpl.
  destruct x.
  simpl.
  apply append_streams_empty_Cons.
Qed.

Lemma append_streams_Cons_empty `{Monoid a} (x : a) xs :
  append_streams (Cons x xs) empty_stream ≈ Cons x (append_streams xs empty_stream).
Proof.
  simpl.
  cofix.
  rewrite (frob_eq (append_streams _ _)).
  rewrite (frob_eq (Cons _ (append_streams _ _))).
  simpl.
  constructor.
    reflexivity.
  apply mempty_right.
Qed.

Lemma append_streams_mempty_right `{Monoid a} x:
  append_streams x empty_stream ≈ Cons (hd x) (append_streams (tl x) empty_stream).
Proof.
  simpl.
  destruct x.
  simpl.
  apply append_streams_Cons_empty.
Qed.

Program Instance Stream_Monoid `{Monoid a} : Monoid (Stream a) := {
  mempty  := empty_stream;
  mappend := append_streams
}.
Next Obligation.
  remember (append_streams _ _).
  eapply stream_equiv_coind
    with (R := fun s1 s2 => stream_equiv s1 (append_streams empty_stream s2)); eauto.
  - intros; simpl; inversion H1; subst; simpl.
    pose proof (append_streams_mempty_left s2).
    rewrite <- H2 in H4.
    simpl in H4.
    inversion H4; subst.
    etransitivity; eauto.
  - intros; simpl; inversion H1; subst; simpl.
    pose proof (append_streams_mempty_left s2).
    rewrite <- H2 in H4.
    simpl in H4.
    inversion H4; subst.
    etransitivity; eauto.
  - rewrite Heqs; reflexivity.
Qed.
Next Obligation.
  remember (append_streams _ _).
  eapply stream_equiv_coind
    with (R := fun s1 s2 => stream_equiv s1 (append_streams s2 empty_stream)); eauto.
  - intros; simpl; inversion H1; subst; simpl.
    pose proof (append_streams_mempty_right s2).
    rewrite <- H2 in H4.
    simpl in H4.
    inversion H4; subst.
    etransitivity; eauto.
  - intros; simpl; inversion H1; subst; simpl.
    pose proof (append_streams_mempty_right s2).
    rewrite <- H2 in H4.
    simpl in H4.
    inversion H4; subst.
    etransitivity; eauto.
  - rewrite Heqs; reflexivity.
Qed.
Next Obligation.
Admitted.

Theorem monoid_homomorphism_mempty `{Monoid a} :
  exists (H : Monoid (Stream a)), denote (a:=a) mempty ≈ mempty.
Proof.
Abort.
