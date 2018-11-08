Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Require Export
  Eff
  Comp
  Choice.


Require Import
  Hask.Control.Monad
  RWS.

Generalizable All Variables.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ALoad: aexp -> aexp.


Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CStore : aexp -> aexp -> com.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.
Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.


Inductive eff_aexp (r : Type) : Type :=
  | E_ANum : nat -> eff_aexp r
  | E_APlus : r -> r -> eff_aexp r
  | E_AMinus : r -> r -> eff_aexp r
  | E_AMult : r -> r -> eff_aexp r.

Definition Fix (f : Type -> Type) :=
  forall r, (forall x, (x -> r) -> f x -> r) -> r.

Inductive eff_bexp (r : Type) : Type :=
  | E_BTrue : eff_bexp r
  | E_BFalse : eff_bexp r
  | E_BEq : Fix eff_aexp -> Fix eff_aexp -> eff_bexp r
  | E_BLe : Fix eff_aexp -> Fix eff_aexp -> eff_bexp r
  | E_BNot : r -> eff_bexp r
  | E_BAnd : r -> r -> eff_bexp r.

Inductive eff_com (r : Type) : Type :=
  | E_CSkip : eff_com r
  | E_CAss : string -> eff_aexp r -> eff_com r
  | E_CIf : eff_bexp r -> r -> r -> eff_com r
  | E_CWhile : eff_bexp r -> r -> eff_com r.