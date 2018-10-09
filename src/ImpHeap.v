Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Require Import Coq.Program.Tactics.

Require Export
  Eff
  Comp
  Choice.


Require Import
  Hask.Control.Monad
  Hask.Data.Maybe
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

Inductive Heap {addr value: Type}: Type -> Type :=
| Read : addr -> Heap value (* Takes an address and return a value *)
| Write : addr -> value -> Heap unit. 

Arguments Heap _ _ _ : clear implicits.

Fixpoint runHeap' `(v: val) `(h: Heap addr val t): t.
  destruct h.
  - exact v.
  - exact tt.
Defined.

Program Fixpoint runHeap `(v: val) `(f: Eff [Heap addr val] t): t :=
  match f with
  | Pure x => x
  | Impure u k => match extract u with
                 | Read a1 => runHeap v (k _)
                 | Write a1 v1 => runHeap v1 (k _)
                 end
  end.
Next Obligation.
  symmetry in Heq_wildcard'.
  subst.
  exact v.
Defined.
Next Obligation.
  rewrite <- Heq_wildcard'.
  exact tt.
Defined.

Program Fixpoint runHeapC `(v: val) `(f: Eff (Heap addr val:: effs) t):
  Eff effs t :=
  match f with
  | Pure x => Pure x
  | Impure u k => match decomp u with
                     | inr r => Impure r (fun y => runHeapC v (k y))
                     | inl l => match l with
                               | Read a1 => runHeapC v (k _)
                               | Write a1 v1 => runHeapC v1 (k _)
                               end
                 end
  end.
Next Obligation.
  exact tt.
Defined.

Definition Locals: Type -> Type := Heap string nat.
Definition HeapCanon: Type -> Type := Heap nat nat.

Fixpoint denote_aexp (a:aexp): Eff [Locals; HeapCanon] nat :=
  match a with
  | ANum n => pure n
  | AId x => send (Read x)
  | APlus a1 a2 => (l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l+r))
  | AMinus a1 a2 => l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l-r)
  | AMult a1 a2 => l <- denote_aexp a1 ; r <- denote_aexp a2 ; pure (l*r)
  | ALoad e => a <- denote_aexp e ; send (Read a)
  end.


Fixpoint denote_bexp (b:bexp): Eff [Locals; HeapCanon] bool :=
  match b with
  | BTrue => pure true
  | BFalse => pure false
  | BEq a1 a2 => (l <- (denote_aexp a1) ; r <- (denote_aexp a2) ; pure (l =? r))
  | BLe a1 a2 => (l <- (denote_aexp a1) ; r <- (denote_aexp a2) ; pure (l <=? r))
  | BAnd b1 b2 => (l <- (denote_bexp b1); r <- (denote_bexp b2); pure (l && r))
  | BNot b' => (r <- denote_bexp b'; pure (negb r))
  end.

Fixpoint denote_imp (c: com): Eff [Locals; HeapCanon] unit :=
  match c with
  | CSkip => pure tt
  | CAss x ax => (a <- denote_aexp ax;
                   send (Write x a);;
                   pure tt)
  | CIf b c1 c2 => b' <- denote_bexp b;
                          if (b':bool)
                          then denote_imp c1
                          else  denote_imp c2
  | CSeq c1 c2 => denote_imp c1 ;; denote_imp c2
  | CStore aaddr aval => addr <- denote_aexp aaddr;
                          val <- denote_aexp aval;
                          send (Write addr val);;
                          pure tt
  end.


Variant RunTimeError : Type -> Type :=
| StackOverflow : RunTimeError Empty_set.

Definition move_heap_helper (move: nat) `(h: HeapCanon v): HeapCanon v :=
  match h with
  | Read addr => Read (addr+move)
  | Write addr val => Write (addr+move) val
  end.

Fixpoint HeapCanon_shiftBy (counter: nat) `(e: Eff (HeapCanon :: effs) t): Eff (HeapCanon :: effs) t :=
  match e with
  | Pure e => pure e
  | Impure u k =>
    let cont := (fun x => HeapCanon_shiftBy counter (k x)) in
    match decomp u with
                 | inl l => Impure (inj (move_heap_helper counter l)) cont
                 | inr r => Impure u cont
                 end
  end.

Definition get_local `(h: Locals t): string :=
  match h with
  | Read addr => addr
  | Write addr _ => addr
  end.

(* In order to add arbitrary effects I need an interpreter for each effect
 * A TypeClass sounds like a good idea to achieve that
 *)
Fixpoint get_locals {t} (e: Eff [Locals; HeapCanon] t):  list string :=
  match e with
  | Pure v => []
  | Impure u k => match decomp u with
                 | inl l => get_local l :: (get_locals (k (runHeap' 0 l)))
                 | inr r => get_locals (k (runHeap' 0 (extract r)))
                 end
  end.

(* TODO: Change this to change the lenght of all locals 
 * HeapCanon_shiftBy (length (get_locals e)) e.
 * We need a minor tweak in the types for this
 *) 
Definition HeapCanon_shift `(e: Eff (HeapCanon :: effs) t) :=
  HeapCanon_shiftBy 10 e.

Fixpoint first_occ `(t_dec: forall (t1 t2: t), ({t1 = t2} + {t1 <> t2}))
         (x: t) (l: list t): nat :=
  match l with
  | [] => 0
  | x' :: xs => match t_dec x x' with
               | left _ => 0
               | right _ => let n := first_occ t_dec x xs in
                             (S n)
               end
  end.

Definition locals_handler {effs} (l: list string) : Locals ~> Eff (HeapCanon::effs) :=
  fun `(H: Locals a) =>
    match H with
    | Read addr => let n := first_occ string_dec addr l in
                      send (Read n) >>= pure
    | Write addr val => let n := first_occ string_dec addr l in
                       send (Write n val);; pure tt
    end.

Definition memory_fusion `(e: Eff [Locals; HeapCanon] unit) :=
  (@interpret _ [HeapCanon] (@locals_handler _ (get_locals e)) unit) e.

Definition effect_swap `(e: Eff ([eff1; eff2]++effs) v) : Eff ([eff2; eff1]++effs) v.
Proof.
  unfold Eff in *.
  induction e.
  - constructor; auto.
  - inversion f; subst.
    -- constructor 2 with x; auto.
       constructor 2; eauto.
       constructor 1; eauto.
    -- inversion X0; subst.
       --- constructor 2 with x; auto.
           constructor; auto.
       --- constructor 2 with x; auto.
           repeat constructor 2.
           auto.
Defined.

Notation "⟦ c ⟧" := (denote_imp c) (at level 40).

Definition x: com := ("X" ::= ANum 3;;; CStore 1 (4+2);;; "Z" ::= ALoad 0;;; SKIP).
Definition plusDet :=
  ⟦ x ⟧.

Notation "⇄ x" := (effect_swap x) (at level 50).

Eval compute in (plusDet).


Eval compute in ((get_locals plusDet)).


Eval compute in (HeapCanon_shift (⇄ plusDet)).
 (* = Impure (UThat (UThis (Write "X"%string 3)))
         (fun _ : unit =>
          Impure (UThat (UThis (Write "Y"%string 4)))
            (fun _ : unit =>
             Impure (UThis (Write 10 5))
               (fun _ : unit =>
                Impure (UThis (Write 11 6))
                  (fun _ : unit =>
                   Impure (UThis (Read 10))
                     (fun x3 : nat =>
                      Impure (UThat (UThis (Write "Z"%string x3))) (fun _ : unit => Pure tt))))))
  *)

Eval compute in (memory_fusion (⇄(HeapCanon_shift (⇄ plusDet)))).
