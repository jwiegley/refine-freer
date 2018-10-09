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

Fixpoint string_to_asciiList (s: string): list ascii :=
  match s with
  | EmptyString => []
  | String x xs => x :: string_to_asciiList xs
  end.

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

Definition HeapCanon_shift `(e: Eff (HeapCanon :: effs) t) := HeapCanon_shiftBy 10 e.

Definition hash_string (s: string): nat :=
  fold_right (fun c n => n * nat_of_ascii c) 1 (string_to_asciiList s).

Eval compute in (hash_string "01").

Definition get_local `(h: Locals t): string :=
  match h with
  | Read addr => addr
  | Write addr _ => addr
  end.

Lemma app_locs : forall v, v.
Admitted.

Fixpoint get_locals' {t effs} (e: Eff (Locals :: effs) t): (forall v, v) -> list string :=
  match e with
  | Pure x => fun _ => []
  | Impure u k => match decomp u with
                 | inl f => fun y => get_local f :: (get_locals' (k (y _))) y
                 | inr u' => fun y => (get_locals' (k (y _))) y
                 end
  end.

Definition get_locals `(e: Eff (Locals :: effs) t) := get_locals' e app_locs.

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

Program Fixpoint locals_handler `(ta: taddr) `(tv: tval) `(e: Eff [Heap taddr tval] t): t :=
  match e with
  | Pure x => x
  | Impure u q => (match extract u with
                 | Read addr => locals_handler ta tv (q _)
                 | Write addr val => locals_handler ta tv (q _)
                 end)
  end.
Next Obligation.
  refine tt.
Qed.

    match H with
    | Read addr => 
    | Write addr val => let n := first_occ string_dec addr l in
                       send (Write n val);; pure tt
    end.

Definition locals_handler {effs} (l: list string) : Locals ~> Eff (HeapCanon::effs) :=
  fun `(H: Locals a) =>
    match H with
    | Read addr => let n := first_occ string_dec addr l in
                      send (Read n) >>= pure
    | Write addr val => let n := first_occ string_dec addr l in
                       send (Write n val);; pure tt
    end.

Definition memory_fusion `(e: Eff (Locals::HeapCanon :: effs) unit) :=
  (@interpret _ (HeapCanon::effs) (@locals_handler _ (get_locals e)) unit) e.

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
Eval compute in nat_of_ascii "0".
