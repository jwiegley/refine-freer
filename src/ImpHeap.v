Require Import
        Coq.Bool.Bool
        Coq.Arith.Arith
        Coq.Arith.EqNat
        Coq.omega.Omega
        Coq.Lists.List
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Program.Tactics.

Require Import
  Hask.Control.Monad
  Hask.Data.Maybe.

Require Export
  Eff
  RWS
  Maps
  Heap.

Import ListNotations.
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

Eval compute in (eqb_string "Y" "Y").

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

Polymorphic Cumulative Inductive RunTimeError@{i j} : Type@{i} -> Type@{j} :=
| NullPointerException : RunTimeError Empty_set.

Definition context := list ((nat : Type)*(nat : Type)).
Definition state := partial_map (nat : Type).

Fixpoint find_key (k: nat) (l: context): option nat :=
  match l with
  | [] => None
  | (x,v) :: xs => if (k =? x) then Some v else find_key k xs
  end.

Program Fixpoint interpret_imptree (e: Eff [Locals; HeapCanon] (unit: Type))
  : Eff [State context; State state; RunTimeError] (unit:Type) :=
  match e with 
  | Pure v => pure tt
  | Impure u k => match decomp u with
                 | inl l => match l with
                           | Read addr => st <- send Get;
                                           match st addr with
                                           | None => send NullPointerException;; pure tt
                                           | Some v => interpret_imptree (k ltac:(subst; refine v))
                                           end
                           | Write a v => st <- send Get;
                                           send (Put (update st a v));;
                                           interpret_imptree (k (runHeap v l));;
                                           pure tt
                           end
                 | inr r => let u' := extract r in
                           match u' with
                           | Read addr => l <- send Get;
                                        match find_key addr l with
                                        | None => send NullPointerException;; pure tt
                                        | Some v => interpret_imptree (k ltac:(subst;refine v))
                                        end
                           | Write a v => l <- send Get;
                                          send (Put ((a, v)::l));;
                                          interpret_imptree (k (runHeap v u'));;
                                          pure tt
                           end
                 end
  end.

Definition app_state (m1 m2: state): state:=
  fun x => match m1 x with
        | Some v => Some v
        | None => m2 x
        end.

Definition run_state `(s: State u t) (v: u): u :=
  match s with
  | Get => v
  | Put x => x
  end.

Program Fixpoint run_state_context_help (acc: context * state)
        (e: Eff [State context; State state; RunTimeError] unit)
  : option (context * state) :=
  match e with
  | Pure c => Some acc
  | Impure u k => match decomp u with
                 | inl l => let st := run_state l [] in
                           let new_acc := ((fst acc) ++ st, snd acc) in
                           run_state_context_help new_acc (k _) 
                 | inr r => match decomp r with
                           | inl l' => let ctx := run_state l' empty in
                                      let new_acc := (fst acc, app_state (snd acc) ctx) in
                                      run_state_context_help new_acc (k _) 
                           | inr r' => None
                           end
                 end
  end.
Next Obligation.
  inversion l; subst.
  - refine [].
  - refine tt.
Defined.
Next Obligation.
  inversion l'.
  - refine empty.
  - refine tt.
Defined.

Definition run_state_context := run_state_context_help ([], empty).

Definition interp_imp e
  : Eff [State context; State state; RunTimeError] unit :=
  (send (Put empty);; send (Put []);; (interpret_imptree e)).

Definition interp := run_state_context \o interp_imp.

Fixpoint interpret_imptree' (e: Eff [HeapCanon] unit):
  Eff [State context; RunTimeError] context :=
  match e with 
  | Pure v => pure []
  | Impure u q => let u' := extract u in
                 match u' with
                 | Read addr => l <- send Get;
                                 match find_key addr l with
                                 | None => send NullPointerException;; pure []
                                 | Some v => xs <- interpret_imptree' (q (runHeap v u'));
                                                                       pure xs
                                 end
                 | Write a v => l <- send Get;
                                 send (Put ((a, v)::l));;
                                 xs <- interpret_imptree' (q (runHeap v u'));
                                 pure ((a,v)::xs)
                 end
  end.

Program Fixpoint run_context (e: Eff [State context; RunTimeError] context) : option context :=
  match e with
  | Pure c => Some c
  | Impure u k => match decomp u with
                 | inl l => run_context (k _)
                 | inr r => None
                 end
  end.
Next Obligation.
  inversion l.
  - refine [].
  - refine tt.
Defined.

Definition interp' e := run_context (send (Put []);; interpret_imptree' e).

Notation "'⟦' c '⟧'" := (denote_imp c) (at level 40).


Definition move_heap (move: nat) `(h: HeapCanon v): HeapCanon v :=
  match h with
  | Read addr => Read (addr+move)
  | Write addr val => Write (addr+move) val
  end.

Fixpoint shiftBy (move: nat) `(e: Eff (HeapCanon :: effs) t)
  : Eff (HeapCanon :: effs) t :=
  match e with
  | Pure e => pure e
  | Impure u k =>
    let cont := (fun x => shiftBy move (k x)) in
    match decomp u with
                 | inl l => Impure (inj (move_heap move l)) cont
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
                 | inl l => get_local l :: (get_locals (k (runHeap 0 l)))
                 | inr r => get_locals (k (runHeap 0 (extract r)))
                 end
  end.

Definition alloc_locals `(e: Eff [Locals; HeapCanon] t) :=
  ⇄ shiftBy (Datatypes.length (get_locals e)) (⇄ e).

Fixpoint first_occ `(t_dec: forall (t1 t2: t), ({t1 = t2} + {t1 <> t2}))
         (x: t) (l: list t):=
  match l with
  | [] => 0
  | x' :: xs => match t_dec x x' with
               | left _ => 0
               | right _ => let n := first_occ t_dec x xs in
                           S n
               end
  end.

Definition locals_handler' {effs} (l: list string) : Locals ~> Eff (HeapCanon::effs) :=
  fun `(H: Locals a) =>
    match H with
    | Read addr => let n := first_occ string_dec addr l in
                      send (Read n) >>= pure
    | Write addr val => let n := first_occ string_dec addr l in
                       send (Write n val);; pure tt
    end.

Definition locals_handler {effs} (e: Eff [Locals; HeapCanon] unit) :=
  @locals_handler' effs (get_locals e).

Definition memory_fusion e :=
  (interpret (locals_handler e) unit) (alloc_locals e).

Definition x: com := ("X" ::= ANum 3;;; CStore 1 ( 4 + 7);;; "Y" ::= ALoad 1;;; "Z" ::= ANum 4).

Definition x_itree := ⟦ x ⟧.

Eval compute in (x_itree).
Eval compute in (get_locals x_itree).
Eval cbn in (interp_imp x_itree).
Eval cbn in (interp x_itree).
Eval compute in (alloc_locals x_itree).
Eval compute in (memory_fusion x_itree).
Eval compute in (interp' (memory_fusion x_itree)).

Lemma xx: exists l, interp x_itree = Some l.
Proof.
  Opaque run_state_context.
  unfold interp.
  cbn.
  Transparent run_state_context.
  simpl.

Fixpoint heapfy (c: nat) (l: list (string*nat)): list (nat*nat) :=
  match l with
  | [] => []
  | (s, n)::xs => (c,n) :: heapfy (S c) xs
  end.

Theorem interp_correct (c:com):
  forall locs heap,
  let e := denote_imp c in
  let xs' := interpret_imptree' (memory_fusion e) in
  (locs, heap) = interpret_imptree e ->
  exists map, map locs heap = xs'.
Proof.
  intros locs heap e xs' H.
  exists (fun (l:list (string * nat)) (h:list (nat*nat)) =>
       heapfy 0 l ++ map (fun x => (fst x + Datatypes.length l, snd x)) h).
Admitted.