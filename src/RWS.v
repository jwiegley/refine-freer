Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Lists.List
  Coq.omega.Omega
  Hask.Control.Monad.

Require Export
  Eff.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

(************************************************************************)

Polymorphic Inductive Reader (e : Type) : Type -> Type := Ask : Reader e e.

Arguments Ask {e}.

Definition ask {e : Type} : Freer (Reader e) e :=
  Impure Ask Pure.

Fixpoint runReader `(x : e) `(f : Freer (Reader e) a) : a :=
  match f with
  | Pure v => v
  | Impure Ask k => runReader x (k x)
  end.

Program Fixpoint runReaderC `(x : e) `(f : Freer (Union (Reader e :: r)) a) :
  Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runReaderC x (k _)
    | inr u => Impure u (fun y => runReaderC x (k y))
    end
  end.
Next Obligation.
  destruct f.
  exact x.
Defined.

(* Definition runReaderC' `(x : e) `(f : Freer (Union (Reader e :: r)) a) := *)
(*   runFreer id f (fun _ 'Ask => x). *)

(************************************************************************)

Inductive Writer (o : Type) : Type -> Type :=
  | Tell : o -> Writer o unit.

Arguments Tell {o} _.

Definition tell `(x : o) : Freer (Writer o) unit := sendF (Tell x).

Fixpoint runWriter `(f : Freer (Writer o) a) : (list o * a) :=
  match f with
  | Pure v => (nil, v)
  | Impure (Tell x) k =>
      let '(l, v) := runWriter (k tt) in (x::l, v)%list
  end.

Program Fixpoint runWriterC `(f : Freer (Union (Writer o :: r)) a) :
  Freer (Union r) (list o * a) :=
  match f with
  | Pure v => Pure (nil, v)
  | Impure u k =>
    match decomp u with
    | inl f =>
      res <- runWriterC (k _) ;
      let '(l, v) := res in
      pure (_ :: l, v)%list
    | inr u => Impure u (fun x => runWriterC (k x))
    end
  end.
Next Obligation.
  destruct f.
  exact o0.
Defined.
Next Obligation.
  destruct f.
  exact tt.
Defined.

(* Program Fixpoint runWriterC' `(f : Freer (Union (Writer o :: r)) a) := *)
(*   runFreer (fun a => list o * a)%type f (fun _ '(Tell x) => tt) _. *)

Definition runWriterP {o r a} :
  Eff (Writer o :: r) a -> Eff r (list o * a) -> Prop :=
  handleRelayP
    (fun x r => r = Pure ([], x))
    (fun t x v =>
       match x in Writer _ a' return a' = t -> _ with
       | Tell s' => fun H => v = rew H in tt
       end eq_refl).

(************************************************************************)

Program Fixpoint runGetPut {e : Type} (x : e)
        `(f : Freer (Union (Reader e :: Writer e :: r)%list) a) :
  Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runGetPut x (k _)
    | inr u =>
      match decomp u with
      | inl f => runGetPut x (k _)
      | inr u => Impure u (runGetPut x \o k)
      end
    end
  end.
Next Obligation.
  destruct f.
  exact x.
Defined.
Next Obligation.
  destruct f.
  exact tt.
Defined.

Polymorphic Inductive State (s : Type) : Type -> Type :=
  | Get : State s s
  | Put : s -> State s unit.

Arguments Get {s}.
Arguments Put {s} _.

Definition State_func `(x : State s a) : s -> (s * a) :=
  match x with
  | Get   => fun s => (s, s)
  | Put s => fun _ => (s, tt)
  end.

Definition runState {s r a} (st : s) : Eff (State s :: r) a -> Eff r (a * s) :=
  handleRelayS
    st
    (fun s x => Pure (x, s))
    (fun t s x k =>
       match x in State _ a' return a' = t -> _ with
       | Get    => fun H => k s  (rew H in s)
       | Put s' => fun H => k s' (rew H in tt)
       end eq_refl).

Definition refineState {s s' a} (AbsR : s -> s' -> Prop) :
  State s a -> State s' a -> Prop :=
  fun old new => forall s, exists s', AbsR s s' ->
    let ro := State_func old s  in
    let rn := State_func new s' in
    AbsR (fst ro) (fst rn) /\ snd ro = snd rn.

Definition runStateP {s r a} :
  s -> Eff (State s :: r) a -> Eff r (s * a) -> Prop :=
  handleRelaySP
    (fun s x r => r = Pure (s, x))
    (fun t s x s' v =>
       match x in State _ a' return a' = t -> _ with
       | Get   => fun H => s' = s /\ v = rew H in s
       | Put z => fun H => s' = z /\ v = rew [id] H in tt
       end eq_refl).
