Require Import
        Eff
        Hask.Control.Monad.

Generalizable All Variables.

Inductive Heap {addr value: Type}: Type -> Type :=
| Read : addr -> Heap value (* Takes an address and return a value *)
| Write : addr -> value -> Heap unit. 

Arguments Heap _ _ _ : clear implicits.

Definition runHeap `(v: val) `(h: Heap addr val t): t :=
  match h with
  | Read _ => v
  | Write _ _ => tt
  end.

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
  rewrite Heq_wildcard' in *.
  exact v.
Defined.
Next Obligation.
  rewrite <- Heq_wildcard'.
  exact tt.
Defined.

