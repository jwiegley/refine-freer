Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Lists.List.

Require Export
  Eff
  Comp
  Choice.

Import ListNotations.

Generalizable All Variables.

Inductive relate {a} : forall {effs}, Eff effs a -> a -> Prop :=
  | RelatePure : forall effs v, relate (effs:=effs) (Pure v) v

  | RelateImpureThis :
      forall `{Computes eff} effs v
             x u (k : x -> Eff (eff :: effs) a),
        forall i, computes u i -> relate (k i) v ->
        relate (Impure (UThis u) k) v

  | RelateImpureThat :
      forall eff effs v
             x u (k : x -> Eff (eff :: effs) a) ret bind,
        relate (Impure u (fun x => handleRelay ret bind (k x))) v ->
        relate (Impure (UThat u) k) v.

Definition refine {effs a} (old new : Eff effs a) : Prop :=
  forall v, relate old v -> relate new v.
