Require Export Imp.
Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.omega.Omega
  Coq.Lists.List.

Require Export
  Eff
  Comp
  Choice.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

Require Import
  Hask.Control.Monad
  RWS.

Inductive IVar (a: Type): Type :=
  | ivar: IVar a.

Inductive Par (s : Type) : Type -> Type :=
  | new : Par s (IVar s)
  | get : IVar s -> Par s s
  | put : IVar s -> s -> Par s unit
  | fork: Par s unit -> Par s unit.

Lemma ivar_unit: forall v, IVar v.
Proof.
  constructor.
Qed.

Definition send_get: Par () () :=
  get () (ivar ()).

Definition put_ex : Eff [Par nat] nat :=
  Impure (UThis (new _))
         (fun i => Impure (UThis (put _ i 3))
                       (fun _ => Impure (UThis (get _ i)) (fun x => pure x))).

Definition spawn a (p: Par a ()): Eff [Par a] (IVar a).
Proof.
  eapply Impure.
  refine (UThis (new _)).
  intro i.
  eapply Impure.
  refine (UThis (fork _ _)).
  2: {
    intro.
    refine (pure i).
  }
Admitted.
(*  
  constructor.

  Impure (UThis (new _))
         (fun i => Impure (UThis (fork _ (Impure (UThis p) (fun x => ))
                       (fun _ => pure i))


  i <- send get;
  pure tt.

  Impure new
         (fun i => Impure (fork (Impure p (fun x => Impure (put i x)
                                                     (fun v => v))))
                             (fun _ => Pure i)).

spawn :: NFData a => Par a -> Par (IVar a)
     spawn p = do 
         i <- new
         fork (do x <- p; put i x)
         return i
*)