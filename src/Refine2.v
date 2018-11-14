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


Program Definition denotes_state {effs v}: Eff (State state :: effs) v -> Eff effs v -> Prop :=
    handleRelayP
      (fun x e => match e with
               | Pure x' =>  x = x'
               | Impure u k => False
               end)
      (fun V (st: State state V) a =>
         match st in State _ a' return V = a' -> _ with
         | Get => fun _ => True
         | Put x => _
         end eq_refl).
Next Obligation.
refine (forall y, x y = 2).
Defined.

Definition swap_spec: Eff [State state] unit :=
  st <- send Get;
  send (Put (st & {X --> st Y; Y --> st X}));;
  pure tt.

Definition swap_impl: com :=
  X ::= Y ;;;
  Y ::= X.


Fixpoint denote_aexp `{Member (State state) effs}
         (a:aexp): Eff effs nat :=
  match a with
  | ANum n => pure n
  | AId x => (st <- send Get;
              pure (st x))
  | APlus a1 a2 => n1 <- denote_aexp a1;
                    n2 <- denote_aexp a2;
                    pure (n1 + n2)
  | AMinus a1 a2 => n1 <- denote_aexp a1;
                    n2 <- denote_aexp a2;
                    pure (n1 - n2)
  | AMult a1 a2 => n1 <- denote_aexp a1;
                    n2 <- denote_aexp a2;
                    pure (n1 * n2)
  end.

Fixpoint denote_bexp `{Member (State state) effs}
         (b:bexp): Eff (effs) bool :=
  match b with
  | BTrue => pure true
  | BFalse => pure false
  | BEq a1 a2 => (x1 <- (denote_aexp a1) ;
                   x2 <- (denote_aexp a2) ;
                   pure (beq_nat x1 x2))
  | BLe a1 a2 => (x1 <- (denote_aexp a1) ;
                   x2 <- (denote_aexp a2) ;
                   pure (leb x1 x2))
  | BAnd b1 b2 => (x1 <- (denote_bexp b1);
                    x2 <- (denote_bexp b2);
                    pure (andb x1 x2))
  | BNot b' => (b'' <- denote_bexp b';
                 pure (negb b''))
  end.

Fixpoint denote_imp `{Member (State state) effs}
         (c: com): Eff effs unit :=
  match c with
  | SKIP => pure tt
  | CAss x ax => (a <- denote_aexp ax;
                   st <- send Get; 
                   send (Put (t_update st x a));;
                   pure tt)
  | IFB b THEN c1 ELSE c2 FI => b' <- denote_bexp b;
                                 if (b':bool)
                                 then denote_imp c1
                                 else  denote_imp c2
  | c1 ;;; c2 => denote_imp c1 ;; denote_imp c2 
  | WHILE b DO c' END => pure tt (* <- bogus *)
  end.

Eval simpl in (denote_imp swap_impl).


Definition refines {a effs} (e1 e2: Eff effs a) := 
  forall t, e2 = t -> e1 = t.



