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

Definition swap_spec1: Eff [State state] unit :=
  st <- send Get;
  send (Put (st & {W --> st Y; X --> st Y}));;
  pure tt.

Definition swap_spec2: Eff [State state] unit :=
  st <- send Get;
  send (Put (st & {W --> st Y}));;
  st' <- send Get;
  send (Put (st' & {X --> st' Y}));;
  pure tt.

Definition swap_impl: com :=
  W ::= Y;;;
  X ::= Y.

Eval cbn in (denote_imp swap_impl).
Eval cbn in swap_spec1.

(* Write a function to transform 
 * (fun x => 1 + (fun y => x + y))
 * into ~~~>
 * (fun x => 1 + x + x)
*)

Definition blah: (nat -> nat -> nat) -> nat -> nat :=
  fun f x => f x x.

Program Fixpoint merge_impures `(e: Eff (State state :: effs) v): Eff (State state :: effs) v :=
  match e with
  | Pure x => pure x
  | Impure u k => let default := (fun x => merge_impures (k x)) in
                 match decomp u with
                 | inl st =>
                   match st with
                   | Get => Impure u (fun x =>
                                       match k x with
                                       | Pure x => pure x
                                       | Impure u' k' =>
                                         match decomp u' with
                                         | inl st' =>
                                           match st' with
                                           | Get => merge_impures (k' _)
                                           | Put y => merge_impures (k x)
                                           end
                                         | _ => merge_impures (k x)
                                         end
                                       end)
                   | Put x => Impure u default
                   end
                 | _ => Impure u default
                 end
  end.

Eval cbn in (merge_impures (denote_imp swap_impl)).
Eval cbn in swap_spec1.
Eval cbn in swap_spec2.

Lemma swap_respects_spec2:
  merge_impures (denote_imp swap_impl) = swap_spec2.
Proof.
  reflexivity.
Qed.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma swap_disrespects_spec2:
  merge_impures (denote_imp swap_impl) <> swap_spec1.
Proof.
  intro.
  inversion H.
  apply inj_pair2 in H1.
  eapply equal_f in H1.
  inversion H1.
  apply inj_pair2 in H2.
Admitted.



Definition merge_impures {effs f x a}: (forall x, f x -> (x -> Eff effs a)) -> 

     = Impure (UThis Get)
         (fun x : string -> nat =>
          Impure (UThis Get)
            (fun x0 : total_map nat =>
             Impure (UThis (Put (x0 & {X --> x Y}))) (fun _ : () => Pure ())))

Lemma normalize_nat : forall (a b: nat),
  ((fun x => (fun y => x + x)) a b) = (fun x => x + x).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Fixpoint normalize_r `(e: Eff (State v :: effs) unit) (b: bool) (c: v)
  : Eff (State v :: effs) unit :=
  match e with
  | Pure x => pure x
  | Impure u (fun x => k) => match decomp u with
                         | inl l => _
                         end
  end.



Definition refines {a effs} (e1 e2: Eff effs a) := 
  forall t, e2 = t -> e1 = t.



