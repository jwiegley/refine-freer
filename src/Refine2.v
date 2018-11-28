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

(* We want an optmization under the state laws, which should be:
 1) get >>= get =~= get
 2) put s' >>= put s =~= put s
 3) put s >>= get =~= s
*)
Open Scope bool_scope.
Fixpoint opt' {effs v} (bget bput b: bool) (s: state) (e: Eff (State state :: effs) v): Eff (State state :: effs) v :=
  match e with
  | Pure x => pure x
  | Impure u k =>
    match decomp u with
    | inl st =>
      match st in State _ state return state = _ -> _ with
      | Get => fun Heq => if (bget || b) then opt' true false b s (k (rew Heq in s))
                      else Impure u (fun x => opt' true false false s (k x))
      | Put st' => fun Heq => if bput then opt' false true true st' (k (rew Heq in tt))
                        else Impure u (fun x => opt' false true true st' (k x))
      end eq_refl
    (*Let's assume for now that we don't know how the effects interact with each other *)
    | _ => Impure u (fun x => opt' false false false s (k x)) 
    end
  end.

Definition opt {effs v} := @opt' effs v false false false (t_empty 0).

Eval cbn in (opt swap_spec2).

Definition swap_spec1_opt: Eff [State state] unit :=
  (opt swap_spec1).

Definition swap_spec2_opt: Eff [State state] unit :=
  (opt swap_spec2).

Definition swap_impl_opt: Eff [State state] unit :=
  (opt (denote_imp swap_impl)).

Eval cbn in ((denote_imp swap_impl)).
(* There is a bug on put put *)
Eval cbn in (swap_impl_opt).
Eval cbn in (swap_spec1_opt).
Eval cbn in (swap_spec2_opt).
(* I need to apply this function multiple times now, until the term normalizes.
What can I do? *)
Eval cbn in (opt swap_spec2_opt).
Eval cbn in (opt swap_impl_opt).

Definition refines {a effs} (e1 e2: Eff effs a) := 
  forall t, e2 = t -> e1 = t.

Lemma swap_impl_respects_spec2:
  opt swap_impl_opt = opt swap_spec2_opt.
Proof.
  reflexivity.
Qed.

Lemma swap_impl_respects_spec1:
  swap_impl_opt = swap_spec1_opt.
Proof.
  reflexivity.
Qed.




