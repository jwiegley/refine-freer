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

Fixpoint denote_imp (c: com): Eff [State state] unit :=
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
Definition state_default: forall eff r, FindElem eff [State state] -> eff r -> r.
  intros.
  inversion X; subst.
  inversion X0; subst.
  refine (t_empty 0).
  refine tt.
  inversion X1.
Defined.

Definition state_size {v} (e: Eff [State state] v): nat := Eff_size e state_default.

Eval compute in (state_size swap_spec1).
Eval compute in (state_size swap_spec2).
Eval compute in (state_size (denote_imp swap_impl)).

Open Scope bool_scope.

Fixpoint opt_getget' (b: bool) (s: state) `(e: Eff [State state] v): Eff [State state]  v :=
  match e with
   | Pure x => pure x
   | Impure u k =>
     let default := fun b' s' x => opt_getget' b' s' (k x) in
     match extract u in State _ s return s = _ -> _ with
     | Get => fun Heq => if b then default true s (rew [id] Heq in s)
             else Impure u (fun x => default true s x)
     | Put x => fun _ => Impure u (default false s)
     end eq_refl
  end.
Definition opt_getget {v} := @opt_getget' false (t_empty 0) v.


Fixpoint opt_putput `(e: Eff [State state] v): Eff [State state] v :=
   match e with
   | Pure x => pure x
   | Impure u k =>
     match extract u in State _ s return s = _ -> _ with
     | Get => fun _ => Impure u (fun x => opt_putput (k x))
     | Put x => fun Heq => let k' := k (rew [id] Heq in tt) in
                       match k' with
                       | Pure t  => Impure u (fun x' => Pure t)
                       | Impure u' k'' =>
                         match extract u' with
                         | Get =>
                           Impure u (fun x' => Impure u' (fun x'' => opt_putput (k'' x'')))
                         | Put y => Impure u' (fun x' => opt_putput (k'' x'))
                         end
                       end
     end eq_refl
   end.

Fixpoint opt_putget `(e: Eff [State state] v): Eff [State state] v :=
   match e with
   | Pure x => pure x
   | Impure u k =>
     match extract u in State _ s return s = _ -> _ with
     | Get => fun _ => Impure u (fun x => opt_putget (k x))
     | Put st =>
       fun Heq => Impure u (fun x => match k x with
                               | Pure x' => Pure x'
                               | @Impure _ _ T' u' k' =>
                                 match extract u' in State _ s return s = T' -> _ with
                                 | Put st' => fun _ => opt_putget (k x)
                                 | Get => fun Heq' => opt_putget (k' (rew [id] Heq' in st))
                                 end eq_refl
                               end)
                            
     end eq_refl
   end.

Definition step_opt {v} := @opt_putget v \o @opt_getget v \o @opt_putput v.

Program Fixpoint opt `(e: Eff [State state] v) {measure (state_size e)} :=
  let step := step_opt e in
  match lt_dec (state_size step) (state_size e) with
  | left _ => opt step
  | _ => step
  end.

Definition swap_spec1_opt: Eff [State state] unit :=
  (opt swap_spec1).

Definition swap_spec2_opt: Eff [State state] unit :=
  (opt swap_spec2).

Definition swap_impl_opt: Eff [State state] unit :=
  (opt (denote_imp swap_impl)).

Eval cbn in ((denote_imp swap_impl)).
(* There is a bug on put put *)
Eval cbn in (swap_spec1_opt).
Eval cbn in (swap_impl_opt).
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




