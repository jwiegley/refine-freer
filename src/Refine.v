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

Generalizable All Variables.

Fixpoint InT `(a : A) (l : list A) : Type :=
  match l with
  | [] => False
  | b :: m => (b = a) + InT a m
  end.

Program Instance Union_Computes {s} :
  (forall eff, InT eff effs -> Computes s eff) -> Computes s (Union effs) := {
  computes := fun _ u v => _
}.
Next Obligation.
  induction effs; intros.
    now inversion v.
  inversion v; subst; clear v.
    refine (computes u X1 X X0).
    apply H.
    now left.
  apply IHeffs; auto.
  intros.
  apply H.
  now right.
Defined.

Section Relate.

Variable s : Type.
Variable effs : list (Type -> Type).
Variable a : Type.

Hypothesis Hcomputes : forall eff, InT eff effs -> Computes s eff.

Inductive relate : s -> Eff effs a -> s -> a -> Prop :=
  | RelatePure :
      forall st v, relate st (Pure v) st v

  | RelateImpure :
      forall st st' st'' v x u (k : x -> Eff effs a),
        forall i, computes st u st' i ->
        relate st' (k i) st'' v ->
        relate st (Impure u k) st'' v.

Definition refine (st : s) (old new : Eff effs a) : Prop :=
  forall (st' : s) v, relate st new st' v -> relate st old st' v.

Require Import
  Hask.Control.Monad
  RWS.

End Relate.

Program Instance Choice_Computes {s} : Computes s Choice := {
  computes := fun _ st '(Pick P) st' v => P v /\ st = st'
}.

Program Instance State_Computes {s} : Computes s (State s) := {
  computes := fun _ st a st' v => State_func a st = (st', v)
}.

Lemma choice_and_state_computes :
  forall eff : Type -> Type,
    InT eff [Choice; State (nat : Type)] -> Computes nat eff.
Proof.
  intros.
  destruct X; subst.
    apply Choice_Computes.
  destruct i; subst.
    apply State_Computes.
  inversion i.
Defined.

Example relate_ex :
  relate _ _ _ choice_and_state_computes
    0
    (send (Put 10) ;;
     x <- send Get ;
     y <- send (Pick (fun x => x <= 10));
     pure (x + y))
    10
    15.
Proof.
  simpl.
  repeat (eapply RelateImpure; eauto; try reflexivity).
    instantiate (1 := 5).       (* here the Pick is resolved *)
    simpl.
    unfold eq_rect_r, eq_rect, eq_sym; simpl.
    split.
      omega.
    reflexivity.
  constructor.
Qed.

Example refine_works :
  refine _ _ _ choice_and_state_computes
    10
    (send (Put 10) ;;
     x <- send Get ;
     y <- send (Pick (fun x => 0 <= x <= 10));
     pure (x + y))
    (y <- send (Pick (fun x => 10 <= x <= 20));
     pure y).
Proof.
  simpl.
  repeat intro.
  inversion H; subst; clear H.
  apply inj_pair2 in H4; subst.
  apply inj_pair2 in H1; subst.
  inversion H6; subst; clear H6.
  inversion H7; subst; clear H7.
  econstructor.
    simpl.
    unfold eq_rect_r, eq_rect, eq_sym; simpl.
    reflexivity.
  econstructor.
    simpl.
    unfold eq_rect_r, eq_rect, eq_sym; simpl.
    reflexivity.
  econstructor.
    simpl.
    unfold eq_rect_r, eq_rect, eq_sym; simpl.
    split.
      instantiate (1 := v - 10).
      omega.
    reflexivity.
  replace (10 + (v - 10)) with v by omega.
  constructor.
Qed.
