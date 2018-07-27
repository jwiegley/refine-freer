Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Lists.List
  Coq.omega.Omega
  Hask.Control.Monad.

Require Export
  Member
  Comp.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

Inductive Choice (A : Type) : Type :=
  | Pick : forall (P : A -> Prop), Choice A.

Arguments Pick {A} P.

(* A Choice "effect" may be refined so long as every value computable from the
   new choice was computable from the original choice. *)
Inductive refineChoice {a} : Choice a -> Choice a -> Prop :=
  RefineChoice : forall old new, (forall v, new ↝ v -> old ↝ v) ->
     refineChoice (Pick new) (Pick old).

Class Computes (eff : Type -> Type) := {
  computes : forall a, eff a -> a -> Prop
}.

Arguments computes {eff _ a} _ _.

Class Relates (eff eff' : Type -> Type) := {
  relates : forall a, eff a -> eff' a -> Prop
}.

Arguments relates {eff eff' _ a} _ _.

(* Given an interpreter that can run any effect down to its denotation in
   Gallina, we can interpret any action. *)
Inductive interpP {effs state a}
          (interpE : forall v, effs v -> v -> state -> state -> Prop) :
          Freer effs a -> a -> state -> state -> Prop :=
  | interpP_Impure :
      forall {t} (u : effs t) (r : t) (k : t -> Freer effs a)
             val pre mid post,
        interpE _ u r pre mid ->
        interpP interpE (k r) val mid post ->
        interpP interpE (Impure u k) val pre post
  | interpP_Pure : forall val pre post,
      interpP interpE (Pure val) val pre post.

Require Import
  RWS.

(* This theorem present the meaning of state, interpreted as an "effect" on an
   input state and resulting in a final value. *)
Theorem meaning_of_State {s v} (f : State s v) (x : v) (start : s) :
  interpP
    (fun v (st : State s v) (x : v) (pre : s) (post : s) =>
       match st in State _ v' return v' = v -> _ with
       | Get   => fun H => post = pre /\ x = rew H in post
       | Put p => fun H => post = p   /\ x = rew H in tt
       end eq_refl)
    (sendF f)
    (match f in State _ v' return v' = v -> _ with
     | Get   => fun H => start
     | Put p => fun H => tt
     end eq_refl)
    start
    (match f in State _ v' return v' = v -> _ with
     | Get   => fun H => start
     | Put p => fun H => p
     end eq_refl).
Proof.
  unfold sendF.
  induction f; simpl;
  eapply interpP_Impure; eauto;
  eapply interpP_Pure.
Qed.

Theorem final {a} {x : Eff [] a} {v state} {pre post : state} :
  run x = v ->
  interpP (fun _ u _ _ _ => False_rect _ (Union_empty _ u)) x v pre post.
Proof.
  simpl; intros; subst.
  induction x; simpl.
    now apply interpP_Pure.
  now inversion f.
Qed.
