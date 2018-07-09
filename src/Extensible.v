Require Import Coq.Program.Program.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Program.Tactics.
Require Import Coq.omega.Omega.
Require Export Hask.Control.Monad.

Import ListNotations.

Generalizable All Variables.
(* Set Primitive Projections. *)
(* Set Universe Polymorphism. *)
(* Unset Transparent Obligations. *)

Inductive UnionF (a : Type) : list (Type -> Type) -> Type :=
  | UThis : forall t r, t a -> UnionF a (t :: r)
  | UThat : forall t r, UnionF a r -> UnionF a (t :: r).

Arguments UThis {a t r} _.
Arguments UThat {a t r} _.

Definition Union (r : list (Type -> Type)) (a : Type) := UnionF a r.

Lemma Union_empty : forall a, Union [] a -> False.
Proof. inversion 1. Qed.

(* A notation for natural transformations. *)
Notation "f ~> g" := (forall x, f x -> g x) (at level 90).

Import EqNotations.

Program Definition decomp `(u : Union (t :: r) v) : t v + Union r v :=
  match u in UnionF _ xs
        return (t :: r)%list = xs -> t v + Union r v with
  | UThis x => fun _ => inl (_ x)
  | UThat x => fun _ => inr x
  end eq_refl.

Definition decomp_rev `(u : Union (r ++ [t]) v) : Union r v + t v.
Proof.
  induction r; simpl in u.
    inversion u; subst.
      exact (inr X).
    inversion X.
  inversion u; subst.
    exact (inl (UThis X)).
  destruct (IHr X).
    exact (inl (UThat u0)).
  exact (inr t0).
Defined.

Program Definition extract `(u : Union [t] v) : t v :=
  match decomp u with | inl x => x | inr x => ! end.
Next Obligation. inversion x. Qed.

Definition weaken {t} `(u : Union r v) : Union (t :: r) v := UThat u.

Definition Pos (t : Type -> Type) (r : list (Type -> Type)) := nat.

Inductive FindElem (t : Type -> Type) : list (Type -> Type) -> Type :=
  | Here : forall xs, FindElem t (t :: xs)
  | Next : forall t' xs, FindElem t xs -> FindElem t (t' :: xs).

Class Member (t : Type -> Type) (r : list (Type -> Type)) := {
  inj : forall v, t v -> Union r v;
  prj : forall v, Union r v -> option (t v);
  hasElem : FindElem t r
}.

Arguments inj {t r _ v} _.
Arguments prj {t r _ v} _.

Program Instance Member_Here (t : Type -> Type) (r : list (Type -> Type)) :
  Member t (t :: r) | 1 := {
  inj := fun _ x => UThis x;
  prj := fun _ u =>
    match decomp u with
    | inl x => Some x
    | inr _ => None
    end;
  hasElem := Here _ _
}.

Program Instance Member_Next (t t' : Type -> Type) (r : list (Type -> Type)) :
  Member t r -> Member t (t' :: r) | 2 := {
  inj := fun _ x => UThat (inj x);
  prj := fun _ u =>
    match decomp u with
    | inl _ => None
    | inr u => prj u
    end;
  hasElem := Next _ _ _ hasElem
}.

Fixpoint inject_last  (t : Type -> Type) (r : list (Type -> Type))
         `(x : t a) : Union (r ++ [t]) a :=
  match r with
  | [] => UThis x
  | _ :: xs => UThat (inject_last t xs x)
  end.

Fixpoint FindElem_last  (t : Type -> Type) (r : list (Type -> Type)) :
  FindElem t (r ++ [t]) :=
  match r with
  | [] => Here _ _
  | _ :: xs => Next _ _ _ (FindElem_last t xs)
  end.

Program Instance Member_Last (t : Type -> Type) (r : list (Type -> Type)) :
  Member t (r ++ [t]) | 2 := {
  inj := fun _ x => inject_last t r x;
  prj := fun _ u =>
    match decomp_rev u with
    | inl _ => None
    | inr x => Some x
    end;
  hasElem := FindElem_last t r
}.

Inductive Freer (f : Type -> Type) (a : Type) : Type :=
  | Pure : a -> Freer f a
  | Impure : forall x, f x -> (x -> Freer f a) -> Freer f a.

Arguments Pure {f a} _.
Arguments Impure {f a x} _ _.

Fixpoint Freer_map {r} `(f : a -> b) (x : Freer r a) : Freer r b :=
  match x with
  | Pure v => Pure (f v)
  | Impure u k => Impure u (fun x => Freer_map f (k x))
  end.

Program Instance Freer_Functor (f : Type -> Type) : Functor (Freer f) := {
  fmap := @Freer_map _
}.

Fixpoint Freer_ap {r} `(f : Freer r (a -> b)) (x : Freer r a) : Freer r b :=
  match f, x with
  | Pure f, Pure v     => Pure (f v)
  | Pure f, Impure u k => Impure u (fun x => Freer_map f (k x))
  | Impure u k, m      => Impure u (fun x => Freer_ap (k x) m)
  end.

Program Instance Freer_Applicative (f : Type -> Type) : Applicative (Freer f) := {
  pure := fun _ => Pure;
  ap := fun _ _ => Freer_ap
}.

Fixpoint Freer_join {r} `(f : Freer r (Freer r a)) : Freer r a :=
  match f with
  | Pure v     => v
  | Impure u k => Impure u (fun x => Freer_join (k x))
  end.

Program Instance Freer_Monad (f : Type -> Type) : Monad (Freer f) := {
  join := @Freer_join _
}.

Module FreerLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Program Instance Freer_FunctorLaws (f : Type -> Type) : FunctorLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold id.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold comp.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.

Program Instance Freer_ApplicativeLaws (f : Type -> Type) : ApplicativeLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  specialize (H y).
  destruct (f1 y); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction u, v, w; simpl; auto;
  f_equal;
  extensionality y; simpl;
  try (specialize (H y);
       destruct (f1 y); auto).
  - induction (f1 y); auto.
    f_equal.
    extensionality z; simpl.
    specialize (H z).
    destruct (f3 z); auto.
  - induction (f1 y); auto.
    f_equal.
    extensionality z; simpl.
    specialize (H z).
    destruct (f3 z); auto.
  - induction (f1 y); auto.
      f_equal.
      extensionality z; simpl.
      induction (f3 z); auto.
      f_equal.
      extensionality w; simpl.
      specialize (H w).
      destruct (f5 w); auto.
    f_equal.
    extensionality z; simpl.
    specialize (H z).
    destruct (f5 z); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction u; auto.
  f_equal.
  extensionality x0.
  specialize (H x0).
  destruct (f1 x0); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  extensionality x0.
  destruct x0; auto.
Qed.

Program Instance Freer_MonadLaws (f : Type -> Type) : MonadLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.

End FreerLaws.

Definition Comp (A : Type) := A -> Prop.

Program Instance Comp_Functor : Functor Comp := {
  fmap := fun A B f (x : Comp A) b => exists a : A, x a /\ f a = b
}.

Program Instance Comp_Applicative : Applicative Comp := {
  pure := fun _ x a => x = a;
  ap   := fun A B mf mx r => exists f x, mf f /\ mx x /\ f x = r
}.

Program Instance Comp_Alternative : Alternative Comp := {
  empty  := fun A _ => False;
  choose := fun A x y s => x s \/ y s (* jww (2016-01-28): right? *)
}.

Program Instance Comp_Monad : Monad Comp := {
  join := fun A m r => exists t : Comp A, t r /\ m t
}.

Module CompLaws.

Import MonadLaws.

Require Import FunctionalExtensionality.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Ltac shatter :=
  unfold comp, id in *;
  repeat
    match goal with
    | [ H : _ = _           |- _               ] => subst
    | [ H : and _ _         |- _               ] => destruct H
    | [ H : exists _ : _, _ |- _               ] => destruct H
    | [                     |- exists _ : _, _ ] => eexists
    | [                     |- and _ _         ] => split
    end;
  simpl in *.

Ltac simplify_comp :=
  repeat let x := fresh "x" in extensionality x;
  try (apply prop_ext; split; intros);
  repeat (simpl; shatter; try constructor; eauto).

Local Obligation Tactic := simpl; intros; simplify_comp.

Program Instance Comp_FunctorLaws     : FunctorLaws Comp.
Program Instance Comp_ApplicativeLaws : ApplicativeLaws Comp.
Program Instance Comp_MonadLaws       : MonadLaws Comp.

End CompLaws.

Fixpoint injF `{Member eff r} `(f : Freer eff a) : Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure f k => Impure (inj f) (fun x => injF (k x))
  end.

Polymorphic Inductive Reader (e : Type) : Type -> Type := Ask : Reader e e.

Arguments Ask {e}.

Definition ask {e : Type} : Freer (Reader e) e :=
  Impure Ask Pure.

Fixpoint runReader `(x : e) `(f : Freer (Reader e) a) : a :=
  match f with
  | Pure v => v
  | Impure Ask k => runReader x (k x)
  end.

Inductive Writer (o : Type) : Type -> Type :=
  | Tell : o -> Writer o unit.

Arguments Tell {o} _.

Definition sendF `(t : f a) : Freer f a := Impure t Pure.

Definition tell `(x : o) : Freer (Writer o) unit := sendF (Tell x).

Fixpoint runWriter `(f : Freer (Writer o) a) : (list o * a) :=
  match f with
  | Pure v => (nil, v)
  | Impure (Tell x) k =>
      let '(l, v) := runWriter (k tt) in (x::l, v)%list
  end.

Program Fixpoint runReaderC `(x : e) `(f : Freer (Union (Reader e :: r)) a) : Freer (Union r) a :=
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

Definition runFreer (T : Type -> Type) `(f : Freer (Union (eff :: r)) a)
           (eta : a -> T a)
           (bind : forall t, eff t -> (t * T a))  :
  Freer (Union r) (T a).
Proof.
  induction f as [v|t u' k IHf].
    exact (Pure (eta v)).
  inversion u'; subst; clear u'.
    exact (let '(t, _) := bind _ X in IHf t).
  exact (Impure X IHf).
Defined.

(* Definition runReaderC' `(x : e) `(f : Freer (Union (Reader e :: r)) a) := *)
(*   runFreer id f (fun _ 'Ask => x). *)

(* Program Fixpoint runWriterC `(f : Freer (Union (Writer o :: r)) a) := *)
(*   runFreer (fun a => list o * a)%type f (fun _ '(Tell x) => tt) _. *)

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
      | inr u => Impure u (fun y => runGetPut x (k y))
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

Inductive Choice (A : Type) : Type :=
  | Pick : forall (P : A -> Prop), Choice A.

Arguments Pick {A} P.

Definition comp `(f : A -> Prop) : Comp A := f.

Definition Eff (effs : list (Type -> Type)) (a : Type) : Type :=
  Freer (Union effs) a.

Program Instance Functor_Eff {r} : Functor (Eff r) := Freer_Functor _.
Program Instance Applicative_Eff {r} : Applicative (Eff r) := Freer_Applicative _.
Program Instance Monad_Eff {r} : Monad (Eff r) := Freer_Monad _.

Definition send `{Member eff effs} `(t : eff a) : Eff effs a :=
  Impure (inj t) Pure.

Program Fixpoint Eff_size `(q : Eff effs a)
        (P : forall eff r, FindElem eff effs -> eff r -> r) : nat :=
  match q with
  | Pure x => 0%nat
  | @Impure _ _ T u k =>
    match effs as xs return effs = xs -> _ with
    | nil => fun _ => !
    | cons _ _ => fun H =>
      match decomp (rew [fun x => Union x T] H in u) with
      | inl f => 1%nat + Eff_size (k (_ u)) P
      | inr u => 1%nat + Eff_size (k (_ u)) P
      end
    end eq_refl
  end.
Next Obligation. inversion u. Qed.
Next Obligation.
  eapply P; eauto.
  constructor.
Defined.
Next Obligation.
  clear -u0 P.
  induction u0.
    eapply P; eauto.
    constructor.
  eapply IHu0; eauto.
  intros.
  eapply P; eauto.
  now constructor.
Defined.

Program Definition run `(f : Eff nil a) : a :=
  match f with
  | Pure x => x
  | Impure u k => False_rect _ _
  end.
Next Obligation.
  (* there are no more choices: effects are not possible *)
  inversion u.
Qed.

Import ListNotations.

Program Fixpoint runM `{Monad m} `(f : Eff [m] a) : m a :=
  match f with
  | Pure x     => pure x
  | Impure u q => extract u >>= (runM \o q)
  end.

(*
Program Fixpoint ejectM {effs m a}
        (ret : forall a, a -> m a)
        (bind : forall a b, m a -> (a -> m b) -> m b)
        (f : Eff (effs ++ [m]) a) : Eff effs (m a) :=
  match f with
  | Pure x => Pure (ret _ x)
  | Impure u q =>
    match decomp_rev u with
    | inl u => Impure u (ejectM ret bind \o q)
    | inr x => _
    end
  end.
Next Obligation.
  apply Pure.
*)

Definition Arr effs a b := a -> Eff effs b.
Arguments Arr effs a b /.

Definition computes_to {A : Type} (ca : Comp A) (a : A) : Prop := ca a.

Notation "c ↝ v" := (computes_to c v) (at level 40).

Fixpoint handleRelay {eff effs a b}
         (ret : a -> Eff effs b)
         (bind : forall v, eff v -> Arr effs v b -> Eff effs b)
         (f : Eff (eff :: effs) a) : Eff effs b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := handleRelay ret bind \o q in
    match decomp u with
    | inl x => bind _ x k
    | inr u => Impure u k
    end
  end.

Fixpoint handleRelayS {eff effs s a b}
         (st : s)
         (ret : s -> a -> Eff effs b)
         (bind : forall v, s -> eff v -> (s -> Arr effs v b) -> Eff effs b)
         (f : Eff (eff :: effs) a) : Eff effs b :=
  match f with
  | Pure x => ret st x
  | Impure u q =>
    let k st' := handleRelayS st' ret bind \o q in
    match decomp u with
    | inl x => bind _ st x k
    | inr u => Impure u (k st)
    end
  end.

Definition interpretWith {eff effs a}
           (bind : forall v, eff v -> Arr effs v a -> Eff effs a) :
  Eff (eff :: effs) a -> Eff effs a := handleRelay Pure bind.

Definition interpret `(handler : eff ~> Eff effs) :
  Eff (eff :: effs) ~> Eff effs :=
  fun _ => interpretWith (fun _ e f => handler _ e >>= f).

Fixpoint interpose' {eff effs a b}
         `{M : Member eff effs}
         (ret : a -> Eff effs b)
         (bind : forall v, eff v -> Arr effs v b -> Eff effs b)
         (f : Eff effs a) : Eff effs b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := interpose' ret bind \o q in
    match @prj eff effs M _ u with
    | Some x => bind _ x k
    | None   => Impure u k
    end
  end.

Definition interposeWith {eff effs a} `{Member eff effs}
           (bind : forall v, eff v -> Arr effs v a -> Eff effs a) :
  Eff effs a -> Eff effs a := interpose' Pure bind.

Definition interpose `{Member eff effs} `(handler : eff ~> Eff effs) :
  Eff effs ~> Eff effs :=
  fun _ => interposeWith (fun _ e f => handler _ e >>= f).

Definition subsume `{Member eff effs} : Eff (eff :: effs) ~> Eff effs :=
  interpret (fun _ => send).

(* A Choice "effect" may be refined so long as every value computable from the
   new choice was computable from the original choice. *)
Inductive refineChoice {a} : Choice a -> Choice a -> Prop :=
  RefineChoice : forall old new, (forall v, new ↝ v -> old ↝ v) ->
     refineChoice (Pick new) (Pick old).

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

Program Fixpoint refineBase {s s' a} (AbsR : s -> s' -> Prop)
        (old : Eff [State s] a) (new : Eff [State s'] a) : Prop :=
  match old, new with
  | Pure x, Pure y => x = y

  | Pure x, Impure u k =>
    match decomp u with
    | inl f => exists s, x = _ (snd (State_func f s))
    | inr u' => False_rect _ (Union_empty _ u')
    end

  | Impure u k, Pure y =>
    match decomp u with
    | inl f  => exists s, _ (snd (State_func f s)) = y
    | inr u' => False_rect _ (Union_empty _ u')
    end

  | Impure xu xk, Impure yu yk =>
    match decomp xu, decomp yu with
    | inl f,   inl g   =>
      exists (old : s) (new : s'), AbsR old new ->
        let ro := State_func f old in
        let rn := State_func g new in
        AbsR (fst ro) (fst rn) /\ snd ro = _ (snd rn)
    | inl _,   inr yu' => False_rect _ (Union_empty _ yu')
    | inr xu', inl _   => False_rect _ (Union_empty _ xu')
    | inr xu', inr _   => False_rect _ (Union_empty _ xu')
    end
  end.
Next Obligation.
  destruct f, g; auto.
  exact tt.
Defined.

Program Fixpoint reduction {s a}
        (act : Eff [Choice; State s] a) (res : a) : Prop :=
  match act with
  | Pure x => x = res
  | Impure u k =>
    match decomp u with
    | inl (Pick P) => exists v, P v /\ reduction (k v) res
    | inr u' =>
      match decomp u' with
      | inl f => exists s, reduction (k (snd (State_func f s))) res
      | inr u' => False_rect _ (Union_empty _ u')
      end
    end
  end.

Example reduction_works :
  reduction (s:=nat) (send (Put 10) ;;
                      x <- send Get ;
                      y <- send (Pick (fun x => x < 10));
                      pure (x + y)) 15.
Proof.
  simpl.
  exists 0, 10, 5.
  omega.
Qed.

Program Fixpoint raise {e} `(f : Eff effs a) : Eff (e :: effs) a :=
  match f with
  | Pure x => Pure x
  | Impure u k => Impure (weaken u) (fun x => raise (k x))
  end.

Local Obligation Tactic := program_simpl; try (eapply Union_empty; eauto).

Program Fixpoint refine_fiat {s s' a} (AbsR : s -> s' -> Prop)
        (n : nat)
        (old : Eff [Choice; State s] a)
        (new : Eff [Choice; State s'] a) : Prop :=
  match n with
  | O => False
  | S n' =>
    match old, new with
    | Pure x, Pure y => x = y

    | Pure x, Impure u k =>
      match decomp u with
      | inl (Pick P) => exists v, P v /\ refine_fiat AbsR n' old (k v)
      | inr u' =>
        match decomp u' with
        | inl f => exists s,
           refine_fiat AbsR n' old (k (_ (snd (State_func f s))))
        | inr u' => !
        end
      end

    | Impure u k, Pure y =>
      match decomp u with
      | inl (Pick P) => exists v, P v /\ refine_fiat AbsR n' (k v) new
      | inr u' =>
        match decomp u' with
        | inl f => exists s,
           refine_fiat AbsR n' (k (_ (snd (State_func f s)))) new
        | inr u' => !
        end
      end

    | Impure xu xk, Impure yu yk =>
      match decomp xu, decomp yu with
      | inl f, inl g => refineChoice f (_ g)

      | inl (Pick P), inr yu' =>
        match decomp yu' with
        | inl g => exists v s,
            P v /\ refine_fiat AbsR n' (xk v) (yk (_ (snd (State_func g s))))
        | inr u' => !
        end

      | inr xu', inl (Pick P) =>
        match decomp xu' with
        | inl f => exists v s,
            P v /\ refine_fiat AbsR n' (xk (_ (snd (State_func f s)))) (yk v)
        | inr u' => !
        end

      | inr xu', inr yu' =>
        match decomp xu', decomp yu' with
        | inl f, inl g => exists s s', AbsR s s' ->
           refine_fiat AbsR n' (xk (_ (snd (State_func f s))))
                          (yk (_ (snd (State_func g s'))))
        | inl _,   inr yu' => !
        | inr xu', inl _   => !
        | inr xu', inr _   => !
        end
      end
    end
  end.

(* This is supposed to be the effect handler for non-deterministic choice,
   which simply denotes the choice as a propositional relation in Gallina over
   the remaining effects to be handled. *)
Inductive choose {a r} : Eff (Choice :: r) a -> Eff r a -> Prop :=
  | PureChoice : forall x,
      choose (Pure x) (Pure x)
  | ImpureChoiceThis : forall A (P : A -> Prop) v k x,
      P v -> choose (k v) x ->
      choose (Impure (UThis (Pick P)) k) x
  | ImpureChoiceThat : forall u k v,
      (* jww (2018-06-19): This is all wrong, more work to be done *)
      choose (k v) (Impure u Pure) ->
      choose (Impure (UThat u) k) (Impure u Pure).

Class Relates (eff eff' : Type -> Type) := {
  relates : forall a, eff a -> eff' a -> Prop
}.

Arguments relates {eff eff' _ a} _ _.

Inductive Identity (A : Type) : A -> Prop :=
  | Id : forall x, Identity A x.

Arguments Id {_} _.

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

Definition Refines {eff eff' state state'}
           (S : state -> state' -> Prop)
           (P : forall v, eff v -> v -> state -> state -> Prop)
           (Q : forall v, eff' v -> v -> state' -> state' -> Prop) : Prop :=
  forall a (x : Freer eff a) (y : Freer eff' a) r pre post pre' post',
    (forall v (p : eff v) (q : eff' v) (x : v) (s t : state) (s' t' : state'),
        S s s' -> S t t' -> Q v q x s' t' -> P v p x s t)
    -> interpP Q y r pre post
    -> interpP P x r pre' post'.

(*
Inductive handleP {eff effs s a}
          (ret : a -> Eff effs a -> s -> s -> Prop)
          (bind : forall v, eff v -> Eff effs a -> s -> s -> Prop) :
          Eff (eff :: effs) a -> Eff effs a -> s -> s -> Prop :=
  | handleP_Impure :
      forall {v} (u : Union (eff :: effs) v)
             (x : v) (k : v -> Eff (eff :: effs) a)
             rest pre mid post,
        match decomp u with
        | inl r => bind v r rest pre mid
        | inr u => handleP ret bind (k x) rest mid post
        end ->
        handleP ret bind (Impure u k) rest pre post
  | handleP_Pure : forall x rest pre post,
      ret x rest pre post ->
      handleP ret bind (Pure x) rest pre post.
*)

Definition handleAll `(f : Eff effs a)
           (handlers : forall eff `{Member eff effs} effs' a,
               Eff (eff :: effs') a -> Eff effs' a) : a.
Proof.
Abort.

Inductive relate {effs a} : Eff effs a -> a -> Prop :=
  | RelPure : forall v, relate (Pure v) v
  | RelImpure :
      (* An effectful action relates to a final value if there exists an
         intermediate state that continues on to produce the value. *)
      forall `{Member eff effs}
             x (u : Union effs x) (k : x -> Eff effs a) i v,
        relate (k i) v -> relate (Impure u k) v.

Example relate_ex :
  relate (send (Put 10) ;;
          x <- send Get ;
          y <- send (Pick (fun x => x <= 10));
          pure (x + y)      : Eff [Choice; State (nat : Type)] nat)
         15.
Proof.
  simpl.
  repeat econstructor; eauto.
  instantiate (1 := 10).
  instantiate (1 := 5).
  constructor.
Qed.

Definition refine {effs a} (old new : Eff effs a) : Prop :=
  forall v, relate old v -> relate new v.

Example refine_works :
  refine (send (Put 10) ;;
          x <- send Get ;
          y <- send (Pick (fun x => x <= 10));
          pure (x + y)      : Eff [Choice; State (nat : Type)] nat)

         (y <- send (Pick (fun x => x <= 10));
          pure y            : Eff [Choice; State (nat : Type)] nat).
Proof.
  simpl.
  repeat intro.
  unshelve eapply RelImpure.
    exact v.
  constructor.
  unshelve econstructor.
    exact 5.
  econstructor.
  repeat econstructor; eauto.
  epick_left.                   (* Put always return unit *)
    now exists 0.
  pick_left 0.                  (* Satisfy the Get request with some answer *)
  refinement.
  exists 5.
  repeat (split; simpl; try omega; auto).
Qed.
