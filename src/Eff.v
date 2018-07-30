Require Import
  Coq.Program.Program
  Coq.Program.Tactics
  Coq.Lists.List
  Coq.omega.Omega
  Hask.Control.Monad.

Require Export
  Member.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

Definition sendF `(t : f a) : Freer f a := Impure t Pure.

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

Definition Eff (effs : list (Type -> Type)) (a : Type) : Type :=
  Freer (Union effs) a.

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

Program Instance Functor_Eff {r} : Functor (Eff r) := Freer_Functor _.
Program Instance Applicative_Eff {r} : Applicative (Eff r) := Freer_Applicative _.
Program Instance Monad_Eff {r} : Monad (Eff r) := Freer_Monad _.

Program Definition run `(f : Eff nil a) : a :=
  match f with
  | Pure x => x
  | Impure u k => False_rect _ _
  end.
Next Obligation.
  (* there are no more choices: effects are not possible *)
  inversion u.
Qed.

Program Fixpoint runM `{Monad m} `(f : Eff [m] a) : m a :=
  match f with
  | Pure x     => pure x
  | Impure u q => extract u >>= (runM \o q)
  end.

Definition Arr effs a b := a -> Eff effs b.
Arguments Arr effs a b /.

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

Inductive handleRelayP {eff effs a b}
          (retP : a -> Eff effs b -> Prop)
          (bindP : forall v, eff v -> v -> Prop) :
          Eff (eff :: effs) a -> Eff effs b -> Prop :=
  | HandlePure : forall x r,
      retP x r -> handleRelayP retP bindP (Pure x) r
  | HandleThis : forall t u v q r,
      bindP t u v ->
      handleRelayP retP bindP (q v) r ->
      handleRelayP retP bindP (Impure (x:=t) (UThis u) q) r
  | HandleThat : forall t u q k,
      (forall y, handleRelayP retP bindP (q y) (k y)) ->
      handleRelayP retP bindP (Impure (x:=t) (UThat u) q) (Impure (x:=t) u k).

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

Inductive handleRelaySP {eff effs s a b}
          (retP : s -> a -> Eff effs b -> Prop)
          (bindP : forall v, s -> eff v -> s -> v -> Prop) :
          s -> Eff (eff :: effs) a -> Eff effs b -> Prop :=
  | HandlePureS : forall st x r,
      retP st x r -> handleRelaySP retP bindP st (Pure x) r
  | HandleThisS : forall st st' t u v q r,
      bindP t st u st' v ->
      handleRelaySP retP bindP st' (q v) r ->
      handleRelaySP retP bindP st (Impure (x:=t) (UThis u) q) r
  | HandleThatS : forall st t u q k,
      (forall st y, handleRelaySP retP bindP st (q y) (k y)) ->
      handleRelaySP retP bindP st (Impure (x:=t) (UThat u) q) (Impure (x:=t) u k).

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

Program Fixpoint raise {e} `(f : Eff effs a) : Eff (e :: effs) a :=
  match f with
  | Pure x => Pure x
  | Impure u k => Impure (weaken u) (fun x => raise (k x))
  end.
