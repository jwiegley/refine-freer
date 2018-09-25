Require Import Coq.Arith.Arith.
Require Import Hask.Data.Monoid.

Generalizable All Variables.

Open Scope nat_scope.
Open Scope bool_scope.

Definition Position := nat.
Definition Length := nat.

(** Model *)
(** A heap is defined as identifying, at every position, whether that
    position falls within an allocated block, and the value there. *)
Definition Heap (a : Type) := Position -> option (Position * Length * a).

(** Algebra *)
Definition alloc (len : Length) `{Monoid a} (heap : Heap a) :
  Heap a -> Position -> Prop := fun res pos =>
    IF 0 < len
    then forall p,
      IF pos <= p < pos + len
      then heap p = None /\ res p = Some (pos, len, mempty)
      else res p = heap p
    else False.

(** Freeing an unallocated block has no meaning. *)
Definition free (pos : Position) `(heap : Heap a) : Heap a -> Prop :=
  fun res =>
    match heap pos with
    | Some (pos', len, val) =>
      forall p,
        IF pos = pos' /\ pos' <= p < pos' + len
        then res p = None
        else res p = heap p
    | None => False
    end.

(** Peeking an unallocated block has no meaning. *)
Definition peek (pos : Position) `(heap : Heap a) : a -> Prop :=
  fun v =>
    match heap pos with
    | Some (_, _, val) => v = val
    | None => False
    end.

(** Poking into an unallocated block has no meaning. *)
Definition poke (pos : Position) `(val : a) (heap : Heap a) : Heap a -> Prop :=
  fun heap =>
    match heap pos with
    | Some (pos', len, _) => heap pos = Some (pos', len, val)
    | None => False
    end.

Require Import Coq.omega.Omega.

Theorem alloc_works len pos `{Monoid a} (heap : Heap a) heap' :
  alloc len heap heap' pos -> heap' pos = Some ((pos, len), mempty).
Proof.
  unfold alloc; intros.
  destruct H0; intuition.
  destruct (H2 pos); intuition; clear H2.
  omega.
Qed.

Theorem alloc_free len pos `{Monoid a} (heap : Heap a) heap' heap'' :
  alloc len heap heap' pos ->
  free pos heap' heap'' ->
  forall p, heap p = heap'' p.
Proof.
  intros.
  pose proof (alloc_works _ _ _ _ H0).
  unfold alloc, free in *.
  destruct (heap' pos); [|contradiction].
  destruct p0, p0.
  inversion H2; subst; clear H2.
  destruct H0; [|intuition].
  destruct H0.
  destruct (H2 p); clear H2.
    destruct H3, H3, H2; subst.
    destruct (H1 p); [|intuition; omega].
    intuition.
    congruence.
  intuition.
  destruct (H1 p); [intuition; omega|].
  destruct H2.
  congruence.
Qed.

Theorem peek_poke pos a (val : a) heap heap' :
  poke pos val heap heap' -> peek pos heap' val.
Proof.
  unfold poke, peek; intros.
  destruct (heap' pos); auto.
  destruct p, p.
  now inversion_clear H.
Qed.

Require Import Coq.Lists.List.

Record HeapR (a : Type) : Type := {
  allocs : list (Position * Length);
  values : list (Position * a);
  next   : Position
}.

Record Valid_HeapR `(heap : HeapR a) := {
  next_avail : forall pos len,
    List.In (pos, len) (allocs _ heap) -> pos + len <= next _ heap;
  values_allocated : forall pos val,
    List.In (pos, val) (values _ heap) ->
      exists pos' len',
        List.In (pos, len') (allocs _ heap) /\ pos' <= pos < pos' + len'
}.

Definition denote `{Monoid a} (h : HeapR a) : Heap a :=
  fun p =>
    match find (fun '(pos, len) => (pos <=? p) && (p <? pos + len))
               (allocs _ h) with
    | Some (pos, len) =>
      Some (pos, len,
            match find (fun '(pos, _) => p =? pos) (values _ h) with
            | Some (_, val) => val
            | None => mempty
            end)
    | None => None
    end.

Program Definition allocR (len : Length) {a} `(!Valid_HeapR heap) :
  option (HeapR a * Position) :=
  match 0 <? len with
  | true =>
    Some ({| allocs := (next _ heap, len) :: allocs _ heap
           ; values := values _ heap
           ; next   := next _ heap + len
           |}, next _ heap)
  | false => None
  end.

Theorem allocR_valid :
  forall a (heapR : HeapR a) heapR' posR len (valid : Valid_HeapR heapR),
    allocR len valid = Some (heapR', posR) -> Valid_HeapR heapR'.
Proof.
  unfold allocR; simpl; intros.
  destruct (0 <? len); [|discriminate].
  inversion_clear H.
  constructor; intros; simpl in *.
  - destruct H.
    inversion_clear H.
      omega.
    apply next_avail in H; auto.
    omega.
  - apply values_allocated in H; auto.
    destruct H, H.
    exists x, x0.
    intros.
    destruct H.
    split; [|omega].
    right; auto.
Qed.

Theorem denote_alloc `{Monoid a} :
  forall heapR len (valid : Valid_HeapR heapR),
    match allocR len valid with
    | Some (heapR', posR) =>
      alloc len (denote heapR) (denote heapR') posR
    | None => True
    end.
Proof.
  simpl; unfold alloc, allocR, denote; intros.
  destruct valid.
  destruct (0 <? len) eqn:?; simpl; intros; auto.
  apply Nat.ltb_lt in Heqb.
  left.
  split; auto.
  intros.
  destruct ((next a heapR <=? p) && (p <? next a heapR + len)) eqn:?.
    left.
    split.
      apply andb_prop in Heqb0.
      destruct Heqb0.
      apply Nat.leb_le in H0.
      apply Nat.leb_le in H1.
      omega.
    destruct (find _ _) eqn:?.
      destruct p0.
      apply find_some in Heqo.
      destruct Heqo.
      apply andb_prop in H1.
      destruct H1.
      apply Nat.leb_le in H1.
      apply Nat.leb_le in H2.
      specialize (next_avail0 _ _ H0); clear H0.
      apply andb_prop in Heqb0.
      destruct Heqb0.
      apply Nat.leb_le in H0.
      apply Nat.leb_le in H3.
      omega.
    split; auto.
    f_equal.
    f_equal.
    destruct (find (fun '(pos, _) => p =? pos)
                   (values a heapR)) eqn:?; auto.
    destruct p0.
    apply find_some in Heqo0.
    destruct Heqo0.
    apply Nat.eqb_eq in H1.
    subst.
    specialize (values_allocated0 _ _ H0); clear H0.
    destruct values_allocated0, H0, H0.
    specialize (next_avail0 _ _ H0); clear H0.
    apply andb_prop in Heqb0.
    destruct Heqb0.
    apply Nat.leb_le in H0.
    apply Nat.ltb_lt in H2.
    omega.
  right.
  split.
    apply Bool.andb_false_iff in Heqb0.
    destruct Heqb0.
      apply Nat.leb_nle in H0.
      omega.
    apply Nat.leb_nle in H0.
    omega.
  destruct (find _ _) eqn:?; auto.
Qed.

Program Definition peekR (pos : Position) {a} `(!Valid_HeapR heapR) :
  option a :=
  match find (fun '(p, _) => pos =? p) (values a heapR) with
  | Some (_, val) => Some val
  | None => None
  end.

Theorem denote_peek `{Monoid a} :
  forall heapR pos (valid : Valid_HeapR heapR),
    match peekR pos valid with
    | Some val => peek pos (denote heapR) val
    | None => True
    end.
Proof.
  unfold peek, peekR, denote; intros.
  destruct (find _ _) eqn:?; auto.
  destruct p.
  destruct (find (fun '(pos0, len) => (pos0 <=? pos) && (pos <? pos0 + len))
                 (allocs a heapR)) eqn:?.
    destruct p.
    assert ((fun pat : nat * a =>
             (let
              '(p, wildcard') as pat' := pat return (pat' = pat -> bool) in
               fun _ : (p, wildcard') = pat => pos =? p) eq_refl) =
            (fun '(pos0, _) => pos =? pos0)).
      Require Import FunctionalExtensionality.
      extensionality pat.
      now destruct pat.
    rewrite <- H0; clear H0.
    now rewrite Heqo.
  apply find_some in Heqo.
  destruct Heqo.
  apply values_allocated in H0; auto.
  destruct H0, H0, H0.
  apply find_none with (x:=(n,x0)) in Heqo0; auto.
  apply Nat.eqb_eq in H1.
  subst.
  apply Bool.andb_false_iff in Heqo0.
  destruct Heqo0.
    apply Nat.leb_nle in H1.
    omega.
  apply Nat.leb_nle in H1.
  omega.
Qed.
