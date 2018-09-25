Require Import
  Fiat.ADT
  Fiat.Computation.IfDec
  Fiat.ADTNotation
  Hask.Data.Monoid
  Coq.Sets.Ensembles
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.omega.Omega.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Open Scope string_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Definition emptyS   := "empty".
Definition allocS   := "alloc".
Definition freeS    := "free".
Definition peekS    := "peek".
Definition pokeS    := "poke".

Definition Pos := nat.
Definition Len := nat.

Definition no_meaning {a : Type} : Comp a := Empty_set a.

Definition guard (P : Prop) :=
  { _ : () | P }.

Section Alloc.

Context `{Monoid a}.

(** This specification for heaps is "ideal" in the sense that it assumes a
    machine with unlimited memory and clients who use the heap appropriately;
    thus it only specifies the meaning of allocation when memory is always
    available and used properly. *)
Definition IdealHeap := Def ADT {
  rep := Pos -> option (Pos * Len * a),

  Def Constructor0 emptyS : rep := ret (fun _ => None),,

  Def Method1 allocS (r : rep) (len : Len) : rep * Pos :=
    guard (0 < len) >>
    addr <- { pos | forall p, pos <= p < pos + len -> r p = None };
    ret ((fun p =>
            if (addr <=? p) && (p <? addr + len)
            then Some (addr, len, mempty)
            else r p), addr),

  Def Method1 freeS (r : rep) (addr : Pos) : rep :=
    match r addr with
    | Some (addr', len, val) =>
      if addr =? addr'
      then
        ret (fun p =>
               if (addr' <=? p) && (p <? addr' + len)
               then None
               else r p)
      else no_meaning
    | None => no_meaning
    end,

  Def Method1 peekS (r : rep) (addr : Pos) : rep * a :=
    match r addr with
    | Some (_, _, val) => ret (r, val)
    | None => no_meaning
    end,

  Def Method2 pokeS (r : rep) (addr : Pos) (w : a) : rep :=
    match r addr with
    | Some (pos', len, _) =>
        ret (fun p =>
               if p =? addr
               then Some (pos', len, w)
               else r p)
    | None => no_meaning
    end

}%ADTParsing.

Inductive HeapError :=
  | ZeroLengthAllocation
  | NoMemoryAvailable (len : Len)
  | NoAllocationAtAddress (addr : Pos)
  | UnallocatedMemoryAccess (addr : Pos).

(** This specification include error handling. *)
Definition RealHeap := Def ADT {
  rep := Rep IdealHeap,         (* denotation is the same *)

  Def Constructor0 emptyS : rep :=
    callCons IdealHeap emptyS,,

  Def Method1 allocS (r : rep) (len : Len) : rep * (HeapError + Pos) :=
    If 0 <? len
    Then
      mpos <- { pos : option nat
              | match pos with
                | Some pos' =>
                  forall p, pos' <= p < pos' + len -> r p = None
                | None => True
                end };
      match mpos with
      | Some pos' =>
        `(r', pos) <- callMeth IdealHeap allocS r len;
        guard (pos = pos') >>
        ret (r', inr pos)
      | None =>
        ret (r, inl (NoMemoryAvailable len))
      end
    Else ret (r, inl ZeroLengthAllocation),

  Def Method1 freeS (r : rep) (addr : Pos) : rep * (HeapError + ()) :=
    match r addr with
    | Some _ =>
      r' <- callMeth IdealHeap freeS r addr;
      ret (r', inr ())
    | None =>
      ret (r, inl (NoAllocationAtAddress addr))
    end,

  Def Method1 peekS (r : rep) (addr : Pos) : rep * (HeapError + a) :=
    match r addr with
    | Some _ =>
      `(r', val) <- callMeth IdealHeap peekS r addr;
      ret (r', inr val)
    | None =>
      ret (r, inl (UnallocatedMemoryAccess addr))
    end,

  Def Method2 pokeS (r : rep) (addr : Pos) (w : a) : rep * (HeapError + ()) :=
    match r addr with
    | Some _ =>
      r' <- callMeth IdealHeap pokeS r addr w;
      ret (r', inr ())
    | None =>
      ret (r, inl (UnallocatedMemoryAccess addr))
    end

}%ADTParsing.

Definition empty : Comp (Rep RealHeap) :=
  Eval simpl in callCons RealHeap emptyS.

Definition alloc (r : Rep RealHeap) (len : Len) :
  Comp (Rep RealHeap * (HeapError + Pos)) :=
  Eval simpl in callMeth RealHeap allocS r len.

Definition free (r : Rep RealHeap) (addr : Pos) :
  Comp (Rep RealHeap * (HeapError + ())) :=
  Eval simpl in callMeth RealHeap freeS r addr.

Definition peek (r : Rep RealHeap) (addr : Pos) :
  Comp (Rep RealHeap * (HeapError + a)) :=
  Eval simpl in callMeth RealHeap peekS r addr.

Definition poke (r : Rep RealHeap) (addr : Pos) (w : a) :
  Comp (Rep RealHeap * (HeapError + ())) :=
  Eval simpl in callMeth RealHeap pokeS r addr w.

Record HeapR (a : Type) : Type := {
  allocs  : list (Pos * Len);
  values  : list (Pos * a);
  next    : Pos;
  heapEnd : Pos
}.

Record Valid_HeapR `(heap : HeapR a) := {
  next_avail : forall pos len,
    List.In (pos, len) (allocs heap) -> pos + len <= next heap;

  next_within : next heap <= heapEnd heap;

  values_allocated : forall pos val,
    List.In (pos, val) (values heap) ->
      exists pos' len',
        List.In (pos, len') (allocs heap) /\ pos' <= pos < pos' + len'
}.

Program Definition allocR (len : Len) (heap : HeapR a) :
  HeapR a * (HeapError + Pos) :=
  match 0 <? len with
  | true =>
    match next heap + len <=? heapEnd heap with
    | true =>
      ({| allocs  := (next heap, len) :: allocs heap
        ; values  := values heap
        ; next    := next heap + len
        ; heapEnd := heapEnd heap
        |}, inr (next heap))
    | false => (heap, inl (NoMemoryAvailable len))
    end
  | false => (heap, inl ZeroLengthAllocation)
  end.

Theorem allocR_valid :
  forall len (heapR : HeapR a),
    Valid_HeapR heapR -> Valid_HeapR (fst (allocR len heapR)).
Proof.
  intros ?? valid.
  unfold allocR.
  destruct (0 <? len); auto.
  destruct (next heapR + len <=? heapEnd heapR) eqn:?; auto.
  constructor; intros; simpl in *.
  - destruct H0.
    inversion_clear H0.
      omega.
    apply next_avail in H0; auto.
    omega.
  - apply Nat.leb_le in Heqb.
    omega.
  - apply values_allocated in H0; auto.
    destruct H0, H0, H0.
    exists x, x0.
    intros.
    destruct H.
    split; [|omega].
    right; auto.
Qed.

Program Definition peekR (pos : Pos) `(!Valid_HeapR heapR) :
  option a :=
  match find (fun '(p, _) => pos =? p) (values heapR) with
  | Some (_, val) => Some val
  | None => None
  end.

Definition denote `{Monoid a} (h : HeapR a) : Rep RealHeap :=
  fun p =>
    match find (fun '(pos, len) => (pos <=? p) && (p <? pos + len))
               (allocs h) with
    | Some (pos, len) =>
      Some (pos, len,
            match find (fun '(pos, _) => p =? pos) (values h) with
            | Some (_, val) => val
            | None => mempty
            end)
    | None => None
    end.

Theorem refine_If_Then_Else' :
  forall (A : Type) (c : bool) (x y r : Comp A),
  (c = true  -> refine x r) ->
  (c = false -> refine y r) ->
  refine (If c Then x Else y) r.
Proof.
  intros.
  destruct c eqn:?; subst; simpl; intuition.
Qed.

Theorem denote_alloc heapR len (valid : Valid_HeapR heapR) :
  refine (alloc (denote heapR) len)
         (match allocR len heapR with
          | (heapR', posR) => ret (denote heapR', posR)
          end).
Proof.
  simpl; unfold alloc, allocR, denote; intros.
  apply refine_If_Then_Else'; intros.
    refine pick val (If next heapR + len <=? heapEnd heapR
                     Then Some (next heapR)
                     Else None).
      unfold Bind2.
      simplify with monad laws; simpl.
      destruct (next heapR + len <=? heapEnd heapR) eqn:?; simpl.
        simplify with monad laws; simpl.
        unfold guard.
        pose proof H0.
        apply Nat.ltb_lt in H1.
        refine pick val (); auto.
        simplify with monad laws; simpl.
        refine pick val (next heapR).
          simplify with monad laws; simpl.
          refine pick val (); auto.
          simplify with monad laws; simpl.
          apply refine_ret_eq.
          rewrite H0.
          f_equal.
          unfold Pos.
          f_equal.
          extensionality p.
          simpl.
          destruct ((next heapR <=? p) && (p <? next heapR + len)) eqn:?.
            f_equal.
            f_equal.
            apply andb_prop in Heqb0.
            destruct Heqb0.
            apply Nat.leb_le in H2.
            apply Nat.ltb_lt in H3.
            destruct (find _ _) eqn:?; auto.
            destruct p0.
            apply find_some in Heqo.
            destruct Heqo.
            apply Nat.eqb_eq in H5.
            subst.
            pose proof (values_allocated valid _ _ H4).
            destruct H5, H5, H5.
            pose proof (next_avail valid _ _ H5).
            omega.
          reflexivity.
        intros.
        destruct (find _ _) eqn:?; auto.
        destruct p0.
        elimtype False.
        apply find_some in Heqo.
        destruct Heqo.
        apply andb_prop in H4.
        destruct H4.
        apply Nat.leb_le in H4.
        apply Nat.ltb_lt in H5.
        pose proof (next_avail valid _ _ H3).
        omega.
      rewrite H0.
      reflexivity.
    destruct (next heapR + len <=? heapEnd heapR) eqn:?; simpl; auto.
    intros.
    destruct (find _ _) eqn:?; auto.
    destruct p0.
    apply find_some in Heqo.
    destruct Heqo.
    apply andb_prop in H3.
    destruct H3.
    apply Nat.leb_le in H3.
    apply Nat.ltb_lt in H4.
    pose proof (next_avail valid _ _ H2).
    omega.
  rewrite H0.
  reflexivity.
Qed.

Theorem Heap : FullySharpened RealHeap.
Proof.
  start sharpening ADT.

  hone representation using (fun o n => Valid_HeapR n /\ denote n = o).

  {
    simplify with monad laws.
    refine pick val {| allocs := nil; values := nil; next := 0; heapEnd := 100 |}.
      finish honing.
    split; auto.
    constructor; simpl; intros.
    - contradiction.
    - omega.
    - contradiction.
  }

  {
    destruct H1.
    subst.
    rewrite (denote_alloc d H1).
    replace (let (heapR', posR) := allocR d r_n in ret (denote heapR', posR))
       with (ret (denote (fst (allocR d r_n)), snd (allocR d r_n)))
       by (destruct (allocR d r_n); simpl; auto).
    simplify with monad laws; simpl.
    refine pick val (fst (allocR d r_n)).
      simplify with monad laws; simpl.
      rewrite <- surjective_pairing.
      finish honing.
    split; auto.
    now apply allocR_valid.
  }

  {
    admit.
  }

  {
    admit.
  }

  {
    admit.
  }

  finish_SharpeningADT_WithoutDelegation.
Admitted.

End Alloc.
