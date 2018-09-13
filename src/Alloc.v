Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Hask.Data.Monoid
  Coq.Sets.Ensembles
  Coq.Arith.Arith.

Open Scope string_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Definition emptyS   := "empty".
Definition allocS   := "alloc".
Definition freeS    := "free".
Definition reallocS := "realloc".
Definition peekS    := "peek".
Definition pokeS    := "poke".
Definition memcpyS  := "memcpy".
Definition memsetS  := "memset".
Definition readS    := "read".
Definition writeS   := "write".

Definition Pos := nat.
Definition Len := nat.

Definition no_meaning {a : Type} : Comp a := Empty_set a.

Definition HeapSpec `{Monoid a} := Def ADT {
  rep := Pos -> option (Pos * Len * a),

  Def Constructor0 emptyS : rep := ret (fun _ => None),,

  Def Method1 allocS (r : rep) (len : Len | 0 < len) : rep * Pos :=
    addr <- { pos | forall p, pos <= p < pos + ` len -> r p = None };
    ret ((fun p =>
            if (addr <=? p) && (p <? addr + ` len)
            then Some (addr, ` len, mempty)
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

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.
