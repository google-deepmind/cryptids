/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`
(<https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB--->,
`cryptid_8`, holdout #661, `suspect_95`).

## Collatz-like Acceleration Rules

```text
Canonical configurations:
S0p(a, b, c) = 0^inf 1 (10)^(a+1) A> 0^(b+1) (10)^(c+1) 01 0^inf
S0z(a, c)    = 0^inf 1 (10)^(a+1) A> (10)^(c+1) 01 0^inf
T1(j, m)     = 0^inf E> (10)^(j+1) 1001 0^m 1 0^inf
T0(j, m)     = 0^inf E> (10)^(j+1) 1001 0^m 11 0^inf
T11(j, m)    = 0^inf E> (10)^(j+1) 1001 0^m 101 0^inf
T3(j, m)     = 0^inf E> (10)^(j+1) 1001 0^m 10001 0^inf
T10(j, m)    = 0^inf E> (10)^(j+1) 1001 0^m 1011 0^inf
Tn(j)        = 0^inf E> (10)^(j+1) 1001 0^inf
Ea(n)        = 0^inf A> 11000010 (10)^n 1000101 0^inf
Eb(k, t)     = 0^inf A> W_29 (0^17 11)^k 0^t 1101 0^inf
Ec(n)        = 0^inf A> 11000010 (10)^n 1 0^inf
Ed(k, t)     = 0^inf A> W_29 (0^17 11)^k 0^t 1 0^inf

Accelerated rules:
S0p(a, 0, c)   -> S0p(0, 2a+1, c+4)
S0p(a, 1, c)   -> S0p(a+2, 0, c+2)
S0p(a, 2, c)   -> S0z(a+2, c)
S0p(a, b+3, c) -> S0p(a+2, b, c)
S0z(a, 0)      -> T1(0, 2a+3)
S0z(a, c+1)    -> S0p(0, 2a+4, c)
T1(j, 0)       -> Tn(0)
T1(j, 1)       -> T11(0, 2j+7)
T1(j, 2)       -> S0p(0, 2j+5, 3)
T1(j, m+3)     -> T1(j+2, m)
T0(j, 0)       -> S0z(j+1, 0)
T0(j, 1)       -> Halt
T0(j, 2)       -> S0z(j+2, 0)
T0(j, m+3)     -> T0(j+2, m)
T11(j, 0)      -> T1(0, 2j+6)
T11(j, 1)      -> T3(0, 2j+7)
T11(j, 2)      -> Ea(j)
T11(j, m+3)    -> T11(j+2, m)
T3(j, 0)       -> T1(0, 2j+8)
T3(j, 1)       -> T10(0, 2j+7)
T3(j, 2)       -> Ec(j)
T3(j, m+3)     -> T3(j+2, m)
T10(j, 0)      -> T0(0, 2j+6)
T10(j, 1)      -> Halt
T10(j, 2)      -> Halt
T10(j, m+3)    -> T10(j+2, m)
Tn(j)          -> Tn(j+2)
Ea(n)          -> Eb(0, 2n+1)
Eb(k, t)       -> Eb(k+1, t)
Ec(n)          -> Ed(0, 2n+1)
Ed(k, t)       -> Ed(k+1, t)

Start: S0p(0, 1, 3), reached after 47 raw TM steps
```

## High-Level Collatz-like Acceleration

`HighLevelState` and `highLevelNext` contract all five `mod 3` sweeps (`S0p`, `T1`, `T11`, `T3`,
`T10`, `T0`) and eliminate `S0z`, `T0`, `T11`, `T3`, `T10`, `Ea`, and `Ec` into a pure closed-form
transition map over `S(b, c)` (`S0p(0, b, c)`), `T(m)` (`T1(0, m)`), and the three non-halting
self-loops `Tn(j)`, `Eb(k, t)`, and `Ed(k, t)`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Canonical-Form & Sweep Lemmas -/

private theorem merge_0 (a b : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0] : List (Fin 2)) ^ a)
      (ListBlank.append (([0] : List (Fin 2)) ^ b) r) =
      ListBlank.append (([0] : List (Fin 2)) ^ (a + b)) r :=
  (ListBlank.append_pow_add ([0] : List (Fin 2)) a b r).symm

private theorem rot_0 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (ListBlank.cons (0 : Fin 2) r) =
      ListBlank.cons (0 : Fin 2) (ListBlank.append (([0] : List (Fin 2)) ^ n) r) :=
  ListBlank.append_pow_comm ([0] : List (Fin 2)) n r

private theorem sq_00 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0, 0] : List (Fin 2)) ^ n) r =
      ListBlank.append (([0] : List (Fin 2)) ^ (2 * n)) r := by
  rw [pair_pow_eq_singleton_pow_two_mul]

private theorem merge_01 (a b : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) r) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + b)) r :=
  (ListBlank.append_pow_add ([0, 1] : List (Fin 2)) a b r).symm

private theorem rot_01 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ n) (ListBlank.cons (0 : Fin 2) r) =
      ListBlank.cons (0 : Fin 2) (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) r) :=
  append_01_pow_zero n r

private theorem merge_10 (a b : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) r) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + b)) r :=
  (ListBlank.append_pow_add ([1, 0] : List (Fin 2)) a b r).symm

private theorem rot_10 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.cons (1 : Fin 2) r) =
      ListBlank.cons (1 : Fin 2) (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r) :=
  append_10_pow_one n r

private theorem zero_pow_default (n : ℕ) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ListBlank.append_pow_succ, ih, ListBlank.append_cons, ListBlank.append_nil,
      ListBlank.cons_zero_default]

private theorem sweep_D_L_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft D l (ListBlank.append (([0, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l) r)
          (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append ([0, 0] : List (Fin 2)) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append ([0, 0] : List (Fin 2)) r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 0] : List (Fin 2)) ^ k)
          (ListBlank.append ([0, 0] : List (Fin 2)) r) =
          ListBlank.append (([0, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_B_R_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append ([0, 1] : List (Fin 2)) l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append ([0, 1] : List (Fin 2)) l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
          (ListBlank.append ([0, 1] : List (Fin 2)) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_E_L_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft E l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft E (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l) r)
          (Cfg.headLeft E (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append ([0, 1] : List (Fin 2)) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append ([0, 1] : List (Fin 2)) r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
          (ListBlank.append ([0, 1] : List (Fin 2)) r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_F_R_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight F (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight F (ListBlank.append ([1, 0] : List (Fin 2)) l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append ([1, 0] : List (Fin 2)) l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
          (ListBlank.append ([1, 0] : List (Fin 2)) l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_D_L_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft D l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft D (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l) r)
          (Cfg.headLeft D (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append ([1, 0] : List (Fin 2)) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append ([1, 0] : List (Fin 2)) r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
          (ListBlank.append ([1, 0] : List (Fin 2)) r) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_A_L_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft SixState.A (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft SixState.A l (ListBlank.append (([0, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft SixState.A
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l) r)
          (Cfg.headLeft SixState.A (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append ([0, 0] : List (Fin 2)) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append ([0, 0] : List (Fin 2)) r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 0] : List (Fin 2)) ^ k)
          (ListBlank.append ([0, 0] : List (Fin 2)) r) =
          ListBlank.append (([0, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem sweep_A_L_01_w1000 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft SixState.A (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append ([1, 0, 0, 0] : List (Fin 2)) r))
      (Cfg.headLeft SixState.A l
        (ListBlank.append ([1, 0, 0, 0] : List (Fin 2))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft SixState.A
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l)
            (ListBlank.append ([1, 0, 0, 0] : List (Fin 2)) r))
          (Cfg.headLeft SixState.A (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append ([1, 0, 0, 0] : List (Fin 2))
              (ListBlank.append ([0, 1] : List (Fin 2)) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append ([0, 1] : List (Fin 2)) r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
          (ListBlank.append ([0, 1] : List (Fin 2)) r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

local macro "bb_exec" : tactic =>
  `(tactic| (
    try simp only [list_pow_zero, list_pow_succ, List.nil_append, List.append_nil,
      ListBlank.append_nil, List.cons_append, ListBlank.append_cons,
      ListBlank.cons_zero_default, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default_fin, ListBlank.tail_default]
    bb_steps))

local macro "bb_eq" : tactic =>
  `(tactic| (
    first
    | rfl
    | simp only [Cfg.headRight, Cfg.headLeft, list_pow_zero, list_pow_succ,
        List.nil_append, List.append_nil, ListBlank.append_nil, List.cons_append,
        ListBlank.append_cons, ListBlank.cons_zero_default, ListBlank.head_cons,
        ListBlank.tail_cons, ListBlank.head_default_fin, ListBlank.tail_default,
        merge_0, rot_0, sq_00, merge_01, rot_01, merge_10, rot_10, zero_pow_default]))

/-! ## Configuration Families and Macro-Transition Rules -/

def cfg_S0z (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append ([1] : List (Fin 2)) default)))
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ c)
        (ListBlank.append ([0, 1] : List (Fin 2)) default)))

def cfg_S0p (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append ([1] : List (Fin 2)) default)))
    (ListBlank.append
      ([0] : List (Fin 2))
      (ListBlank.append
        (([0] : List (Fin 2)) ^ b)
        (ListBlank.append
          ([1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1] : List (Fin 2)) default)))))

def cfg_T1 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1] : List (Fin 2)) default)))))

def cfg_T0 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 1] : List (Fin 2)) default)))))

def cfg_T11 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))))

def cfg_T3 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))))

def cfg_T10 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append
          ([1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))))

def cfg_Tn (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    default
    (ListBlank.append
      ([1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ j)
        (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)))

def cfg_Ea (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))

def cfg_Eb (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
        1] : List (Fin 2))
      (ListBlank.append
        (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append
          (([0] : List (Fin 2)) ^ t)
          (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))

def cfg_Ec (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0] : List (Fin 2))
      (ListBlank.append
        (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append ([1] : List (Fin 2)) default)))

def cfg_Ed (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    default
    (ListBlank.append
      ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
        1] : List (Fin 2))
      (ListBlank.append
        (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append
          (([0] : List (Fin 2)) ^ t)
          (ListBlank.append ([1] : List (Fin 2)) default))))

private theorem rule_S0z_0 (a : ℕ) :
    ReachesPlus target (cfg_S0z a 0) (cfg_T1 0 (2 * a + 3)) := by
  have h0 :
      ReachesPlus target
        (cfg_S0z a 0)
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append ([1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    unfold cfg_S0z
    bb_exec
  have h1 :=
    sweep_D_L_01 a
      (ListBlank.append ([1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight B
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([0, 0, 0, 0, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h3 :
      (Cfg.headRight B
        (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
        (ListBlank.append
          (([0, 0] : List (Fin 2)) ^ a)
          (ListBlank.append ([0, 0, 0, 0, 0, 1] : List (Fin 2)) default))) =
        (Cfg.headRight B
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * a))
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_eq
  have h4 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * a))
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * a))
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  rw [h3] at a2
  have a3 := a2.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ (2 * a))
            (ListBlank.append ([1] : List (Fin 2)) default)))) =
        (cfg_T1 0 (2 * a + 3)) := by
    unfold cfg_T1
    bb_eq
  rw [heq] at a3
  exact a3

private theorem rule_S0z_1 (a c : ℕ) :
    ReachesPlus target (cfg_S0z a (c + 1)) (cfg_S0p 0 (2 * a + 4) c) := by
  have h0 :
      ReachesPlus target
        (cfg_S0z a (c + 1))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append ([1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([0, 1] : List (Fin 2)) default)))) := by
    unfold cfg_S0z
    bb_exec
  have h1 :=
    sweep_D_L_01 a
      (ListBlank.append ([1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 0, 0, 0, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append ([0, 1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 0, 0, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight SixState.A
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ a)
              (ListBlank.append
                ([0, 0, 0, 0, 1, 0] : List (Fin 2))
                (ListBlank.append
                  (([1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append ([0, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
        (ListBlank.append
          ([0] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 0, 0, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([0, 1] : List (Fin 2)) default)))))) =
        (cfg_S0p 0 (2 * a + 4) c) := by
    unfold cfg_S0p
    bb_eq
  rw [heq] at a2
  exact a2

private theorem rule_S0p_2 (a c : ℕ) :
    ReachesPlus target (cfg_S0p a 0 c) (cfg_S0p 0 (2 * a + 1) (c + 4)) := by
  have h0 :
      ReachesPlus target
        (cfg_S0p a 0 c)
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1] : List (Fin 2)) default))) := by
    unfold cfg_S0p
    bb_exec
  have h1 :=
    sweep_B_R_10 c
      (ListBlank.append
        ([0, 1, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([0, 1, 1, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([0, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([0, 1, 1, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 c
      (ListBlank.append
        ([0, 1, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append
            ([0, 1, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight F
          (ListBlank.append
            ([1, 0, 1, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h5 :=
    sweep_F_R_01 c
      (ListBlank.append
        ([1, 0, 1, 1, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h6 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([1, 0, 1, 1, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([1, 0, 1, 1, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h7 :=
    sweep_D_L_10 c
      (ListBlank.append
        ([1, 0, 1, 1, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h8 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append
            ([1, 0, 1, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append ([1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h9 :=
    sweep_D_L_01 a
      (ListBlank.append ([1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
  have h10 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight SixState.A
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ a)
              (ListBlank.append
                ([0, 1, 0, 1, 0] : List (Fin 2))
                (ListBlank.append
                  (([1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have a9 := a8.trans_star h9
  have a10 := a9.trans h10
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
        (ListBlank.append
          ([0] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))))) =
        (cfg_S0p 0 (2 * a + 1) (c + 4)) := by
    unfold cfg_S0p
    bb_eq
  rw [heq] at a10
  exact a10

private theorem rule_S0p_3 (a c : ℕ) :
    ReachesPlus target (cfg_S0p a 1 c) (cfg_S0p (a + 2) 0 (c + 2)) := by
  have h0 :
      ReachesPlus target
        (cfg_S0p a 1 c)
        (Cfg.headRight B
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1] : List (Fin 2)) default))) := by
    unfold cfg_S0p
    bb_exec
  have h1 :=
    sweep_B_R_10 c
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([1, 0, 1, 1, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([0, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([1, 0, 1, 1, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 c
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight F
          (ListBlank.append
            ([1, 1, 1, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h5 :=
    sweep_F_R_01 c
      (ListBlank.append
        ([1, 1, 1, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h6 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([1, 1, 1, 1, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([0, 1, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append
              ([1, 1, 1, 1, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0, 1] : List (Fin 2)) ^ a)
                (ListBlank.append ([1] : List (Fin 2)) default))))
          (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h7 :=
    sweep_D_L_10 c
      (ListBlank.append
        ([1, 1, 1, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append ([1] : List (Fin 2)) default)))
      (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h8 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append
            ([1, 1, 1, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ a)
              (ListBlank.append ([1] : List (Fin 2)) default)))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append ([1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h9 :=
    sweep_E_L_01 a
      (ListBlank.append ([1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 0, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
  have h10 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight F
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h11 :=
    sweep_F_R_01 a
      (ListBlank.append ([1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 0, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
  have h12 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ a)
              (ListBlank.append ([1, 1] : List (Fin 2)) default)))
          (ListBlank.append
            ([0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have a9 := a8.trans_star h9
  have a10 := a9.trans h10
  have a11 := a10.trans_star h11
  have a12 := a11.trans h12
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append
          ([0, 1, 0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([1, 1] : List (Fin 2)) default)))
        (ListBlank.append
          ([0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) =
        (cfg_S0p (a + 2) 0 (c + 2)) := by
    unfold cfg_S0p
    bb_eq
  rw [heq] at a12
  exact a12

private theorem rule_S0p_4 (a c : ℕ) :
    ReachesPlus target (cfg_S0p a 2 c) (cfg_S0z (a + 2) c) := by
  have h0 :
      ReachesPlus target
        (cfg_S0p a 2 c)
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append ([1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 0, 1, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([0, 1] : List (Fin 2)) default)))) := by
    unfold cfg_S0p
    bb_exec
  have h1 :=
    sweep_E_L_01 a
      (ListBlank.append ([1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 0, 1, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append ([0, 1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 0, 1, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight F
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 0, 1, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h3 :=
    sweep_F_R_01 a
      (ListBlank.append ([1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 0, 1, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append ([0, 1] : List (Fin 2)) default)))
  have h4 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 0, 1, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([0, 1] : List (Fin 2)) default))))
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ a)
              (ListBlank.append ([1, 1] : List (Fin 2)) default)))
          (ListBlank.append
            ([1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append
          ([0, 1, 0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([1, 1] : List (Fin 2)) default)))
        (ListBlank.append
          ([1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append ([0, 1] : List (Fin 2)) default)))) =
        (cfg_S0z (a + 2) c) := by
    unfold cfg_S0z
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_S0p_5 (a b c : ℕ) :
    ReachesPlus target (cfg_S0p a (b + 3) c) (cfg_S0p (a + 2) b c) := by
  have h0 :
      ReachesPlus target
        (cfg_S0p a (b + 3) c)
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append ([1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ b)
              (ListBlank.append
                ([1, 0] : List (Fin 2))
                (ListBlank.append
                  (([1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append ([0, 1] : List (Fin 2)) default)))))) := by
    unfold cfg_S0p
    bb_exec
  have h1 :=
    sweep_E_L_01 a
      (ListBlank.append ([1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 0, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ b)
          (ListBlank.append
            ([1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([0, 1] : List (Fin 2)) default)))))
  have h2 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ b)
                (ListBlank.append
                  ([1, 0] : List (Fin 2))
                  (ListBlank.append
                    (([1, 0] : List (Fin 2)) ^ c)
                    (ListBlank.append ([0, 1] : List (Fin 2)) default)))))))
        (Cfg.headRight F
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append
              ([0, 1, 0, 0, 1, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ b)
                (ListBlank.append
                  ([1, 0] : List (Fin 2))
                  (ListBlank.append
                    (([1, 0] : List (Fin 2)) ^ c)
                    (ListBlank.append ([0, 1] : List (Fin 2)) default))))))) := by
    bb_exec
  have h3 :=
    sweep_F_R_01 a
      (ListBlank.append ([1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 0, 1, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ b)
          (ListBlank.append
            ([1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append ([0, 1] : List (Fin 2)) default)))))
  have h4 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ b)
              (ListBlank.append
                ([1, 0] : List (Fin 2))
                (ListBlank.append
                  (([1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append ([0, 1] : List (Fin 2)) default))))))
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ a)
              (ListBlank.append ([1, 1] : List (Fin 2)) default)))
          (ListBlank.append
            ([0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ b)
              (ListBlank.append
                ([1, 0] : List (Fin 2))
                (ListBlank.append
                  (([1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append ([0, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append
          ([0, 1, 0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ a)
            (ListBlank.append ([1, 1] : List (Fin 2)) default)))
        (ListBlank.append
          ([0] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ b)
            (ListBlank.append
              ([1, 0] : List (Fin 2))
              (ListBlank.append
                (([1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append ([0, 1] : List (Fin 2)) default)))))) =
        (cfg_S0p (a + 2) b c) := by
    unfold cfg_S0p
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T1_6 (j : ℕ) :
    ReachesPlus target (cfg_T1 j 0) (cfg_Tn 0) := by
  have h0 :
      ReachesPlus target
        (cfg_T1 j 0)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T1
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          default) := by
    bb_exec
  have h3 :=
    sweep_D_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      default
  have h4 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append (([0, 0] : List (Fin 2)) ^ j) default))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append (([0, 0] : List (Fin 2)) ^ j) default))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append (([0, 0] : List (Fin 2)) ^ j) default))) =
        (cfg_Tn 0) := by
    unfold cfg_Tn
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T1_7 (j : ℕ) :
    ReachesPlus target (cfg_T1 j 1) (cfg_T11 0 (2 * j + 7)) := by
  have h0 :
      ReachesPlus target
        (cfg_T1 j 1)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T1
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight F
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h5 :=
    sweep_F_R_01 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h6 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft SixState.A
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h7 :=
    sweep_A_L_10 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)
  have h8 :
      ReachesPlus target
        (Cfg.headLeft SixState.A
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) =
        (cfg_T11 0 (2 * j + 7)) := by
    unfold cfg_T11
    bb_eq
  rw [heq] at a8
  exact a8

private theorem rule_T1_8 (j : ℕ) :
    ReachesPlus target (cfg_T1 j 2) (cfg_S0p 0 (2 * j + 5) 3) := by
  have h0 :
      ReachesPlus target
        (cfg_T1 j 2)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T1
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_D_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              default)))
        (Cfg.headRight SixState.A
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append
                ([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
                default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
        (ListBlank.append
          ([0, 0, 0] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              default)))) =
        (cfg_S0p 0 (2 * j + 5) 3) := by
    unfold cfg_S0p
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T1_9 (j m : ℕ) :
    ReachesPlus target (cfg_T1 j (m + 3)) (cfg_T1 (j + 2) m) := by
  have h0 :
      ReachesPlus target
        (cfg_T1 j (m + 3))
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    unfold cfg_T1
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1] : List (Fin 2)) default)))
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append
                ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
                (ListBlank.append
                  (([0] : List (Fin 2)) ^ m)
                  (ListBlank.append ([1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1] : List (Fin 2)) default)))))) =
        (cfg_T1 (j + 2) m) := by
    unfold cfg_T1
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T0_10 (j : ℕ) :
    ReachesPlus target (cfg_T0 j 0) (cfg_S0z (j + 1) 0) := by
  have h0 :
      ReachesPlus target
        (cfg_T0 j 0)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T0
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 1, 1] : List (Fin 2)) default))
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
          (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append
          ([0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
        (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)) =
        (cfg_S0z (j + 1) 0) := by
    unfold cfg_S0z
    bb_eq
  rw [heq] at a2
  exact a2

private theorem halt_T0_11 (j : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T0 j 1) cfg' ∧ (step target cfg').isNone := by
  refine ⟨(Cfg.headRight F
      (ListBlank.append
        ([1, 1, 0, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
      (ListBlank.append ([1] : List (Fin 2)) default)),
    ?_, by bb_halt⟩
  have h0 :
      ReachesPlus target
        (cfg_T0 j 1)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T0
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headRight F
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
          (ListBlank.append ([1] : List (Fin 2)) default)) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  exact a2

private theorem rule_T0_12 (j : ℕ) :
    ReachesPlus target (cfg_T0 j 2) (cfg_S0z (j + 2) 0) := by
  have h0 :
      ReachesPlus target
        (cfg_T0 j 2)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T0
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight F
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h5 :=
    sweep_F_R_01 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1] : List (Fin 2)) default)
  have h6 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1] : List (Fin 2)) default))
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))
          (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append
          ([0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))
        (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)) =
        (cfg_S0z (j + 2) 0) := by
    unfold cfg_S0z
    bb_eq
  rw [heq] at a6
  exact a6

private theorem rule_T0_13 (j m : ℕ) :
    ReachesPlus target (cfg_T0 j (m + 3)) (cfg_T0 (j + 2) m) := by
  have h0 :
      ReachesPlus target
        (cfg_T0 j (m + 3))
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 1] : List (Fin 2)) default))))) := by
    unfold cfg_T0
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 1] : List (Fin 2)) default))))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 1] : List (Fin 2)) default)))
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append
                ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
                (ListBlank.append
                  (([0] : List (Fin 2)) ^ m)
                  (ListBlank.append ([1, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 1] : List (Fin 2)) default)))))) =
        (cfg_T0 (j + 2) m) := by
    unfold cfg_T0
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T11_14 (j : ℕ) :
    ReachesPlus target (cfg_T11 j 0) (cfg_T1 0 (2 * j + 6)) := by
  have h0 :
      ReachesPlus target
        (cfg_T11 j 0)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T11
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_D_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))) =
        (cfg_T1 0 (2 * j + 6)) := by
    unfold cfg_T1
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T11_15 (j : ℕ) :
    ReachesPlus target (cfg_T11 j 1) (cfg_T3 0 (2 * j + 7)) := by
  have h0 :
      ReachesPlus target
        (cfg_T11 j 1)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T11
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight F
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h5 :=
    sweep_F_R_01 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h6 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft SixState.A
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h7 :=
    sweep_A_L_10 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)
  have h8 :
      ReachesPlus target
        (Cfg.headLeft SixState.A
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)))) =
        (cfg_T3 0 (2 * j + 7)) := by
    unfold cfg_T3
    bb_eq
  rw [heq] at a8
  exact a8

private theorem rule_T11_16 (j : ℕ) :
    ReachesPlus target (cfg_T11 j 2) (cfg_Ea j) := by
  have h0 :
      ReachesPlus target
        (cfg_T11 j 2)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T11
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft SixState.A
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_A_L_01_w1000 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft SixState.A
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight SixState.A
          default
          (ListBlank.append
            ([1, 1, 0, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight SixState.A
        default
        (ListBlank.append
          ([1, 1, 0, 0, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) =
        (cfg_Ea j) := by
    unfold cfg_Ea
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T11_17 (j m : ℕ) :
    ReachesPlus target (cfg_T11 j (m + 3)) (cfg_T11 (j + 2) m) := by
  have h0 :
      ReachesPlus target
        (cfg_T11 j (m + 3))
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 1] : List (Fin 2)) default))))) := by
    unfold cfg_T11
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append
                ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
                (ListBlank.append
                  (([0] : List (Fin 2)) ^ m)
                  (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 1] : List (Fin 2)) default)))))) =
        (cfg_T11 (j + 2) m) := by
    unfold cfg_T11
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T3_18 (j : ℕ) :
    ReachesPlus target (cfg_T3 j 0) (cfg_T1 0 (2 * j + 8)) := by
  have h0 :
      ReachesPlus target
        (cfg_T3 j 0)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T3
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 1, 0, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_D_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 0, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 0, 0, 1] : List (Fin 2)) default)))) =
        (cfg_T1 0 (2 * j + 8)) := by
    unfold cfg_T1
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T3_19 (j : ℕ) :
    ReachesPlus target (cfg_T3 j 1) (cfg_T10 0 (2 * j + 7)) := by
  have h0 :
      ReachesPlus target
        (cfg_T3 j 1)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T3
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)))
        (Cfg.headRight F
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h5 :=
    sweep_F_R_01 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)
  have h6 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headLeft SixState.A
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h7 :=
    sweep_A_L_10 j
      (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)
  have h8 :
      ReachesPlus target
        (Cfg.headLeft SixState.A
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)))) =
        (cfg_T10 0 (2 * j + 7)) := by
    unfold cfg_T10
    bb_eq
  rw [heq] at a8
  exact a8

private theorem rule_T3_20 (j : ℕ) :
    ReachesPlus target (cfg_T3 j 2) (cfg_Ec j) := by
  have h0 :
      ReachesPlus target
        (cfg_T3 j 2)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_T3
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft SixState.A
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_A_L_01_w1000 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft SixState.A
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1] : List (Fin 2)) default))))
        (Cfg.headRight SixState.A
          default
          (ListBlank.append
            ([1, 1, 0, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight SixState.A
        default
        (ListBlank.append
          ([1, 1, 0, 0, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1] : List (Fin 2)) default)))) =
        (cfg_Ec j) := by
    unfold cfg_Ec
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T3_21 (j m : ℕ) :
    ReachesPlus target (cfg_T3 j (m + 3)) (cfg_T3 (j + 2) m) := by
  have h0 :
      ReachesPlus target
        (cfg_T3 j (m + 3))
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default))))) := by
    unfold cfg_T3
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default))))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append
                ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
                (ListBlank.append
                  (([0] : List (Fin 2)) ^ m)
                  (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 0, 0, 1] : List (Fin 2)) default)))))) =
        (cfg_T3 (j + 2) m) := by
    unfold cfg_T3
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_T10_22 (j : ℕ) :
    ReachesPlus target (cfg_T10 j 0) (cfg_T0 0 (2 * j + 6)) := by
  have h0 :
      ReachesPlus target
        (cfg_T10 j 0)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 1, 0, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T10
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 1, 0, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 1, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_D_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) default)))) =
        (cfg_T0 0 (2 * j + 6)) := by
    unfold cfg_T0
    bb_eq
  rw [heq] at a4
  exact a4

private theorem halt_T10_23 (j : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T10 j 1) cfg' ∧ (step target cfg').isNone := by
  refine ⟨(Cfg.headRight F
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
      (ListBlank.append ([1] : List (Fin 2)) default)),
    ?_, by bb_halt⟩
  have h0 :
      ReachesPlus target
        (cfg_T10 j 1)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T10
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headRight F
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
          (ListBlank.append ([1] : List (Fin 2)) default)) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  exact a2

private theorem halt_T10_24 (j : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T10 j 2) cfg' ∧ (step target cfg').isNone := by
  refine ⟨(Cfg.headRight F
      (ListBlank.append
        ([1, 1, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
      (ListBlank.append ([1] : List (Fin 2)) default)),
    ?_, by bb_halt⟩
  have h0 :
      ReachesPlus target
        (cfg_T10 j 2)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default))) := by
    unfold cfg_T10
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1, 0, 0, 1, 0, 1, 1] : List (Fin 2)) default))
        (Cfg.headRight F
          (ListBlank.append
            ([1, 1, 0, 1, 1, 0, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
          (ListBlank.append ([1] : List (Fin 2)) default)) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  exact a2

private theorem rule_T10_25 (j m : ℕ) :
    ReachesPlus target (cfg_T10 j (m + 3)) (cfg_T10 (j + 2) m) := by
  have h0 :
      ReachesPlus target
        (cfg_T10 j (m + 3))
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))))) := by
    unfold cfg_T10
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([1, 0, 0, 1, 0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default))))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append
            ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append
        ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0] : List (Fin 2)) ^ m)
          (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append
                ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
                (ListBlank.append
                  (([0] : List (Fin 2)) ^ m)
                  (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append
              ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
              (ListBlank.append
                (([0] : List (Fin 2)) ^ m)
                (ListBlank.append ([1, 0, 1, 1] : List (Fin 2)) default)))))) =
        (cfg_T10 (j + 2) m) := by
    unfold cfg_T10
    bb_eq
  rw [heq] at a4
  exact a4

private theorem rule_Tn_26 (j : ℕ) :
    ReachesPlus target (cfg_Tn j) (cfg_Tn (j + 2)) := by
  have h0 :
      ReachesPlus target
        (cfg_Tn j)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_Tn
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) =
        (cfg_Tn (j + 2)) := by
    unfold cfg_Tn
    bb_eq
  rw [heq] at a4
  exact a4

set_option maxHeartbeats 600000 in
-- 14-step macro-transition over a 29-symbol word requires additional heartbeats
private theorem rule_Ea_27 (n : ℕ) :
    ReachesPlus target (cfg_Ea n) (cfg_Eb 0 (2 * n + 1)) := by
  have h0 :
      ReachesPlus target
        (cfg_Ea n)
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    unfold cfg_Ea
    bb_exec
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h4 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h5 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight B
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ n)
            (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h6 :=
    sweep_B_R_10 n
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
          1] : List (Fin 2))
        default)
      (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default)
  have h7 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ n)
            (ListBlank.append
              ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
                1] : List (Fin 2))
              default))
          (ListBlank.append ([1, 0, 0, 0, 1, 0, 1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ n)
            (ListBlank.append
              ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
                1] : List (Fin 2))
              default))
          (ListBlank.append ([0, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h8 :=
    sweep_D_L_01 n
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
          1] : List (Fin 2))
        default)
      (ListBlank.append ([0, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default)
  have h9 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ n)
            (ListBlank.append ([0, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ n)
            (ListBlank.append ([0, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h10 :
      (Cfg.headRight B
        (ListBlank.append
          ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
            1] : List (Fin 2))
          default)
        (ListBlank.append
          (([0, 0] : List (Fin 2)) ^ n)
          (ListBlank.append ([0, 0, 0, 1, 1, 0, 1] : List (Fin 2)) default))) =
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_eq
  have h11 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight D
          (ListBlank.append
            ([1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h12 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append
            ([1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight B
          (ListBlank.append ([1, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have h13 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append ([1, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))
        (Cfg.headRight SixState.A
          default
          (ListBlank.append
            ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans h1
  have a2 := a1.trans h2
  have a3 := a2.trans h3
  have a4 := a3.trans h4
  have a5 := a4.trans h5
  have a6 := a5.trans_star h6
  have a7 := a6.trans h7
  have a8 := a7.trans_star h8
  have a9 := a8.trans h9
  rw [h10] at a9
  have a10 := a9.trans h11
  have a11 := a10.trans h12
  have a12 := a11.trans h13
  have heq :
      (Cfg.headRight SixState.A
        default
        (ListBlank.append
          ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0,
            0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ (2 * n))
            (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))) =
        (cfg_Eb 0 (2 * n + 1)) := by
    unfold cfg_Eb
    bb_eq
  rw [heq] at a12
  exact a12

set_option maxHeartbeats 600000 in
-- 14-step macro-transition over a 29-symbol word requires additional heartbeats
private theorem rule_Eb_28 (k t : ℕ) :
    ReachesPlus target (cfg_Eb k t) (cfg_Eb (k + 1) t) := by
  have h0 :
      ReachesPlus target
        (cfg_Eb k t)
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    unfold cfg_Eb
    bb_exec
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h4 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h5 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h6 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight C
          (ListBlank.append
            ([1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h7 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append
            ([1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          (ListBlank.append ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h8 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight C
          (ListBlank.append ([1, 0, 1, 1, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have h9 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append ([1, 0, 1, 1, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default)))))
        (Cfg.headRight SixState.A
          default
          (ListBlank.append
            ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans h1
  have a2 := a1.trans h2
  have a3 := a2.trans h3
  have a4 := a3.trans h4
  have a5 := a4.trans h5
  have a6 := a5.trans h6
  have a7 := a6.trans h7
  have a8 := a7.trans h8
  have a9 := a8.trans h9
  have heq :
      (Cfg.headRight SixState.A
        default
        (ListBlank.append
          ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0,
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
            1] : List (Fin 2))
          (ListBlank.append
            (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append
              (([0] : List (Fin 2)) ^ t)
              (ListBlank.append ([1, 1, 0, 1] : List (Fin 2)) default))))) =
        (cfg_Eb (k + 1) t) := by
    unfold cfg_Eb
    bb_eq
  rw [heq] at a9
  exact a9

set_option maxHeartbeats 600000 in
-- 14-step macro-transition over a 29-symbol word requires additional heartbeats
private theorem rule_Ec_29 (n : ℕ) :
    ReachesPlus target (cfg_Ec n) (cfg_Ed 0 (2 * n + 1)) := by
  have h0 :
      ReachesPlus target
        (cfg_Ec n)
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    unfold cfg_Ec
    bb_exec
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h4 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h5 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([1, 0] : List (Fin 2)) ^ n)
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight B
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ n)
            (ListBlank.append ([1] : List (Fin 2)) default))) := by
    bb_exec
  have h6 :=
    sweep_B_R_10 n
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
          1] : List (Fin 2))
        default)
      (ListBlank.append ([1] : List (Fin 2)) default)
  have h7 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ n)
            (ListBlank.append
              ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
                1] : List (Fin 2))
              default))
          (ListBlank.append ([1] : List (Fin 2)) default))
        (Cfg.headLeft D
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ n)
            (ListBlank.append
              ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
                1] : List (Fin 2))
              default))
          (ListBlank.append ([0, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  have h8 :=
    sweep_D_L_01 n
      (ListBlank.append
        ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
          1] : List (Fin 2))
        default)
      (ListBlank.append ([0, 0, 0, 1] : List (Fin 2)) default)
  have h9 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append
            ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ n)
            (ListBlank.append ([0, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            (([0, 0] : List (Fin 2)) ^ n)
            (ListBlank.append ([0, 0, 0, 1] : List (Fin 2)) default))) := by
    bb_exec
  have h10 :
      (Cfg.headRight B
        (ListBlank.append
          ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
            1] : List (Fin 2))
          default)
        (ListBlank.append
          (([0, 0] : List (Fin 2)) ^ n)
          (ListBlank.append ([0, 0, 0, 1] : List (Fin 2)) default))) =
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_eq
  have h11 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight D
          (ListBlank.append
            ([1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h12 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append
            ([1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight B
          (ListBlank.append ([1, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have h13 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append ([1, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1,
              0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default))))
        (Cfg.headRight SixState.A
          default
          (ListBlank.append
            ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              0, 0, 1, 0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ (2 * n))
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans h1
  have a2 := a1.trans h2
  have a3 := a2.trans h3
  have a4 := a3.trans h4
  have a5 := a4.trans h5
  have a6 := a5.trans_star h6
  have a7 := a6.trans h7
  have a8 := a7.trans_star h8
  have a9 := a8.trans h9
  rw [h10] at a9
  have a10 := a9.trans h11
  have a11 := a10.trans h12
  have a12 := a11.trans h13
  have heq :
      (Cfg.headRight SixState.A
        default
        (ListBlank.append
          ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0,
            0, 1, 0] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ (2 * n))
            (ListBlank.append ([1] : List (Fin 2)) default)))) =
        (cfg_Ed 0 (2 * n + 1)) := by
    unfold cfg_Ed
    bb_eq
  rw [heq] at a12
  exact a12

set_option maxHeartbeats 600000 in
-- 14-step macro-transition over a 29-symbol word requires additional heartbeats
private theorem rule_Ed_30 (k t : ℕ) :
    ReachesPlus target (cfg_Ed k t) (cfg_Ed (k + 1) t) := by
  have h0 :
      ReachesPlus target
        (cfg_Ed k t)
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    unfold cfg_Ed
    bb_exec
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append ([1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          default
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h4 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
              1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h5 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h6 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
              0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2))
            default)
          (ListBlank.append
            ([1, 0, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight C
          (ListBlank.append
            ([1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h7 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append
            ([1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
              1] : List (Fin 2))
            default)
          (ListBlank.append
            ([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight E
          (ListBlank.append ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h8 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight C
          (ListBlank.append ([1, 0, 1, 1, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have h9 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append ([1, 0, 1, 1, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default)))))
        (Cfg.headRight SixState.A
          default
          (ListBlank.append
            ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
              0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
              1] : List (Fin 2))
            (ListBlank.append
              (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append
                (([0] : List (Fin 2)) ^ t)
                (ListBlank.append ([1] : List (Fin 2)) default))))) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans h1
  have a2 := a1.trans h2
  have a3 := a2.trans h3
  have a4 := a3.trans h4
  have a5 := a4.trans h5
  have a6 := a5.trans h6
  have a7 := a6.trans h7
  have a8 := a7.trans h8
  have a9 := a8.trans h9
  have heq :
      (Cfg.headRight SixState.A
        default
        (ListBlank.append
          ([1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0,
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
            1] : List (Fin 2))
          (ListBlank.append
            (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append
              (([0] : List (Fin 2)) ^ t)
              (ListBlank.append ([1] : List (Fin 2)) default))))) =
        (cfg_Ed (k + 1) t) := by
    unfold cfg_Ed
    bb_eq
  rw [heq] at a9
  exact a9

private def cfg_T1s (b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ 2)
        (ListBlank.append ([1] : List (Fin 2)) default)))
    (ListBlank.append
      ([0] : List (Fin 2))
      (ListBlank.append
        (([0] : List (Fin 2)) ^ b)
        (ListBlank.append ([1, 0] : List (Fin 2)) default)))

private def cfg_Tns (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight SixState.A
    (ListBlank.append
      ([0, 1] : List (Fin 2))
      (ListBlank.append
        (([0, 1] : List (Fin 2)) ^ (j + 2))
        (ListBlank.append ([1] : List (Fin 2)) default)))
    default

private theorem to_T1s (b : ℕ) :
    ReachesPlus target (cfg_T1 0 (b + 1)) (cfg_T1s b) := by
  have h0 :
      ReachesPlus target
        (cfg_T1 0 (b + 1))
        (Cfg.headRight SixState.A
          (ListBlank.append ([0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            ([0] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ b)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    unfold cfg_T1
    bb_exec
  have heq :
      (Cfg.headRight SixState.A
        (ListBlank.append ([0, 1, 0, 1, 0, 1, 1] : List (Fin 2)) default)
        (ListBlank.append
          ([0] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ b)
            (ListBlank.append ([1] : List (Fin 2)) default)))) =
        (cfg_T1s b) := by
    unfold cfg_T1s
    bb_eq
  rw [heq] at h0
  exact h0

private theorem rule_T1s_0 :
    ReachesPlus target (cfg_T1s 0) (cfg_T11 0 7) := by
  unfold cfg_T1s cfg_T11
  bb_exec

private theorem rule_T1s_1 :
    ReachesPlus target (cfg_T1s 1) (cfg_S0p 0 5 3) := by
  unfold cfg_T1s cfg_S0p
  bb_exec

private theorem rule_T1s_2 (m : ℕ) :
    ReachesPlus target (cfg_T1s (m + 2)) (cfg_T1 2 m) := by
  have h0 :
      ReachesPlus target
        (cfg_T1s (m + 2))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0] : List (Fin 2)) ^ m)
              (ListBlank.append ([1] : List (Fin 2)) default)))) := by
    unfold cfg_T1s
    bb_exec
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0] : List (Fin 2)) ^ m)
            (ListBlank.append ([1] : List (Fin 2)) default)))) =
        (cfg_T1 2 m) := by
    unfold cfg_T1
    bb_eq
  rw [heq] at h0
  exact h0

private theorem eq_Tns (j : ℕ) :
    (Cfg.headRight SixState.A
      (ListBlank.append
        ([0, 1, 0, 1] : List (Fin 2))
        (ListBlank.append
          (([0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
      default) =
      (cfg_Tns j) := by
  unfold cfg_Tns
  bb_eq

private theorem to_Tns (j : ℕ) :
    ReachesPlus target (cfg_Tn j) (cfg_Tns j) := by
  have h0 :
      ReachesPlus target
        (cfg_Tn j)
        (Cfg.headRight B
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([1, 0] : List (Fin 2)) ^ j)
            (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default))) := by
    unfold cfg_Tn
    bb_exec
  have h1 :=
    sweep_B_R_10 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) default))
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
          default) := by
    bb_exec
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  rw [eq_Tns j] at a2
  exact a2

private theorem from_Tns (j : ℕ) :
    ReachesPlus target (cfg_Tns j) (cfg_Tn (j + 2)) := by
  have h2 :
      ReachesPlus target
        (Cfg.headRight SixState.A
          (ListBlank.append
            ([0, 1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)))
          default)
        (Cfg.headLeft E
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 1] : List (Fin 2)) default))
          (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)) := by
    bb_exec
  rw [eq_Tns j] at h2
  have h3 :=
    sweep_E_L_01 j
      (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
      (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append ([0, 1, 1] : List (Fin 2)) default)
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))
        (Cfg.headRight E
          default
          (ListBlank.append
            ([1, 0, 1] : List (Fin 2))
            (ListBlank.append
              (([0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) := by
    bb_exec
  have a3 := h2.trans_star h3
  have a4 := a3.trans h4
  have heq :
      (Cfg.headRight E
        default
        (ListBlank.append
          ([1, 0, 1] : List (Fin 2))
          (ListBlank.append
            (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append ([0, 1, 0, 1, 0, 0, 1] : List (Fin 2)) default)))) =
        (cfg_Tn (j + 2)) := by
    unfold cfg_Tn
    bb_eq
  rw [heq] at a4
  exact a4

/-! ## Closed Pattern Set (`IsClosedPatternSet`, Level A) -/

def pat_S0p_T1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some SixState.A
    right := .sym 0 (.rep [0] 1 (.rep [1, 0] 2 (.rep [0, 1] 3 .default))) }

def cond_S0p_T1 : VarCond :=
  .or (.and (.ge_const 3 1) (.and (.not (.ge_const 3 2)) (.ge_const 2 1)))
    (.or
      (.and (.not (.ge_const 3 1))
        (.and (.ge_const 2 1)
          (.and (.not (.ge_const 2 2))
            (.and (.ge_const 0 2) (.not (.ge_const 0 3))))))
      (.and (.not (.ge_const 3 1))
        (.and (.not (.ge_const 2 1))
          (.and (.not (.ge_const 1 1)) (.ge_const 0 2)))))

def pat_Ebd : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some SixState.A
    right :=
      .sym 1
        (.rep
          [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
          3
          (.rep [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] 0
            (.rep [0] 1 (.sym 1 (.rep [1, 0, 1] 2 .default))))) }

def cond_Ebd : VarCond :=
  .and (.not (.ge_const 2 2)) (.and (.ge_const 3 1) (.not (.ge_const 3 2)))

/-- Two-pattern closed invariant set for `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_S0p_T1, cond_S0p_T1), (pat_Ebd, cond_Ebd)]

private theorem eval_pat_S0p (vars : ℕ → ℕ) (c : ℕ)
    (h2 : vars 2 = c + 1) (h3 : vars 3 = 1) :
    evalTapePattern pat_S0p_T1 vars = cfg_S0p (vars 0) (vars 1) c := by
  simp only [pat_S0p_T1, cfg_S0p, evalTapePattern, evalTapeExpr, h2, h3]
  bb_eq

private theorem eval_pat_T1s (vars : ℕ → ℕ)
    (h0 : vars 0 = 2) (h2 : vars 2 = 1) (h3 : vars 3 = 0) :
    evalTapePattern pat_S0p_T1 vars = cfg_T1s (vars 1) := by
  simp only [pat_S0p_T1, cfg_T1s, evalTapePattern, evalTapeExpr, h0, h2, h3]
  bb_eq

private theorem eval_pat_Tns (vars : ℕ → ℕ) (j : ℕ)
    (h0 : vars 0 = j + 2) (h1 : vars 1 = 0) (h2 : vars 2 = 0) (h3 : vars 3 = 0) :
    evalTapePattern pat_S0p_T1 vars = cfg_Tns j := by
  simp only [pat_S0p_T1, cfg_Tns, evalTapePattern, evalTapeExpr, h0, h1, h2, h3]
  bb_eq

private theorem eval_pat_Ebd_0 (vars : ℕ → ℕ) (h2 : vars 2 = 0) (h3 : vars 3 = 1) :
    evalTapePattern pat_Ebd vars = cfg_Ed (vars 0) (vars 1) := by
  simp only [pat_Ebd, cfg_Ed, evalTapePattern, evalTapeExpr, h2, h3]
  rfl

private theorem eval_pat_Ebd_1 (vars : ℕ → ℕ) (h2 : vars 2 = 1) (h3 : vars 3 = 1) :
    evalTapePattern pat_Ebd vars = cfg_Eb (vars 0) (vars 1) := by
  simp only [pat_Ebd, cfg_Eb, evalTapePattern, evalTapeExpr, h2, h3]
  rfl

private theorem mem_S0p (a b c : ℕ) : IsInPatternSet ps (cfg_S0p a b c) := by
  let vars : ℕ → ℕ := fun i => match i with | 0 => a | 1 => b | 2 => c + 1 | 3 => 1 | _ => 0
  refine ⟨(pat_S0p_T1, cond_S0p_T1), List.Mem.head _, vars,
    (eval_pat_S0p vars c rfl rfl).symm, ?_⟩
  simp only [cond_S0p_T1, evalVarCond, vars]
  omega

private theorem mem_T1s (b : ℕ) : IsInPatternSet ps (cfg_T1s b) := by
  let vars : ℕ → ℕ := fun i => match i with | 0 => 2 | 1 => b | 2 => 1 | _ => 0
  refine ⟨(pat_S0p_T1, cond_S0p_T1), List.Mem.head _, vars,
    (eval_pat_T1s vars rfl rfl rfl).symm, ?_⟩
  simp only [cond_S0p_T1, evalVarCond, vars]
  omega

private theorem mem_Tns (j : ℕ) : IsInPatternSet ps (cfg_Tns j) := by
  let vars : ℕ → ℕ := fun i => match i with | 0 => j + 2 | _ => 0
  refine ⟨(pat_S0p_T1, cond_S0p_T1), List.Mem.head _, vars,
    (eval_pat_Tns vars j rfl rfl rfl rfl).symm, ?_⟩
  simp only [cond_S0p_T1, evalVarCond, vars]
  omega

private theorem mem_Eb (k t : ℕ) : IsInPatternSet ps (cfg_Eb k t) := by
  refine ⟨(pat_Ebd, cond_Ebd), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => k | 1 => t | 2 => 1 | 3 => 1 | _ => 0,
    rfl, show ¬ (1 ≥ 2) ∧ (1 ≥ 1 ∧ ¬ (1 ≥ 2)) from by decide⟩

private theorem mem_Ed (k t : ℕ) : IsInPatternSet ps (cfg_Ed k t) := by
  refine ⟨(pat_Ebd, cond_Ebd), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => k | 1 => t | 2 => 0 | 3 => 1 | _ => 0,
    rfl, show ¬ (0 ≥ 2) ∧ (1 ≥ 1 ∧ ¬ (1 ≥ 2)) from by decide⟩

private theorem step_S0z (a c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_S0z a c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c
  · exact ⟨cfg_T1s (2 * a + 2), (rule_S0z_0 a).trans (to_T1s (2 * a + 2)),
      Or.inl (mem_T1s (2 * a + 2))⟩
  · exact ⟨cfg_S0p 0 (2 * a + 4) c, rule_S0z_1 a c, Or.inl (mem_S0p 0 (2 * a + 4) c)⟩

private theorem step_S0p (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_S0p a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | _ | b
  · exact ⟨cfg_S0p 0 (2 * a + 1) (c + 4), rule_S0p_2 a c,
      Or.inl (mem_S0p 0 (2 * a + 1) (c + 4))⟩
  · exact ⟨cfg_S0p (a + 2) 0 (c + 2), rule_S0p_3 a c,
      Or.inl (mem_S0p (a + 2) 0 (c + 2))⟩
  · obtain ⟨cfg', h1, h2⟩ := step_S0z (a + 2) c
    exact ⟨cfg', (rule_S0p_4 a c).trans h1, h2⟩
  · exact ⟨cfg_S0p (a + 2) b c, rule_S0p_5 a b c, Or.inl (mem_S0p (a + 2) b c)⟩

private theorem step_T0 (j m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T0 j m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction m using Nat.strongRecOn generalizing j with
  | ind m ih =>
    rcases m with _ | _ | _ | m
    · obtain ⟨cfg', h1, h2⟩ := step_S0z (j + 1) 0
      exact ⟨cfg', (rule_T0_10 j).trans h1, h2⟩
    · obtain ⟨cfg', hh1, hh2⟩ := halt_T0_11 j
      exact ⟨cfg', hh1, Or.inr hh2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_S0z (j + 2) 0
      exact ⟨cfg', (rule_T0_12 j).trans h1, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := ih m (by omega) (j + 2)
      exact ⟨cfg', (rule_T0_13 j m).trans h1, h2⟩

private theorem step_T10 (j m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T10 j m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction m using Nat.strongRecOn generalizing j with
  | ind m ih =>
    rcases m with _ | _ | _ | m
    · obtain ⟨cfg', h1, h2⟩ := step_T0 0 (2 * j + 6)
      exact ⟨cfg', (rule_T10_22 j).trans h1, h2⟩
    · obtain ⟨cfg', hh1, hh2⟩ := halt_T10_23 j
      exact ⟨cfg', hh1, Or.inr hh2⟩
    · obtain ⟨cfg', hh1, hh2⟩ := halt_T10_24 j
      exact ⟨cfg', hh1, Or.inr hh2⟩
    · obtain ⟨cfg', h1, h2⟩ := ih m (by omega) (j + 2)
      exact ⟨cfg', (rule_T10_25 j m).trans h1, h2⟩

private theorem step_Ea (n : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Ea n) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  ⟨cfg_Eb 0 (2 * n + 1), rule_Ea_27 n, Or.inl (mem_Eb 0 (2 * n + 1))⟩

private theorem step_Eb (k t : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Eb k t) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  ⟨cfg_Eb (k + 1) t, rule_Eb_28 k t, Or.inl (mem_Eb (k + 1) t)⟩

private theorem step_Ec (n : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Ec n) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  ⟨cfg_Ed 0 (2 * n + 1), rule_Ec_29 n, Or.inl (mem_Ed 0 (2 * n + 1))⟩

private theorem step_Ed (k t : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Ed k t) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  ⟨cfg_Ed (k + 1) t, rule_Ed_30 k t, Or.inl (mem_Ed (k + 1) t)⟩

private theorem step_T3 (j m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T3 j m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction m using Nat.strongRecOn generalizing j with
  | ind m ih =>
    rcases m with _ | _ | _ | m
    · exact ⟨cfg_T1s (2 * j + 7), (rule_T3_18 j).trans (to_T1s (2 * j + 7)),
        Or.inl (mem_T1s (2 * j + 7))⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T10 0 (2 * j + 7)
      exact ⟨cfg', (rule_T3_19 j).trans h1, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_Ec j
      exact ⟨cfg', (rule_T3_20 j).trans h1, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := ih m (by omega) (j + 2)
      exact ⟨cfg', (rule_T3_21 j m).trans h1, h2⟩

private theorem step_T11 (j m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T11 j m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction m using Nat.strongRecOn generalizing j with
  | ind m ih =>
    rcases m with _ | _ | _ | m
    · exact ⟨cfg_T1s (2 * j + 5), (rule_T11_14 j).trans (to_T1s (2 * j + 5)),
        Or.inl (mem_T1s (2 * j + 5))⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T3 0 (2 * j + 7)
      exact ⟨cfg', (rule_T11_15 j).trans h1, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_Ea j
      exact ⟨cfg', (rule_T11_16 j).trans h1, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := ih m (by omega) (j + 2)
      exact ⟨cfg', (rule_T11_17 j m).trans h1, h2⟩

private theorem step_T1 (j m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T1 j m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction m using Nat.strongRecOn generalizing j with
  | ind m ih =>
    rcases m with _ | _ | _ | m
    · exact ⟨cfg_Tns 0, (rule_T1_6 j).trans (to_Tns 0), Or.inl (mem_Tns 0)⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T11 0 (2 * j + 7)
      exact ⟨cfg', (rule_T1_7 j).trans h1, h2⟩
    · exact ⟨cfg_S0p 0 (2 * j + 5) 3, rule_T1_8 j, Or.inl (mem_S0p 0 (2 * j + 5) 3)⟩
    · obtain ⟨cfg', h1, h2⟩ := ih m (by omega) (j + 2)
      exact ⟨cfg', (rule_T1_9 j m).trans h1, h2⟩

private theorem step_T1s (b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T1s b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | m
  · obtain ⟨cfg', h1, h2⟩ := step_T11 0 7
    exact ⟨cfg', rule_T1s_0.trans h1, h2⟩
  · exact ⟨cfg_S0p 0 5 3, rule_T1s_1, Or.inl (mem_S0p 0 5 3)⟩
  · obtain ⟨cfg', h1, h2⟩ := step_T1 2 m
    exact ⟨cfg', (rule_T1s_2 m).trans h1, h2⟩

private theorem step_Tns (j : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Tns j) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  ⟨cfg_Tns (j + 2), (from_Tns j).trans (to_Tns (j + 2)), Or.inl (mem_Tns (j + 2))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_S0p 0 1 3) := by
  have h0 :
      ReachesPlus target
        (init [])
        (Cfg.headRight B
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append ([0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            default)) := by
    bb_steps
  have h1 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append ([1] : List (Fin 2)) default)
          (ListBlank.append ([0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] : List (Fin 2))
            default))
        (cfg_S0p 0 1 3) := by
    unfold cfg_S0p
    bb_exec
  exact (h0.trans h1).to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_S0p 0 1 3, init_reaches_start, mem_S0p 0 1 3⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · simp only [cond_S0p_T1, evalVarCond] at h_cond
    rcases h_cond with ⟨h3a, h3b, h2a⟩ | ⟨h3a, h2a, h2b, h0a, h0b⟩ | ⟨h3a, h2a, h1a, h0a⟩
    · have h3 : vars 3 = 1 := by omega
      rcases h2 : vars 2 with _ | c
      · omega
      · rw [eval_pat_S0p vars c h2 h3]
        exact step_S0p (vars 0) (vars 1) c
    · have h3 : vars 3 = 0 := by omega
      have h2 : vars 2 = 1 := by omega
      have h0 : vars 0 = 2 := by omega
      rw [eval_pat_T1s vars h0 h2 h3]
      exact step_T1s (vars 1)
    · have h3 : vars 3 = 0 := by omega
      have h2 : vars 2 = 0 := by omega
      have h1 : vars 1 = 0 := by omega
      rcases h0 : vars 0 with _ | _ | j
      · omega
      · omega
      · rw [eval_pat_Tns vars j h0 h1 h2 h3]
        exact step_Tns j
  · simp only [cond_Ebd, evalVarCond] at h_cond
    have h3 : vars 3 = 1 := by omega
    rcases h2 : vars 2 with _ | _ | n
    · rw [eval_pat_Ebd_0 vars h2 h3]
      exact step_Ed (vars 0) (vars 1)
    · rw [eval_pat_Ebd_1 vars h2 h3]
      exact step_Eb (vars 0) (vars 1)
    · omega

/-- `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`. -/
inductive State where
  | S0p (a b c : ℕ)
  | S0z (a c : ℕ)
  | T1 (j m : ℕ)
  | T0 (j m : ℕ)
  | T11 (j m : ℕ)
  | T3 (j m : ℕ)
  | T10 (j m : ℕ)
  | Tn (j : ℕ)
  | Ea (n : ℕ)
  | Eb (k t : ℕ)
  | Ec (n : ℕ)
  | Ed (k t : ℕ)

/-- Initial symbolic state `S0p 0 1 3`, reached after 47 raw TM steps. -/
def start : State := .S0p 0 1 3

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .S0p a b c => cfg_S0p a b c
  | .S0z a c => cfg_S0z a c
  | .T1 j m => cfg_T1 j m
  | .T0 j m => cfg_T0 j m
  | .T11 j m => cfg_T11 j m
  | .T3 j m => cfg_T3 j m
  | .T10 j m => cfg_T10 j m
  | .Tn j => cfg_Tn j
  | .Ea n => cfg_Ea n
  | .Eb k t => cfg_Eb k t
  | .Ec n => cfg_Ec n
  | .Ed k t => cfg_Ed k t

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .S0p a 0 c => some (.S0p 0 (2 * a + 1) (c + 4))
  | .S0p a 1 c => some (.S0p (a + 2) 0 (c + 2))
  | .S0p a 2 c => some (.S0z (a + 2) c)
  | .S0p a (b + 3) c => some (.S0p (a + 2) b c)
  | .S0z a 0 => some (.T1 0 (2 * a + 3))
  | .S0z a (c + 1) => some (.S0p 0 (2 * a + 4) c)
  | .T1 _ 0 => some (.Tn 0)
  | .T1 j 1 => some (.T11 0 (2 * j + 7))
  | .T1 j 2 => some (.S0p 0 (2 * j + 5) 3)
  | .T1 j (m + 3) => some (.T1 (j + 2) m)
  | .T0 j 0 => some (.S0z (j + 1) 0)
  | .T0 _ 1 => none
  | .T0 j 2 => some (.S0z (j + 2) 0)
  | .T0 j (m + 3) => some (.T0 (j + 2) m)
  | .T11 j 0 => some (.T1 0 (2 * j + 6))
  | .T11 j 1 => some (.T3 0 (2 * j + 7))
  | .T11 j 2 => some (.Ea j)
  | .T11 j (m + 3) => some (.T11 (j + 2) m)
  | .T3 j 0 => some (.T1 0 (2 * j + 8))
  | .T3 j 1 => some (.T10 0 (2 * j + 7))
  | .T3 j 2 => some (.Ec j)
  | .T3 j (m + 3) => some (.T3 (j + 2) m)
  | .T10 j 0 => some (.T0 0 (2 * j + 6))
  | .T10 _ 1 => none
  | .T10 _ 2 => none
  | .T10 j (m + 3) => some (.T10 (j + 2) m)
  | .Tn j => some (.Tn (j + 2))
  | .Ea n => some (.Eb 0 (2 * n + 1))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ec n => some (.Ed 0 (2 * n + 1))
  | .Ed k t => some (.Ed (k + 1) t)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro s s' hnext
    rcases s with
      ⟨a, b, c⟩ | ⟨a, c⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩ |
      ⟨j⟩ | ⟨n⟩ | ⟨k, t⟩ | ⟨n⟩ | ⟨k, t⟩
    · rcases b with _ | _ | _ | b <;>
        simp only [next, Option.some.injEq] at hnext <;> subst hnext
      · exact rule_S0p_2 a c
      · exact rule_S0p_3 a c
      · exact rule_S0p_4 a c
      · exact rule_S0p_5 a b c
    · rcases c with _ | c <;>
        simp only [next, Option.some.injEq] at hnext <;> subst hnext
      · exact rule_S0z_0 a
      · exact rule_S0z_1 a c
    · rcases m with _ | _ | _ | m <;>
        simp only [next, Option.some.injEq] at hnext <;> subst hnext
      · exact rule_T1_6 j
      · exact rule_T1_7 j
      · exact rule_T1_8 j
      · exact rule_T1_9 j m
    · rcases m with _ | _ | _ | m
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_T0_10 j
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_T0_12 j
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_T0_13 j m
    · rcases m with _ | _ | _ | m <;>
        simp only [next, Option.some.injEq] at hnext <;> subst hnext
      · exact rule_T11_14 j
      · exact rule_T11_15 j
      · exact rule_T11_16 j
      · exact rule_T11_17 j m
    · rcases m with _ | _ | _ | m <;>
        simp only [next, Option.some.injEq] at hnext <;> subst hnext
      · exact rule_T3_18 j
      · exact rule_T3_19 j
      · exact rule_T3_20 j
      · exact rule_T3_21 j m
    · rcases m with _ | _ | _ | m
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_T10_22 j
      · simp [next] at hnext
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_T10_25 j m
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_Tn_26 j
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_Ea_27 n
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_Eb_28 k t
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_Ec_29 n
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_Ed_30 k t
  step_none := by
    rintro s hnext
    rcases s with
      ⟨a, b, c⟩ | ⟨a, c⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩ |
      ⟨j⟩ | ⟨n⟩ | ⟨k, t⟩ | ⟨n⟩ | ⟨k, t⟩
    · rcases b with _ | _ | _ | b <;> simp [next] at hnext
    · rcases c with _ | c <;> simp [next] at hnext
    · rcases m with _ | _ | _ | m <;> simp [next] at hnext
    · rcases m with _ | _ | _ | m
      · simp [next] at hnext
      · obtain ⟨cfg', hp, hh⟩ := halt_T0_11 j
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
      · simp [next] at hnext
    · rcases m with _ | _ | _ | m <;> simp [next] at hnext
    · rcases m with _ | _ | _ | m <;> simp [next] at hnext
    · rcases m with _ | _ | _ | m
      · simp [next] at hnext
      · obtain ⟨cfg', hp, hh⟩ := halt_T10_23 j
        exact ⟨cfg', hp.to_star, hh⟩
      · obtain ⟨cfg', hp, hh⟩ := halt_T10_24 j
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · simp [next] at hnext
    · simp [next] at hnext
    · simp [next] at hnext
    · simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- Contracted configuration families (`S`, `T`, and the three infinite self-loops `Tn`, `Eb`,
`Ed`) for the high-level Collatz-like acceleration. -/
inductive HighLevelState where
  | S (b c : ℕ)
  | T (m : ℕ)
  | Tn (j : ℕ)
  | Eb (k t : ℕ)
  | Ed (k t : ℕ)
  deriving DecidableEq, Repr

/-- Initial state `S 1 3` (`S0p(0, 1, 3)`) for the high-level Collatz-like acceleration. -/
def highLevelStart : HighLevelState := .S 1 3

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .S b c => .S0p 0 b c
  | .T m => .T1 0 m
  | .Tn j => .Tn j
  | .Eb k t => .Eb k t
  | .Ed k t => .Ed k t

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- High-level closed-form transition function contracting all five `mod 3` sweeps (`S0p`, `T1`,
`T11`, `T3`, `T10`, `T0`) and eliminating `S0z`, `T0`, `T11`, `T3`, `T10`, `Ea`, and `Ec`. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .S b c =>
    let a := 2 * (b / 3)
    if b % 3 = 0 then some (.S (2 * a + 1) (c + 4))
    else if b % 3 = 1 then some (.S (2 * a + 5) (c + 6))
    else if c = 0 then some (.T (2 * a + 7))
    else some (.S (2 * a + 8) (c - 1))
  | .T m =>
    let j0 := 2 * (m / 3)
    if m % 3 = 0 then some (.Tn 0)
    else if m % 3 = 2 then some (.S (2 * j0 + 5) 3)
    else
      let m1 := 2 * j0 + 7
      let j1 := 2 * (m1 / 3)
      if m1 % 3 = 0 then some (.T (2 * j1 + 6))
      else if m1 % 3 = 2 then some (.Eb 0 (2 * j1 + 1))
      else
        let m2 := 2 * j1 + 7
        let j2 := 2 * (m2 / 3)
        if m2 % 3 = 0 then some (.T (2 * j2 + 8))
        else if m2 % 3 = 2 then some (.Ed 0 (2 * j2 + 1))
        else
          let m3 := 2 * j2 + 7
          let j3 := 2 * (m3 / 3)
          if m3 % 3 ≠ 0 then none
          else
            let m4 := 2 * j3 + 6
            let j4 := 2 * (m4 / 3)
            if m4 % 3 = 1 then none
            else if m4 % 3 = 0 then some (.T (2 * j4 + 5))
            else some (.T (2 * j4 + 7))
  | .Tn j => some (.Tn (j + 2))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ed k t => some (.Ed (k + 1) t)

private theorem reaches_S0p_drain : ∀ (k a r c : ℕ),
    CollatzReachesStar next (.S0p a (3 * k + r) c) (.S0p (a + 2 * k) r c)
  | 0, a, r, c => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, a, r, c => by
    have ih := reaches_S0p_drain k (a + 2) r c
    have ha : a + 2 + 2 * k = a + 2 * (k + 1) := by omega
    rw [ha] at ih
    have h_step : next (.S0p a (3 * (k + 1) + r) c) = some (.S0p (a + 2) (3 * k + r) c) := by
      have hb : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
      rw [hb]
      rfl
    exact CollatzReachesStar.head h_step ih

private theorem reaches_T1_drain : ∀ (k j r : ℕ),
    CollatzReachesStar next (.T1 j (3 * k + r)) (.T1 (j + 2 * k) r)
  | 0, j, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, j, r => by
    have ih := reaches_T1_drain k (j + 2) r
    have hj : j + 2 + 2 * k = j + 2 * (k + 1) := by omega
    rw [hj] at ih
    have h_step : next (.T1 j (3 * (k + 1) + r)) = some (.T1 (j + 2) (3 * k + r)) := by
      have hm : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
      rw [hm]
      rfl
    exact CollatzReachesStar.head h_step ih

private theorem reaches_T0_drain : ∀ (k j r : ℕ),
    CollatzReachesStar next (.T0 j (3 * k + r)) (.T0 (j + 2 * k) r)
  | 0, j, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, j, r => by
    have ih := reaches_T0_drain k (j + 2) r
    have hj : j + 2 + 2 * k = j + 2 * (k + 1) := by omega
    rw [hj] at ih
    have h_step : next (.T0 j (3 * (k + 1) + r)) = some (.T0 (j + 2) (3 * k + r)) := by
      have hm : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
      rw [hm]
      rfl
    exact CollatzReachesStar.head h_step ih

private theorem reaches_T11_drain : ∀ (k j r : ℕ),
    CollatzReachesStar next (.T11 j (3 * k + r)) (.T11 (j + 2 * k) r)
  | 0, j, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, j, r => by
    have ih := reaches_T11_drain k (j + 2) r
    have hj : j + 2 + 2 * k = j + 2 * (k + 1) := by omega
    rw [hj] at ih
    have h_step : next (.T11 j (3 * (k + 1) + r)) = some (.T11 (j + 2) (3 * k + r)) := by
      have hm : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
      rw [hm]
      rfl
    exact CollatzReachesStar.head h_step ih

private theorem reaches_T3_drain : ∀ (k j r : ℕ),
    CollatzReachesStar next (.T3 j (3 * k + r)) (.T3 (j + 2 * k) r)
  | 0, j, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, j, r => by
    have ih := reaches_T3_drain k (j + 2) r
    have hj : j + 2 + 2 * k = j + 2 * (k + 1) := by omega
    rw [hj] at ih
    have h_step : next (.T3 j (3 * (k + 1) + r)) = some (.T3 (j + 2) (3 * k + r)) := by
      have hm : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
      rw [hm]
      rfl
    exact CollatzReachesStar.head h_step ih

private theorem reaches_T10_drain : ∀ (k j r : ℕ),
    CollatzReachesStar next (.T10 j (3 * k + r)) (.T10 (j + 2 * k) r)
  | 0, j, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, j, r => by
    have ih := reaches_T10_drain k (j + 2) r
    have hj : j + 2 + 2 * k = j + 2 * (k + 1) := by omega
    rw [hj] at ih
    have h_step : next (.T10 j (3 * (k + 1) + r)) = some (.T10 (j + 2) (3 * k + r)) := by
      have hm : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
      rw [hm]
      rfl
    exact CollatzReachesStar.head h_step ih

private theorem stepsTo_S (b c : ℕ) :
    CollatzStepsTo next (.S0p 0 b c) ((highLevelNext (.S b c)).map toState) := by
  have h_drain := reaches_S0p_drain (b / 3) 0 (b % 3) c
  have hb : 3 * (b / 3) + b % 3 = b := by omega
  rw [hb, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  dsimp only [highLevelNext]
  split_ifs with hr0 hr1 hc0
  · rw [hr0]
    exact CollatzStepsTo.of_eq rfl
  · rw [hr1]
    refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
    dsimp only [next, toState, Option.map]
    congr 2
  · have hr2 : b % 3 = 2 := by omega
    rw [hr2, hc0]
    refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
    dsimp only [next, toState, Option.map]
    congr 2
  · have hr2 : b % 3 = 2 := by omega
    rcases c with _ | c
    · exact absurd rfl hc0
    · rw [hr2]
      refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
      dsimp only [next, toState, Option.map]
      congr 2

private theorem stepsTo_T0 (m4 : ℕ) :
    CollatzStepsTo next (.T0 0 m4)
      ((let j4 := 2 * (m4 / 3)
        if m4 % 3 = 1 then none
        else if m4 % 3 = 0 then some (HighLevelState.T (2 * j4 + 5))
        else some (HighLevelState.T (2 * j4 + 7))).map toState) := by
  have h_drain := reaches_T0_drain (m4 / 3) 0 (m4 % 3)
  have hm : 3 * (m4 / 3) + m4 % 3 = m4 := by omega
  rw [hm, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  dsimp only []
  split_ifs with hr1 hr0
  · rw [hr1]
    exact CollatzStepsTo.of_eq rfl
  · rw [hr0]
    refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
    dsimp only [next, toState, Option.map]
    congr 2
  · have hr2 : m4 % 3 = 2 := by omega
    rw [hr2]
    refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
    dsimp only [next, toState, Option.map]
    congr 2

private theorem stepsTo_T10 (m3 : ℕ) :
    CollatzStepsTo next (.T10 0 m3)
      ((let j3 := 2 * (m3 / 3)
        if m3 % 3 ≠ 0 then none
        else
          let m4 := 2 * j3 + 6
          let j4 := 2 * (m4 / 3)
          if m4 % 3 = 1 then none
          else if m4 % 3 = 0 then some (HighLevelState.T (2 * j4 + 5))
          else some (HighLevelState.T (2 * j4 + 7))).map toState) := by
  have h_drain := reaches_T10_drain (m3 / 3) 0 (m3 % 3)
  have hm : 3 * (m3 / 3) + m3 % 3 = m3 := by omega
  rw [hm, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  by_cases hr0 : m3 % 3 = 0
  · simp only [hr0]
    exact CollatzStepsTo.head rfl (stepsTo_T0 (2 * (2 * (m3 / 3)) + 6))
  · simp only [ne_eq, hr0, not_false_eq_true, ↓reduceIte, Option.map_none]
    rcases (by omega : m3 % 3 = 1 ∨ m3 % 3 = 2) with hr1 | hr2
    · rw [hr1]
      exact CollatzStepsTo.of_eq rfl
    · rw [hr2]
      exact CollatzStepsTo.of_eq rfl

private theorem stepsTo_T3 (m2 : ℕ) :
    CollatzStepsTo next (.T3 0 m2)
      ((let j2 := 2 * (m2 / 3)
        if m2 % 3 = 0 then some (HighLevelState.T (2 * j2 + 8))
        else if m2 % 3 = 2 then some (HighLevelState.Ed 0 (2 * j2 + 1))
        else
          let m3 := 2 * j2 + 7
          let j3 := 2 * (m3 / 3)
          if m3 % 3 ≠ 0 then none
          else
            let m4 := 2 * j3 + 6
            let j4 := 2 * (m4 / 3)
            if m4 % 3 = 1 then none
            else if m4 % 3 = 0 then some (HighLevelState.T (2 * j4 + 5))
            else some (HighLevelState.T (2 * j4 + 7))).map toState) := by
  have h_drain := reaches_T3_drain (m2 / 3) 0 (m2 % 3)
  have hm : 3 * (m2 / 3) + m2 % 3 = m2 := by omega
  rw [hm, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  by_cases hr0 : m2 % 3 = 0
  · simp only [hr0, ↓reduceIte]
    exact CollatzStepsTo.of_eq rfl
  · by_cases hr2 : m2 % 3 = 2
    · simp only [hr2, ↓reduceIte]
      exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · have hr1 : m2 % 3 = 1 := by omega
      simp only [hr1]
      exact CollatzStepsTo.head rfl (stepsTo_T10 (2 * (2 * (m2 / 3)) + 7))

private theorem stepsTo_T11 (m1 : ℕ) :
    CollatzStepsTo next (.T11 0 m1)
      ((let j1 := 2 * (m1 / 3)
        if m1 % 3 = 0 then some (HighLevelState.T (2 * j1 + 6))
        else if m1 % 3 = 2 then some (HighLevelState.Eb 0 (2 * j1 + 1))
        else
          let m2 := 2 * j1 + 7
          let j2 := 2 * (m2 / 3)
          if m2 % 3 = 0 then some (HighLevelState.T (2 * j2 + 8))
          else if m2 % 3 = 2 then some (HighLevelState.Ed 0 (2 * j2 + 1))
          else
            let m3 := 2 * j2 + 7
            let j3 := 2 * (m3 / 3)
            if m3 % 3 ≠ 0 then none
            else
              let m4 := 2 * j3 + 6
              let j4 := 2 * (m4 / 3)
              if m4 % 3 = 1 then none
              else if m4 % 3 = 0 then some (HighLevelState.T (2 * j4 + 5))
              else some (HighLevelState.T (2 * j4 + 7))).map toState) := by
  have h_drain := reaches_T11_drain (m1 / 3) 0 (m1 % 3)
  have hm : 3 * (m1 / 3) + m1 % 3 = m1 := by omega
  rw [hm, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  by_cases hr0 : m1 % 3 = 0
  · simp only [hr0, ↓reduceIte]
    exact CollatzStepsTo.of_eq rfl
  · by_cases hr2 : m1 % 3 = 2
    · simp only [hr2, ↓reduceIte]
      exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · have hr1 : m1 % 3 = 1 := by omega
      simp only [hr1]
      exact CollatzStepsTo.head rfl (stepsTo_T3 (2 * (2 * (m1 / 3)) + 7))

private theorem stepsTo_T1 (m : ℕ) :
    CollatzStepsTo next (.T1 0 m) ((highLevelNext (.T m)).map toState) := by
  have h_drain := reaches_T1_drain (m / 3) 0 (m % 3)
  have hm : 3 * (m / 3) + m % 3 = m := by omega
  rw [hm, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  dsimp only [highLevelNext]
  by_cases hr0 : m % 3 = 0
  · simp only [hr0, ↓reduceIte]
    exact CollatzStepsTo.of_eq rfl
  · by_cases hr2 : m % 3 = 2
    · simp only [hr2, ↓reduceIte]
      exact CollatzStepsTo.of_eq rfl
    · have hr1 : m % 3 = 1 := by omega
      simp only [hr1]
      exact CollatzStepsTo.head rfl (stepsTo_T11 (2 * (2 * (m / 3)) + 7))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro (⟨b, c⟩ | ⟨m⟩ | ⟨j⟩ | ⟨k, t⟩ | ⟨k, t⟩)
  · exact stepsTo_S b c
  · exact stepsTo_T1 m
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl

/-- `target` halts from the blank tape if and only if the high-level acceleration `highLevelNext`
halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` if and only if the high-level acceleration
`highLevelNext` halts from `highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH
