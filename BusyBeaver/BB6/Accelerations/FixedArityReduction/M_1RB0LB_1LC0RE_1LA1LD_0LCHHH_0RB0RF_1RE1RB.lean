/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`
(**cryptid_9**, holdout #245, `suspect_96`; see
<https://wiki.bbchallenge.org/wiki/1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB>, and exact
left-right mirror image of `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---` (**cryptid_8**, holdout
#661, `suspect_95`)).

Starting from the blank tape (`init []`), the trajectory enters a 12-family Collatz-like system
at $T_1(0, 1)$ in 22 raw TM steps (and reaches the primary hub $S_{0p}(0, 125, 3)$ in 7 macro
transitions), where every configuration advances in `ReachesPlus` either to another canonical
configuration or to a halting configuration (`D1 -> ---`).

## Collatz-like Acceleration Rules

Compacted 2-pattern / 9-rule slice-accelerated system:

```text
Consider:
S0p(a, b, c) = 0^inf 10 (01)^c 01 0^b B> 001 (01)^a 1 0^inf
T1(j, m)     = 0^inf 1 0^m 1001 (01)^j 0 F> 1 0^inf
T0(j, m)     = 0^inf 11 0^m 1001 (01)^j 0 F> 1 0^inf
T11(j, m)    = 0^inf 101 0^m 1001 (01)^j 0 F> 1 0^inf
T3(j, m)     = 0^inf 10001 0^m 1001 (01)^j 0 F> 1 0^inf
T10(j, m)    = 0^inf 1101 0^m 1001 (01)^j 0 F> 1 0^inf
Tn(j)        = 0^inf 1001 (01)^j 0 F> 1 0^inf
Eb(k, t)     = 0^inf 1011 0^t (11 0^17)^k 1000 (10)^11 0001 B> 1 0^inf
Ed(k, t)     = 0^inf 1 0^t (11 0^17)^k 1000 (10)^11 0001 B> 1 0^inf

1. S0p(0, 3k, c)       -> S0p(0, 4k+1, c+4)
   S0p(0, 3k+1, c)     -> S0p(0, 4k+5, c+6)
   S0p(0, 3k+2, c+1)   -> S0p(0, 4k+8, c)
   S0p(0, 3k+2, 0)     -> T1(0, 4k+7)
2. T1(0, 3k)           -> Tn(0)
   T1(0, 3k+1)         -> T11(0, 4k+7)
   T1(0, 3k+2)         -> S0p(0, 4k+5, 3)
3. T11(0, 3k)          -> T1(0, 4k+6)
   T11(0, 3k+1)        -> T3(0, 4k+7)
   T11(0, 3k+2)        -> Eb(0, 4k+1)
4. T3(0, 3k)           -> T1(0, 4k+8)
   T3(0, 3k+1)         -> T10(0, 4k+7)
   T3(0, 3k+2)         -> Ed(0, 4k+1)
5. T10(0, 3k)          -> T0(0, 4k+6)
   T10(0, 3k+1)        -> Halt
   T10(0, 3k+2)        -> Halt
6. T0(0, 3k)           -> T1(0, 4k+5)
   T0(0, 3k+1)         -> Halt
   T0(0, 3k+2)         -> T1(0, 4k+7)
7. Tn(j)               -> Tn(j+2)
8. Eb(k, t)            -> Eb(k+1, t)
9. Ed(k, t)            -> Ed(k+1, t)

Start: T1(0, 1) at step 22 (reaches S0p(0, 125, 3) in 7 macro transitions)
```

## High-Level Collatz-like Acceleration

`HighLevelState` and `highLevelNext` contract all five `mod 3` sweeps (`S0p`, `T1`, `T11`, `T3`,
`T10`, `T0`) and eliminate `S0z`, `T0`, `T11`, `T3`, `T10`, `Ea`, and `Ec` into a pure closed-form
transition map over `S(b, c)` (`S0p(0, b, c)`), `T(m)` (`T1(0, m)`), and the three non-halting
self-loops `Tn(j)`, `Eb(k, t)`, and `Ed(k, t)`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Tape Normalization and Execution Helpers -/

private theorem merge_0 (a b : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0] : List (Fin 2)) ^ a)
      (ListBlank.append (([0] : List (Fin 2)) ^ b) r) =
      ListBlank.append (([0] : List (Fin 2)) ^ (a + b)) r :=
  (ListBlank.append_pow_add [0] a b r).symm

private theorem rot_0 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (ListBlank.cons (0 : Fin 2) r) =
      ListBlank.cons (0 : Fin 2) (ListBlank.append (([0] : List (Fin 2)) ^ n) r) := by
  simpa using ListBlank.append_pow_comm ([0] : List (Fin 2)) n r

private theorem sq_00 (k : ℕ) :
    ([0, 0] : List (Fin 2)) ^ k = ([0] : List (Fin 2)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 0 k

private theorem merge_01 (a b : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) r) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + b)) r :=
  (ListBlank.append_pow_add [0, 1] a b r).symm

private theorem rot_01 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ n) (ListBlank.cons (0 : Fin 2) r) =
      ListBlank.cons (0 : Fin 2) (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) r) :=
  append_01_pow_zero n r

private theorem merge_10 (a b : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) r) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + b)) r :=
  (ListBlank.append_pow_add [1, 0] a b r).symm

private theorem rot_10 (n : ℕ) (r : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.cons (1 : Fin 2) r) =
      ListBlank.cons (1 : Fin 2) (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r) :=
  append_10_pow_one n r

private theorem zero_pow_default (n : ℕ) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ListBlank.append_pow_succ, ih]
    exact ListBlank.cons_zero_default

local macro "step_once" : tactic =>
  `(tactic| (
    first
    | refine ReachesPlus.head (by
        try simp only [ListBlank.head_cons, ListBlank.head_default_fin]
        rfl) ?_
    | refine ReachesStar.head (by
        try simp only [ListBlank.head_cons, ListBlank.head_default_fin]
        rfl) ?_
    try simp only [Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      Tape.write, ListBlank.cons_zero_default, ListBlank.head_default_fin,
      ListBlank.tail_default]))

local macro "step_block" : tactic =>
  `(tactic| (
    try simp only [init_nil_eq_headRight, Cfg.headRight, Cfg.headLeft, Tape.mk',
      list_pow_zero, list_pow_succ, List.nil_append, List.append_nil,
      ListBlank.append_nil, List.cons_append, ListBlank.append_cons,
      ListBlank.cons_zero_default, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default_fin, ListBlank.tail_default]
    repeat (first | exact ReachesStar.refl _ _ | step_once)))

local macro "norm_tape" : tactic =>
  `(tactic| (
    first
    | rfl
    | simp only [Cfg.headRight, Cfg.headLeft, Tape.mk', list_pow_zero, list_pow_succ,
        List.nil_append, List.append_nil, ListBlank.append_nil, List.cons_append,
        ListBlank.append_cons, ListBlank.cons_zero_default, ListBlank.head_cons,
        ListBlank.tail_cons, ListBlank.head_default_fin, ListBlank.tail_default,
        merge_0, rot_0, sq_00, merge_01, rot_01, merge_10, rot_10, zero_pow_default]))
private theorem sweep_E_R_01 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headRight E l (ListBlank.append (([0, 1] : List (Fin 2))^k) r)) (Cfg.headRight E
    (ListBlank.append (([0, 0] : List (Fin 2))^k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headRight E l (ListBlank.append (([0, 1] : List (Fin
        2))^(k+1)) r)) (Cfg.headRight E (ListBlank.append [0, 0] l) (ListBlank.append (([0, 1] :
        List (Fin 2))^k) r)) := by
      step_block
    have h2 := ih ((ListBlank.append [0, 0] l)) r
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([0, 0] : List (Fin 2))^k) ((ListBlank.append [0, 0] l))))
        = ((ListBlank.append (([0, 0] : List (Fin 2))^(k+1)) l)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star
private theorem sweep_C_L_10 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin 2))^k) l) r) (Cfg.headLeft C l
    (ListBlank.append (([0, 1] : List (Fin 2))^k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin
        2))^(k+1)) l) r) (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin 2))^k) l)
        (ListBlank.append [0, 1] r)) := by
      step_block
    have h2 := ih l ((ListBlank.append [0, 1] r))
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([0, 1] : List (Fin 2))^k) ((ListBlank.append [0, 1] r))))
        = ((ListBlank.append (([0, 1] : List (Fin 2))^(k+1)) r)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star
private theorem sweep_F_R_01 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headRight F l (ListBlank.append (([0, 1] : List (Fin 2))^k) r)) (Cfg.headRight F
    (ListBlank.append (([0, 1] : List (Fin 2))^k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headRight F l (ListBlank.append (([0, 1] : List (Fin
        2))^(k+1)) r)) (Cfg.headRight F (ListBlank.append [0, 1] l) (ListBlank.append (([0, 1] :
        List (Fin 2))^k) r)) := by
      step_block
    have h2 := ih ((ListBlank.append [0, 1] l)) r
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([0, 1] : List (Fin 2))^k) ((ListBlank.append [0, 1] l))))
        = ((ListBlank.append (([0, 1] : List (Fin 2))^(k+1)) l)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star
private theorem sweep_D_L_01 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^k) l) r) (Cfg.headLeft D l
    (ListBlank.append (([1, 0] : List (Fin 2))^k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin
        2))^(k+1)) l) r) (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^k) l)
        (ListBlank.append [1, 0] r)) := by
      step_block
    have h2 := ih l ((ListBlank.append [1, 0] r))
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([1, 0] : List (Fin 2))^k) ((ListBlank.append [1, 0] r))))
        = ((ListBlank.append (([1, 0] : List (Fin 2))^(k+1)) r)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star
private theorem sweep_E_R_10 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headRight E l (ListBlank.append (([1, 0] : List (Fin 2))^k) r)) (Cfg.headRight E
    (ListBlank.append (([1, 0] : List (Fin 2))^k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headRight E l (ListBlank.append (([1, 0] : List (Fin
        2))^(k+1)) r)) (Cfg.headRight E (ListBlank.append [1, 0] l) (ListBlank.append (([1, 0] :
        List (Fin 2))^k) r)) := by
      step_block
    have h2 := ih ((ListBlank.append [1, 0] l)) r
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([1, 0] : List (Fin 2))^k) ((ListBlank.append [1, 0] l))))
        = ((ListBlank.append (([1, 0] : List (Fin 2))^(k+1)) l)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star
private theorem sweep_B_R_10 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2))^k) r)) (Cfg.headRight B
    (ListBlank.append (([0, 0] : List (Fin 2))^k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin
        2))^(k+1)) r)) (Cfg.headRight B (ListBlank.append [0, 0] l) (ListBlank.append (([1, 0] :
        List (Fin 2))^k) r)) := by
      step_block
    have h2 := ih ((ListBlank.append [0, 0] l)) r
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([0, 0] : List (Fin 2))^k) ((ListBlank.append [0, 0] l))))
        = ((ListBlank.append (([0, 0] : List (Fin 2))^(k+1)) l)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star
private theorem sweep_B_R_01_w1000 (k : ℕ) (l r : ListBlank (Fin 2)) : ReachesStar target
    (Cfg.headRight B (ListBlank.append [1, 0, 0, 0] l) (ListBlank.append (([0, 1] : List (Fin
    2))^k) r)) (Cfg.headRight B (ListBlank.append [1, 0, 0, 0] ((ListBlank.append (([0, 1] :
    List (Fin 2))^k) l))) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target (Cfg.headRight B (ListBlank.append [1, 0, 0, 0] l)
        (ListBlank.append (([0, 1] : List (Fin 2))^(k+1)) r)) (Cfg.headRight B (ListBlank.append
        [1, 0, 0, 0] ((ListBlank.append [0, 1] l))) (ListBlank.append (([0, 1] : List (Fin
        2))^k) r)) := by
      step_block
    have h2 := ih ((ListBlank.append [0, 1] l)) r
    have h3 := h1.trans_star h2
    have h_pow : ((ListBlank.append (([0, 1] : List (Fin 2))^k) ((ListBlank.append [0, 1] l))))
        = ((ListBlank.append (([0, 1] : List (Fin 2))^(k+1)) l)) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rw [h_pow] at h3
    exact h3.to_star

def cfg_S0z (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))) (ListBlank.append [1, 0, 1] ((ListBlank.append
      (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))))))
def cfg_S0p (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append [1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))))
      (ListBlank.append [0, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [1] default)))))))
def cfg_T1 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1] default))))))))) (ListBlank.append [1] default)))
def cfg_T0 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 1] default))))))))) (ListBlank.append [1] default)))
def cfg_T11 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1] default))))))))) (ListBlank.append [1] default)))
def cfg_T3 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 0, 0, 1] default))))))))) (ListBlank.append [1] default)))
def cfg_T10 (j m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1, 1] default))))))))) (ListBlank.append [1] default)))
def cfg_Tn (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight F (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j))
      ((ListBlank.append [1, 0, 0, 1] default))))) (ListBlank.append [1] default)))
def cfg_Ea (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(n)) ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [1]
      default)))
def cfg_Eb (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1, 1, 0, 1] default))))))) (ListBlank.append [1] default)))
def cfg_Ec (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(n)) ((ListBlank.append [1] default))))) (ListBlank.append [1] default)))
def cfg_Ed (k t : ℕ) : Cfg (Fin 2) (Fin 6) :=
  ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1] default))))))) (ListBlank.append [1] default)))

private theorem rule_S0z_0 (a : ℕ) : ReachesPlus target (cfg_S0z a 0) (cfg_T1 0 (2*a+3)) := by
  have h0 : ReachesPlus target (cfg_S0z a 0) (Cfg.headRight E (ListBlank.append [0, 0, 0, 0, 0,
      1] default) (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default)))) := by
    unfold cfg_S0z
    step_block
  have h1 := sweep_E_R_01 a ((ListBlank.append [0, 0, 0, 0, 0, 1] default)) ((ListBlank.append
      [1] default))
  have h2 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(a))
      ((ListBlank.append [0, 0, 0, 0, 0, 1] default))) (ListBlank.append [1] default))
      (Cfg.headLeft C (ListBlank.append (([0, 0] : List (Fin 2))^(a)) ((ListBlank.append [0, 0,
      0, 0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1] default)) := by
    step_block
  have h3 : ((Cfg.headLeft C (ListBlank.append (([0, 0] : List (Fin 2))^(a)) ((ListBlank.append
      [0, 0, 0, 0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1] default))) = ((Cfg.headRight
      C (ListBlank.append [0, 0, 0, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*a))
      ((ListBlank.append [1] default))))) (ListBlank.append [0, 1, 0, 1, 1] default))) := by
    norm_tape
  have h4 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0, 0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(2*a)) ((ListBlank.append [1] default)))))
      (ListBlank.append [0, 1, 0, 1, 1] default)) (Cfg.headRight F (ListBlank.append [0, 1, 0,
      0, 1, 0, 0, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*a)) ((ListBlank.append [1]
      default))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  rw [h3] at a2
  have a3 := a2.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0, 0, 0] ((ListBlank.append
      (([0] : List (Fin 2))^(2*a)) ((ListBlank.append [1] default))))) (ListBlank.append [1]
      default))) = (cfg_T1 0 (2*a+3)) := by
    unfold cfg_T1
    norm_tape
  rw [heq] at a3
  exact a3
private theorem rule_S0z_1 (a c : ℕ) : ReachesPlus target (cfg_S0z a (c+1)) (cfg_S0p 0 (2*a+4)
    c) := by
  have h0 : ReachesPlus target (cfg_S0z a (c+1)) (Cfg.headRight E (ListBlank.append [0, 0, 0, 0,
      1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1]
      default))))) (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default)))) := by
    unfold cfg_S0z
    step_block
  have h1 := sweep_E_R_01 a ((ListBlank.append [0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] :
      List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))) ((ListBlank.append [1]
      default))
  have h2 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(a))
      ((ListBlank.append [0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))))) (ListBlank.append [1] default)) (Cfg.headRight B
      (ListBlank.append (([0, 0] : List (Fin 2))^(a)) ((ListBlank.append [0, 0, 0, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))))
      (ListBlank.append [0, 0, 1, 1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have heq : ((Cfg.headRight B (ListBlank.append (([0, 0] : List (Fin 2))^(a))
      ((ListBlank.append [0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))))) (ListBlank.append [0, 0, 1, 1] default))) =
      (cfg_S0p 0 (2*a+4) c) := by
    unfold cfg_S0p
    norm_tape
  rw [heq] at a2
  exact a2
private theorem rule_S0p_2 (a c : ℕ) : ReachesPlus target (cfg_S0p a 0 c) (cfg_S0p 0 (2*a+1)
    (c+4)) := by
  have h0 : ReachesPlus target (cfg_S0p a 0 c) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(c)) ((ListBlank.append [0, 1] default))) (ListBlank.append [0, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))))) :=
      by
    unfold cfg_S0p
    step_block
  have h1 := sweep_C_L_10 c ((ListBlank.append [0, 1] default)) ((ListBlank.append [0, 1, 1, 0,
      1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(c)) ((ListBlank.append [0, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] default) (ListBlank.append (([0, 1] :
      List (Fin 2))^(c)) ((ListBlank.append [0, 1, 1, 0, 1] ((ListBlank.append (([0, 1] : List
      (Fin 2))^(a)) ((ListBlank.append [1] default)))))))) := by
    step_block
  have h3 := sweep_F_R_01 c ((ListBlank.append [0, 1, 0, 0, 1] default)) ((ListBlank.append [0,
      1, 1, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default))))))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1, 0, 0, 1] default))) (ListBlank.append [0, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(c)) ((ListBlank.append [0, 1,
      0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1, 1] ((ListBlank.append (([0, 1] : List
      (Fin 2))^(a)) ((ListBlank.append [1] default)))))) := by
    step_block
  have h5 := sweep_D_L_01 c ((ListBlank.append [0, 1, 0, 0, 1] default)) ((ListBlank.append [1,
      0, 1, 1, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default))))))
  have h6 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 0, 1] default)
      (ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 1, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))))
      (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default) (ListBlank.append
      (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 1, 1] ((ListBlank.append (([0,
      1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))))))) := by
    step_block
  have h7 := sweep_E_R_10 c ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [1] default))))))
  have h8 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))
      (Cfg.headRight E (ListBlank.append [0, 1, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin
      2))^(c)) ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))) (ListBlank.append (([0,
      1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))) := by
    step_block
  have h9 := sweep_E_R_01 a ((ListBlank.append [0, 1, 0, 1, 0] ((ListBlank.append (([1, 0] :
      List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))))
      ((ListBlank.append [1] default))
  have h10 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(a))
      ((ListBlank.append [0, 1, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))))) (ListBlank.append [1] default))
      (Cfg.headRight B (ListBlank.append (([0, 0] : List (Fin 2))^(a)) ((ListBlank.append [0, 1,
      0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 0,
      1, 0, 0, 1] default))))))) (ListBlank.append [0, 0, 1, 1] default)) := by
    step_block
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
  have heq : ((Cfg.headRight B (ListBlank.append (([0, 0] : List (Fin 2))^(a))
      ((ListBlank.append [0, 1, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))))) (ListBlank.append [0, 0, 1, 1]
      default))) = (cfg_S0p 0 (2*a+1) (c+4)) := by
    unfold cfg_S0p
    norm_tape
  rw [heq] at a10
  exact a10
private theorem rule_S0p_3 (a c : ℕ) : ReachesPlus target (cfg_S0p a 1 c) (cfg_S0p (a+2) 0
    (c+2)) := by
  have h0 : ReachesPlus target (cfg_S0p a 1 c) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(c)) ((ListBlank.append [0, 1] default))) (ListBlank.append [1, 0, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))))) :=
      by
    unfold cfg_S0p
    step_block
  have h1 := sweep_C_L_10 c ((ListBlank.append [0, 1] default)) ((ListBlank.append [1, 0, 1, 1,
      0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default))))))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] default) (ListBlank.append (([0, 1] :
      List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 1, 0, 1] ((ListBlank.append (([0, 1] :
      List (Fin 2))^(a)) ((ListBlank.append [1] default)))))))) := by
    step_block
  have h3 := sweep_F_R_01 c ((ListBlank.append [0, 1, 0, 0, 1] default)) ((ListBlank.append [1,
      0, 1, 1, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default))))))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1, 0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(c)) ((ListBlank.append [0, 1,
      0, 0, 1] default))) (ListBlank.append [1, 1, 1, 1, 0, 1] ((ListBlank.append (([0, 1] :
      List (Fin 2))^(a)) ((ListBlank.append [1] default)))))) := by
    step_block
  have h5 := sweep_D_L_01 c ((ListBlank.append [0, 1, 0, 0, 1] default)) ((ListBlank.append [1,
      1, 1, 1, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default))))))
  have h6 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 0, 1] default)
      (ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 1, 1, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))))
      (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default) (ListBlank.append
      (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 1, 1, 1, 0, 1] ((ListBlank.append
      (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))))))) := by
    step_block
  have h7 := sweep_E_R_10 c ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))
      ((ListBlank.append [1, 1, 1, 1, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [1] default))))))
  have h8 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))) (ListBlank.append [1, 1, 1, 1, 0,
      1] ((ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default))))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))) (ListBlank.append
      (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1] default)))) := by
    step_block
  have h9 := sweep_F_R_01 a ((ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] :
      List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))))
      ((ListBlank.append [1] default))
  have h10 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))))) (ListBlank.append [1] default))
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [0, 1,
      0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1,
      0, 1, 0, 0, 1] default))))))) (ListBlank.append [1, 1] default)) := by
    step_block
  have h11 := sweep_D_L_01 a ((ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] :
      List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))))))
      ((ListBlank.append [1, 1] default))
  have h12 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [1, 0, 1, 0, 1, 0, 0,
      1] default))))) (ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1]
      default)))) (Cfg.headRight B (ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))) (ListBlank.append [0, 0, 1, 0, 1,
      0] ((ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1]
      default)))))) := by
    step_block
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
  have heq : ((Cfg.headRight B (ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [1, 0, 1, 0, 1, 0, 0, 1] default))) (ListBlank.append [0, 0, 1, 0, 1,
      0] ((ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1]
      default))))))) = (cfg_S0p (a+2) 0 (c+2)) := by
    unfold cfg_S0p
    norm_tape
  rw [heq] at a12
  exact a12
private theorem rule_S0p_4 (a c : ℕ) : ReachesPlus target (cfg_S0p a 2 c) (cfg_S0z (a+2) c) :=
    by
  have h0 : ReachesPlus target (cfg_S0p a 2 c) (Cfg.headRight F (ListBlank.append [0, 1, 0, 0,
      1, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1]
      default))))) (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default)))) := by
    unfold cfg_S0p
    step_block
  have h1 := sweep_F_R_01 a ((ListBlank.append [0, 1, 0, 0, 1, 1, 0] ((ListBlank.append (([1, 0]
      : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))) ((ListBlank.append [1]
      default))
  have h2 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [0, 1, 0, 0, 1, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))))) (ListBlank.append [1] default)) (Cfg.headLeft D
      (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [0, 1, 0, 0, 1, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))))
      (ListBlank.append [1, 1] default)) := by
    step_block
  have h3 := sweep_D_L_01 a ((ListBlank.append [0, 1, 0, 0, 1, 1, 0] ((ListBlank.append (([1, 0]
      : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))) ((ListBlank.append [1, 1]
      default))
  have h4 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 0, 1, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))
      (ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1] default))))
      (Cfg.headRight B (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))) (ListBlank.append [1, 0, 1, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1] default))))))
      := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight B (ListBlank.append [0] ((ListBlank.append (([1, 0] : List (Fin
      2))^(c)) ((ListBlank.append [0, 1] default))))) (ListBlank.append [1, 0, 1, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1] default)))))))
      = (cfg_S0z (a+2) c) := by
    unfold cfg_S0z
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_S0p_5 (a b c : ℕ) : ReachesPlus target (cfg_S0p a (b+3) c) (cfg_S0p (a+2) b
    c) := by
  have h0 : ReachesPlus target (cfg_S0p a (b+3) c) (Cfg.headRight F (ListBlank.append [0, 1, 0,
      0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append [1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1]
      default))))))))) (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [1]
      default)))) := by
    unfold cfg_S0p
    step_block
  have h1 := sweep_F_R_01 a ((ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(b)) ((ListBlank.append [1, 0] ((ListBlank.append (([1, 0] : List (Fin
      2))^(c)) ((ListBlank.append [0, 1] default)))))))))) ((ListBlank.append [1] default))
  have h2 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(a))
      ((ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(b))
      ((ListBlank.append [1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c))
      ((ListBlank.append [0, 1] default))))))))))) (ListBlank.append [1] default)) (Cfg.headLeft
      D (ListBlank.append (([0, 1] : List (Fin 2))^(a)) ((ListBlank.append [0, 1, 0, 0, 1, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append [1, 0] ((ListBlank.append
      (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default)))))))))))
      (ListBlank.append [1, 1] default)) := by
    step_block
  have h3 := sweep_D_L_01 a ((ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(b)) ((ListBlank.append [1, 0] ((ListBlank.append (([1, 0] : List (Fin
      2))^(c)) ((ListBlank.append [0, 1] default)))))))))) ((ListBlank.append [1, 1] default))
  have h4 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 0, 1, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append [1, 0] ((ListBlank.append
      (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default))))))))) (ListBlank.append
      (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1, 1] default)))) (Cfg.headRight B
      (ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append [1, 0] ((ListBlank.append
      (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1] default))))))) (ListBlank.append
      [0, 0, 1, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(a)) ((ListBlank.append [1,
      1] default)))))) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight B (ListBlank.append (([0] : List (Fin 2))^(b)) ((ListBlank.append
      [1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(c)) ((ListBlank.append [0, 1]
      default))))))) (ListBlank.append [0, 0, 1, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(a)) ((ListBlank.append [1, 1] default))))))) = (cfg_S0p (a+2) b c) := by
    unfold cfg_S0p
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T1_6 (j : ℕ) : ReachesPlus target (cfg_T1 j 0) (cfg_Tn 0) := by
  have h0 : ReachesPlus target (cfg_T1 j 0) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 1] default))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_T1
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 1] default)) ((ListBlank.append [0,
      1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight E default (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_E_R_01 j default ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      default) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight F (ListBlank.append [0, 1,
      0, 0, 1] ((ListBlank.append (([0, 0] : List (Fin 2))^(j)) default))) (ListBlank.append [1]
      default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] :
      List (Fin 2))^(j)) default))) (ListBlank.append [1] default))) = (cfg_Tn 0) := by
    unfold cfg_Tn
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T1_7 (j : ℕ) : ReachesPlus target (cfg_T1 j 1) (cfg_T11 0 (2*j+7)) := by
  have h0 : ReachesPlus target (cfg_T1 j 1) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 1] default))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_T1
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 1] default)) ((ListBlank.append
      [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1] default) (ListBlank.append
      (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1] default))) (ListBlank.append [0, 1, 1]
      default)) (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1]
      default)) := by
    step_block
  have h5 := sweep_D_L_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1] default))
  have h6 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1]
      default) (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))) (Cfg.headRight B (ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1] default)
      (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))) := by
    step_block
  have h7 := sweep_B_R_10 j ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1] default))
  have h8 : ReachesPlus target (Cfg.headRight B (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1] default))) (ListBlank.append [1, 0, 1, 1]
      default)) (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0,
      0] : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1] default)))))
      (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0, 0]
      : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1] default)))))
      (ListBlank.append [1] default))) = (cfg_T11 0 (2*j+7)) := by
    unfold cfg_T11
    norm_tape
  rw [heq] at a8
  exact a8
private theorem rule_T1_8 (j : ℕ) : ReachesPlus target (cfg_T1 j 2) (cfg_S0p 0 (2*j+5) 3) := by
  have h0 : ReachesPlus target (cfg_T1 j 2) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 1] default))) (ListBlank.append [0, 1,
      1] default)) := by
    unfold cfg_T1
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight E (ListBlank.append [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_E_R_01 j ((ListBlank.append [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] default))) (ListBlank.append
      [0, 1, 1] default)) (Cfg.headRight B (ListBlank.append [0, 0] ((ListBlank.append (([0, 0]
      : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1]
      default))))) (ListBlank.append [0, 0, 1, 1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight B (ListBlank.append [0, 0] ((ListBlank.append (([0, 0] : List (Fin
      2))^(j)) ((ListBlank.append [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] default)))))
      (ListBlank.append [0, 0, 1, 1] default))) = (cfg_S0p 0 (2*j+5) 3) := by
    unfold cfg_S0p
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T1_9 (j m : ℕ) : ReachesPlus target (cfg_T1 j (m+3)) (cfg_T1 (j+2) m) := by
  have h0 : ReachesPlus target (cfg_T1 j (m+3)) (Cfg.headLeft C (ListBlank.append (([1, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1] default))))))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_T1
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1] default)))))) ((ListBlank.append [0, 1, 1]
      default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(m)) ((ListBlank.append [1] default)))))
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List
      (Fin 2))^(m)) ((ListBlank.append [1] default))))) (ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1] default)))))) ((ListBlank.append [0, 1, 1]
      default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1] default))))))) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight
      F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1] default))))))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin
      2))^(m)) ((ListBlank.append [1] default))))))))) (ListBlank.append [1] default))) =
      (cfg_T1 (j+2) m) := by
    unfold cfg_T1
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T0_10 (j : ℕ) : ReachesPlus target (cfg_T0 j 0) (cfg_S0z (j+1) 0) := by
  have h0 : ReachesPlus target (cfg_T0 j 0) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 1, 1] default))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_T0
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 1, 1] default)) ((ListBlank.append
      [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 1, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight B (ListBlank.append [0, 0, 1] default) (ListBlank.append [1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))))) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have heq : ((Cfg.headRight B (ListBlank.append [0, 0, 1] default) (ListBlank.append [1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default))))))) = (cfg_S0z (j+1) 0) := by
    unfold cfg_S0z
    norm_tape
  rw [heq] at a2
  exact a2
private theorem halt_T0_11 (j : ℕ) : ∃ cfg', ((ReachesPlus target (cfg_T0 j 1) cfg')) ∧ (step
    target cfg').isNone := by
  refine ⟨((Cfg.headRight D default (ListBlank.append [1, 1, 1, 0, 1, 0, 1] ((ListBlank.append
      (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))))), ?_, by bb_halt⟩
  have h0 : ReachesPlus target (cfg_T0 j 1) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 1, 1] default))) (ListBlank.append [0, 1,
      1] default)) := by
    unfold cfg_T0
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 1, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight D default (ListBlank.append [1, 1, 1, 0, 1, 0, 1] ((ListBlank.append (([0,
      1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))))) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  exact a2
private theorem rule_T0_12 (j : ℕ) : ReachesPlus target (cfg_T0 j 2) (cfg_S0z (j+2) 0) := by
  have h0 : ReachesPlus target (cfg_T0 j 2) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 1] default))) (ListBlank.append [0,
      1, 1] default)) := by
    unfold cfg_T0
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 1, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight F (ListBlank.append [0, 1, 0, 1] default) (ListBlank.append
      (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1] default)) ((ListBlank.append [0, 1,
      1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1] default))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1,
      0, 1] default))) (ListBlank.append [1, 0, 1, 1] default)) := by
    step_block
  have h5 := sweep_D_L_01 j ((ListBlank.append [0, 1, 0, 1] default)) ((ListBlank.append [1, 0,
      1, 1] default))
  have h6 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 1] default)
      (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))) (Cfg.headRight B (ListBlank.append [0, 0, 1] default) (ListBlank.append [1, 0,
      1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))))) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have heq : ((Cfg.headRight B (ListBlank.append [0, 0, 1] default) (ListBlank.append [1, 0, 1,
      0] ((ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default))))))) = (cfg_S0z (j+2) 0) := by
    unfold cfg_S0z
    norm_tape
  rw [heq] at a6
  exact a6
private theorem rule_T0_13 (j m : ℕ) : ReachesPlus target (cfg_T0 j (m+3)) (cfg_T0 (j+2) m) :=
    by
  have h0 : ReachesPlus target (cfg_T0 j (m+3)) (Cfg.headLeft C (ListBlank.append (([1, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 1] default))))))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_T0
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 1] default)))))) ((ListBlank.append [0, 1, 1]
      default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(m)) ((ListBlank.append [1, 1] default)))))
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List
      (Fin 2))^(m)) ((ListBlank.append [1, 1] default))))) (ListBlank.append (([0, 1] : List
      (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 1] default)))))) ((ListBlank.append [0, 1, 1]
      default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 1] default))))))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 1] default))))))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin
      2))^(m)) ((ListBlank.append [1, 1] default))))))))) (ListBlank.append [1] default))) =
      (cfg_T0 (j+2) m) := by
    unfold cfg_T0
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T11_14 (j : ℕ) : ReachesPlus target (cfg_T11 j 0) (cfg_T1 0 (2*j+6)) := by
  have h0 : ReachesPlus target (cfg_T11 j 0) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 1, 0, 1] default))) (ListBlank.append [0, 1,
      1] default)) := by
    unfold cfg_T11
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 1, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 1, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight E (ListBlank.append [0, 0, 0, 0, 0, 0, 1] default) (ListBlank.append (([0,
      1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_E_R_01 j ((ListBlank.append [0, 0, 0, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 0, 0, 0, 1] default))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] : List (Fin
      2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1] default))))) (ListBlank.append [1]
      default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1] default))))) (ListBlank.append
      [1] default))) = (cfg_T1 0 (2*j+6)) := by
    unfold cfg_T1
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T11_15 (j : ℕ) : ReachesPlus target (cfg_T11 j 1) (cfg_T3 0 (2*j+7)) := by
  have h0 : ReachesPlus target (cfg_T11 j 1) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1] default))) (ListBlank.append [0,
      1, 1] default)) := by
    unfold cfg_T11
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] default))) (ListBlank.append [0, 1,
      1] default)) (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] default))) (ListBlank.append [1, 0,
      1, 1] default)) := by
    step_block
  have h5 := sweep_D_L_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1] default))
  have h6 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
      1] default) (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1,
      1] default)))) (Cfg.headRight B (ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
      default) (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))) := by
    step_block
  have h7 := sweep_B_R_10 j ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1] default))
  have h8 : ReachesPlus target (Cfg.headRight B (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] default))) (ListBlank.append [1, 0,
      1, 1] default)) (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append
      (([0, 0] : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
      default))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0, 0]
      : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1] default)))))
      (ListBlank.append [1] default))) = (cfg_T3 0 (2*j+7)) := by
    unfold cfg_T3
    norm_tape
  rw [heq] at a8
  exact a8
private theorem rule_T11_16 (j : ℕ) : ReachesPlus target (cfg_T11 j 2) (cfg_Ea j) := by
  have h0 : ReachesPlus target (cfg_T11 j 2) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 1] default))) (ListBlank.append
      [0, 1, 1] default)) := by
    unfold cfg_T11
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) := by
    step_block
  have h3 := sweep_B_R_01_w1000 j ((ListBlank.append [0, 1, 0, 0, 0, 1, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight B (ListBlank.append [1, 0, 0, 0]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 0, 0, 0, 1, 0,
      1] default))))) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight B (ListBlank.append
      [1, 0, 0, 0, 0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0,
      1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1] ((ListBlank.append (([0, 1]
      : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 0, 0, 0, 1, 0, 1] default)))))
      (ListBlank.append [1] default))) = (cfg_Ea j) := by
    unfold cfg_Ea
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T11_17 (j m : ℕ) : ReachesPlus target (cfg_T11 j (m+3)) (cfg_T11 (j+2) m)
    := by
  have h0 : ReachesPlus target (cfg_T11 j (m+3)) (Cfg.headLeft C (ListBlank.append (([1, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1] default))))))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_T11
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1] default)))))) ((ListBlank.append [0, 1, 1]
      default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1] default)))))
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List
      (Fin 2))^(m)) ((ListBlank.append [1, 0, 1] default))))) (ListBlank.append (([0, 1] : List
      (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1] default)))))) ((ListBlank.append [0, 1, 1]
      default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1] default))))))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1] default))))))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin
      2))^(m)) ((ListBlank.append [1, 0, 1] default))))))))) (ListBlank.append [1] default))) =
      (cfg_T11 (j+2) m) := by
    unfold cfg_T11
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T3_18 (j : ℕ) : ReachesPlus target (cfg_T3 j 0) (cfg_T1 0 (2*j+8)) := by
  have h0 : ReachesPlus target (cfg_T3 j 0) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 1, 0, 0, 0, 1] default))) (ListBlank.append
      [0, 1, 1] default)) := by
    unfold cfg_T3
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 1, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 1, 0, 0, 0, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight E (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_E_R_01 j ((ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1] default))) (ListBlank.append [0, 1, 1]
      default)) (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1] default)))))
      (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1] default)))))
      (ListBlank.append [1] default))) = (cfg_T1 0 (2*j+8)) := by
    unfold cfg_T1
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T3_19 (j : ℕ) : ReachesPlus target (cfg_T3 j 1) (cfg_T10 0 (2*j+7)) := by
  have h0 : ReachesPlus target (cfg_T3 j 1) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 1, 0, 0, 0, 1] default)))
      (ListBlank.append [0, 1, 1] default)) := by
    unfold cfg_T3
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 1, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 0, 0, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1, 1] default))) (ListBlank.append [0, 1, 1]
      default)) (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1, 1] default))) (ListBlank.append [1, 0, 1,
      1] default)) := by
    step_block
  have h5 := sweep_D_L_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1, 1] default))
      ((ListBlank.append [1, 0, 1, 1] default))
  have h6 : ReachesPlus target (Cfg.headLeft D (ListBlank.append [0, 1, 0, 1, 0, 0, 0, 0, 1, 1]
      default) (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))) (Cfg.headRight B (ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1, 1] default)
      (ListBlank.append (([1, 0] : List (Fin 2))^(j)) ((ListBlank.append [1, 0, 1, 1]
      default)))) := by
    step_block
  have h7 := sweep_B_R_10 j ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1, 1] default))
      ((ListBlank.append [1, 0, 1, 1] default))
  have h8 : ReachesPlus target (Cfg.headRight B (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1, 1] default))) (ListBlank.append [1, 0, 1,
      1] default)) (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append
      (([0, 0] : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1, 1]
      default))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have a5 := a4.trans_star h5
  have a6 := a5.trans h6
  have a7 := a6.trans_star h7
  have a8 := a7.trans h8
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1, 0] ((ListBlank.append (([0, 0]
      : List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 0, 1, 1] default)))))
      (ListBlank.append [1] default))) = (cfg_T10 0 (2*j+7)) := by
    unfold cfg_T10
    norm_tape
  rw [heq] at a8
  exact a8
private theorem rule_T3_20 (j : ℕ) : ReachesPlus target (cfg_T3 j 2) (cfg_Ec j) := by
  have h0 : ReachesPlus target (cfg_T3 j 2) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1] default)))
      (ListBlank.append [0, 1, 1] default)) := by
    unfold cfg_T3
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 0, 0,
      1] default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_B_R_01_w1000 j ((ListBlank.append [0, 1] default)) ((ListBlank.append [0, 1,
      1] default))
  have h4 : ReachesPlus target (Cfg.headRight B (ListBlank.append [1, 0, 0, 0]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1] default)))))
      (ListBlank.append [0, 1, 1] default)) (Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0,
      1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1] default)))))
      (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1] ((ListBlank.append (([0, 1]
      : List (Fin 2))^(j)) ((ListBlank.append [0, 1] default))))) (ListBlank.append [1]
      default))) = (cfg_Ec j) := by
    unfold cfg_Ec
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T3_21 (j m : ℕ) : ReachesPlus target (cfg_T3 j (m+3)) (cfg_T3 (j+2) m) :=
    by
  have h0 : ReachesPlus target (cfg_T3 j (m+3)) (Cfg.headLeft C (ListBlank.append (([1, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 0, 0, 1] default))))))) (ListBlank.append [0,
      1, 1] default)) := by
    unfold cfg_T3
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 0, 0, 1] default)))))) ((ListBlank.append [0,
      1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(m)) ((ListBlank.append [1, 0, 0, 0, 1]
      default))))) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append
      (([0] : List (Fin 2))^(m)) ((ListBlank.append [1, 0, 0, 0, 1] default)))))
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 0, 0, 1] default)))))) ((ListBlank.append [0,
      1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 0, 0, 1] default))))))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 0, 0, 1] default))))))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin
      2))^(m)) ((ListBlank.append [1, 0, 0, 0, 1] default))))))))) (ListBlank.append [1]
      default))) = (cfg_T3 (j+2) m) := by
    unfold cfg_T3
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_T10_22 (j : ℕ) : ReachesPlus target (cfg_T10 j 0) (cfg_T0 0 (2*j+6)) := by
  have h0 : ReachesPlus target (cfg_T10 j 0) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 1, 0, 1, 1] default))) (ListBlank.append [0,
      1, 1] default)) := by
    unfold cfg_T10
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 1, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 1, 0, 1, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight E (ListBlank.append [0, 0, 0, 0, 0, 0, 1, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      := by
    step_block
  have h3 := sweep_E_R_01 j ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(j))
      ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 1] default))) (ListBlank.append [0, 1, 1]
      default)) (Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 1] default)))))
      (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1, 0, 0, 1] ((ListBlank.append (([0, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [0, 0, 0, 0, 0, 0, 1, 1] default)))))
      (ListBlank.append [1] default))) = (cfg_T0 0 (2*j+6)) := by
    unfold cfg_T0
    norm_tape
  rw [heq] at a4
  exact a4
private theorem halt_T10_23 (j : ℕ) : ∃ cfg', ((ReachesPlus target (cfg_T10 j 1) cfg')) ∧ (step
    target cfg').isNone := by
  refine ⟨((Cfg.headRight D default (ListBlank.append [1, 1, 0, 1, 1, 0, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default))))))), ?_, by bb_halt⟩
  have h0 : ReachesPlus target (cfg_T10 j 1) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 1] default))) (ListBlank.append
      [0, 1, 1] default)) := by
    unfold cfg_T10
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 1, 0, 1, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight D default (ListBlank.append [1, 1, 0, 1, 1, 0, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))))) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  exact a2
private theorem halt_T10_24 (j : ℕ) : ∃ cfg', ((ReachesPlus target (cfg_T10 j 2) cfg')) ∧ (step
    target cfg').isNone := by
  refine ⟨((Cfg.headRight D default (ListBlank.append [1, 1, 1, 0, 1, 1, 0, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default))))))), ?_, by bb_halt⟩
  have h0 : ReachesPlus target (cfg_T10 j 2) (Cfg.headLeft C (ListBlank.append (([1, 0] : List
      (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 1, 1] default)))
      (ListBlank.append [0, 1, 1] default)) := by
    unfold cfg_T10
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 1, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 1, 0, 1, 1]
      default) (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))) (Cfg.headRight D default (ListBlank.append [1, 1, 1, 0, 1, 1, 0, 1, 0, 1]
      ((ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1]
      default)))))) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  exact a2
private theorem rule_T10_25 (j m : ℕ) : ReachesPlus target (cfg_T10 j (m+3)) (cfg_T10 (j+2) m)
    := by
  have h0 : ReachesPlus target (cfg_T10 j (m+3)) (Cfg.headLeft C (ListBlank.append (([1, 0] :
      List (Fin 2))^(j)) ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1, 1] default))))))) (ListBlank.append [0, 1,
      1] default)) := by
    unfold cfg_T10
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1, 0, 0, 0] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1, 1] default)))))) ((ListBlank.append [0, 1,
      1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1, 0, 0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1, 1] default)))))
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List
      (Fin 2))^(m)) ((ListBlank.append [1, 0, 1, 1] default))))) (ListBlank.append (([0, 1] :
      List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] :
      List (Fin 2))^(m)) ((ListBlank.append [1, 0, 1, 1] default)))))) ((ListBlank.append [0, 1,
      1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1, 1] default))))))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin 2))^(m))
      ((ListBlank.append [1, 0, 1, 1] default))))))))) (ListBlank.append [1] default)) := by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] ((ListBlank.append (([0] : List (Fin
      2))^(m)) ((ListBlank.append [1, 0, 1, 1] default))))))))) (ListBlank.append [1] default)))
      = (cfg_T10 (j+2) m) := by
    unfold cfg_T10
    norm_tape
  rw [heq] at a4
  exact a4
private theorem rule_Tn_26 (j : ℕ) : ReachesPlus target (cfg_Tn j) (cfg_Tn (j+2)) := by
  have h0 : ReachesPlus target (cfg_Tn j) (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin
      2))^(j)) ((ListBlank.append [1, 0, 0, 1] default))) (ListBlank.append [0, 1, 1] default))
      := by
    unfold cfg_Tn
    step_block
  have h1 := sweep_C_L_10 j ((ListBlank.append [1, 0, 0, 1] default)) ((ListBlank.append [0, 1,
      1] default))
  have h2 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default))))
      (Cfg.headRight F (ListBlank.append [0, 1, 0, 1, 0, 0, 1] default) (ListBlank.append (([0,
      1] : List (Fin 2))^(j)) ((ListBlank.append [0, 1, 1] default)))) := by
    step_block
  have h3 := sweep_F_R_01 j ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] default))
      ((ListBlank.append [0, 1, 1] default))
  have h4 : ReachesPlus target (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] default))) (ListBlank.append [0, 1, 1] default))
      (Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin 2))^(j))
      ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] default))))) (ListBlank.append [1] default)) :=
      by
    step_block
  have a0 := h0
  have a1 := a0.trans_star h1
  have a2 := a1.trans h2
  have a3 := a2.trans_star h3
  have a4 := a3.trans h4
  have heq : ((Cfg.headRight F (ListBlank.append [0, 1] ((ListBlank.append (([0, 1] : List (Fin
      2))^(j)) ((ListBlank.append [0, 1, 0, 1, 0, 0, 1] default))))) (ListBlank.append [1]
      default))) = (cfg_Tn (j+2)) := by
    unfold cfg_Tn
    norm_tape
  rw [heq] at a4
  exact a4

set_option maxHeartbeats 800000 in
-- Multi-block transition with long tape prefix.
private theorem rule_Ea_27 (n : ℕ) : ReachesPlus target (cfg_Ea n) (cfg_Eb 0 (2*n+1)) := by
  have h0 : ReachesPlus target (cfg_Ea n) (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [0, 1, 1]
      default)) := by
    unfold cfg_Ea
    step_block
  have h1 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1, 0, 0,
      0, 1, 0, 1] default))))) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight F
      (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1, 0, 0, 0, 1, 0, 1]
      default))))) default) := by
    step_block
  have h2 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) default) (Cfg.headRight A
      (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin
      2))^(n)) ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [0, 1, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h3 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1, 0, 0, 0, 1, 0, 1]
      default))))) (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0,
      0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1, 0, 0, 0,
      1, 0, 1] default))))) (ListBlank.append [1, 0, 1, 1] default)) := by
    step_block
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [1, 0, 1, 1]
      default)) (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [1, 1] default))
      := by
    step_block
  have h5 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))))) (ListBlank.append [1, 1] default))
      (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1, 0,
      0, 0, 1, 0, 1] default))) (ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h6 := sweep_C_L_10 n ((ListBlank.append [1, 0, 0, 0, 1, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 1] default))
  have h7 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1, 0, 0, 0, 1, 0, 1] default)
      (ListBlank.append (([0, 1] : List (Fin 2))^(n)) ((ListBlank.append [1, 0, 1, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)))) (Cfg.headRight E
      (ListBlank.append [0, 0, 0, 1, 1, 0, 1] default) (ListBlank.append (([0, 1] : List (Fin
      2))^(n)) ((ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 1] default)))) := by
    step_block
  have h8 := sweep_E_R_01 n ((ListBlank.append [0, 0, 0, 1, 1, 0, 1] default))
      ((ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 1] default))
  have h9 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(n))
      ((ListBlank.append [0, 0, 0, 1, 1, 0, 1] default))) (ListBlank.append [1, 0, 1, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headLeft C
      (ListBlank.append (([0, 0] : List (Fin 2))^(n)) ((ListBlank.append [0, 0, 0, 1, 1, 0, 1]
      default))) (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h10 : ((Cfg.headLeft C (ListBlank.append (([0, 0] : List (Fin 2))^(n)) ((ListBlank.append
      [0, 0, 0, 1, 1, 0, 1] default))) (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))) = ((Cfg.headRight C (ListBlank.append
      [0, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1, 1, 0, 1]
      default))))) (ListBlank.append [0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 1] default))) := by
    norm_tape
  have h11 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0] ((ListBlank.append
      (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1, 1, 0, 1] default)))))
      (ListBlank.append [0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 1] default)) (Cfg.headRight E (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
      1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1, 1, 0, 1]
      default))))) (ListBlank.append [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
      default)) := by
    step_block
  have h12 : ReachesPlus target (Cfg.headRight E (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0,
      0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1, 1, 0,
      1] default))))) (ListBlank.append [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
      default)) (Cfg.headRight C (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n))
      ((ListBlank.append [1, 1, 0, 1] default))))) (ListBlank.append [1, 1, 1, 0, 1, 1]
      default)) := by
    step_block
  have h13 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin
      2))^(2*n)) ((ListBlank.append [1, 1, 0, 1] default))))) (ListBlank.append [1, 1, 1, 0, 1,
      1] default)) (Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin
      2))^(2*n)) ((ListBlank.append [1, 1, 0, 1] default))))) (ListBlank.append [1] default)) :=
      by
    step_block
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
  have heq : ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n))
      ((ListBlank.append [1, 1, 0, 1] default))))) (ListBlank.append [1] default))) = (cfg_Eb 0
      (2*n+1)) := by
    unfold cfg_Eb
    norm_tape
  rw [heq] at a12
  exact a12

set_option maxHeartbeats 800000 in
-- Multi-block transition with long tape prefix.
private theorem rule_Eb_28 (k t : ℕ) : ReachesPlus target (cfg_Eb k t) (cfg_Eb (k+1) t) := by
  have h0 : ReachesPlus target (cfg_Eb k t) (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) (ListBlank.append [0, 1, 1] default)) := by
    unfold cfg_Eb
    step_block
  have h1 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight F (ListBlank.append
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1, 1, 0, 1] default))))))) default) := by
    step_block
  have h2 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) default) (Cfg.headRight A (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append
      (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1] default)))))))
      (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h3 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append
      (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1] default)))))))
      (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headRight E
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] :
      List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1] default))))))) (ListBlank.append [1, 0,
      1, 1] default)) := by
    step_block
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0,
      0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] :
      List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1,
      0, 1] default))))))) (ListBlank.append [1, 0, 1, 1] default)) (Cfg.headRight E
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append
      (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1] default)))))))
      (ListBlank.append [1, 1] default)) := by
    step_block
  have h5 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append
      [1, 1, 0, 1] default))))))) (ListBlank.append [1, 1] default)) (Cfg.headRight C
      (ListBlank.append [0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1, 1, 0, 1] default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h6 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
      1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      (Cfg.headRight A (ListBlank.append [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append
      [1, 1, 0, 1] default))))))) (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h7 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin
      2))^(t)) ((ListBlank.append [1, 1, 0, 1] default))))))) (ListBlank.append [0, 1, 0, 1, 1,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headRight F
      (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1, 1, 0, 1] default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 1] default)) := by
    step_block
  have h8 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append
      (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k))
      ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) (ListBlank.append [0, 1, 0, 1, 1, 1, 1] default)) := by
    step_block
  have h9 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List
      (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0,
      1] default))))))) (ListBlank.append [0, 1, 0, 1, 1, 1, 1] default)) (Cfg.headRight B
      (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append
      (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k))
      ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1, 0, 1]
      default))))))) (ListBlank.append [1] default)) := by
    step_block
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
  have heq : ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] :
      List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1, 1,
      0, 1] default))))))) (ListBlank.append [1] default))) = (cfg_Eb (k+1) t) := by
    unfold cfg_Eb
    norm_tape
  rw [heq] at a9
  exact a9

set_option maxHeartbeats 800000 in
-- Multi-block transition with long tape prefix.
private theorem rule_Ec_29 (n : ℕ) : ReachesPlus target (cfg_Ec n) (cfg_Ed 0 (2*n+1)) := by
  have h0 : ReachesPlus target (cfg_Ec n) (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1] default))))) (ListBlank.append [0, 1, 1] default)) := by
    unfold cfg_Ec
    step_block
  have h1 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1]
      default))))) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight F (ListBlank.append [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List
      (Fin 2))^(n)) ((ListBlank.append [1] default))))) default) := by
    step_block
  have h2 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1] default))))) default) (Cfg.headRight A (ListBlank.append [0, 0, 0,
      0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append
      [1] default))))) (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) :=
      by
    step_block
  have h3 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1] default)))))
      (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headRight E
      (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
      ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1] default)))))
      (ListBlank.append [1, 0, 1, 1] default)) := by
    step_block
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1] default))))) (ListBlank.append [1, 0, 1, 1] default))
      (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1]
      default))))) (ListBlank.append [1, 1] default)) := by
    step_block
  have h5 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0] ((ListBlank.append (([1, 0] : List (Fin 2))^(n))
      ((ListBlank.append [1] default))))) (ListBlank.append [1, 1] default)) (Cfg.headLeft C
      (ListBlank.append (([1, 0] : List (Fin 2))^(n)) ((ListBlank.append [1] default)))
      (ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 1] default)) := by
    step_block
  have h6 := sweep_C_L_10 n ((ListBlank.append [1] default)) ((ListBlank.append [1, 0, 1, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
  have h7 : ReachesPlus target (Cfg.headLeft C (ListBlank.append [1] default) (ListBlank.append
      (([0, 1] : List (Fin 2))^(n)) ((ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)))) (Cfg.headRight E (ListBlank.append
      [0, 0, 0, 1] default) (ListBlank.append (([0, 1] : List (Fin 2))^(n)) ((ListBlank.append
      [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
      default)))) := by
    step_block
  have h8 := sweep_E_R_01 n ((ListBlank.append [0, 0, 0, 1] default)) ((ListBlank.append [1, 0,
      1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
  have h9 : ReachesPlus target (Cfg.headRight E (ListBlank.append (([0, 0] : List (Fin 2))^(n))
      ((ListBlank.append [0, 0, 0, 1] default))) (ListBlank.append [1, 0, 1, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headLeft C
      (ListBlank.append (([0, 0] : List (Fin 2))^(n)) ((ListBlank.append [0, 0, 0, 1] default)))
      (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 1] default)) := by
    step_block
  have h10 : ((Cfg.headLeft C (ListBlank.append (([0, 0] : List (Fin 2))^(n)) ((ListBlank.append
      [0, 0, 0, 1] default))) (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))) = ((Cfg.headRight C (ListBlank.append [0, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1] default)))))
      (ListBlank.append [0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 1] default))) := by
    norm_tape
  have h11 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0] ((ListBlank.append
      (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1] default))))) (ListBlank.append [0, 0,
      1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      (Cfg.headRight E (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0]
      ((ListBlank.append (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1] default)))))
      (ListBlank.append [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h12 : ReachesPlus target (Cfg.headRight E (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0,
      0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n)) ((ListBlank.append [1]
      default))))) (ListBlank.append [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
      default)) (Cfg.headRight C (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n))
      ((ListBlank.append [1] default))))) (ListBlank.append [1, 1, 1, 0, 1, 1] default)) := by
    step_block
  have h13 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin
      2))^(2*n)) ((ListBlank.append [1] default))))) (ListBlank.append [1, 1, 1, 0, 1, 1]
      default)) (Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n))
      ((ListBlank.append [1] default))))) (ListBlank.append [1] default)) := by
    step_block
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
  have heq : ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0] ((ListBlank.append (([0] : List (Fin 2))^(2*n))
      ((ListBlank.append [1] default))))) (ListBlank.append [1] default))) = (cfg_Ed 0 (2*n+1))
      := by
    unfold cfg_Ed
    norm_tape
  rw [heq] at a12
  exact a12

set_option maxHeartbeats 800000 in
-- Multi-block transition with long tape prefix.
private theorem rule_Ed_30 (k t : ℕ) : ReachesPlus target (cfg_Ed k t) (cfg_Ed (k+1) t) := by
  have h0 : ReachesPlus target (cfg_Ed k t) (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [0, 1, 1] default)) := by
    unfold cfg_Ed
    step_block
  have h1 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [0, 1, 1] default)) (Cfg.headRight F (ListBlank.append
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1] default))))))) default) := by
    step_block
  have h2 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) default) (Cfg.headRight A (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append
      (([0] : List (Fin 2))^(t)) ((ListBlank.append [1] default))))))) (ListBlank.append [0, 1,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h3 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append
      (([0] : List (Fin 2))^(t)) ((ListBlank.append [1] default))))))) (ListBlank.append [0, 1,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headRight E (ListBlank.append [1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1] default))))))) (ListBlank.append [1, 0, 1, 1] default)) := by
    step_block
  have h4 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0,
      0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] :
      List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [1, 0, 1, 1] default)) (Cfg.headRight E (ListBlank.append
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin
      2))^(t)) ((ListBlank.append [1] default))))))) (ListBlank.append [1, 1] default)) := by
    step_block
  have h5 : ReachesPlus target (Cfg.headRight E (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append
      [1] default))))))) (ListBlank.append [1, 1] default)) (Cfg.headRight C (ListBlank.append
      [0, 0, 0, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append
      [1] default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      := by
    step_block
  have h6 : ReachesPlus target (Cfg.headRight C (ListBlank.append [0, 0, 0, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
      1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      (Cfg.headRight A (ListBlank.append [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append
      [1] default))))))) (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 1] default)) := by
    step_block
  have h7 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin
      2))^(t)) ((ListBlank.append [1] default))))))) (ListBlank.append [0, 1, 0, 1, 1, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default)) (Cfg.headRight F
      (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t))
      ((ListBlank.append [1] default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      1] default)) := by
    step_block
  have h8 : ReachesPlus target (Cfg.headRight F (ListBlank.append [0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
      ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin
      2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] default))
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append
      (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k))
      ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1] default)))))))
      (ListBlank.append [0, 1, 0, 1, 1, 1, 1] default)) := by
    step_block
  have h9 : ReachesPlus target (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List
      (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [0, 1, 0, 1, 1, 1, 1] default)) (Cfg.headRight B
      (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] ((ListBlank.append
      (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : List (Fin 2))^(k))
      ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1] default)))))))
      (ListBlank.append [1] default)) := by
    step_block
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
  have heq : ((Cfg.headRight B (ListBlank.append [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 1] ((ListBlank.append (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] :
      List (Fin 2))^(k)) ((ListBlank.append (([0] : List (Fin 2))^(t)) ((ListBlank.append [1]
      default))))))) (ListBlank.append [1] default))) = (cfg_Ed (k+1) t) := by
    unfold cfg_Ed
    norm_tape
  rw [heq] at a9
  exact a9



/-! ## Countdown Inductions and Multiplicative Slice Accelerations -/

private theorem countdown_S0p (k a b c : ℕ) :
    ReachesStar target (cfg_S0p a (b + 3 * k) c) (cfg_S0p (a + 2 * k) b c) := by
  induction k generalizing a b with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : b + 3 * (k + 1) = (b + 3 * k) + 3 := by omega
    have h2 : a + 2 * (k + 1) = (a + 2) + 2 * k := by omega
    rw [h1, h2]
    exact ((rule_S0p_5 a (b + 3 * k) c).trans_star (ih (a + 2) b)).to_star

private theorem countdown_T1 (k j m : ℕ) :
    ReachesStar target (cfg_T1 j (m + 3 * k)) (cfg_T1 (j + 2 * k) m) := by
  induction k generalizing j m with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : m + 3 * (k + 1) = (m + 3 * k) + 3 := by omega
    have h2 : j + 2 * (k + 1) = (j + 2) + 2 * k := by omega
    rw [h1, h2]
    exact ((rule_T1_9 j (m + 3 * k)).trans_star (ih (j + 2) m)).to_star

private theorem countdown_T0 (k j m : ℕ) :
    ReachesStar target (cfg_T0 j (m + 3 * k)) (cfg_T0 (j + 2 * k) m) := by
  induction k generalizing j m with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : m + 3 * (k + 1) = (m + 3 * k) + 3 := by omega
    have h2 : j + 2 * (k + 1) = (j + 2) + 2 * k := by omega
    rw [h1, h2]
    exact ((rule_T0_13 j (m + 3 * k)).trans_star (ih (j + 2) m)).to_star

private theorem countdown_T11 (k j m : ℕ) :
    ReachesStar target (cfg_T11 j (m + 3 * k)) (cfg_T11 (j + 2 * k) m) := by
  induction k generalizing j m with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : m + 3 * (k + 1) = (m + 3 * k) + 3 := by omega
    have h2 : j + 2 * (k + 1) = (j + 2) + 2 * k := by omega
    rw [h1, h2]
    exact ((rule_T11_17 j (m + 3 * k)).trans_star (ih (j + 2) m)).to_star

private theorem countdown_T3 (k j m : ℕ) :
    ReachesStar target (cfg_T3 j (m + 3 * k)) (cfg_T3 (j + 2 * k) m) := by
  induction k generalizing j m with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : m + 3 * (k + 1) = (m + 3 * k) + 3 := by omega
    have h2 : j + 2 * (k + 1) = (j + 2) + 2 * k := by omega
    rw [h1, h2]
    exact ((rule_T3_21 j (m + 3 * k)).trans_star (ih (j + 2) m)).to_star

private theorem countdown_T10 (k j m : ℕ) :
    ReachesStar target (cfg_T10 j (m + 3 * k)) (cfg_T10 (j + 2 * k) m) := by
  induction k generalizing j m with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : m + 3 * (k + 1) = (m + 3 * k) + 3 := by omega
    have h2 : j + 2 * (k + 1) = (j + 2) + 2 * k := by omega
    rw [h1, h2]
    exact ((rule_T10_25 j (m + 3 * k)).trans_star (ih (j + 2) m)).to_star

private theorem accel_S0p_mod0 (k c : ℕ) :
    ReachesPlus target (cfg_S0p 0 (3 * k) c) (cfg_S0p 0 (4 * k + 1) (c + 4)) := by
  have hcd := countdown_S0p k 0 0 c
  simp only [Nat.zero_add] at hcd
  have hr := rule_S0p_2 (2 * k) c
  have heq : 2 * (2 * k) + 1 = 4 * k + 1 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_S0p_mod1 (k c : ℕ) :
    ReachesPlus target (cfg_S0p 0 (3 * k + 1) c) (cfg_S0p 0 (4 * k + 5) (c + 6)) := by
  have hcd := countdown_S0p k 0 1 c
  have hb : 1 + 3 * k = 3 * k + 1 := by omega
  simp only [Nat.zero_add, hb] at hcd
  have hr1 := rule_S0p_3 (2 * k) c
  have hr2 := rule_S0p_2 (2 * k + 2) (c + 2)
  have heq1 : 2 * (2 * k + 2) + 1 = 4 * k + 5 := by omega
  have heq2 : (c + 2) + 4 = c + 6 := by omega
  rw [heq1, heq2] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

private theorem accel_S0p_mod2_succ (k c : ℕ) :
    ReachesPlus target (cfg_S0p 0 (3 * k + 2) (c + 1)) (cfg_S0p 0 (4 * k + 8) c) := by
  have hcd := countdown_S0p k 0 2 (c + 1)
  have hb : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hb] at hcd
  have hr1 := rule_S0p_4 (2 * k) (c + 1)
  have hr2 := rule_S0z_1 (2 * k + 2) c
  have heq : 2 * (2 * k + 2) + 4 = 4 * k + 8 := by omega
  rw [heq] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

private theorem accel_S0p_mod2_zero (k : ℕ) :
    ReachesPlus target (cfg_S0p 0 (3 * k + 2) 0) (cfg_T1 0 (4 * k + 7)) := by
  have hcd := countdown_S0p k 0 2 0
  have hb : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hb] at hcd
  have hr1 := rule_S0p_4 (2 * k) 0
  have hr2 := rule_S0z_0 (2 * k + 2)
  have heq : 2 * (2 * k + 2) + 3 = 4 * k + 7 := by omega
  rw [heq] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

private theorem accel_T1_mod0 (k : ℕ) :
    ReachesPlus target (cfg_T1 0 (3 * k)) (cfg_Tn 0) := by
  have hcd := countdown_T1 k 0 0
  simp only [Nat.zero_add] at hcd
  exact hcd.trans_plus (rule_T1_6 (2 * k))

private theorem accel_T1_mod1 (k : ℕ) :
    ReachesPlus target (cfg_T1 0 (3 * k + 1)) (cfg_T11 0 (4 * k + 7)) := by
  have hcd := countdown_T1 k 0 1
  have hm : 1 + 3 * k = 3 * k + 1 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr := rule_T1_7 (2 * k)
  have heq : 2 * (2 * k) + 7 = 4 * k + 7 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T1_mod2 (k : ℕ) :
    ReachesPlus target (cfg_T1 0 (3 * k + 2)) (cfg_S0p 0 (4 * k + 5) 3) := by
  have hcd := countdown_T1 k 0 2
  have hm : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr := rule_T1_8 (2 * k)
  have heq : 2 * (2 * k) + 5 = 4 * k + 5 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T11_mod0 (k : ℕ) :
    ReachesPlus target (cfg_T11 0 (3 * k)) (cfg_T1 0 (4 * k + 6)) := by
  have hcd := countdown_T11 k 0 0
  simp only [Nat.zero_add] at hcd
  have hr := rule_T11_14 (2 * k)
  have heq : 2 * (2 * k) + 6 = 4 * k + 6 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T11_mod1 (k : ℕ) :
    ReachesPlus target (cfg_T11 0 (3 * k + 1)) (cfg_T3 0 (4 * k + 7)) := by
  have hcd := countdown_T11 k 0 1
  have hm : 1 + 3 * k = 3 * k + 1 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr := rule_T11_15 (2 * k)
  have heq : 2 * (2 * k) + 7 = 4 * k + 7 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T11_mod2 (k : ℕ) :
    ReachesPlus target (cfg_T11 0 (3 * k + 2)) (cfg_Eb 0 (4 * k + 1)) := by
  have hcd := countdown_T11 k 0 2
  have hm : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr1 := rule_T11_16 (2 * k)
  have hr2 := rule_Ea_27 (2 * k)
  have heq : 2 * (2 * k) + 1 = 4 * k + 1 := by omega
  rw [heq] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

private theorem accel_T3_mod0 (k : ℕ) :
    ReachesPlus target (cfg_T3 0 (3 * k)) (cfg_T1 0 (4 * k + 8)) := by
  have hcd := countdown_T3 k 0 0
  simp only [Nat.zero_add] at hcd
  have hr := rule_T3_18 (2 * k)
  have heq : 2 * (2 * k) + 8 = 4 * k + 8 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T3_mod1 (k : ℕ) :
    ReachesPlus target (cfg_T3 0 (3 * k + 1)) (cfg_T10 0 (4 * k + 7)) := by
  have hcd := countdown_T3 k 0 1
  have hm : 1 + 3 * k = 3 * k + 1 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr := rule_T3_19 (2 * k)
  have heq : 2 * (2 * k) + 7 = 4 * k + 7 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T3_mod2 (k : ℕ) :
    ReachesPlus target (cfg_T3 0 (3 * k + 2)) (cfg_Ed 0 (4 * k + 1)) := by
  have hcd := countdown_T3 k 0 2
  have hm : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr1 := rule_T3_20 (2 * k)
  have hr2 := rule_Ec_29 (2 * k)
  have heq : 2 * (2 * k) + 1 = 4 * k + 1 := by omega
  rw [heq] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

private theorem accel_T10_mod0 (k : ℕ) :
    ReachesPlus target (cfg_T10 0 (3 * k)) (cfg_T0 0 (4 * k + 6)) := by
  have hcd := countdown_T10 k 0 0
  simp only [Nat.zero_add] at hcd
  have hr := rule_T10_22 (2 * k)
  have heq : 2 * (2 * k) + 6 = 4 * k + 6 := by omega
  rw [heq] at hr
  exact hcd.trans_plus hr

private theorem accel_T10_mod1_halt (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T10 0 (3 * k + 1)) cfg' ∧
      (step target cfg').isNone := by
  have hcd := countdown_T10 k 0 1
  have hm : 1 + 3 * k = 3 * k + 1 := by omega
  simp only [Nat.zero_add, hm] at hcd
  obtain ⟨cfg', hh1, hh2⟩ := halt_T10_23 (2 * k)
  exact ⟨cfg', hcd.trans_plus hh1, hh2⟩

private theorem accel_T10_mod2_halt (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T10 0 (3 * k + 2)) cfg' ∧
      (step target cfg').isNone := by
  have hcd := countdown_T10 k 0 2
  have hm : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hm] at hcd
  obtain ⟨cfg', hh1, hh2⟩ := halt_T10_24 (2 * k)
  exact ⟨cfg', hcd.trans_plus hh1, hh2⟩

private theorem accel_T0_mod0 (k : ℕ) :
    ReachesPlus target (cfg_T0 0 (3 * k)) (cfg_T1 0 (4 * k + 5)) := by
  have hcd := countdown_T0 k 0 0
  simp only [Nat.zero_add] at hcd
  have hr1 := rule_T0_10 (2 * k)
  have hr2 := rule_S0z_0 (2 * k + 1)
  have heq : 2 * (2 * k + 1) + 3 = 4 * k + 5 := by omega
  rw [heq] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

private theorem accel_T0_mod1_halt (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T0 0 (3 * k + 1)) cfg' ∧
      (step target cfg').isNone := by
  have hcd := countdown_T0 k 0 1
  have hm : 1 + 3 * k = 3 * k + 1 := by omega
  simp only [Nat.zero_add, hm] at hcd
  obtain ⟨cfg', hh1, hh2⟩ := halt_T0_11 (2 * k)
  exact ⟨cfg', hcd.trans_plus hh1, hh2⟩

private theorem accel_T0_mod2 (k : ℕ) :
    ReachesPlus target (cfg_T0 0 (3 * k + 2)) (cfg_T1 0 (4 * k + 7)) := by
  have hcd := countdown_T0 k 0 2
  have hm : 2 + 3 * k = 3 * k + 2 := by omega
  simp only [Nat.zero_add, hm] at hcd
  have hr1 := rule_T0_12 (2 * k)
  have hr2 := rule_S0z_0 (2 * k + 2)
  have heq : 2 * (2 * k + 2) + 3 = 4 * k + 7 := by omega
  rw [heq] at hr2
  exact hcd.trans_plus (hr1.trans hr2)

/-! ## Level A: Closed Pattern Set (`ps`, `is_closed_pattern_set`, `has_collatz_reduction`) -/

/-- Hub pattern `pat_B` unifying `S0p(0, b, c)`, `Eb(k, t)`, and `Ed(k, t)`. -/
def pat_B : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0] 2 (.rep [1, 0] 0 (.rep [1, 0] 3 (.rep [0, 1] 0
      (.rep [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
          1
        (.rep [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] 4
          (.rep [0] 5 (.rep [1, 1, 0] 6 (.rep [1] 1 .default))))))))
    head := some B
    right := .rep [0, 0, 1] 0 (.sym 1 .default) }

/-- Variable condition for `pat_B`. -/
def cond_B : VarCond :=
  .or (.and (.ge_const 0 1) (.and (.not (.ge_const 0 2)) (.and (.not (.ge_const 1 1))
        (.and (.not (.ge_const 4 1)) (.and (.not (.ge_const 5 1)) (.not (.ge_const 6 1)))))))
      (.and (.not (.ge_const 0 1)) (.and (.ge_const 1 1) (.and (.not (.ge_const 1 2))
        (.and (.not (.ge_const 2 1)) (.and (.not (.ge_const 3 1)) (.not (.ge_const 6 2)))))))

/-- Hub pattern `pat_F` unifying `T1(0, m)` and `Tn(j)`. -/
def pat_F : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1
      (.rep [0] 2 (.rep [1] 0 .default)))))))
    head := some F
    right := .sym 1 .default }

/-- Variable condition for `pat_F`. -/
def cond_F : VarCond :=
  .or (.and (.ge_const 0 1) (.and (.not (.ge_const 0 2)) (.not (.ge_const 1 1))))
      (.and (.not (.ge_const 0 1)) (.not (.ge_const 2 1)))

/-- Closed two-pattern set for `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_B, cond_B), (pat_F, cond_F)]

private theorem mem_S0p_0 (b c : ℕ) : IsInPatternSet ps (cfg_S0p 0 b c) := by
  refine ⟨(pat_B, cond_B), List.Mem.head _,
    fun i => match i with | 0 => 1 | 2 => b | 3 => c | _ => 0, ?_, ?_⟩
  · simp only [pat_B, cfg_S0p, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
      evalTapeExpr_rep, list_pow_zero, list_pow_succ, List.append_nil,
      ListBlank.append_nil, ListBlank.append_cons]
  · simp [cond_B, evalVarCond]

private theorem mem_Eb (k t : ℕ) : IsInPatternSet ps (cfg_Eb k t) := by
  refine ⟨(pat_B, cond_B), List.Mem.head _,
    fun i => match i with | 1 => 1 | 4 => k | 5 => t | 6 => 1 | _ => 0, ?_, ?_⟩
  · simp only [pat_B, cfg_Eb, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
      evalTapeExpr_rep, list_pow_zero, list_pow_succ, List.append_nil,
      ListBlank.append_nil, ListBlank.append_cons]
  · simp [cond_B, evalVarCond]

private theorem mem_Ed (k t : ℕ) : IsInPatternSet ps (cfg_Ed k t) := by
  refine ⟨(pat_B, cond_B), List.Mem.head _,
    fun i => match i with | 1 => 1 | 4 => k | 5 => t | _ => 0, ?_, ?_⟩
  · simp only [pat_B, cfg_Ed, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
      evalTapeExpr_rep, list_pow_zero, list_pow_succ, List.append_nil,
      ListBlank.append_nil, ListBlank.append_cons]
  · simp [cond_B, evalVarCond]

private theorem mem_T1_0 (m : ℕ) : IsInPatternSet ps (cfg_T1 0 m) := by
  refine ⟨(pat_F, cond_F), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => 1 | 2 => m | _ => 0, ?_, ?_⟩
  · simp only [pat_F, cfg_T1, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
      evalTapeExpr_rep, list_pow_zero, list_pow_succ, List.append_nil,
      ListBlank.append_nil, ListBlank.append_cons]
  · simp [cond_F, evalVarCond]

private theorem mem_Tn (j : ℕ) : IsInPatternSet ps (cfg_Tn j) := by
  refine ⟨(pat_F, cond_F), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 1 => j | _ => 0, ?_, ?_⟩
  · simp only [pat_F, cfg_Tn, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
      evalTapeExpr_rep, list_pow_zero, ListBlank.append_nil, ListBlank.append_cons]
  · simp [cond_F, evalVarCond]

private theorem step_S0p_0 (b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_S0p 0 b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have hmod : b = 3 * (b / 3) ∨ b = 3 * (b / 3) + 1 ∨ b = 3 * (b / 3) + 2 := by omega
  rcases hmod with hb0 | hb1 | hb2
  · rw [hb0]
    exact ⟨cfg_S0p 0 (4 * (b / 3) + 1) (c + 4), accel_S0p_mod0 (b / 3) c,
      Or.inl (mem_S0p_0 (4 * (b / 3) + 1) (c + 4))⟩
  · rw [hb1]
    exact ⟨cfg_S0p 0 (4 * (b / 3) + 5) (c + 6), accel_S0p_mod1 (b / 3) c,
      Or.inl (mem_S0p_0 (4 * (b / 3) + 5) (c + 6))⟩
  · rw [hb2]
    rcases c with _ | c
    · exact ⟨cfg_T1 0 (4 * (b / 3) + 7), accel_S0p_mod2_zero (b / 3),
        Or.inl (mem_T1_0 (4 * (b / 3) + 7))⟩
    · exact ⟨cfg_S0p 0 (4 * (b / 3) + 8) c, accel_S0p_mod2_succ (b / 3) c,
        Or.inl (mem_S0p_0 (4 * (b / 3) + 8) c)⟩

private theorem step_T0_0 (m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T0 0 m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have hmod : m = 3 * (m / 3) ∨ m = 3 * (m / 3) + 1 ∨ m = 3 * (m / 3) + 2 := by omega
  rcases hmod with hm0 | hm1 | hm2
  · rw [hm0]
    exact ⟨cfg_T1 0 (4 * (m / 3) + 5), accel_T0_mod0 (m / 3),
      Or.inl (mem_T1_0 (4 * (m / 3) + 5))⟩
  · rw [hm1]
    obtain ⟨cfg', hh1, hh2⟩ := accel_T0_mod1_halt (m / 3)
    exact ⟨cfg', hh1, Or.inr hh2⟩
  · rw [hm2]
    exact ⟨cfg_T1 0 (4 * (m / 3) + 7), accel_T0_mod2 (m / 3),
      Or.inl (mem_T1_0 (4 * (m / 3) + 7))⟩

private theorem step_T10_0 (m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T10 0 m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have hmod : m = 3 * (m / 3) ∨ m = 3 * (m / 3) + 1 ∨ m = 3 * (m / 3) + 2 := by omega
  rcases hmod with hm0 | hm1 | hm2
  · rw [hm0]
    obtain ⟨cfg', h1, h2⟩ := step_T0_0 (4 * (m / 3) + 6)
    exact ⟨cfg', (accel_T10_mod0 (m / 3)).trans h1, h2⟩
  · rw [hm1]
    obtain ⟨cfg', hh1, hh2⟩ := accel_T10_mod1_halt (m / 3)
    exact ⟨cfg', hh1, Or.inr hh2⟩
  · rw [hm2]
    obtain ⟨cfg', hh1, hh2⟩ := accel_T10_mod2_halt (m / 3)
    exact ⟨cfg', hh1, Or.inr hh2⟩

private theorem step_T3_0 (m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T3 0 m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have hmod : m = 3 * (m / 3) ∨ m = 3 * (m / 3) + 1 ∨ m = 3 * (m / 3) + 2 := by omega
  rcases hmod with hm0 | hm1 | hm2
  · rw [hm0]
    exact ⟨cfg_T1 0 (4 * (m / 3) + 8), accel_T3_mod0 (m / 3),
      Or.inl (mem_T1_0 (4 * (m / 3) + 8))⟩
  · rw [hm1]
    obtain ⟨cfg', h1, h2⟩ := step_T10_0 (4 * (m / 3) + 7)
    exact ⟨cfg', (accel_T3_mod1 (m / 3)).trans h1, h2⟩
  · rw [hm2]
    exact ⟨cfg_Ed 0 (4 * (m / 3) + 1), accel_T3_mod2 (m / 3),
      Or.inl (mem_Ed 0 (4 * (m / 3) + 1))⟩

private theorem step_T11_0 (m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T11 0 m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have hmod : m = 3 * (m / 3) ∨ m = 3 * (m / 3) + 1 ∨ m = 3 * (m / 3) + 2 := by omega
  rcases hmod with hm0 | hm1 | hm2
  · rw [hm0]
    exact ⟨cfg_T1 0 (4 * (m / 3) + 6), accel_T11_mod0 (m / 3),
      Or.inl (mem_T1_0 (4 * (m / 3) + 6))⟩
  · rw [hm1]
    obtain ⟨cfg', h1, h2⟩ := step_T3_0 (4 * (m / 3) + 7)
    exact ⟨cfg', (accel_T11_mod1 (m / 3)).trans h1, h2⟩
  · rw [hm2]
    exact ⟨cfg_Eb 0 (4 * (m / 3) + 1), accel_T11_mod2 (m / 3),
      Or.inl (mem_Eb 0 (4 * (m / 3) + 1))⟩

private theorem step_T1_0 (m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T1 0 m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have hmod : m = 3 * (m / 3) ∨ m = 3 * (m / 3) + 1 ∨ m = 3 * (m / 3) + 2 := by omega
  rcases hmod with hm0 | hm1 | hm2
  · rw [hm0]
    exact ⟨cfg_Tn 0, accel_T1_mod0 (m / 3), Or.inl (mem_Tn 0)⟩
  · rw [hm1]
    obtain ⟨cfg', h1, h2⟩ := step_T11_0 (4 * (m / 3) + 7)
    exact ⟨cfg', (accel_T1_mod1 (m / 3)).trans h1, h2⟩
  · rw [hm2]
    exact ⟨cfg_S0p 0 (4 * (m / 3) + 5) 3, accel_T1_mod2 (m / 3),
      Or.inl (mem_S0p_0 (4 * (m / 3) + 5) 3)⟩

private theorem init_reaches_T1 : ReachesPlus target (init []) (cfg_T1 0 1) := by
  unfold cfg_T1
  step_block

private theorem init_reaches_S0p : ReachesPlus target (init []) (cfg_S0p 0 125 3) := by
  have h1 := init_reaches_T1.trans (accel_T1_mod1 0)
  have h2 := h1.trans (accel_T11_mod1 2)
  have h3 := h2.trans (accel_T3_mod0 5)
  have h4 := h3.trans (accel_T1_mod1 9)
  have h5 := h4.trans (accel_T11_mod1 14)
  have h6 := h5.trans (accel_T3_mod0 21)
  exact h6.trans (accel_T1_mod2 30)

/-- `ps` is a closed pattern set for `target`. -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_S0p 0 125 3, init_reaches_S0p.to_star, mem_S0p_0 125 3⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · simp only [cond_B, evalVarCond] at h_cond
    rcases h_cond with ⟨h0a, h0b, h1, h4, h5, h6⟩ | ⟨h0, h1a, h1b, h2, h3, h6⟩
    · have hv0 : vars 0 = 1 := by omega
      have hv1 : vars 1 = 0 := by omega
      have hv4 : vars 4 = 0 := by omega
      have hv5 : vars 5 = 0 := by omega
      have hv6 : vars 6 = 0 := by omega
      have heval : evalTapePattern pat_B vars = cfg_S0p 0 (vars 2) (vars 3) := by
        simp only [pat_B, cfg_S0p, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
          evalTapeExpr_rep, hv0, hv1, hv4, hv5, hv6, list_pow_zero, list_pow_succ,
          List.append_nil, ListBlank.append_nil, ListBlank.append_cons]
      rw [heval]
      exact step_S0p_0 (vars 2) (vars 3)
    · have hv0 : vars 0 = 0 := by omega
      have hv1 : vars 1 = 1 := by omega
      have hv2 : vars 2 = 0 := by omega
      have hv3 : vars 3 = 0 := by omega
      have hv6 : vars 6 = 0 ∨ vars 6 = 1 := by omega
      rcases hv6 with hv6_0 | hv6_1
      · have heval : evalTapePattern pat_B vars = cfg_Ed (vars 4) (vars 5) := by
          simp only [pat_B, cfg_Ed, evalTapePattern_some, evalTapeExpr_default,
              evalTapeExpr_sym,
            evalTapeExpr_rep, hv0, hv1, hv2, hv3, hv6_0, list_pow_zero, list_pow_succ,
            List.append_nil, ListBlank.append_nil, ListBlank.append_cons]
        rw [heval]
        exact ⟨cfg_Ed (vars 4 + 1) (vars 5), rule_Ed_30 (vars 4) (vars 5),
          Or.inl (mem_Ed (vars 4 + 1) (vars 5))⟩
      · have heval : evalTapePattern pat_B vars = cfg_Eb (vars 4) (vars 5) := by
          simp only [pat_B, cfg_Eb, evalTapePattern_some, evalTapeExpr_default,
              evalTapeExpr_sym,
            evalTapeExpr_rep, hv0, hv1, hv2, hv3, hv6_1, list_pow_zero, list_pow_succ,
            List.append_nil, ListBlank.append_nil, ListBlank.append_cons]
        rw [heval]
        exact ⟨cfg_Eb (vars 4 + 1) (vars 5), rule_Eb_28 (vars 4) (vars 5),
          Or.inl (mem_Eb (vars 4 + 1) (vars 5))⟩
  · simp only [cond_F, evalVarCond] at h_cond
    rcases h_cond with ⟨h0a, h0b, h1⟩ | ⟨h0, h2⟩
    · have hv0 : vars 0 = 1 := by omega
      have hv1 : vars 1 = 0 := by omega
      have heval : evalTapePattern pat_F vars = cfg_T1 0 (vars 2) := by
        simp only [pat_F, cfg_T1, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
          evalTapeExpr_rep, hv0, hv1, list_pow_zero, list_pow_succ,
          List.append_nil, ListBlank.append_nil, ListBlank.append_cons]
      rw [heval]
      exact step_T1_0 (vars 2)
    · have hv0 : vars 0 = 0 := by omega
      have hv2 : vars 2 = 0 := by omega
      have heval : evalTapePattern pat_F vars = cfg_Tn (vars 1) := by
        simp only [pat_F, cfg_Tn, evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym,
          evalTapeExpr_rep, hv0, hv2, list_pow_zero, ListBlank.append_nil, ListBlank.append_cons]
      rw [heval]
      exact ⟨cfg_Tn (vars 1 + 2), rule_Tn_26 (vars 1), Or.inl (mem_Tn (vars 1 + 2))⟩

/-- `target` has a Collatz-like reduction via `ps`. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Level B: Collatz-like Acceleration (`State`, `start`, `encode`, `next`) -/

/-- Canonical configuration families for the Collatz-like acceleration of `target`. -/
inductive State where
  | S0z (a c : ℕ)
  | S0p (a b c : ℕ)
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
  deriving DecidableEq, Repr

/-- Initial accelerated state `T1(0, 1)`, reached from `init []` in 22 steps. -/
def start : State := .T1 0 1

/-- Decode an accelerated `State` into its concrete Turing machine configuration. -/
@[simp]
def encode : State → Cfg (Fin 2) (Fin 6)
  | .S0z a c => cfg_S0z a c
  | .S0p a b c => cfg_S0p a b c
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

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .S0z a 0 => some (.T1 0 (2 * a + 3))
  | .S0z a (c + 1) => some (.S0p 0 (2 * a + 4) c)
  | .S0p a 0 c => some (.S0p 0 (2 * a + 1) (c + 4))
  | .S0p a 1 c => some (.S0p (a + 2) 0 (c + 2))
  | .S0p a 2 c => some (.S0z (a + 2) c)
  | .S0p a (b + 3) c => some (.S0p (a + 2) b c)
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

/-- `next` is a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := by
    dsimp [start, encode]
    exact init_reaches_T1.to_star
  step_some s s' hnext := by
    rcases s with
      ⟨a, _ | c⟩ | ⟨a, _ | _ | _ | b, c⟩ | ⟨j, _ | _ | _ | m⟩ | ⟨j, _ | _ | _ | m⟩ |
      ⟨j, _ | _ | _ | m⟩ | ⟨j, _ | _ | _ | m⟩ | ⟨j, _ | _ | _ | m⟩ | ⟨j⟩ | ⟨n⟩ | ⟨k, t⟩ |
      ⟨n⟩ | ⟨k, t⟩ <;>
      dsimp [next] at hnext <;>
      (try contradiction) <;>
      injection hnext with h_eq <;>
      subst h_eq <;>
      dsimp [encode]
    · exact rule_S0z_0 a
    · exact rule_S0z_1 a c
    · exact rule_S0p_2 a c
    · exact rule_S0p_3 a c
    · exact rule_S0p_4 a c
    · exact rule_S0p_5 a b c
    · exact rule_T1_6 j
    · exact rule_T1_7 j
    · exact rule_T1_8 j
    · exact rule_T1_9 j m
    · exact rule_T0_10 j
    · exact rule_T0_12 j
    · exact rule_T0_13 j m
    · exact rule_T11_14 j
    · exact rule_T11_15 j
    · exact rule_T11_16 j
    · exact rule_T11_17 j m
    · exact rule_T3_18 j
    · exact rule_T3_19 j
    · exact rule_T3_20 j
    · exact rule_T3_21 j m
    · exact rule_T10_22 j
    · exact rule_T10_25 j m
    · exact rule_Tn_26 j
    · exact rule_Ea_27 n
    · exact rule_Eb_28 k t
    · exact rule_Ec_29 n
    · exact rule_Ed_30 k t
  step_none s hnext := by
    rcases s with
      ⟨a, _ | c⟩ | ⟨a, _ | _ | _ | b, c⟩ | ⟨j, _ | _ | _ | m⟩ | ⟨j, _ | _ | _ | m⟩ |
      ⟨j, _ | _ | _ | m⟩ | ⟨j, _ | _ | _ | m⟩ | ⟨j, _ | _ | _ | m⟩ | ⟨j⟩ | ⟨n⟩ | ⟨k, t⟩ |
      ⟨n⟩ | ⟨k, t⟩ <;>
      dsimp [next] at hnext <;>
      (try contradiction) <;>
      dsimp [encode]
    · obtain ⟨cfg', h1, h2⟩ := halt_T0_11 j
      exact ⟨cfg', h1.to_star, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := halt_T10_23 j
      exact ⟨cfg', h1.to_star, h2⟩
    · obtain ⟨cfg', h1, h2⟩ := halt_T10_24 j
      exact ⟨cfg', h1.to_star, h2⟩

/-- `target` halts iff the accelerated transition function `next` halts from `start`. -/
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

/-- Initial state `T 1` (`T1(0, 1)`) for the high-level Collatz-like acceleration. -/
def highLevelStart : HighLevelState := .T 1

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

end BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
