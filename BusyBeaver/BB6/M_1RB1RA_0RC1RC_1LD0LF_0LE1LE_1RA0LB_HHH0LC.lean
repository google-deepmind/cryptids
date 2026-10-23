/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC` (Counter6)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`
(see <https://wiki.bbchallenge.org/wiki/Counter6>)
(**Counter6**, `cryptid_11`, holdout `#125`, `suspect_91`).

Starting from the blank tape (`init []`), the trajectory reaches a closed system of 12 canonical
configuration sub-families (`D7`, `D74`, `D75`, `D76`, `D77`, `D158`, `D160`, `D162`, `D230`,
`D231`, `D294`, `D296`) unified into a single `TapePattern` `pat_A` with a 12-way parameter guard
`cond_A`.

## Collatz-like Acceleration Rules

```text
Base hub template:
D_base(a, b, r) = 0^inf (11)^(a+1) D> (11)^(b+1) r

Sub-families:
D7(a, b)         = D_base(a, b, 1 0^inf)
D74(a, b)        = D_base(a, b, 0101 0^inf)
D75(a, b, c)     = D_base(a, b, 000 (00)^c 101 0^inf)
D76(a, b, c)     = D_base(a, b, 0111 (11)^c 01 0^inf)
D77(a, b, c, d)  = D_base(a, b, 000 (00)^c 111 (11)^d 01 0^inf)
D158(a, b, c)    = D_base(a, b, 011 (11)^c 01 0^inf)
D160(a, b, c)    = D_base(a, b, 0100 (00)^c 101 0^inf)
D162(a, b, c, d) = D_base(a, b, 0100 (00)^c 111 (11)^d 01 0^inf)
D230(a, b, c)    = D_base(a, b, 00 (00)^c 1 0^inf)
D231(a, b, c, d) = D_base(a, b, 000 (00)^c 11 (11)^d 01 0^inf)
D294(a, b, c)    = D_base(a, b, 01000 (00)^c 1 0^inf)
D296(a, b, c, d) = D_base(a, b, 0100 (00)^c 11 (11)^d 01 0^inf)

Left-shift rule (all 12 families X):
X(a+1, b, ...)      -> X(a, b+1, ...)

Boundary rules (a = 0):
D7(0, b)            -> D77(0, 0, 0, b+1)
D74(0, b)           -> D7(b+2, 0)
D75(0, b, 0)        -> D158(b+1, 0, 0)
D75(0, b, c+1)      -> D160(b+1, 0, c)
D76(0, b, 0)        -> D75(0, 0, b+2)
D76(0, b, c+1)      -> D77(0, 0, b+2, c)
D77(0, b, 0, d)     -> D158(b+1, 0, d+1)
D77(0, b, c+1, d)   -> D162(b+1, 0, c, d)
D158(0, b, 0)       -> D230(0, 0, b+3)
D158(0, b, c+1)     -> D231(0, 0, b+2, c)
D160(0, b, 0)       -> D74(b+2, 0)
D160(0, b, c+1)     -> D75(b+2, 0, c)
D162(0, b, 0, d)    -> D76(b+2, 0, d)
D162(0, b, c+1, d)  -> D77(b+2, 0, c, d)
D230(0, b, 0)       -> Halt
D230(0, b, 1)       -> D74(b+1, 0)
D230(0, b, c+2)     -> D294(b+1, 0, c)
D231(0, b, 0, d)    -> D76(b+1, 0, d)
D231(0, b, c+1, d)  -> D296(b+1, 0, c, d)
D294(0, b, c)       -> D230(b+2, 0, c)
D296(0, b, 0, d)    -> D158(b+2, 0, d)
D296(0, b, c+1, d)  -> D231(b+2, 0, c, d)

Start: D7(0, 0), reached after 12 raw TM steps
```

## High-Level Collatz-like Acceleration

`HighLevelState` and `highLevelNext` collapse all 12 `State` families (`D7..D296`, up to 4
counters) with zero recursive helpers into a single closed-form map over `D(p, x, d)` (`p : Bool`,
`x d : ℕ`), where `D(false, x, d)` encodes `D76(0, x, d)` and `D(true, x, d)` encodes
`D231(0, 0, x, d)`, starting from `D(true, 3, 1)`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Rightward shift across `(11)^k` in state `A`. -/
private theorem shift_A_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [1, 1] l)
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift in state `C` converting `(11)^k` on the left to `(00)^k` on the right. -/
private theorem shift_C_11_to_00 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [1] (ListBlank.append (([0, 0] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight C
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [0, 0] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([0, 0] : List (Fin 2)) ^ k) (ListBlank.append [0, 0] r) =
          ListBlank.append (([0, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward shift in state `D` moving `(11)^k` from the left to the right. -/
private theorem shift_D_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l))
        (ListBlank.append [1] r))
      (Cfg.headRight D (ListBlank.append [1] l)
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight D
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l)))
            (ListBlank.append [1] r))
          (Cfg.headRight D
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l))
            (ListBlank.append [1] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l)) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] l) := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Base configuration template `0^∞ (11)^(a+1) D> (11)^(b+1) r`. -/
def cfg_D_base (a b : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b) r))

/-- Left-shift rule for `a ≥ 1`: `D_base(a + 1, b, r) -> D_base(a, b + 1, r)`. -/
private theorem step_D_left (a b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target (cfg_D_base (a + 1) b r) (cfg_D_base a (b + 1) r) := by
  unfold cfg_D_base
  rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) a,
    ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) b]
  bb_steps

/-- From `D_base(0, b, r)`, bounce off the left blank tape and shift right in state `A` to `r`. -/
private theorem sweep_D_zero_to_A (b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target (cfg_D_base 0 b r)
      (Cfg.headRight A
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
          (ListBlank.append [1, 1, 1] default))
        r) := by
  have h1 :
      ReachesPlus target (cfg_D_base 0 b r)
        (Cfg.headRight A
          (ListBlank.append [1, 1] (ListBlank.append [1, 1, 1] default))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ b) r)) := by
    unfold cfg_D_base
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_A_11 b
    (ListBlank.append [1, 1] (ListBlank.append [1, 1, 1] default)) r
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1]
          (ListBlank.append [1, 1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
          (ListBlank.append [1, 1, 1] default) := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_l] at h12

/-- Equivalent form of `sweep_D_zero_to_A` with `[1, 1, 1]` at the head of the left tape. -/
private theorem sweep_D_zero_to_A_top (b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target (cfg_D_base 0 b r)
      (Cfg.headRight A
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) default))
        r) := by
  have h := sweep_D_zero_to_A b r
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
        (ListBlank.append [1, 1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) default) := by
    have h1 :
        ListBlank.append [1, 1, 1] (default : ListBlank (Fin 2)) =
          ListBlank.append [1] (ListBlank.append [1, 1] default) := rfl
    rw [h1, swap_1_11_pow, ListBlank.append_pow_comm]
    rfl
  rwa [h_l] at h

/-- Sweep for `a = 0` when the right suffix starts with `[0, 1, 0]`. -/
private theorem sweep_D_zero_010 (b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (cfg_D_base 0 b (ListBlank.append [0, 1, 0] r))
      (cfg_D_base (b + 2) 0 r) := by
  have h1 := sweep_D_zero_to_A_top b (ListBlank.append [0, 1, 0] r)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) default))
          (ListBlank.append [0, 1, 0] r))
        (cfg_D_base (b + 2) 0 r) := by
    unfold cfg_D_base
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) (b + 1),
      list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1.trans h2

/-- Sweep for `a = 0` when the right suffix starts with `[0, 0, 0]`. -/
private theorem sweep_D_zero_000 (b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (cfg_D_base 0 b (ListBlank.append [0, 0, 0] r))
      (cfg_D_base (b + 1) 0 (ListBlank.append [0, 1] r)) := by
  have h1 := sweep_D_zero_to_A_top b (ListBlank.append [0, 0, 0] r)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) default))
          (ListBlank.append [0, 0, 0] r))
        (cfg_D_base (b + 1) 0 (ListBlank.append [0, 1] r)) := by
    unfold cfg_D_base
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1.trans h2

/-- Sweep for `a = 0` when the right suffix starts with `[0, 1, 1]`. -/
private theorem sweep_D_zero_011 (b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (cfg_D_base 0 b (ListBlank.append [0, 1, 1] r))
      (cfg_D_base 0 0
        (ListBlank.append [0, 0, 0]
          (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2)) r))) := by
  have h1 := sweep_D_zero_to_A b (ListBlank.append [0, 1, 1] r)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
            (ListBlank.append [1, 1, 1] default))
          (ListBlank.append [0, 1, 1] r))
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 2))
            (ListBlank.append [1, 1, 1] default))
          (ListBlank.append [1] r)) := by
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) (b + 1)]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_11_to_00 (b + 2) (ListBlank.append [1, 1, 1] default) r
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1, 1, 1] default)
          (ListBlank.append [1] (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2)) r)))
        (cfg_D_base 0 0
          (ListBlank.append [0, 0, 0]
            (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2)) r))) := by
    unfold cfg_D_base
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h123.trans h4

/-! ## Canonical Hub Configurations -/

def cfg_D7 (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b (ListBlank.append [1] default)

def cfg_D74 (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b (ListBlank.append [0, 1, 0, 1] default)

def cfg_D75 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 0, 1] default)))

def cfg_D76 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1] default)))

def cfg_D77 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def cfg_D158 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1] default)))

def cfg_D160 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 0, 1] default)))

def cfg_D162 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def cfg_D230 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1] default)))

def cfg_D231 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

def cfg_D294 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1] default)))

def cfg_D296 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_D_base a b
    (ListBlank.append [0, 1, 0, 0]
      (ListBlank.append (([0, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [0, 1] default)))))

/-! ## Boundary Step Lemmas (`a = 0`) -/

private theorem step_D7_zero (b : ℕ) :
    ReachesPlus target (cfg_D7 0 b) (cfg_D77 0 0 0 (b + 1)) := by
  have h1 := sweep_D_zero_to_A_top b (ListBlank.append [1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) default))
          (ListBlank.append [1] default))
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 2))
            (ListBlank.append [1] default))
          (ListBlank.append [1] (ListBlank.append [1, 0, 1] default))) := by
    have h_l :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) default) := by
      rw [ListBlank.append_pow_succ, swap_1_11_pow]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_D_11 (b + 2) default (ListBlank.append [1, 0, 1] default)
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight D (ListBlank.append [1] default)
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 2))
              (ListBlank.append [1, 0, 1] default))))
        (cfg_D77 0 0 0 (b + 1)) := by
    unfold cfg_D77 cfg_D_base
    rw [list_pow_zero, ListBlank.append_nil,
      ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) (b + 1)]
    have h_sw :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
          (ListBlank.append [1, 0, 1] (default : ListBlank (Fin 2))) =
          ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
              (ListBlank.append [0, 1] default)) :=
      swap_1_11_pow (b + 1) (ListBlank.append [0, 1] default)
    rw [h_sw]
    bb_steps
  exact h123.trans h4

private theorem step_D74_zero (b : ℕ) :
    ReachesPlus target (cfg_D74 0 b) (cfg_D7 (b + 2) 0) :=
  sweep_D_zero_010 b (ListBlank.append [1] default)

private theorem step_D75_zero_zero (b : ℕ) :
    ReachesPlus target (cfg_D75 0 b 0) (cfg_D158 (b + 1) 0 0) :=
  sweep_D_zero_000 b (ListBlank.append [1, 0, 1] default)

private theorem step_D75_zero_succ (b c : ℕ) :
    ReachesPlus target (cfg_D75 0 b (c + 1)) (cfg_D160 (b + 1) 0 c) := by
  unfold cfg_D75 cfg_D160
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_000 b _

private theorem step_D76_zero_zero (b : ℕ) :
    ReachesPlus target (cfg_D76 0 b 0) (cfg_D75 0 0 (b + 2)) :=
  sweep_D_zero_011 b (ListBlank.append [1, 0, 1] default)

private theorem step_D76_zero_succ (b c : ℕ) :
    ReachesPlus target (cfg_D76 0 b (c + 1)) (cfg_D77 0 0 (b + 2) c) := by
  unfold cfg_D76 cfg_D77
  rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) c]
  exact sweep_D_zero_011 b _

private theorem step_D77_zero_zero (b d : ℕ) :
    ReachesPlus target (cfg_D77 0 b 0 d) (cfg_D158 (b + 1) 0 (d + 1)) := by
  unfold cfg_D77 cfg_D158
  rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
  exact sweep_D_zero_000 b _

private theorem step_D77_zero_succ (b c d : ℕ) :
    ReachesPlus target (cfg_D77 0 b (c + 1) d) (cfg_D162 (b + 1) 0 c d) := by
  unfold cfg_D77 cfg_D162
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_000 b _

private theorem step_D158_zero_zero (b : ℕ) :
    ReachesPlus target (cfg_D158 0 b 0) (cfg_D230 0 0 (b + 3)) := by
  have h := sweep_D_zero_011 b (ListBlank.append [0, 1] default)
  have h_r :
      ListBlank.append [0, 0, 0]
        (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [0, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [0, 0]
          (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 3))
            (ListBlank.append [1] default)) := by
    have h_sw :
        ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [0] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
          ListBlank.append [0]
            (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2))
              (ListBlank.append [1] default)) :=
      swap_single_pair_pow 0 (b + 2) (ListBlank.append [1] default)
    change ListBlank.append [0, 0]
      (ListBlank.append [0]
        (ListBlank.append (([0, 0] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [0] (ListBlank.append [1] default)))) = _
    rw [h_sw, ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) (b + 2)]
    rfl
  unfold cfg_D158 cfg_D230
  rw [list_pow_zero, ListBlank.append_nil, ← h_r]
  exact h

private theorem step_D158_zero_succ (b c : ℕ) :
    ReachesPlus target (cfg_D158 0 b (c + 1)) (cfg_D231 0 0 (b + 2) c) := by
  unfold cfg_D158 cfg_D231
  rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) c]
  exact sweep_D_zero_011 b _

private theorem step_D160_zero_zero (b : ℕ) :
    ReachesPlus target (cfg_D160 0 b 0) (cfg_D74 (b + 2) 0) :=
  sweep_D_zero_010 b (ListBlank.append [0, 1, 0, 1] default)

private theorem step_D160_zero_succ (b c : ℕ) :
    ReachesPlus target (cfg_D160 0 b (c + 1)) (cfg_D75 (b + 2) 0 c) := by
  unfold cfg_D160 cfg_D75
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_010 b _

private theorem step_D162_zero_zero (b d : ℕ) :
    ReachesPlus target (cfg_D162 0 b 0 d) (cfg_D76 (b + 2) 0 d) :=
  sweep_D_zero_010 b _

private theorem step_D162_zero_succ (b c d : ℕ) :
    ReachesPlus target (cfg_D162 0 b (c + 1) d) (cfg_D77 (b + 2) 0 c d) := by
  unfold cfg_D162 cfg_D77
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_010 b _

private theorem step_D230_halt (b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D230 0 b 0) cfg' ∧ (step target cfg').isNone := by
  have h1 := sweep_D_zero_to_A b (ListBlank.append [0, 0, 1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
            (ListBlank.append [1, 1, 1] default))
          (ListBlank.append [0, 0, 1] default))
        (Cfg.headRight F
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
              (ListBlank.append [1, 1, 1] default)))
          default) := by
    bb_steps
  refine ⟨_, h1.trans h2, ?_⟩
  bb_halt

private theorem step_D230_zero_one (b : ℕ) :
    ReachesPlus target (cfg_D230 0 b 1) (cfg_D74 (b + 1) 0) :=
  sweep_D_zero_000 b (ListBlank.append [0, 1] default)

private theorem step_D230_zero_ge2 (b c : ℕ) :
    ReachesPlus target (cfg_D230 0 b (c + 2)) (cfg_D294 (b + 1) 0 c) := by
  unfold cfg_D230 cfg_D294
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) (c + 1),
    ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_000 b _

private theorem step_D231_zero_zero (b d : ℕ) :
    ReachesPlus target (cfg_D231 0 b 0 d) (cfg_D76 (b + 1) 0 d) :=
  sweep_D_zero_000 b _

private theorem step_D231_zero_succ (b c d : ℕ) :
    ReachesPlus target (cfg_D231 0 b (c + 1) d) (cfg_D296 (b + 1) 0 c d) := by
  unfold cfg_D231 cfg_D296
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_000 b _

private theorem step_D294_zero (b c : ℕ) :
    ReachesPlus target (cfg_D294 0 b c) (cfg_D230 (b + 2) 0 c) :=
  sweep_D_zero_010 b _

private theorem step_D296_zero_zero (b d : ℕ) :
    ReachesPlus target (cfg_D296 0 b 0 d) (cfg_D158 (b + 2) 0 d) :=
  sweep_D_zero_010 b _

private theorem step_D296_zero_succ (b c d : ℕ) :
    ReachesPlus target (cfg_D296 0 b (c + 1) d) (cfg_D231 (b + 2) 0 c d) := by
  unfold cfg_D296 cfg_D231
  rw [ListBlank.append_pow_succ ([0, 0] : List (Fin 2)) c]
  exact sweep_D_zero_010 b _

private theorem init_reaches_start : ReachesStar target (init []) (cfg_D7 0 0) := by
  have h : ReachesPlus target (init []) (cfg_D7 0 0) := by
    unfold cfg_D7 cfg_D_base
    rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_nil]
    bb_steps
  exact h.to_star

/-! ## Canonical Pattern Set (Level A) -/

/-- Right-tape expression for the unified hub pattern `pat_A`. -/
def pat_A_right : TapeExpr (Fin 2) :=
  .sym 1 (.sym 1
    (.rep [1, 1] 1
      (.rep [1] 2
        (.rep [0, 1] 3
          (.rep [0] 4
            (.rep [0, 0] 5
              (.rep [1] 6
                (.rep [1, 1] 7
                  (.rep [0, 1] 8 .default)))))))))

/-- Unified canonical tape pattern `pat_A`. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some D
    right := pat_A_right }

/-- Variable equality constraint `vars idx = val` encoded as a `VarCond`. -/
def eq_const (idx val : ℕ) : VarCond :=
  .and (.ge_const idx val) (.not (.ge_const idx (val + 1)))

@[simp]
private theorem eval_eq_const (idx val : ℕ) (vars : ℕ → ℕ) :
    evalVarCond (eq_const idx val) vars ↔ vars idx = val := by
  simp only [eq_const, evalVarCond]
  omega

@[simp]
private theorem eval_and (c1 c2 : VarCond) (vars : ℕ → ℕ) :
    evalVarCond (.and c1 c2) vars ↔ evalVarCond c1 vars ∧ evalVarCond c2 vars :=
  Iff.rfl

@[simp]
private theorem eval_or (c1 c2 : VarCond) (vars : ℕ → ℕ) :
    evalVarCond (.or c1 c2) vars ↔ evalVarCond c1 vars ∨ evalVarCond c2 vars :=
  Iff.rfl

def cond_case_7 : VarCond :=
  .and (eq_const 2 1) (.and (eq_const 3 0) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 0) (.and (eq_const 7 0) (eq_const 8 0))))))

def cond_case_74 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 0) (.and (eq_const 7 0) (eq_const 8 1))))))

def cond_case_75 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 3)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 1)))))

def cond_case_76 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 2) (eq_const 8 1)))))

def cond_case_77 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 3)
    (.and (eq_const 6 3) (eq_const 8 1))))

def cond_case_158 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 0)
    (.and (eq_const 5 0) (.and (eq_const 6 1) (eq_const 8 1)))))

def cond_case_160 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 2)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 1)))))

def cond_case_162 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 2)
    (.and (eq_const 6 3) (eq_const 8 1))))

def cond_case_230 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 2)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 0)))))

def cond_case_231 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 0) (.and (eq_const 4 3)
    (.and (eq_const 6 2) (eq_const 8 1))))

def cond_case_294 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 3)
    (.and (eq_const 6 1) (.and (eq_const 7 0) (eq_const 8 0)))))

def cond_case_296 : VarCond :=
  .and (eq_const 2 0) (.and (eq_const 3 1) (.and (eq_const 4 2)
    (.and (eq_const 6 2) (eq_const 8 1))))

/-- Parameter guard selecting the 12 canonical hub configurations of `pat_A`. -/
def cond_A : VarCond :=
  .or cond_case_7 (.or cond_case_74 (.or cond_case_75 (.or cond_case_76
    (.or cond_case_77 (.or cond_case_158 (.or cond_case_160 (.or cond_case_162
      (.or cond_case_230 (.or cond_case_231 (.or cond_case_294 cond_case_296))))))))))

/-- Closed pattern set for `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, cond_A)]

private theorem mem_ps_A : (pat_A, cond_A) ∈ ps :=
  .head _

private theorem in_ps_D7 (a b : ℕ) : IsInPatternSet ps (cfg_D7 a b) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with | 0 => a | 1 => b | 2 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D7, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_7]

private theorem in_ps_D74 (a b : ℕ) : IsInPatternSet ps (cfg_D74 a b) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with | 0 => a | 1 => b | 3 => 1 | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D74, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_74]

private theorem in_ps_D75 (a b c : ℕ) : IsInPatternSet ps (cfg_D75 a b c) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 4 => 3 | 5 => c | 6 => 1 | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D75, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_75]

private theorem in_ps_D76 (a b c : ℕ) : IsInPatternSet ps (cfg_D76 a b c) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 3 => 1 | 6 => 2 | 7 => c | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D76, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_76]

private theorem in_ps_D77 (a b c d : ℕ) : IsInPatternSet ps (cfg_D77 a b c d) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 4 => 3 | 5 => c | 6 => 3 | 7 => d | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D77, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_77]

private theorem in_ps_D158 (a b c : ℕ) : IsInPatternSet ps (cfg_D158 a b c) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 3 => 1 | 6 => 1 | 7 => c | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D158, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_158]

private theorem in_ps_D160 (a b c : ℕ) : IsInPatternSet ps (cfg_D160 a b c) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 3 => 1 | 4 => 2 | 5 => c | 6 => 1 | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D160, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_160]

private theorem in_ps_D162 (a b c d : ℕ) : IsInPatternSet ps (cfg_D162 a b c d) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 3 => 1 | 4 => 2 | 5 => c | 6 => 3 | 7 => d | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D162, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_162]

private theorem in_ps_D230 (a b c : ℕ) : IsInPatternSet ps (cfg_D230 a b c) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 4 => 2 | 5 => c | 6 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D230, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_230]

private theorem in_ps_D231 (a b c d : ℕ) : IsInPatternSet ps (cfg_D231 a b c d) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 4 => 3 | 5 => c | 6 => 2 | 7 => d | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D231, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_231]

private theorem in_ps_D294 (a b c : ℕ) : IsInPatternSet ps (cfg_D294 a b c) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 3 => 1 | 4 => 3 | 5 => c | 6 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D294, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_294]

private theorem in_ps_D296 (a b c d : ℕ) : IsInPatternSet ps (cfg_D296 a b c d) := by
  refine ⟨(pat_A, cond_A), mem_ps_A,
    fun k => match k with
      | 0 => a | 1 => b | 3 => 1 | 4 => 2 | 5 => c | 6 => 2 | 7 => d | 8 => 1 | _ => 0, ?_, ?_⟩
  · simp [cfg_D296, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ]
  · simp [cond_A, cond_case_296]

/-! ## Collatz-Like Acceleration (Level B & Closure) -/

/-- Symbolic configuration state space for `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`. -/
inductive State where
  | D7 (a b : ℕ)
  | D74 (a b : ℕ)
  | D75 (a b c : ℕ)
  | D76 (a b c : ℕ)
  | D77 (a b c d : ℕ)
  | D158 (a b c : ℕ)
  | D160 (a b c : ℕ)
  | D162 (a b c d : ℕ)
  | D230 (a b c : ℕ)
  | D231 (a b c d : ℕ)
  | D294 (a b c : ℕ)
  | D296 (a b c d : ℕ)

/-- Initial symbolic state `D7(0, 0)`, reached after 12 raw TM steps. -/
def start : State := .D7 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .D7 a b => cfg_D7 a b
  | .D74 a b => cfg_D74 a b
  | .D75 a b c => cfg_D75 a b c
  | .D76 a b c => cfg_D76 a b c
  | .D77 a b c d => cfg_D77 a b c d
  | .D158 a b c => cfg_D158 a b c
  | .D160 a b c => cfg_D160 a b c
  | .D162 a b c d => cfg_D162 a b c d
  | .D230 a b c => cfg_D230 a b c
  | .D231 a b c d => cfg_D231 a b c d
  | .D294 a b c => cfg_D294 a b c
  | .D296 a b c d => cfg_D296 a b c d

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .D7 0 b => some (.D77 0 0 0 (b + 1))
  | .D7 (a + 1) b => some (.D7 a (b + 1))
  | .D74 0 b => some (.D7 (b + 2) 0)
  | .D74 (a + 1) b => some (.D74 a (b + 1))
  | .D75 0 b 0 => some (.D158 (b + 1) 0 0)
  | .D75 0 b (c + 1) => some (.D160 (b + 1) 0 c)
  | .D75 (a + 1) b c => some (.D75 a (b + 1) c)
  | .D76 0 b 0 => some (.D75 0 0 (b + 2))
  | .D76 0 b (c + 1) => some (.D77 0 0 (b + 2) c)
  | .D76 (a + 1) b c => some (.D76 a (b + 1) c)
  | .D77 0 b 0 d => some (.D158 (b + 1) 0 (d + 1))
  | .D77 0 b (c + 1) d => some (.D162 (b + 1) 0 c d)
  | .D77 (a + 1) b c d => some (.D77 a (b + 1) c d)
  | .D158 0 b 0 => some (.D230 0 0 (b + 3))
  | .D158 0 b (c + 1) => some (.D231 0 0 (b + 2) c)
  | .D158 (a + 1) b c => some (.D158 a (b + 1) c)
  | .D160 0 b 0 => some (.D74 (b + 2) 0)
  | .D160 0 b (c + 1) => some (.D75 (b + 2) 0 c)
  | .D160 (a + 1) b c => some (.D160 a (b + 1) c)
  | .D162 0 b 0 d => some (.D76 (b + 2) 0 d)
  | .D162 0 b (c + 1) d => some (.D77 (b + 2) 0 c d)
  | .D162 (a + 1) b c d => some (.D162 a (b + 1) c d)
  | .D230 0 _ 0 => none
  | .D230 0 b 1 => some (.D74 (b + 1) 0)
  | .D230 0 b (c + 2) => some (.D294 (b + 1) 0 c)
  | .D230 (a + 1) b c => some (.D230 a (b + 1) c)
  | .D231 0 b 0 d => some (.D76 (b + 1) 0 d)
  | .D231 0 b (c + 1) d => some (.D296 (b + 1) 0 c d)
  | .D231 (a + 1) b c d => some (.D231 a (b + 1) c d)
  | .D294 0 b c => some (.D230 (b + 2) 0 c)
  | .D294 (a + 1) b c => some (.D294 a (b + 1) c)
  | .D296 0 b 0 d => some (.D158 (b + 2) 0 d)
  | .D296 0 b (c + 1) d => some (.D231 (b + 2) 0 c d)
  | .D296 (a + 1) b c d => some (.D296 a (b + 1) c d)

private theorem encode_in_ps (s : State) : IsInPatternSet ps (encode s) := by
  cases s with
  | D7 a b => exact in_ps_D7 a b
  | D74 a b => exact in_ps_D74 a b
  | D75 a b c => exact in_ps_D75 a b c
  | D76 a b c => exact in_ps_D76 a b c
  | D77 a b c d => exact in_ps_D77 a b c d
  | D158 a b c => exact in_ps_D158 a b c
  | D160 a b c => exact in_ps_D160 a b c
  | D162 a b c d => exact in_ps_D162 a b c d
  | D230 a b c => exact in_ps_D230 a b c
  | D231 a b c d => exact in_ps_D231 a b c d
  | D294 a b c => exact in_ps_D294 a b c
  | D296 a b c d => exact in_ps_D296 a b c d

private theorem ps_to_state (vars : ℕ → ℕ) (h_cond : evalVarCond cond_A vars) :
    ∃ s : State, evalTapePattern pat_A vars = encode s := by
  simp only [cond_A, cond_case_7, cond_case_74, cond_case_75, cond_case_76, cond_case_77,
    cond_case_158, cond_case_160, cond_case_162, cond_case_230, cond_case_231, cond_case_294,
    cond_case_296, eval_or, eval_and, eval_eq_const] at h_cond
  rcases h_cond with ⟨h2, h3, h4, h5, h6, h7, h8⟩ | h_cond
  · refine ⟨.D7 (vars 0) (vars 1), ?_⟩
    simp [encode, cfg_D7, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h5, h6, h7, h8]
  rcases h_cond with ⟨h2, h3, h4, h5, h6, h7, h8⟩ | h_cond
  · refine ⟨.D74 (vars 0) (vars 1), ?_⟩
    simp [encode, cfg_D74, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h5, h6, h7, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h7, h8⟩ | h_cond
  · refine ⟨.D75 (vars 0) (vars 1) (vars 5), ?_⟩
    simp [encode, cfg_D75, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h7, h8]
  rcases h_cond with ⟨h2, h3, h4, h5, h6, h8⟩ | h_cond
  · refine ⟨.D76 (vars 0) (vars 1) (vars 7), ?_⟩
    simp [encode, cfg_D76, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h5, h6, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h8⟩ | h_cond
  · refine ⟨.D77 (vars 0) (vars 1) (vars 5) (vars 7), ?_⟩
    simp [encode, cfg_D77, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h8]
  rcases h_cond with ⟨h2, h3, h4, h5, h6, h8⟩ | h_cond
  · refine ⟨.D158 (vars 0) (vars 1) (vars 7), ?_⟩
    simp [encode, cfg_D158, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h5, h6, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h7, h8⟩ | h_cond
  · refine ⟨.D160 (vars 0) (vars 1) (vars 5), ?_⟩
    simp [encode, cfg_D160, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h7, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h8⟩ | h_cond
  · refine ⟨.D162 (vars 0) (vars 1) (vars 5) (vars 7), ?_⟩
    simp [encode, cfg_D162, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h7, h8⟩ | h_cond
  · refine ⟨.D230 (vars 0) (vars 1) (vars 5), ?_⟩
    simp [encode, cfg_D230, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h7, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h8⟩ | h_cond
  · refine ⟨.D231 (vars 0) (vars 1) (vars 5) (vars 7), ?_⟩
    simp [encode, cfg_D231, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h7, h8⟩ | h_cond
  · refine ⟨.D294 (vars 0) (vars 1) (vars 5), ?_⟩
    simp [encode, cfg_D294, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
      h2, h3, h4, h6, h7, h8]
  rcases h_cond with ⟨h2, h3, h4, h6, h8⟩
  refine ⟨.D296 (vars 0) (vars 1) (vars 5) (vars 7), ?_⟩
  simp [encode, cfg_D296, cfg_D_base, pat_A, pat_A_right, Cfg.headRight, list_pow_succ,
    h2, h3, h4, h6, h8]

private theorem step_some_state (s s' : State) (hnext : next s = some s') :
    ReachesPlus target (encode s) (encode s') := by
  cases s with
  | D7 a b =>
    rcases a with _ | a
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D7_zero b
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D74 a b =>
    rcases a with _ | a
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D74_zero b
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D75 a b c =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D75_zero_zero b
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D75_zero_succ b c
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D76 a b c =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D76_zero_zero b
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D76_zero_succ b c
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D77 a b c d =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D77_zero_zero b d
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D77_zero_succ b c d
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D158 a b c =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D158_zero_zero b
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D158_zero_succ b c
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D160 a b c =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D160_zero_zero b
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D160_zero_succ b c
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D162 a b c d =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D162_zero_zero b d
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D162_zero_succ b c d
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D230 a b c =>
    rcases a with _ | a
    · rcases c with _ | _ | c
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D230_zero_one b
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D230_zero_ge2 b c
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D231 a b c d =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D231_zero_zero b d
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D231_zero_succ b c d
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D294 a b c =>
    rcases a with _ | a
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D294_zero b c
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _
  | D296 a b c d =>
    rcases a with _ | a
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D296_zero_zero b d
      · simp only [next, Option.some.injEq] at hnext; subst hnext
        exact step_D296_zero_succ b c d
    · simp only [next, Option.some.injEq] at hnext; subst hnext
      exact step_D_left a b _

private theorem step_none_state (s : State) (hnext : next s = none) :
    ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  cases s with
  | D7 a b => rcases a with _ | a <;> simp [next] at hnext
  | D74 a b => rcases a with _ | a <;> simp [next] at hnext
  | D75 a b c => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D76 a b c => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D77 a b c d => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D158 a b c => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D160 a b c => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D162 a b c d => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D230 a b c =>
    rcases a with _ | a
    · rcases c with _ | _ | c
      · exact step_D230_halt b
      · simp [next] at hnext
      · simp [next] at hnext
    · simp [next] at hnext
  | D231 a b c d => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext
  | D294 a b c => rcases a with _ | a <;> simp [next] at hnext
  | D296 a b c d => rcases a with _ | a <;> rcases c with _ | c <;> simp [next] at hnext

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_D7 0 0, init_reaches_start, in_ps_D7 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · obtain ⟨s, hs⟩ := ps_to_state vars h_cond
    rw [hs]
    rcases hnext : next s with _ | s'
    · obtain ⟨cfg', hp, hh⟩ := step_none_state s hnext
      exact ⟨cfg', hp, Or.inr hh⟩
    · exact ⟨encode s', step_some_state s s' hnext, Or.inl (encode_in_ps s')⟩
  · nomatch h_mem

/-- `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := step_some_state
  step_none s hnext := by
    obtain ⟨cfg', hp, hh⟩ := step_none_state s hnext
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- Single-family state space `D(p, x, d)` for the high-level Collatz-like acceleration
(`p = false` represents `D76(0, x, d)`; `p = true` represents `D231(0, 0, x, d)`). -/
inductive HighLevelState where
  | D (p : Bool) (x d : ℕ)
  deriving DecidableEq, Repr

/-- Initial state `D true 3 1` (`D231(0, 0, 3, 1)`), reached from `start = D7(0, 0)` in 4 steps. -/
def highLevelStart : HighLevelState := .D true 3 1

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .D false x d => .D76 0 x d
  | .D true x d => .D231 0 0 x d

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- High-level closed-form transition function collapsing all 12 `State` families into
`D(p, x, d)`. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .D false x 0 =>
    let k := (x + 2) / 2
    if x % 2 = 0 then
      if (3 * k + 4) % 2 = 0 then none
      else some (.D true 3 (3 * ((3 * k + 4) / 2) + 4))
    else
      some (.D true 3 (3 * k + 6))
  | .D false x (d + 1) =>
    let k := (x + 2) / 2
    if x % 2 = 0 then some (.D true (3 * k + 3) d)
    else some (.D false (3 * k + 3) d)
  | .D true x d =>
    let k := x / 2
    if x % 2 = 0 then some (.D false (3 * k + 1) d)
    else if d = 0 then
      if (3 * k + 6) % 2 = 0 then none
      else some (.D true 3 (3 * ((3 * k + 6) / 2) + 4))
    else some (.D true (3 * k + 5) (d - 1))

private theorem reachesStar_trans {s₁ s₂ s₃ : State}
    (h₁ : CollatzReachesStar next s₁ s₂) (h₂ : CollatzReachesStar next s₂ s₃) :
    CollatzReachesStar next s₁ s₃ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  refine ⟨m + n, ?_⟩
  unfold CollatzReachesIn at *
  rw [Nat.add_comm, Function.iterate_add_apply, hm, hn]

private theorem shift_D7 : ∀ (a b : ℕ),
    CollatzReachesStar next (.D7 a b) (.D7 0 (a + b))
  | 0, b => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b => by
    have ih := shift_D7 a (b + 1)
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D74 : ∀ (a b : ℕ),
    CollatzReachesStar next (.D74 a b) (.D74 0 (a + b))
  | 0, b => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b => by
    have ih := shift_D74 a (b + 1)
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D75 : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D75 a b c) (.D75 0 (a + b) c)
  | 0, b, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := shift_D75 a (b + 1) c
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D76 : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D76 a b c) (.D76 0 (a + b) c)
  | 0, b, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := shift_D76 a (b + 1) c
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D77 : ∀ (a b c d : ℕ),
    CollatzReachesStar next (.D77 a b c d) (.D77 0 (a + b) c d)
  | 0, b, _, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c, d => by
    have ih := shift_D77 a (b + 1) c d
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D158 : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D158 a b c) (.D158 0 (a + b) c)
  | 0, b, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := shift_D158 a (b + 1) c
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D160 : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D160 a b c) (.D160 0 (a + b) c)
  | 0, b, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := shift_D160 a (b + 1) c
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D162 : ∀ (a b c d : ℕ),
    CollatzReachesStar next (.D162 a b c d) (.D162 0 (a + b) c d)
  | 0, b, _, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c, d => by
    have ih := shift_D162 a (b + 1) c d
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D230 : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D230 a b c) (.D230 0 (a + b) c)
  | 0, b, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := shift_D230 a (b + 1) c
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D231 : ∀ (a b c d : ℕ),
    CollatzReachesStar next (.D231 a b c d) (.D231 0 (a + b) c d)
  | 0, b, _, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c, d => by
    have ih := shift_D231 a (b + 1) c d
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D294 : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D294 a b c) (.D294 0 (a + b) c)
  | 0, b, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := shift_D294 a (b + 1) c
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem shift_D296 : ∀ (a b c d : ℕ),
    CollatzReachesStar next (.D296 a b c d) (.D296 0 (a + b) c d)
  | 0, b, _, _ => by rw [Nat.zero_add]; exact CollatzReachesStar.refl next _
  | a + 1, b, c, d => by
    have ih := shift_D296 a (b + 1) c d
    have hab : a + (b + 1) = a + 1 + b := by omega
    rw [hab] at ih
    exact CollatzReachesStar.head rfl ih

private theorem drain_D75 : ∀ (k n r : ℕ),
    CollatzReachesStar next (.D75 0 n (2 * k + r)) (.D75 0 (n + 3 * k) r)
  | 0, n, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, n, r => by
    have h1 : next (.D75 0 n (2 * (k + 1) + r)) = some (.D160 (n + 1) 0 (2 * k + r + 1)) := by
      have hc : 2 * (k + 1) + r = (2 * k + r + 1) + 1 := by omega
      rw [hc]
      rfl
    have ih := drain_D75 k (n + 3) r
    have hn : n + 3 + 3 * k = n + 3 * (k + 1) := by omega
    rw [hn] at ih
    exact CollatzReachesStar.head h1
      (reachesStar_trans (shift_D160 (n + 1) 0 _)
        (CollatzReachesStar.head rfl
          (reachesStar_trans (shift_D75 (n + 3) 0 _) ih)))

private theorem drain_D77 : ∀ (k n r d : ℕ),
    CollatzReachesStar next (.D77 0 n (2 * k + r) d) (.D77 0 (n + 3 * k) r d)
  | 0, n, r, _ => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, n, r, d => by
    have h1 : next (.D77 0 n (2 * (k + 1) + r) d) =
        some (.D162 (n + 1) 0 (2 * k + r + 1) d) := by
      have hc : 2 * (k + 1) + r = (2 * k + r + 1) + 1 := by omega
      rw [hc]
      rfl
    have ih := drain_D77 k (n + 3) r d
    have hn : n + 3 + 3 * k = n + 3 * (k + 1) := by omega
    rw [hn] at ih
    exact CollatzReachesStar.head h1
      (reachesStar_trans (shift_D162 (n + 1) 0 _ d)
        (CollatzReachesStar.head rfl
          (reachesStar_trans (shift_D77 (n + 3) 0 _ d) ih)))

private theorem drain_D230 : ∀ (k n r : ℕ),
    CollatzReachesStar next (.D230 0 n (2 * k + r)) (.D230 0 (n + 3 * k) r)
  | 0, n, r => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, n, r => by
    have h1 : next (.D230 0 n (2 * (k + 1) + r)) = some (.D294 (n + 1) 0 (2 * k + r)) := by
      have hc : 2 * (k + 1) + r = (2 * k + r) + 2 := by omega
      rw [hc]
      rfl
    have ih := drain_D230 k (n + 3) r
    have hn : n + 3 + 3 * k = n + 3 * (k + 1) := by omega
    rw [hn] at ih
    exact CollatzReachesStar.head h1
      (reachesStar_trans (shift_D294 (n + 1) 0 _)
        (CollatzReachesStar.head rfl
          (reachesStar_trans (shift_D230 (n + 3) 0 _) ih)))

private theorem drain_D231 : ∀ (k n r d : ℕ),
    CollatzReachesStar next (.D231 0 n (2 * k + r) d) (.D231 0 (n + 3 * k) r d)
  | 0, n, r, _ => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, n, r, d => by
    have h1 : next (.D231 0 n (2 * (k + 1) + r) d) =
        some (.D296 (n + 1) 0 (2 * k + r + 1) d) := by
      have hc : 2 * (k + 1) + r = (2 * k + r + 1) + 1 := by omega
      rw [hc]
      rfl
    have ih := drain_D231 k (n + 3) r d
    have hn : n + 3 + 3 * k = n + 3 * (k + 1) := by omega
    rw [hn] at ih
    exact CollatzReachesStar.head h1
      (reachesStar_trans (shift_D296 (n + 1) 0 _ d)
        (CollatzReachesStar.head rfl
          (reachesStar_trans (shift_D231 (n + 3) 0 _ d) ih)))

private theorem stepsTo_D74 (b : ℕ) :
    CollatzStepsTo next (.D74 0 b) (some (.D231 0 0 3 (b + 3))) :=
  CollatzStepsTo.head rfl
    (CollatzStepsTo.of_reachesStar (shift_D7 (b + 2) 0)
      (CollatzStepsTo.head rfl
        (CollatzStepsTo.head rfl
          (CollatzStepsTo.head rfl
            (CollatzStepsTo.of_eq rfl)))))

private theorem stepsTo_D230 (c : ℕ) :
    CollatzStepsTo next (.D230 0 0 c)
      ((if c % 2 = 0 then none
        else some (HighLevelState.D true 3 (3 * (c / 2) + 4))).map toState) := by
  have h_drain := drain_D230 (c / 2) 0 (c % 2)
  have hc : 2 * (c / 2) + c % 2 = c := by omega
  rw [hc, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  by_cases hr0 : c % 2 = 0
  · simp only [hr0, ↓reduceIte]
    exact CollatzStepsTo.of_eq rfl
  · have hr1 : c % 2 = 1 := by omega
    simp only [hr1]
    exact CollatzStepsTo.head rfl
      (CollatzStepsTo.of_reachesStar (shift_D74 (3 * (c / 2) + 1) 0)
        (stepsTo_D74 (3 * (c / 2) + 1)))

private theorem start_reaches_highLevelStart :
    CollatzReachesStar next start (toState highLevelStart) :=
  CollatzReachesStar.head rfl
    (CollatzReachesStar.head rfl
      (CollatzReachesStar.head rfl
        (CollatzReachesStar.single rfl)))

private theorem stepsTo_D_false_zero (x : ℕ) :
    CollatzStepsTo next (.D76 0 x 0) ((highLevelNext (.D false x 0)).map toState) := by
  refine CollatzStepsTo.head rfl ?_
  have h_drain := drain_D75 ((x + 2) / 2) 0 ((x + 2) % 2)
  have hx : 2 * ((x + 2) / 2) + (x + 2) % 2 = x + 2 := by omega
  rw [hx, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  dsimp only [highLevelNext]
  by_cases hx0 : x % 2 = 0
  · have hx2 : (x + 2) % 2 = 0 := by omega
    simp only [hx0, ↓reduceIte, hx2]
    exact CollatzStepsTo.head rfl
      (CollatzStepsTo.of_reachesStar (shift_D158 (3 * ((x + 2) / 2) + 1) 0 0)
        (CollatzStepsTo.head rfl
          (stepsTo_D230 (3 * ((x + 2) / 2) + 4))))
  · have hx2 : (x + 2) % 2 = 1 := by omega
    simp only [hx0, ↓reduceIte, hx2]
    exact CollatzStepsTo.head rfl
      (CollatzStepsTo.of_reachesStar (shift_D160 (3 * ((x + 2) / 2) + 1) 0 0)
        (CollatzStepsTo.head rfl
          (CollatzStepsTo.of_reachesStar (shift_D74 (3 * ((x + 2) / 2) + 3) 0)
            (stepsTo_D74 (3 * ((x + 2) / 2) + 3)))))

private theorem stepsTo_D_false_succ (x d : ℕ) :
    CollatzStepsTo next (.D76 0 x (d + 1))
      ((highLevelNext (.D false x (d + 1))).map toState) := by
  refine CollatzStepsTo.head rfl ?_
  have h_drain := drain_D77 ((x + 2) / 2) 0 ((x + 2) % 2) d
  have hx : 2 * ((x + 2) / 2) + (x + 2) % 2 = x + 2 := by omega
  rw [hx, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  dsimp only [highLevelNext]
  by_cases hx0 : x % 2 = 0
  · have hx2 : (x + 2) % 2 = 0 := by omega
    simp only [hx0, ↓reduceIte, hx2]
    exact CollatzStepsTo.head rfl
      (CollatzStepsTo.of_reachesStar (shift_D158 (3 * ((x + 2) / 2) + 1) 0 (d + 1))
        (CollatzStepsTo.of_eq rfl))
  · have hx2 : (x + 2) % 2 = 1 := by omega
    simp only [hx0, ↓reduceIte, hx2]
    exact CollatzStepsTo.head rfl
      (CollatzStepsTo.of_reachesStar (shift_D162 (3 * ((x + 2) / 2) + 1) 0 0 d)
        (CollatzReachesPlus.head rfl (shift_D76 (3 * ((x + 2) / 2) + 3) 0 d)))

private theorem stepsTo_D_true (x d : ℕ) :
    CollatzStepsTo next (.D231 0 0 x d) ((highLevelNext (.D true x d)).map toState) := by
  have h_drain := drain_D231 (x / 2) 0 (x % 2) d
  have hx : 2 * (x / 2) + x % 2 = x := by omega
  rw [hx, Nat.zero_add] at h_drain
  refine CollatzStepsTo.of_reachesStar h_drain ?_
  dsimp only [highLevelNext]
  by_cases hx0 : x % 2 = 0
  · simp only [hx0, ↓reduceIte]
    exact CollatzReachesPlus.head rfl (shift_D76 (3 * (x / 2) + 1) 0 d)
  · have hx1 : x % 2 = 1 := by omega
    simp only [hx1]
    refine CollatzStepsTo.head rfl
      (CollatzStepsTo.of_reachesStar (shift_D296 (3 * (x / 2) + 1) 0 0 d)
        (CollatzStepsTo.head rfl
          (CollatzStepsTo.of_reachesStar (shift_D158 (3 * (x / 2) + 3) 0 d) ?_)))
    rcases d with _ | d
    · simp only [↓reduceIte]
      exact CollatzStepsTo.head rfl (stepsTo_D230 (3 * (x / 2) + 6))
    · have hd_ne : d + 1 ≠ 0 := by omega
      simp only [hd_ne, ↓reduceIte, Nat.add_sub_cancel]
      exact CollatzStepsTo.of_eq rfl

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) start_reaches_highLevelStart ?_
  rintro ⟨_ | _, x, d⟩
  · rcases d with _ | d
    · exact stepsTo_D_false_zero x
    · exact stepsTo_D_false_succ x d
  · exact stepsTo_D_true x d

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

end BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC
