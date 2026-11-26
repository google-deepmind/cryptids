/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout #50 (`suspect_47`, listed on
[`User:RobinCodes/Next_Steps`](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps))
`1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`.

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(m, k, b) := 0^\infty\,1^m\,(10)^k\,\mathrm{C}{>}\,1^b\,0^\infty$$
at $C(0, 0, 2)$ in 2 steps, and every $C(m, k, b)$ advances in `ReachesPlus` either to another
$C(m', k', b')$ or to a halting configuration (when $m = 2$, $k = 0$, and $b \ge 2$).

## Collatz-like Acceleration Rules

```text
Consider:
C(m, k, b) = 0^inf 1^m (10)^k C> 1^b 0^inf

C(m, k, 0)         -> C(m+1, 0, 2k+2)
C(0, k, 1)         -> C(2k+3, 0, 2)
C(0, k, b+2)       -> C(2k+2, 1, b)
C(1, 0, b+1)       -> C(0, 0, b+3)
C(1, k+1, 1)       -> C(2k+7, 0, 2)
C(1, k+1, b+2)     -> C(2k+6, 1, b)
C(2, 0, 1)         -> C(0, 1, 0)
C(2, 0, b+2)       -> Halt
C(2, 1, b+1)       -> C(0, 1, b+1)
C(2, k+2, 1)       -> C(2k+7, 0, 2)
C(2, k+2, b+2)     -> C(2k+6, 1, b)
C(m+3, k, b+1)     -> C(m, k+2, b)

Start: C(0, 0, 2), reached after 2 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Turnaround Lemmas -/

/-- Rightward shift across `(01)^k` in state `A`, writing `(11)^k` onto the left tape. -/
private theorem shift_A_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [1, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_A_01_ones (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  rw [← one_pow_two_mul]
  exact shift_A_01 k l r

/-- Leftward shift across `(10)^k 1` in state `C`, converting each `10` into `11` on the right
tape. -/
private theorem shift_C_10_to_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
        (ListBlank.append [1] r))
      (Cfg.headRight C
        (ListBlank.append [1] l)
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1]
              (ListBlank.append [0, 1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [1] r))
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward shift across `(10)^k` in state `C` when scanning `1`, placing `(01)^k` on the right
tape. -/
private theorem shift_C_10_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight C
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Rightward shift across `(01)^k` in state `C`, placing `(10)^k` onto the left tape. -/
private theorem shift_C_01_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight C (ListBlank.append [0, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$C(m, k, b) := 0^\infty\,1^m\,(10)^k\,\mathrm{C}{>}\,1^b\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.rep [1] 0 .default)
    head := some C
    right := .rep [1] 2 .default }

/-- Closed pattern set for `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Configuration $C(m, k, b)$. -/
private def cfg_C (m k b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ m) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ b) default)

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_C (m k b : ℕ) : IsInPatternSet ps (cfg_C m k b) :=
  ⟨(pat_C, .true), List.Mem.head _,
    fun i => match i with | 0 => m | 1 => k | 2 => b | _ => 0, rfl, trivial⟩

/-! ## Shared Left-Boundary Helper Lemmas -/

private theorem combine_ones_left (a n : ℕ) :
    ListBlank.append (([1] : List (Fin 2)) ^ n)
      (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2))) =
      ListBlank.append (([1] : List (Fin 2)) ^ (a + n)) default := by
  rw [← ListBlank.append_pow_add]
  exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)

private theorem step_D_zero (a : ℕ) :
    ReachesPlus target
      (Cfg.headRight D default
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (cfg_C (2 * a + 3) 0 2) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default)) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a, list_pow_one]
    bb_steps
  have h2 := shift_A_01_ones (a + 1) (ListBlank.append (([1] : List (Fin 2)) ^ 1) default) default
  have h12 := h1.trans_star h2
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (a + 1)))
        (ListBlank.append (([1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 3)) default := by
    rw [combine_ones_left 1 (2 * (a + 1))]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  rw [h_comb] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 3)) default)
          default)
        (cfg_C (2 * a + 3) 0 2) := by
    unfold cfg_C
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [list_pow_zero, ListBlank.append_nil, h_two]
    bb_steps
  exact h12.trans h3

private theorem step_D_succ (a b : ℕ) :
    ReachesPlus target
      (Cfg.headRight D default
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
          (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)))
      (cfg_C (2 * a + 2) 1 b) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a, list_pow_one]
    bb_steps
  have h2 := shift_A_01_ones (a + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)
  have h12 := h1.trans_star h2
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (a + 1)))
        (ListBlank.append (([1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ 1)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 2)) default) := by
    rw [combine_ones_left 1 (2 * (a + 1)), combine_ones_left (2 * a + 2) 1]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  rw [h_comb] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 2)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))
        (cfg_C (2 * a + 2) 1 b) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b, list_pow_one, list_pow_one]
    bb_steps
  exact h12.trans h3

/-! ## Accelerated Transition Rules -/

/-- Rule 1 (`b = 0`): `C(m, k, 0) -> C(m + 1, 0, 2k + 2)`. -/
private theorem step_C_b0 (m k : ℕ) :
    ReachesPlus target (cfg_C m k 0) (cfg_C (m + 1) 0 (2 * k + 2)) := by
  have h1 :
      ReachesPlus target (cfg_C m k 0)
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
              (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil, list_pow_one]
    bb_steps
  have h2 := shift_C_10_to_11 k
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default) := by
    rw [list_pow_zero, ListBlank.append_nil]
    have h_1 : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
    nth_rw 1 [h_1]
    exact combine_ones_left m 1
  have h_r :
      ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default := by
    rw [one_pow_two_mul, ← ListBlank.append_pow_add]
    have h_1 : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
    nth_rw 1 [h_1]
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  unfold cfg_C
  rwa [h_l, h_r] at h12

/-- Rule 2 (`m ≥ 3, b ≥ 1`): `C(m + 3, k, b + 1) -> C(m, k + 2, b)`. -/
private theorem step_C_m3 (m k b : ℕ) :
    ReachesPlus target (cfg_C (m + 3) k (b + 1)) (cfg_C m (k + 2) b) := by
  have h_start :
      cfg_C (m + 3) k (b + 1) =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + 3)) default))
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default)) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  have h1 := shift_C_10_left k
    (ListBlank.append (([1] : List (Fin 2)) ^ (m + 3)) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ b) default)
  rw [← h_start] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + 3)) default)
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ m) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 3)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m) default) := by
      have h_add : m + 3 = 3 + m := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, list_pow_one, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := shift_C_01_right (k + 1)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1] : List (Fin 2)) ^ m) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ b) default)
  have h123 := h12.trans_star h3
  have h_comb :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
          (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ m) default) := by
    rw [← ListBlank.append_pow_add]
  unfold cfg_C
  rwa [h_comb] at h123

/-- Rule 3 (`m = 0, b = 1`): `C(0, k, 1) -> C(2k + 3, 0, 2)`. -/
private theorem step_C_m0_b1 (k : ℕ) :
    ReachesPlus target (cfg_C 0 k 1) (cfg_C (2 * k + 3) 0 2) := by
  have h_start :
      cfg_C 0 k 1 =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
          (ListBlank.append [1] default) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil, list_pow_one]
  have h1 := shift_C_10_left k default default
  rw [← h_start] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)))
        (Cfg.headRight D default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) default)) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
    bb_steps
  have h12 := h1.trans_plus h2
  exact h12.trans (step_D_zero k)

/-- Rule 4 (`m = 0, b ≥ 2`): `C(0, k, b + 2) -> C(2k + 2, 1, b)`. -/
private theorem step_C_m0_b2 (k b : ℕ) :
    ReachesPlus target (cfg_C 0 k (b + 2)) (cfg_C (2 * k + 2) 1 b) := by
  have h_start :
      cfg_C 0 k (b + 2) =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) (b + 1)]
  have h1 := shift_C_10_left k default
    (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)
  rw [← h_start] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
              (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))))
        (Cfg.headRight D default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
    bb_steps
  have h12 := h1.trans_plus h2
  exact h12.trans (step_D_succ k b)

/-- Rule 5 (`m = 1, k = 0, b ≥ 1`): `C(1, 0, b + 1) -> C(0, 0, b + 3)`. -/
private theorem step_C_m1_k0 (b : ℕ) :
    ReachesPlus target (cfg_C 1 0 (b + 1)) (cfg_C 0 0 (b + 3)) := by
  unfold cfg_C
  have h_b3 :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := by
    have h_eq : b + 3 = 3 + b := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  rw [list_pow_zero, ListBlank.append_nil, list_pow_one,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) b, h_b3]
  bb_steps

/-- Helper turnaround for `m = 1, k ≥ 1`: reaches `D>` on `(01)^{k+3} r`. -/
private theorem turnaround_m1_k1 (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r)))
      (Cfg.headRight D default
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3)) r)) := by
  have h_r3 :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3)) r =
        ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r) := by
    have h_eq : k + 3 = 3 + k := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  rw [list_pow_one, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k, h_r3]
  bb_steps

/-- Rule 6 (`m = 1, k ≥ 1, b = 1`): `C(1, k + 1, 1) -> C(2k + 7, 0, 2)`. -/
private theorem step_C_m1_k1_b1 (k : ℕ) :
    ReachesPlus target (cfg_C 1 (k + 1) 1) (cfg_C (2 * k + 7) 0 2) := by
  have h_start :
      cfg_C 1 (k + 1) 1 =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
          (ListBlank.append [1] default) := by
    unfold cfg_C
    rw [list_pow_one]
  have h1 := shift_C_10_left (k + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default) default
  rw [← h_start] at h1
  have h2 := turnaround_m1_k1 k default
  have h12 := h1.trans_plus h2
  have h3 := step_D_zero (k + 2)
  have h_eq : 2 * (k + 2) + 3 = 2 * k + 7 := by omega
  rw [h_eq] at h3
  exact h12.trans h3

/-- Rule 7 (`m = 1, k ≥ 1, b ≥ 2`): `C(1, k + 1, b + 2) -> C(2k + 6, 1, b)`. -/
private theorem step_C_m1_k1_b2 (k b : ℕ) :
    ReachesPlus target (cfg_C 1 (k + 1) (b + 2)) (cfg_C (2 * k + 6) 1 b) := by
  have h_start :
      cfg_C 1 (k + 1) (b + 2) =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (b + 1)]
  have h1 := shift_C_10_left (k + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)
  rw [← h_start] at h1
  have h2 := turnaround_m1_k1 k (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)
  have h12 := h1.trans_plus h2
  have h3 := step_D_succ (k + 2) b
  have h_eq : 2 * (k + 2) + 2 = 2 * k + 6 := by omega
  rw [h_eq] at h3
  exact h12.trans h3

/-- Rule 8 (`m = 2, k = 0, b = 1`): `C(2, 0, 1) -> C(0, 1, 0)`. -/
private theorem step_C_m2_k0_b1 :
    ReachesPlus target (cfg_C 2 0 1) (cfg_C 0 1 0) := by
  unfold cfg_C
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [list_pow_zero, ListBlank.append_nil, list_pow_one, list_pow_one, h_two]
  bb_steps

/-- Rule 9 (`m = 2, k = 0, b ≥ 2`): `C(2, 0, b + 2)` halts in 7 steps at state `F` reading `1`. -/
private theorem step_C_m2_k0_b2_halt (b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C 2 0 (b + 2)) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F (ListBlank.append [1] default)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)), ?_, ?_⟩
  · unfold cfg_C
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    have h_b2 :
        ListBlank.append (([1] : List (Fin 2)) ^ (b + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := by
      have h_eq : b + 2 = 2 + b := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [list_pow_zero, ListBlank.append_nil, h_two, h_b2]
    bb_steps
  · bb_halt

/-- Rule 10 (`m = 2, k = 1, b ≥ 1`): `C(2, 1, b + 1) -> C(0, 1, b + 1)`. -/
private theorem step_C_m2_k1 (b : ℕ) :
    ReachesPlus target (cfg_C 2 1 (b + 1)) (cfg_C 0 1 (b + 1)) := by
  unfold cfg_C
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [list_pow_zero, ListBlank.append_nil, list_pow_one, h_two,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  bb_steps

/-- Helper turnaround for `m = 2, k ≥ 2`: reaches `D>` on `(01)^{k+3} r`. -/
private theorem turnaround_m2_k2 (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight D default
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3)) r)) := by
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  have h_r2 :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2)) r =
        ListBlank.append [0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r) := by
    have h_eq : k + 2 = 2 + k := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  have h_r3 :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3)) r =
        ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r) := by
    have h_eq : k + 3 = 3 + k := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  rw [h_two, h_r2, h_r3]
  bb_steps

/-- Rule 11 (`m = 2, k ≥ 2, b = 1`): `C(2, k + 2, 1) -> C(2k + 7, 0, 2)`. -/
private theorem step_C_m2_k2_b1 (k : ℕ) :
    ReachesPlus target (cfg_C 2 (k + 2) 1) (cfg_C (2 * k + 7) 0 2) := by
  have h_start :
      cfg_C 2 (k + 2) 1 =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
            (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
          (ListBlank.append [1] default) := by
    unfold cfg_C
    rw [list_pow_one]
  have h1 := shift_C_10_left (k + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ 2) default) default
  rw [← h_start] at h1
  have h2 := turnaround_m2_k2 k default
  have h12 := h1.trans_plus h2
  have h3 := step_D_zero (k + 2)
  have h_eq : 2 * (k + 2) + 3 = 2 * k + 7 := by omega
  rw [h_eq] at h3
  exact h12.trans h3

/-- Rule 12 (`m = 2, k ≥ 2, b ≥ 2`): `C(2, k + 2, b + 2) -> C(2k + 6, 1, b)`. -/
private theorem step_C_m2_k2_b2 (k b : ℕ) :
    ReachesPlus target (cfg_C 2 (k + 2) (b + 2)) (cfg_C (2 * k + 6) 1 b) := by
  have h_start :
      cfg_C 2 (k + 2) (b + 2) =
        Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2))
            (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (b + 1)]
  have h1 := shift_C_10_left (k + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)
  rw [← h_start] at h1
  have h2 := turnaround_m2_k2 k (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default)
  have h12 := h1.trans_plus h2
  have h3 := step_D_succ (k + 2) b
  have h_eq : 2 * (k + 2) + 2 = 2 * k + 6 := by omega
  rw [h_eq] at h3
  exact h12.trans h3

private theorem step_C (m k b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C m k b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | b'
  · exact ⟨cfg_C (m + 1) 0 (2 * k + 2), step_C_b0 m k,
      Or.inl (in_ps_C (m + 1) 0 (2 * k + 2))⟩
  · rcases m with _ | _ | _ | m'
    · rcases b' with _ | b''
      · exact ⟨cfg_C (2 * k + 3) 0 2, step_C_m0_b1 k,
          Or.inl (in_ps_C (2 * k + 3) 0 2)⟩
      · exact ⟨cfg_C (2 * k + 2) 1 b'', step_C_m0_b2 k b'',
          Or.inl (in_ps_C (2 * k + 2) 1 b'')⟩
    · rcases k with _ | k'
      · exact ⟨cfg_C 0 0 (b' + 3), step_C_m1_k0 b',
          Or.inl (in_ps_C 0 0 (b' + 3))⟩
      · rcases b' with _ | b''
        · exact ⟨cfg_C (2 * k' + 7) 0 2, step_C_m1_k1_b1 k',
            Or.inl (in_ps_C (2 * k' + 7) 0 2)⟩
        · exact ⟨cfg_C (2 * k' + 6) 1 b'', step_C_m1_k1_b2 k' b'',
            Or.inl (in_ps_C (2 * k' + 6) 1 b'')⟩
    · rcases k with _ | _ | k'
      · rcases b' with _ | b''
        · exact ⟨cfg_C 0 1 0, step_C_m2_k0_b1, Or.inl (in_ps_C 0 1 0)⟩
        · obtain ⟨cfg', h_plus, h_halt⟩ := step_C_m2_k0_b2_halt b''
          exact ⟨cfg', h_plus, Or.inr h_halt⟩
      · exact ⟨cfg_C 0 1 (b' + 1), step_C_m2_k1 b',
          Or.inl (in_ps_C 0 1 (b' + 1))⟩
      · rcases b' with _ | b''
        · exact ⟨cfg_C (2 * k' + 7) 0 2, step_C_m2_k2_b1 k',
            Or.inl (in_ps_C (2 * k' + 7) 0 2)⟩
        · exact ⟨cfg_C (2 * k' + 6) 1 b'', step_C_m2_k2_b2 k' b'',
            Or.inl (in_ps_C (2 * k' + 6) 1 b'')⟩
    · exact ⟨cfg_C m' (k + 2) b', step_C_m3 m' k b',
        Or.inl (in_ps_C m' (k + 2) b')⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 0 0 2) := by
  have h_init : ReachesPlus target (init []) (cfg_C 0 0 2) := by
    unfold cfg_C
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [list_pow_zero, list_pow_zero, ListBlank.append_nil, ListBlank.append_nil, h_two]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 0 0 2, init_reaches_start, in_ps_C 0 0 2⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_C]
  exact step_C (vars 0) (vars 1) (vars 2)

/-- `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`. -/
inductive State where
  /-- $C(m, k, b) := 0^\infty\,1^m\,(10)^k\,\mathrm{C}{>}\,1^b\,0^\infty$. -/
  | C (m k b : ℕ)

/-- Initial symbolic state $C(0, 0, 2)$, reached after 2 raw TM steps. -/
def start : State := .C 0 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C m k b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ m) default))
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default)

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C m k 0 => some (.C (m + 1) 0 (2 * k + 2))
  | .C 0 k 1 => some (.C (2 * k + 3) 0 2)
  | .C 0 k (b + 2) => some (.C (2 * k + 2) 1 b)
  | .C 1 0 (b + 1) => some (.C 0 0 (b + 3))
  | .C 1 (k + 1) 1 => some (.C (2 * k + 7) 0 2)
  | .C 1 (k + 1) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C 2 0 1 => some (.C 0 1 0)
  | .C 2 0 (_ + 2) => none
  | .C 2 1 (b + 1) => some (.C 0 1 (b + 1))
  | .C 2 (k + 2) 1 => some (.C (2 * k + 7) 0 2)
  | .C 2 (k + 2) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C (m + 3) k (b + 1) => some (.C m (k + 2) b)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨m, k, b⟩ s' hnext
    rcases b with _ | b'
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_C_b0 m k
    · rcases m with _ | _ | _ | m'
      · rcases b' with _ | b''
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_m0_b1 k
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_m0_b2 k b''
      · rcases k with _ | k'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_m1_k0 b'
        · rcases b' with _ | b''
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact step_C_m1_k1_b1 k'
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact step_C_m1_k1_b2 k' b''
      · rcases k with _ | _ | k'
        · rcases b' with _ | b''
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact step_C_m2_k0_b1
          · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_m2_k1 b'
        · rcases b' with _ | b''
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact step_C_m2_k2_b1 k'
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact step_C_m2_k2_b2 k' b''
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_m3 m' k b'
  step_none := by
    rintro ⟨m, k, b⟩ hnext
    rcases b with _ | b'
    · simp [next] at hnext
    · rcases m with _ | _ | _ | m'
      · rcases b' with _ | b'' <;> simp [next] at hnext
      · rcases k with _ | k'
        · simp [next] at hnext
        · rcases b' with _ | b'' <;> simp [next] at hnext
      · rcases k with _ | _ | k'
        · rcases b' with _ | b''
          · simp [next] at hnext
          · obtain ⟨cfg', hp, hh⟩ := step_C_m2_k0_b2_halt b''
            exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
        · rcases b' with _ | b'' <;> simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH
