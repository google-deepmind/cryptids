/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`
(<https://wiki.bbchallenge.org/wiki/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF>,
**HydraShift6**, `cryptid_12`, holdout #545, `suspect_85`).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$A(m, n) := 0^\infty\,1^{m+1}\,(01)^n\,0\,\mathrm{A}{>}\,0^\infty$$
at $A(0, 1)$ in 15 steps, and every $A(m, n)$ advances in `ReachesPlus` either to another
$A(m', n')$ or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
A(m, n) = 0^inf 1^(m+1) (01)^n 0 A> 0^inf

A(0, 2i)       -> Halt
A(0, 2i+1)     -> A(6i+6, 1)
A(1, 2i)       -> Halt
A(1, 2i+1)     -> Halt
A(2, 2i)       -> A(6i+5, 1)
A(2, 2i+1)     -> A(6i+9, 1)
A(3, 2i)       -> A(0, 3i+3)
A(3, 2i+1)     -> A(0, 3i+5)
A(m+4, 2i)     -> A(m, 3i+4)
A(m+4, 2i+1)   -> A(m, 3i+6)

Start: A(0, 1), reached after 15 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Bounce Lemmas -/

/-- Rightward E-A shift across `1^(2k)`, depositing `(10)^k` on the left. -/
private theorem shift_EA (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight E (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r) := by
      have h_add : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_split]
    have h1 :
        ReachesPlus target
          (Cfg.headRight E l
            (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)))
          (Cfg.headRight E (ListBlank.append [1, 0] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
      bb_steps
    have h2 := ih (ListBlank.append [1, 0] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward D-B shift across `(10)^k`, depositing `1^(2k)` on the right. -/
private theorem shift_D_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0] r))
      (Cfg.headRight D l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 :
        ReachesPlus target
          (Cfg.headRight D
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l))
            (ListBlank.append [0] r))
          (Cfg.headRight D
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append [0] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r := by
      have h_two : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      rw [h_two, ← ListBlank.append_pow_add]
      exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) r) (by omega)
    rwa [h_pow] at h3

/-- Rightward shift across `1^k` in state `F`. -/
private theorem shift_F_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
          (Cfg.headRight F (ListBlank.append [1] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward E-A sweep across `1^(2k)` followed by F-turnaround and leftward D-B sweep. -/
private theorem bounce_E_to_D (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) default))
      (Cfg.headRight D l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default))) := by
  have h1 := shift_EA k l default
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) default)
        (Cfg.headRight D (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
          (ListBlank.append [0] (ListBlank.append [1] default))) := by
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := shift_D_left k l (ListBlank.append [1] default)
  have h123 := h12.trans_star h3
  have h_pow :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append [1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_pow] at h123

/-- Consume one `1` to the left of `A` on `0 1^(2k+2)` and bounce back to `D` on `0 1^(2k+5)`. -/
private theorem step_A1_to_D (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1] l)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)))
      (Cfg.headRight D l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) default))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight A (ListBlank.append [1] l)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)))
        (Cfg.headRight E l
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 2))) default)) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default) := by
      have h_add : 2 * k + 2 = 1 + (2 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 2))) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default) := by
      have h_add : 2 * (k + 2) = 3 + (2 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, h_r]
    bb_steps
  have h2 := bounce_E_to_D (k + 2) l
  have h12 := h1.trans h2
  have h_eq : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rwa [h_eq] at h12

/-- One iteration of the pair-absorption loop: consumes `(10)^2` on the left and adds `6` ones on
the right. -/
private theorem absorb_one (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1, 0, 1, 0] l)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)))
      (Cfg.headRight A l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 8)) default))) := by
  have h_l :
      ListBlank.append ([1, 0, 1, 0] : List (Fin 2)) l =
        ListBlank.append [1] (ListBlank.append [0, 1, 0] l) := rfl
  rw [h_l]
  have h1 := step_A1_to_D k (ListBlank.append [0, 1, 0] l)
  have h2 :
      ReachesPlus target
        (Cfg.headRight D (ListBlank.append [0, 1, 0] l)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) default)))
        (Cfg.headRight A l
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 8)) default))) := by
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 8)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) default) := by
      have h_add : 2 * k + 8 = 3 + (2 * k + 5) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  exact h1.trans h2

/-- `i` iterations of `absorb_one`, consuming `(10)^(2i)` on the left and growing the right `1`-run
from `2k + 2` to `2k + 6i + 2`. -/
private theorem absorb_iter (i k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i)) l)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)))
      (Cfg.headRight A l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6 * i + 2)) default))) := by
  induction i generalizing k with
  | zero => exact ReachesStar.refl _ _
  | succ i ih =>
    have h_split :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * (i + 1))) l =
          ListBlank.append [1, 0, 1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i)) l) := by
      have h_add : 2 * (i + 1) = 2 + 2 * i := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_split]
    have h1 := absorb_one k (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i)) l)
    have h_k1 : 2 * k + 8 = 2 * (k + 3) + 2 := by omega
    rw [h_k1] at h1
    have h2 := ih (k + 3)
    have h3 := (h1.trans_star h2).to_star
    have h_k2 : 2 * (k + 3) + 6 * i + 2 = 2 * k + 6 * (i + 1) + 2 := by omega
    rwa [h_k2] at h3

/-- Full absorption phase for even `n = 2i` followed by `step_A1_to_D`. -/
private theorem even_to_D (i : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * i))
          (ListBlank.append [0] (ListBlank.append [1] l)))
        default)
      (Cfg.headRight D l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 2) + 1)) default))) := by
  rw [append_01_pow_zero]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i)) (ListBlank.append [1] l)))
          default)
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i)) (ListBlank.append [1] l))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * 0 + 2)) default))) := by
    have h2 : (([1] : List (Fin 2)) ^ (2 * 0 + 2)) = [1, 1] := rfl
    rw [h2]
    bb_steps
  have h2 := absorb_iter i 0 (ListBlank.append [1] l)
  have h12 := h1.trans_star h2
  have h_eq1 : 2 * 0 + 6 * i + 2 = 2 * (3 * i) + 2 := by omega
  rw [h_eq1] at h12
  have h3 := step_A1_to_D (3 * i) l
  have h123 := h12.trans h3
  have h_eq2 : 2 * (3 * i) + 5 = 2 * (3 * i + 2) + 1 := by omega
  rwa [h_eq2] at h123

/-- Full absorption phase for odd `n = 2i + 1` reaching state `C`. -/
private theorem odd_to_C (i : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * i + 1))
          (ListBlank.append [0] (ListBlank.append [1] l)))
        default)
      (Cfg.headRight C l
        (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) default)) := by
  rw [append_01_pow_zero]
  have h_split :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i + 1)) (ListBlank.append [1] l) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i))
          (ListBlank.append [1, 0, 1] l) := by
    rw [list_pow_succ', ListBlank.append_assoc]
    rfl
  rw [h_split]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i))
              (ListBlank.append [1, 0, 1] l)))
          default)
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (2 * i))
            (ListBlank.append [1, 0, 1] l))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * 0 + 2)) default))) := by
    have h2 : (([1] : List (Fin 2)) ^ (2 * 0 + 2)) = [1, 1] := rfl
    rw [h2]
    bb_steps
  have h2 := absorb_iter i 0 (ListBlank.append [1, 0, 1] l)
  have h12 := h1.trans_star h2
  have h_eq1 : 2 * 0 + 6 * i + 2 = 2 * (3 * i) + 2 := by omega
  have h_l :
      ListBlank.append ([1, 0, 1] : List (Fin 2)) l =
        ListBlank.append [1] (ListBlank.append [0, 1] l) := rfl
  rw [h_eq1, h_l] at h12
  have h3 := step_A1_to_D (3 * i) (ListBlank.append [0, 1] l)
  have h123 := h12.trans h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight D (ListBlank.append [0, 1] l)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i) + 5)) default)))
        (Cfg.headRight C l
          (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) default)) := by
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i) + 5)) default) := by
      have h_add : 6 * i + 8 = 3 + (2 * (3 * i) + 5) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  exact h123.trans h4

/-- Odd absorption phase for `m ≥ 1` (at least two `1`s), continuing from `odd_to_C` to `D`. -/
private theorem odd_to_D (i : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * i + 1))
          (ListBlank.append [0] (ListBlank.append [1] (ListBlank.append [1] l))))
        default)
      (Cfg.headRight D (ListBlank.append [1] l)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 4) + 1)) default))) := by
  have h1 := odd_to_C i (ListBlank.append [1] l)
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1] l)
          (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) default))
        (Cfg.headRight E (ListBlank.append [1] l)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 4))) default)) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 7)) default) := by
      have h_add : 6 * i + 8 = 1 + (6 * i + 7) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 4)))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 7)) default) := by
      have h_add : 2 * (3 * i + 4) = 1 + (6 * i + 7) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, h_r]
    bb_steps
  have h12 := h1.trans h2
  have h3 := bounce_E_to_D (3 * i + 4) (ListBlank.append [1] l)
  exact h12.trans h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$A(m, n) := 0^\infty\,1^{m+1}\,(01)^n\,0\,\mathrm{A}{>}\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some A
    right := .default }

/-- Closed pattern set for `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

/-- Configuration $A(m, n)$. -/
private def cfg_A (m n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default)))
    default

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) :=
  rfl

private theorem in_ps_A (m n : ℕ) : IsInPatternSet ps (cfg_A m n) :=
  ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => m | 1 => n | _ => 0, rfl, trivial⟩

/-! ## Shared Closing Lemmas -/

/-- From `F` on `1^(k+3)` with blank left tape, sweep right and turn around into `cfg_A k 1`. -/
private theorem sweep_F_to_A1 (k : ℕ) :
    ReachesPlus target
      (Cfg.headRight F default
        (ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) default))
      (cfg_A k 1) := by
  have h1 := shift_F_right (k + 3) default default
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default) := by
    have h_add : k + 3 = 2 + (k + 1) := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_split] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default))
          default)
        (cfg_A k 1) := by
    unfold cfg_A
    rw [list_pow_one]
    bb_steps
  exact h1.trans_plus h2

/-- Closing from `D` when `1` remains on the left (`m = 1`): halts in 4 steps. -/
private theorem close_D_m1_halt (j : ℕ) :
    ∃ cfg',
      ReachesPlus target
        (Cfg.headRight D (ListBlank.append [1] default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
        cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headRight C default
    (ListBlank.append [0, 1, 1, 1, 1]
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)), ?_, by bb_halt⟩
  bb_steps

/-- Closing from `D` when `1^2` remains on the left (`m = 2`): resets to `cfg_A (2j + 1) 1`. -/
private theorem close_D_m2_reset (j : ℕ) :
    ReachesPlus target
      (Cfg.headRight D (ListBlank.append [1, 1] default)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
      (cfg_A (2 * j + 1) 1) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D (ListBlank.append [1, 1] default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
        (Cfg.headRight F default
          (ListBlank.append (([1] : List (Fin 2)) ^ ((2 * j + 1) + 3)) default)) := by
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ ((2 * j + 1) + 3))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default) := by
      have h_add : (2 * j + 1) + 3 = 3 + (2 * j + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  exact h1.trans (sweep_F_to_A1 (2 * j + 1))

/-- Closing from `D` when `1^3 ++ l` remains on the left (`m ≥ 3`): shifts to
`(01)^(j+2) ++ [0] ++ l`. -/
private theorem close_D_shift (j : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D (ListBlank.append [1, 1, 1] l)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 2))
          (ListBlank.append [0] l))
        default) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D (ListBlank.append [1, 1, 1] l)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
        (Cfg.headRight E l
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (j + 2)))
            (ListBlank.append [1] default))) := by
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (j + 2)))
          (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default) := by
      have h_one : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
      nth_rw 2 [h_one]
      rw [← ListBlank.append_pow_add]
      have h_add : 2 * (j + 2) + 1 = 4 + (2 * j + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h2 := shift_EA (j + 2) l (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 2)) l)
          (ListBlank.append [1] default))
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (j + 2)) l))
          default) := by
    bb_steps
  have h123 := h12.trans h3
  rwa [← append_01_pow_zero] at h123

/-! ## Accelerated Transition Rules -/

/-- Rule 1: $A(0, 2i)$ halts. -/
private theorem step_A_m0_even (i : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 0 (2 * i)) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_A
  rw [list_pow_one]
  have h1 := even_to_D i default
  have h2 :
      ReachesPlus target
        (Cfg.headRight D default
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 2) + 1)) default)))
        (Cfg.headRight C default
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 2) + 1)) default))) := by
    bb_steps
  refine ⟨_, h1.trans h2, by bb_halt⟩

/-- Rule 2: $A(0, 2i + 1) \to^+ A(6i + 6, 1)$. -/
private theorem step_A_m0_odd (i : ℕ) :
    ReachesPlus target (cfg_A 0 (2 * i + 1)) (cfg_A (6 * i + 6) 1) := by
  unfold cfg_A
  rw [list_pow_one]
  have h1 := odd_to_C i default
  have h2 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) default))
        (Cfg.headRight F default
          (ListBlank.append (([1] : List (Fin 2)) ^ ((6 * i + 6) + 3)) default)) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 8)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 6)) default) := by
      have h_add : 6 * i + 8 = 2 + (6 * i + 6) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ ((6 * i + 6) + 3))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (6 * i + 6)) default) := by
      have h_add : (6 * i + 6) + 3 = 3 + (6 * i + 6) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, h_r]
    bb_steps
  exact (h1.trans h2).trans (sweep_F_to_A1 (6 * i + 6))

/-- Rule 3: $A(1, 2i)$ halts. -/
private theorem step_A_m1_even (i : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 1 (2 * i)) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_A
  have h_two :
      ListBlank.append (([1] : List (Fin 2)) ^ (1 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append [1] default) := rfl
  rw [h_two]
  have h1 := even_to_D i (ListBlank.append [1] default)
  obtain ⟨cfg', h2, h_halt⟩ := close_D_m1_halt (3 * i + 2)
  exact ⟨cfg', h1.trans h2, h_halt⟩

/-- Rule 4: $A(1, 2i + 1)$ halts. -/
private theorem step_A_m1_odd (i : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 1 (2 * i + 1)) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_A
  have h_two :
      ListBlank.append (([1] : List (Fin 2)) ^ (1 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append [1] default) := rfl
  rw [h_two]
  have h1 := odd_to_D i default
  obtain ⟨cfg', h2, h_halt⟩ := close_D_m1_halt (3 * i + 4)
  exact ⟨cfg', h1.trans h2, h_halt⟩

/-- Rule 5: $A(2, 2i) \to^+ A(6i + 5, 1)$. -/
private theorem step_A_m2_even (i : ℕ) :
    ReachesPlus target (cfg_A 2 (2 * i)) (cfg_A (6 * i + 5) 1) := by
  have h_three :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append [1, 1] default) := rfl
  have h1 :
      ReachesPlus target (cfg_A 2 (2 * i))
        (Cfg.headRight D (ListBlank.append [1, 1] default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 2) + 1)) default))) := by
    unfold cfg_A
    rw [h_three]
    exact even_to_D i (ListBlank.append [1, 1] default)
  have h12 := h1.trans (close_D_m2_reset (3 * i + 2))
  have h_eq : 2 * (3 * i + 2) + 1 = 6 * i + 5 := by omega
  rwa [h_eq] at h12

/-- Rule 6: $A(2, 2i + 1) \to^+ A(6i + 9, 1)$. -/
private theorem step_A_m2_odd (i : ℕ) :
    ReachesPlus target (cfg_A 2 (2 * i + 1)) (cfg_A (6 * i + 9) 1) := by
  have h_three :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append [1] (ListBlank.append [1] default)) := rfl
  have h1 :
      ReachesPlus target (cfg_A 2 (2 * i + 1))
        (Cfg.headRight D (ListBlank.append [1, 1] default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 4) + 1)) default))) := by
    unfold cfg_A
    rw [h_three]
    exact odd_to_D i (ListBlank.append [1] default)
  have h12 := h1.trans (close_D_m2_reset (3 * i + 4))
  have h_eq : 2 * (3 * i + 4) + 1 = 6 * i + 9 := by omega
  rwa [h_eq] at h12

/-- Helper converting `(01)^(k+1) ++ [0] ++ default` into `cfg_A 0 k`. -/
private theorem normalize_m3_target (k : ℕ) :
    Cfg.headRight A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [0] default))
      default = cfg_A 0 k := by
  unfold cfg_A
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rw [h_def, list_pow_succ', ListBlank.append_assoc, list_pow_one]
  rfl

/-- Rule 7: $A(3, 2i) \to^+ A(0, 3i + 3)$. -/
private theorem step_A_m3_even (i : ℕ) :
    ReachesPlus target (cfg_A 3 (2 * i)) (cfg_A 0 (3 * i + 3)) := by
  have h_four :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append [1, 1, 1] default) := rfl
  have h1 :
      ReachesPlus target (cfg_A 3 (2 * i))
        (Cfg.headRight D (ListBlank.append [1, 1, 1] default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 2) + 1)) default))) := by
    unfold cfg_A
    rw [h_four]
    exact even_to_D i (ListBlank.append [1, 1, 1] default)
  have h2 := close_D_shift (3 * i + 2) default
  have h_eq : 3 * i + 2 + 2 = (3 * i + 3) + 1 := by omega
  rw [h_eq, normalize_m3_target (3 * i + 3)] at h2
  exact h1.trans h2

/-- Rule 8: $A(3, 2i + 1) \to^+ A(0, 3i + 5)$. -/
private theorem step_A_m3_odd (i : ℕ) :
    ReachesPlus target (cfg_A 3 (2 * i + 1)) (cfg_A 0 (3 * i + 5)) := by
  have h_four :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append [1] (ListBlank.append [1, 1] default)) := rfl
  have h1 :
      ReachesPlus target (cfg_A 3 (2 * i + 1))
        (Cfg.headRight D (ListBlank.append [1, 1, 1] default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 4) + 1)) default))) := by
    unfold cfg_A
    rw [h_four]
    exact odd_to_D i (ListBlank.append [1, 1] default)
  have h2 := close_D_shift (3 * i + 4) default
  have h_eq : 3 * i + 4 + 2 = (3 * i + 5) + 1 := by omega
  rw [h_eq, normalize_m3_target (3 * i + 5)] at h2
  exact h1.trans h2

/-- Rule 9: $A(m + 4, 2i) \to^+ A(m, 3i + 4)$. -/
private theorem step_A_m_ge4_even (m i : ℕ) :
    ReachesPlus target (cfg_A (m + 4) (2 * i)) (cfg_A m (3 * i + 4)) := by
  have h_five :
      ListBlank.append (([1] : List (Fin 2)) ^ (m + 4 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1]
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default)) := by
    have h_add : m + 4 + 1 = 4 + (m + 1) := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h1 :
      ReachesPlus target (cfg_A (m + 4) (2 * i))
        (Cfg.headRight D
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 2) + 1)) default))) := by
    unfold cfg_A
    rw [h_five]
    exact even_to_D i
      (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default))
  have h2 := close_D_shift (3 * i + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default)
  have h_eq : 3 * i + 2 + 2 = 3 * i + 4 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

/-- Rule 10: $A(m + 4, 2i + 1) \to^+ A(m, 3i + 6)$. -/
private theorem step_A_m_ge4_odd (m i : ℕ) :
    ReachesPlus target (cfg_A (m + 4) (2 * i + 1)) (cfg_A m (3 * i + 6)) := by
  have h_five :
      ListBlank.append (([1] : List (Fin 2)) ^ (m + 4 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1]
          (ListBlank.append [1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default))) := by
    have h_add : m + 4 + 1 = 4 + (m + 1) := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h1 :
      ReachesPlus target (cfg_A (m + 4) (2 * i + 1))
        (Cfg.headRight D
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (3 * i + 4) + 1)) default))) := by
    unfold cfg_A
    rw [h_five]
    exact odd_to_D i
      (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default))
  have h2 := close_D_shift (3 * i + 4)
    (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default)
  have h_eq : 3 * i + 4 + 2 = 3 * i + 6 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem step_A_all (m n : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A m n) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases m with _ | _ | _ | _ | m'
  · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨cfg', h1, h2⟩ := step_A_m0_even i
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_A (6 * i + 6) 1, step_A_m0_odd i, Or.inl (in_ps_A (6 * i + 6) 1)⟩
  · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨cfg', h1, h2⟩ := step_A_m1_even i
      exact ⟨cfg', h1, Or.inr h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_A_m1_odd i
      exact ⟨cfg', h1, Or.inr h2⟩
  · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨cfg_A (6 * i + 5) 1, step_A_m2_even i, Or.inl (in_ps_A (6 * i + 5) 1)⟩
    · exact ⟨cfg_A (6 * i + 9) 1, step_A_m2_odd i, Or.inl (in_ps_A (6 * i + 9) 1)⟩
  · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨cfg_A 0 (3 * i + 3), step_A_m3_even i, Or.inl (in_ps_A 0 (3 * i + 3))⟩
    · exact ⟨cfg_A 0 (3 * i + 5), step_A_m3_odd i, Or.inl (in_ps_A 0 (3 * i + 5))⟩
  · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨cfg_A m' (3 * i + 4), step_A_m_ge4_even m' i, Or.inl (in_ps_A m' (3 * i + 4))⟩
    · exact ⟨cfg_A m' (3 * i + 6), step_A_m_ge4_odd m' i, Or.inl (in_ps_A m' (3 * i + 6))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 0 1) := by
  have h_init : ReachesPlus target (init []) (cfg_A 0 1) := by
    unfold cfg_A
    rw [list_pow_one]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 1, init_reaches_start, in_ps_A 0 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A_all (vars 0) (vars 1)

/-- `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`. -/
inductive State where
  /-- $A(m, n) := 0^\infty\,1^{m+1}\,(01)^n\,0\,\mathrm{A}{>}\,0^\infty$. -/
  | A (m n : ℕ)

/-- Initial symbolic state $A(0, 1)$, reached after 15 raw TM steps. -/
def start : State := .A 0 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A m n =>
    Cfg.headRight SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) default)))
      default

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A 0 n =>
    if n % 2 = 0 then none
    else some (.A (6 * (n / 2) + 6) 1)
  | .A 1 _ => none
  | .A 2 n =>
    if n % 2 = 0 then some (.A (6 * (n / 2) + 5) 1)
    else some (.A (6 * (n / 2) + 9) 1)
  | .A 3 n =>
    if n % 2 = 0 then some (.A 0 (3 * (n / 2) + 3))
    else some (.A 0 (3 * (n / 2) + 5))
  | .A (m + 4) n =>
    if n % 2 = 0 then some (.A m (3 * (n / 2) + 4))
    else some (.A m (3 * (n / 2) + 6))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨m, n⟩ s' hnext
    rcases m with _ | _ | _ | _ | m'
    · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have h_mod : (2 * i) % 2 = 0 := by omega
        simp [next, h_mod] at hnext
      · have h_mod : (2 * i + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * i + 1) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m0_odd i
    · simp [next] at hnext
    · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have h_mod : (2 * i) % 2 = 0 := by omega
        have h_div : (2 * i) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m2_even i
      · have h_mod : (2 * i + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * i + 1) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m2_odd i
    · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have h_mod : (2 * i) % 2 = 0 := by omega
        have h_div : (2 * i) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m3_even i
      · have h_mod : (2 * i + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * i + 1) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m3_odd i
    · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have h_mod : (2 * i) % 2 = 0 := by omega
        have h_div : (2 * i) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m_ge4_even m' i
      · have h_mod : (2 * i + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * i + 1) / 2 = i := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_m_ge4_odd m' i
  step_none := by
    rintro ⟨m, n⟩ hnext
    rcases m with _ | _ | _ | _ | m'
    · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨cfg', hp, hh⟩ := step_A_m0_even i
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · rcases nat_even_or_odd_two_mul n with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨cfg', hp, hh⟩ := step_A_m1_even i
        exact ⟨cfg', hp.to_star, hh⟩
      · obtain ⟨cfg', hp, hh⟩ := step_A_m1_odd i
        exact ⟨cfg', hp.to_star, hh⟩
    · by_cases h : n % 2 = 0 <;> simp [next, h] at hnext
    · by_cases h : n % 2 = 0 <;> simp [next, h] at hnext
    · by_cases h : n % 2 = 0 <;> simp [next, h] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF
