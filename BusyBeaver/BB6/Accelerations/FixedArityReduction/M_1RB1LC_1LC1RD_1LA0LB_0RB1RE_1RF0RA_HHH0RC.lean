/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`
(see <https://wiki.bbchallenge.org/wiki/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC>)
(holdout #39 (`suspect_46`)).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$B(a, k, c) := 0^\infty\,1^a\,(10)^k\,\mathrm{B}{>}\,1^c\,0^\infty$$
at $B(5, 0, 1)$ in 12 steps, and every $B(a, k, c)$ advances in `ReachesPlus` either to another
$B(a', k', c')$ or to a halting configuration (when $c = 2$).

## Collatz-like Acceleration Rules

```text
Consider:
B(a, k, c) = 0^inf 1^a (10)^k B> 1^c 0^inf

B(0, k, 0)         -> B(1, 0, 2k+2)
B(1, 0, 0)         -> B(5, 0, 1)
B(1, k+1, 0)       -> B(2, 2, 2k+1)
B(a+2, k, 0)       -> B(a, 1, 2k+1)
B(a, k, 1)         -> B(a, k+1, 0)
B(a, k, 2)         -> Halt
B(a, k, 3)         -> B(a, k+2, 1)
B(a+1, k, d+4)     -> B(a, k+1, d+3)
B(0, 2m, d+4)      -> B(4m+2, 2, d+1)
B(0, 2m+1, d+4)    -> B(4m+5, 0, d+4)

Start: B(5, 0, 1), reached after 12 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Helper & Shift Lemmas -/

private theorem one_pow_four_mul (m : ℕ) :
    ([1, 1, 1, 1] : List (Fin 2)) ^ m = ([1] : List (Fin 2)) ^ (4 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, list_pow_add, ih, list_pow_add]
    rfl

private theorem zero_one_pow_two_mul (m : ℕ) :
    ([0, 1, 0, 1] : List (Fin 2)) ^ m = ([0, 1] : List (Fin 2)) ^ (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, list_pow_add, ih, list_pow_add]
    rfl

/-- `<C` shifts leftward over `(10)^k`, converting each `10` into `11` on the right tape. -/
private theorem shift_C_left_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft C l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft C
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)) r)
          (Cfg.headLeft C
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] r)) := by
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

/-- `<B` shifts leftward over `(10)^k`, preserving `(10)^k` on the right tape. -/
private theorem shift_B_left_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft B (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft B l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft B
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)) r)
          (Cfg.headLeft B
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [0, 1] r)) := by
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

/-- `B>` shifts rightward over `1 (01)^k`, placing `(10)^k` onto the left tape. -/
private theorem shift_B_right_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight B (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l
            (ListBlank.append [1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight B (ListBlank.append [0, 1] l)
            (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- `E>` shifts rightward over `(0101)^m`, writing `1^{4m}` onto the left tape. -/
private theorem shift_E_0101 (m : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ m) r))
      (Cfg.headRight E (ListBlank.append (([1, 1, 1, 1] : List (Fin 2)) ^ m) l) r) := by
  induction m generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ m ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E l
            (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ (m + 1)) r))
          (Cfg.headRight E (ListBlank.append [1, 1, 1, 1] l)
            (ListBlank.append (([0, 1, 0, 1] : List (Fin 2)) ^ m) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1, 1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1, 1, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1, 1] l) =
          ListBlank.append (([1, 1, 1, 1] : List (Fin 2)) ^ (m + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_E_0101_ones (m : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m)) r))
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m)) l) r) := by
  rw [← zero_one_pow_two_mul, ← one_pow_four_mul]
  exact shift_E_0101 m l r

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$B(a, k, c) := 0^\infty\,1^a\,(10)^k\,\mathrm{B}{>}\,1^c\,0^\infty$. -/
def pat_B : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.rep [1] 0 .default)
    head := some B
    right := .rep [1] 2 .default }

/-- Closed pattern set for `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_B, .true)]

/-- Configuration $B(a, k, c)$. -/
private def cfg_B (a k c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ c) default)

private theorem eval_pat_B (vars : ℕ → ℕ) :
    evalTapePattern pat_B vars = cfg_B (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_B (a k c : ℕ) : IsInPatternSet ps (cfg_B a k c) :=
  ⟨(pat_B, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => k | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

/-- Rule 1 (`c = 1`): `B(a, k, 1) -> B(a, k + 1, 0)` in `2` steps. -/
private theorem rule_c1 (a k : ℕ) :
    ReachesPlus target (cfg_B a k 1) (cfg_B a (k + 1) 0) := by
  unfold cfg_B
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
  bb_steps

/-- Rule 2 (`c = 2`, Halts): `B(a, k, 2)` halts in `3` steps at state `F` reading `0`. -/
private theorem rule_c2_halt (a k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_B a k 2) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 1, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
    default, ?_, by bb_halt⟩
  unfold cfg_B
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h2]
  bb_steps

/-- Rule 3 (`c = 3`): `B(a, k, 3) -> B(a, k + 2, 1)` in `12` steps. -/
private theorem rule_c3 (a k : ℕ) :
    ReachesPlus target (cfg_B a k 3) (cfg_B a (k + 2) 1) := by
  unfold cfg_B
  have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h3, list_pow_one,
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (k + 1),
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
  bb_steps

/-- Rule 4 (`c = 0, a = 0`): `B(0, k, 0) -> B(1, 0, 2k + 2)` in `2k + 3` steps. -/
private theorem rule_c0_a0 (k : ℕ) :
    ReachesPlus target (cfg_B 0 k 0) (cfg_B 1 0 (2 * k + 2)) := by
  have h1 :
      ReachesPlus target (cfg_B 0 k 0)
        (Cfg.headLeft C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)) := by
    unfold cfg_B
    rw [list_pow_zero, list_pow_one]
    bb_steps
  have h2 := shift_C_left_10 k
    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))
        (Cfg.headRight B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))) := by
    rw [list_pow_zero, list_pow_zero, list_pow_one]
    bb_steps
  have h123 := h12.trans h3
  have h_r :
      ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default := by
    have h_1 : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
    rw [one_pow_two_mul, ← ListBlank.append_pow_add]
    nth_rw 1 [h_1]
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  unfold cfg_B
  rwa [h_r] at h123

/-- Rule 5 (`c = 0, a = 1, k = 0`): `B(1, 0, 0) -> B(5, 0, 1)` in `11` steps. -/
private theorem rule_c0_a1_k0 :
    ReachesPlus target (cfg_B 1 0 0) (cfg_B 5 0 1) := by
  unfold cfg_B
  have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
  rw [list_pow_zero, list_pow_one, h5]
  bb_steps

/-- Rule 6 (`c = 0, a = 1, k ≥ 1`): `B(1, k + 1, 0) -> B(2, 2, 2k + 1)` in `2k + 18` steps. -/
private theorem rule_c0_a1_k1 (k : ℕ) :
    ReachesPlus target (cfg_B 1 (k + 1) 0) (cfg_B 2 2 (2 * k + 1)) := by
  have h1 :
      ReachesPlus target (cfg_B 1 (k + 1) 0)
        (Cfg.headLeft C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)) := by
    unfold cfg_B
    rw [list_pow_zero, list_pow_one]
    bb_steps
  have h2 := shift_C_left_10 (k + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))
        (Cfg.headRight B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))) := by
    have h2_01 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    have h2_1 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k, list_pow_one, h2_01, h2_1]
    bb_steps
  have h123 := h12.trans h3
  have h_r :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default := by
    rw [one_pow_two_mul, ← ListBlank.append_pow_add]
  unfold cfg_B
  rwa [h_r] at h123

/-- Rule 7 (`c = 0, a ≥ 2`): `B(a + 2, k, 0) -> B(a, 1, 2k + 1)` in `2k + 4` steps. -/
private theorem rule_c0_a2 (a k : ℕ) :
    ReachesPlus target (cfg_B (a + 2) k 0) (cfg_B a 1 (2 * k + 1)) := by
  have h1 :
      ReachesPlus target (cfg_B (a + 2) k 0)
        (Cfg.headLeft C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)) := by
    unfold cfg_B
    rw [list_pow_zero, list_pow_one]
    bb_steps
  have h2 := shift_C_left_10 k
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))
        (Cfg.headRight B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (a + 1),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) a, list_pow_one]
    bb_steps
  have h123 := h12.trans h3
  have h_r :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default := by
    rw [one_pow_two_mul, ← ListBlank.append_pow_add]
  unfold cfg_B
  rwa [h_r] at h123

/-- Rule 8 (`c = d + 4, a ≥ 1`): `B(a + 1, k, d + 4) -> B(a, k + 1, d + 3)` in `4k + 9` steps. -/
private theorem rule_c4_a1 (a k d : ℕ) :
    ReachesPlus target (cfg_B (a + 1) k (d + 4)) (cfg_B a (k + 1) (d + 3)) := by
  have h1 :
      ReachesPlus target (cfg_B (a + 1) k (d + 4))
        (Cfg.headLeft B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    unfold cfg_B
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
      have h_eq : d + 4 = 4 + d := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h2 := shift_B_left_10 k
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  have h3 :
      Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) =
      Cfg.headRight B
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    exact Cfg.headLeft_cons _ _ _ _
  rw [h3] at h12
  have h4 := shift_B_right_10 k
    (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h124 := h12.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (cfg_B a (k + 1) (d + 3)) := by
    unfold cfg_B
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 3)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
      have h_eq : d + 3 = 3 + d := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k, h_r]
    bb_steps
  exact h124.trans h5

/-- Rule 9 (`c = d + 4, a = 0, k = 2m`):
`B(0, 2m, d + 4) -> B(4m + 2, 2, d + 1)` in `10m + 21` steps. -/
private theorem rule_c4_a0_even (m d : ℕ) :
    ReachesPlus target (cfg_B 0 (2 * m) (d + 4)) (cfg_B (4 * m + 2) 2 (d + 1)) := by
  have h1 :
      ReachesPlus target (cfg_B 0 (2 * m) (d + 4))
        (Cfg.headLeft B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m))
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    unfold cfg_B
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
      have h_eq : d + 4 = 4 + d := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h2 := shift_B_left_10 (2 * m)
    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)
    (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft B
          (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m))
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m))
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))) := by
    have h3_1 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [list_pow_zero, h3_1]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_E_0101_ones m
    (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)
    (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h1234 := h123.trans_star h4
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (4 * m))
        (ListBlank.append (([1] : List (Fin 2)) ^ 3) (default : ListBlank (Fin 2))) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 2)) default) := by
    have h_1 : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
    rw [← ListBlank.append_pow_add]
    nth_rw 2 [h_1]
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  rw [h_comb] at h1234
  have h5 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 2)) default))
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (cfg_B (4 * m + 2) 2 (d + 1)) := by
    unfold cfg_B
    have h2_01 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h2_01, ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    bb_steps
  exact h1234.trans h5

/-- Rule 10 (`c = d + 4, a = 0, k = 2m + 1`):
`B(0, 2m + 1, d + 4) -> B(4m + 5, 0, d + 4)` in `10m + 18` steps. -/
private theorem rule_c4_a0_odd (m d : ℕ) :
    ReachesPlus target (cfg_B 0 (2 * m + 1) (d + 4)) (cfg_B (4 * m + 5) 0 (d + 4)) := by
  have h1 :
      ReachesPlus target (cfg_B 0 (2 * m + 1) (d + 4))
        (Cfg.headLeft B
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    unfold cfg_B
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
      have h_eq : d + 4 = 4 + d := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h2 := shift_B_left_10 (2 * m + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)
    (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft B
          (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))) := by
    have h3_1 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [list_pow_zero, h3_1]
    bb_steps
  have h123 := h12.trans h3
  have h_split :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m + 1))
        (ListBlank.append [0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * m))
          (ListBlank.append [0, 1]
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    rw [ListBlank.append_pow_add ([0, 1] : List (Fin 2)) (2 * m) 1]
    rfl
  rw [h_split] at h123
  have h4 := shift_E_0101_ones m
    (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)
    (ListBlank.append [0, 1]
      (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
  have h1234 := h123.trans_star h4
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (4 * m))
        (ListBlank.append (([1] : List (Fin 2)) ^ 3) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 3)) default := by
    rw [← ListBlank.append_pow_add]
  rw [h_comb] at h1234
  have h5 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 3)) default)
          (ListBlank.append [0, 1]
            (ListBlank.append [0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (cfg_B (4 * m + 5) 0 (d + 4)) := by
    unfold cfg_B
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 5)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 3)) default) := by
      have h_eq : 4 * m + 5 = 2 + (4 * m + 3) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
      have h_eq : d + 4 = 4 + d := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [list_pow_zero, ListBlank.append_nil, h_l, h_r]
    bb_steps
  exact h1234.trans h5

private theorem step_B (a k c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_B a k c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a'
    · exact ⟨cfg_B 1 0 (2 * k + 2), rule_c0_a0 k, Or.inl (in_ps_B 1 0 (2 * k + 2))⟩
    · rcases k with _ | k'
      · exact ⟨cfg_B 5 0 1, rule_c0_a1_k0, Or.inl (in_ps_B 5 0 1)⟩
      · exact ⟨cfg_B 2 2 (2 * k' + 1), rule_c0_a1_k1 k', Or.inl (in_ps_B 2 2 (2 * k' + 1))⟩
    · exact ⟨cfg_B a' 1 (2 * k + 1), rule_c0_a2 a' k, Or.inl (in_ps_B a' 1 (2 * k + 1))⟩
  · exact ⟨cfg_B a (k + 1) 0, rule_c1 a k, Or.inl (in_ps_B a (k + 1) 0)⟩
  · obtain ⟨cfg', h_plus, h_halt⟩ := rule_c2_halt a k
    exact ⟨cfg', h_plus, Or.inr h_halt⟩
  · exact ⟨cfg_B a (k + 2) 1, rule_c3 a k, Or.inl (in_ps_B a (k + 2) 1)⟩
  · rcases a with _ | a'
    · rcases nat_even_or_odd_two_mul k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨cfg_B (4 * m + 2) 2 (d + 1), rule_c4_a0_even m d,
          Or.inl (in_ps_B (4 * m + 2) 2 (d + 1))⟩
      · exact ⟨cfg_B (4 * m + 5) 0 (d + 4), rule_c4_a0_odd m d,
          Or.inl (in_ps_B (4 * m + 5) 0 (d + 4))⟩
    · exact ⟨cfg_B a' (k + 1) (d + 3), rule_c4_a1 a' k d,
        Or.inl (in_ps_B a' (k + 1) (d + 3))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_B 5 0 1) := by
  have h_init : ReachesPlus target (init []) (cfg_B 5 0 1) := by
    unfold cfg_B
    have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
    rw [list_pow_zero, list_pow_one, h5]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_B 5 0 1, init_reaches_start, in_ps_B 5 0 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_B]
  exact step_B (vars 0) (vars 1) (vars 2)

/-- `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. -/
inductive State where
  /-- $B(a, k, c) := 0^\infty\,1^a\,(10)^k\,\mathrm{B}{>}\,1^c\,0^\infty$. -/
  | B (a k c : ℕ)

/-- Initial symbolic state $B(5, 0, 1)$, reached after 12 raw TM steps. -/
def start : State := .B 5 0 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .B a k c =>
    Cfg.headRight SixState.B
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([1] : List (Fin 2)) ^ c) default)

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .B a k 1 => some (.B a (k + 1) 0)
  | .B _ _ 2 => none
  | .B a k 3 => some (.B a (k + 2) 1)
  | .B 0 k 0 => some (.B 1 0 (2 * k + 2))
  | .B 1 0 0 => some (.B 5 0 1)
  | .B 1 (k + 1) 0 => some (.B 2 2 (2 * k + 1))
  | .B (a + 2) k 0 => some (.B a 1 (2 * k + 1))
  | .B 0 k (d + 4) =>
    if k % 2 = 0 then some (.B (4 * (k / 2) + 2) 2 (d + 1))
    else some (.B (4 * (k / 2) + 5) 0 (d + 4))
  | .B (a + 1) k (d + 4) => some (.B a (k + 1) (d + 3))

private theorem next_sound (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨a, k, c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a'
    · exact rule_c0_a0 k
    · rcases k with _ | k'
      · exact rule_c0_a1_k0
      · exact rule_c0_a1_k1 k'
    · exact rule_c0_a2 a' k
  · dsimp only [next]; exact rule_c1 a k
  · dsimp only [next]; exact rule_c2_halt a k
  · dsimp only [next]; exact rule_c3 a k
  · rcases a with _ | a'
    · dsimp only [next]
      split_ifs with h_even
      · have hk : k = 2 * (k / 2) := by omega
        have h_rule := rule_c4_a0_even (k / 2) d
        change ReachesPlus target (cfg_B 0 k (d + 4)) (cfg_B (4 * (k / 2) + 2) 2 (d + 1))
        rwa [← hk] at h_rule
      · have hk : k = 2 * (k / 2) + 1 := by omega
        have h_rule := rule_c4_a0_odd (k / 2) d
        change ReachesPlus target (cfg_B 0 k (d + 4)) (cfg_B (4 * (k / 2) + 5) 0 (d + 4))
        rwa [← hk] at h_rule
    · dsimp only [next]; exact rule_c4_a1 a' k d

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    intro s s' hnext
    have hs := next_sound s
    rwa [hnext] at hs
  step_none := by
    intro s hnext
    have hs := next_sound s
    rw [hnext] at hs
    obtain ⟨cfg', hp, hh⟩ := hs
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC
