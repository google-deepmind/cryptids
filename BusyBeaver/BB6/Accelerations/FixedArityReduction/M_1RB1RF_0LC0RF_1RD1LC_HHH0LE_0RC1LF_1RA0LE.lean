/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`
(<https://wiki.bbchallenge.org/wiki/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE>, holdout #694,
`suspect_35`, analyzed by S. Ligocki).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$A(a, b) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^{b+1}\,0^\infty \qquad (a, b \ge 0)$$
at $A(1, 0)$ in 7 steps, and every $A(a, b)$ advances in `ReachesPlus` either to another
$A(a', b')$ or to a halting configuration (when $a = 2k + 1$ and $b = 2k + 3$).

## Collatz-like Acceleration Rules

Writing $A(a, b) = 0^\infty\,1^a\,\mathrm{A}{>}\,1^{b+1}\,0^\infty$ for $a, b \ge 0$ (equivalently
$0^\infty\,1^a\,\mathrm{A}{>}\,1^B\,0^\infty$ with $B = b + 1 \ge 1$):

```text
Consider:
A(a, b) = 0^inf 1^a A> 1^{b+1} 0^inf

A(2k, 0)            -> A(3, 2k+1)
A(2k, 1)            -> A(2k+1, 0)
A(2k, b+2)          -> A(2k+3, b)
A(2k+1, 2m)         -> A(4m+3, 2k-2m+2)   if m <= k
A(2k+1, 2m+1)       -> A(4m+7, 2k-2m-2)   if m + 1 <= k
A(2k+1, 2k+1)       -> A(4k+1, 0)
A(2k+1, 2k+2)       -> A(4k+7, 0)
A(2k+1, 2k+3)       -> Halt
A(2k+1, 2k+4)       -> A(4k+5, 0)
A(2k+1, 2k+5+c)     -> A(4k+7, c)

Start: A(1, 0), reached after 7 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Leftward shift across `1^n` in state `C` (`C1 -> 1LC`). -/
private theorem shift_C_left (n : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ n) l) r)
      (Cfg.headLeft C l (ListBlank.append (([1] : List (Fin 2)) ^ n) r)) := by
  induction n generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ n ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft C
            (ListBlank.append (([1] : List (Fin 2)) ^ (n + 1)) l) r)
          (Cfg.headLeft C
            (ListBlank.append (([1] : List (Fin 2)) ^ n) l)
            (ListBlank.append [1] r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h12 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ n) (ListBlank.append [1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (n + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h12

/-- Leftward sweep across `1^{2n}` in state `E`, producing `(01)^n` (`E1 -> 1LF`, `F1 -> 0LE`). -/
private theorem shift_E_left (n : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n)) l) r)
      (Cfg.headLeft E l (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r)) := by
  induction n generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ n ih =>
    have h_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (n + 1))) l =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n)) l) := by
      have h_mul : 2 * (n + 1) = 2 + 2 * n := by omega
      rw [h_mul, ListBlank.append_pow_add]
      rfl
    rw [h_split]
    have h1 :
        ReachesPlus target
          (Cfg.headLeft E
            (ListBlank.append [1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n)) l)) r)
          (Cfg.headLeft E
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n)) l)
            (ListBlank.append [0, 1] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h12 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ n) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h12

/-- Rightward sweep across `(01)^n` in state `F`, producing `1^{2n}` (`F0 -> 1RA`, `A1 -> 1RF`). -/
private theorem shift_F_right (n : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r))
      (Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ (2 * n)) l) r) := by
  induction n generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ n ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 1)) r))
          (Cfg.headRight F (ListBlank.append [1, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h12 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * n)) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (n + 1))) l := by
      have h2_eq : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      rw [h2_eq, ← ListBlank.append_pow_add]
      exact congrArg (fun k => ListBlank.append (([1] : List (Fin 2)) ^ k) l) (by omega)
    rwa [h_pow] at h12

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern $A(a, b) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^{b+1}\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

/-- Closed pattern set for `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

/-- Configuration $A(a, b) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^{b+1}\,0^\infty$. -/
private def cfg_A (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) :=
  rfl

private theorem in_ps_A (a b : ℕ) : IsInPatternSet ps (cfg_A a b) :=
  ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | _ => 0, rfl, trivial⟩

/-! ## Return-Sweep Helpers -/

/-- From $0^\infty\,1\,1^{2m}\,{<}\mathrm{E}\,0\,1^{b+1}\,0^\infty$, the machine sweeps left in `E`,
bounces off the left blank boundary, and sweeps right in `F` to reach $A(2m + 3, b)$. -/
private theorem sweep_E_odd_to_A (m b : ℕ) :
    ReachesPlus target
      (Cfg.headLeft E
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m))
          (ListBlank.append [1] default))
        (ListBlank.append [0]
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))
      (cfg_A (2 * m + 3) b) := by
  have h1 := shift_E_left m (ListBlank.append [1] default)
    (ListBlank.append [0]
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
  have h2 :
      ReachesPlus target
        (Cfg.headLeft E (ListBlank.append [1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [0]
              (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))
        (Cfg.headRight F (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [0]
              (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))) := by
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := shift_F_right m (ListBlank.append [1, 1] default)
    (ListBlank.append [0]
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) (ListBlank.append [1, 1] default))
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))
        (cfg_A (2 * m + 3) b) := by
    unfold cfg_A
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 3)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m))
              (ListBlank.append [1, 1] default)) := by
      have h2_eq : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      have h1_eq : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
      rw [h2_eq, ← ListBlank.append_pow_add]
      nth_rw 2 [h1_eq]
      rw [← ListBlank.append_pow_add]
      exact congrArg (fun k => ListBlank.append (([1] : List (Fin 2)) ^ k) default) (by omega)
    rw [h_l]
    bb_steps
  exact h123.trans h4

/-- From $0^\infty\,1^{2m}\,0\,1^{b+2}\,{<}\mathrm{C}\,0^\infty$, the machine shifts left across
$1^{b+2}$, flips the `0` separator in `C`/`D`, and finishes via `sweep_E_odd_to_A` at
$A(2m + 3, b)$. -/
private theorem sweep_C_to_A (m b : ℕ) :
    ReachesPlus target
      (Cfg.headLeft C
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) default)))
        default)
      (cfg_A (2 * m + 3) b) := by
  have h1 := shift_C_left (b + 2)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) default))
    default
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := by
    have h_add : b + 2 = 2 + b := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_r] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headLeft C
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) default))
          (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m)) (ListBlank.append [1] default))
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
    rw [ListBlank.append_pow_comm ([1] : List (Fin 2)) (2 * m) default]
    bb_steps
  exact (h1.trans_plus h2).trans (sweep_E_odd_to_A m b)

/-! ## Even-`a` Macro-Transition Rules (Rules 1, 2, 3) -/

/-- General $b = 0$ rule: $A(a, 0) \to A(3, a + 1)$ for all $a \ge 0$ (covers Rule 1 and the
$m = 0$ case of Rule 5). -/
private theorem step_A_b0 (a : ℕ) :
    ReachesPlus target (cfg_A a 0) (cfg_A 3 (a + 1)) := by
  have h1 :
      ReachesPlus target (cfg_A a 0)
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ ((a + 1) + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * 0)) default)))
          default) := by
    unfold cfg_A
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ ((a + 1) + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * 0))
              (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
      have h_add : (a + 1) + 2 = 3 + a := by omega
      rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_cons, ListBlank.append_nil,
        ListBlank.cons_zero_default, h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1.trans (sweep_C_to_A 0 (a + 1))

/-- Rule 1: $A(2k, 0) \to A(3, 2k + 1)$. -/
private theorem step_R1 (k : ℕ) :
    ReachesPlus target (cfg_A (2 * k) 0) (cfg_A 3 (2 * k + 1)) :=
  step_A_b0 (2 * k)

/-- Rule 2: $A(2k, 1) \to A(2k + 1, 0)$. -/
private theorem step_R2 (k : ℕ) :
    ReachesPlus target (cfg_A (2 * k) 1) (cfg_A (2 * k + 1) 0) := by
  have h1 :
      ReachesPlus target (cfg_A (2 * k) 1)
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [1] default))
          default) := by
    unfold cfg_A
    rw [ListBlank.append_pow_comm ([1] : List (Fin 2)) (2 * k) default, list_pow_one]
    bb_steps
  have h2 := shift_E_left k (ListBlank.append [1] default) default
  have h12 := h1.trans_star h2
  rcases k with _ | k'
  · have h3 :
        ReachesPlus target
          (Cfg.headLeft E (ListBlank.append [1] default)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
          (cfg_A 1 0) := by
      unfold cfg_A
      rw [list_pow_zero, list_pow_one, ListBlank.append_nil]
      bb_steps
    exact h12.trans h3
  · have h_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (k' + 1)) (default : ListBlank (Fin 2)) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ k') (ListBlank.append [0, 1] default) := by
      rw [list_pow_succ', ListBlank.append_assoc]
    rw [h_r] at h12
    have h3 :
        ReachesPlus target
          (Cfg.headLeft E (ListBlank.append [1] default)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k')
              (ListBlank.append [0, 1] default)))
          (Cfg.headRight F (ListBlank.append [1, 1] default)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k')
              (ListBlank.append [0, 1] default))) := by
      bb_steps
    have h123 := h12.trans h3
    have h4 :=
      shift_F_right k' (ListBlank.append [1, 1] default) (ListBlank.append [0, 1] default)
    have h1234 := h123.trans_star h4
    have h5 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k')) (ListBlank.append [1, 1] default))
            (ListBlank.append [0, 1] default))
          (cfg_A (2 * (k' + 1) + 1) 0) := by
      unfold cfg_A
      have h_l :
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k' + 1) + 1))
            (default : ListBlank (Fin 2)) =
            ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k'))
                (ListBlank.append [1, 1] default)) := by
        have h2_eq : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
        have h1_eq : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
        rw [h2_eq, ← ListBlank.append_pow_add]
        nth_rw 2 [h1_eq]
        rw [← ListBlank.append_pow_add]
        exact congrArg (fun m => ListBlank.append (([1] : List (Fin 2)) ^ m) default) (by omega)
      rw [h_l, list_pow_zero, ListBlank.append_nil]
      bb_steps
    exact h1234.trans h5

/-- Rule 3: $A(2k, b + 2) \to A(2k + 3, b)$. -/
private theorem step_R3 (k b : ℕ) :
    ReachesPlus target (cfg_A (2 * k) (b + 2)) (cfg_A (2 * k + 3) b) := by
  have h1 :
      ReachesPlus target (cfg_A (2 * k) (b + 2))
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [1] default))
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
    unfold cfg_A
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (b + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := by
      have h_add : b + 2 = 2 + b := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r, ListBlank.append_pow_comm ([1] : List (Fin 2)) (2 * k) default]
    bb_steps
  exact h1.trans (sweep_E_odd_to_A k b)

/-! ## Odd-`a` Inner Cycle and Macro-Transition Rules (Rules 4–10) -/

/-- Intermediate cycle configuration
$C(x, y, z) := 0^\infty\,1^x\,0\,\mathrm{C}{>}\,(01)^{y+1}\,0\,1^z\,0^\infty$. -/
private def cfg_C (x y z : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ x) default))
    (ListBlank.append [0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ y)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))))

/-- Entry from $A(2k + 1, z + 1)$ into $C(0, k, z)$. -/
private theorem enter_C (k z : ℕ) :
    ReachesPlus target (cfg_A (2 * k + 1) (z + 1)) (cfg_C 0 k z) := by
  have h1 :
      ReachesPlus target (cfg_A (2 * k + 1) (z + 1))
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) default)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))) := by
    unfold cfg_A
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (default : ListBlank (Fin 2)) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default) := by
      have h_eq : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h_eq, ListBlank.append_pow_succ]
    rw [h_l, ListBlank.append_pow_succ ([1] : List (Fin 2)) z]
    bb_steps
  have h2 := shift_E_left (k + 1) default
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))))
        (cfg_C 0 k z) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h12.trans h3

/-- Half-cycle from $C(x, y + 1, z)$ to
$0^\infty\,1^{x+4}\,0\,1^{2y+1}\,\mathrm{A}{>}\,1^z\,0^\infty$. -/
private theorem step_C_half (x y z : ℕ) :
    ReachesPlus target (cfg_C x (y + 1) z)
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * y + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default)))
        (ListBlank.append (([1] : List (Fin 2)) ^ z) default)) := by
  have h1 :
      ReachesPlus target (cfg_C x (y + 1) z)
        (Cfg.headRight F
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ y)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default)))) := by
    unfold cfg_C
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ x) default) := by
      have h_add : x + 4 = 4 + x := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) y, h_l]
    bb_steps
  have h2 := shift_F_right y
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default))
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * y))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default)))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * y + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ z) default)) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * y)]
    bb_steps
  exact h12.trans h3

/-- Full cycle $C(x, y + 1, z + 2) \to C(x + 4, y, z)$. -/
private theorem step_C_cycle (x y z : ℕ) :
    ReachesPlus target (cfg_C x (y + 1) (z + 2)) (cfg_C (x + 4) y z) := by
  have h1 := step_C_half x y (z + 2)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * y + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ (z + 2)) default))
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (y + 1)))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default)))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (y + 1)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * y + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default))) := by
      have h_eq : 2 * (y + 1) = (2 * y + 1) + 1 := by omega
      rw [h_eq, ListBlank.append_pow_succ]
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (z + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ z) default) := by
      have h_add : z + 2 = 2 + z := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, h_r]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_E_left (y + 1)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default))
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (x + 4)) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (y + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ z) default))))
        (cfg_C (x + 4) y z) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) y]
    bb_steps
  exact h123.trans h4

/-- Iterated cycle $C(x, y + t, z + 2t) \to^* C(x + 4t, y, z)$. -/
private theorem loop_C (t x y z : ℕ) :
    ReachesStar target (cfg_C x (y + t) (z + 2 * t)) (cfg_C (x + 4 * t) y z) := by
  induction t generalizing x y z with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero]
    exact ReachesStar.refl _ _
  | succ t ih =>
    have h_y : y + (t + 1) = (y + t) + 1 := by omega
    have h_z : z + 2 * (t + 1) = (z + 2 * t) + 2 := by omega
    have h_x : x + 4 * (t + 1) = (x + 4) + 4 * t := by omega
    rw [h_y, h_z, h_x]
    exact (step_C_cycle x (y + t) (z + 2 * t)).to_star.trans (ih (x + 4) y z)

/-- Rule 4: $A(2k + 1, 2m + 1) \to A(4m + 7, 2(k - m - 1))$ for $m + 1 \le k$. -/
private theorem step_R4 (k m : ℕ) (hm : m + 1 ≤ k) :
    ReachesPlus target
      (cfg_A (2 * k + 1) (2 * m + 1))
      (cfg_A (4 * m + 7) (2 * (k - m - 1))) := by
  have h1 := enter_C k (2 * m)
  have h2 := loop_C m 0 (k - m - 1 + 1) 0
  have h_k : k - m - 1 + 1 + m = k := by omega
  simp only [Nat.zero_add, h_k] at h2
  have h12 := h1.trans_star h2
  have h3 := step_C_half (4 * m) (k - m - 1) 0
  have h123 := h12.trans h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k - m - 1) + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m + 4)) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k - m - 1) + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (2 * m + 2))) default)))
          default) := by
    have h_m : 2 * (2 * m + 2) = 4 * m + 4 := by omega
    rw [h_m, ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * (k - m - 1) + 1),
      list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h1234 := h123.trans h4
  have h5 := sweep_C_to_A (2 * m + 2) (2 * (k - m - 1))
  have h_out : 2 * (2 * m + 2) + 3 = 4 * m + 7 := by omega
  rw [h_out] at h5
  exact h1234.trans h5

/-- Rule 5: $A(2k + 1, 2m) \to A(4m + 3, 2(k - m) + 2)$ for $m \le k$. -/
private theorem step_R5 (k m : ℕ) (hm : m ≤ k) :
    ReachesPlus target
      (cfg_A (2 * k + 1) (2 * m))
      (cfg_A (4 * m + 3) (2 * (k - m) + 2)) := by
  rcases m with _ | m'
  · simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
    exact step_A_b0 (2 * k + 1)
  · have h_b : 2 * (m' + 1) = (2 * m' + 1) + 1 := by omega
    rw [h_b]
    have h1 := enter_C k (2 * m' + 1)
    have h2 := loop_C m' 0 (k - (m' + 1) + 1) 1
    have h_k : k - (m' + 1) + 1 + m' = k := by omega
    have h_z : 1 + 2 * m' = 2 * m' + 1 := by omega
    simp only [Nat.zero_add, h_k, h_z] at h2
    have h12 := h1.trans_star h2
    have h3 := step_C_half (4 * m') (k - (m' + 1)) 1
    have h123 := h12.trans h3
    have h4 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k - (m' + 1)) + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m' + 4)) default)))
            (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
          (Cfg.headLeft C
            (ListBlank.append (([1] : List (Fin 2)) ^ ((2 * (k - (m' + 1)) + 2) + 2))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (2 * m' + 2))) default)))
            default) := by
      have h_m : 2 * (2 * m' + 2) = 4 * m' + 4 := by omega
      have h_l :
          ListBlank.append (([1] : List (Fin 2)) ^ ((2 * (k - (m' + 1)) + 2) + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m' + 4))
                (default : ListBlank (Fin 2)))) =
            ListBlank.append [1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k - (m' + 1)) + 1))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (4 * m' + 4)) default))) := by
        have h_add : (2 * (k - (m' + 1)) + 2) + 2 = 3 + (2 * (k - (m' + 1)) + 1) := by omega
        rw [h_add, ListBlank.append_pow_add]
        rfl
      rw [h_m, h_l, list_pow_one]
      bb_steps
    have h1234 := h123.trans h4
    have h5 := sweep_C_to_A (2 * m' + 2) (2 * (k - (m' + 1)) + 2)
    have h_out : 2 * (2 * m' + 2) + 3 = 4 * (m' + 1) + 3 := by omega
    rw [h_out] at h5
    exact h1234.trans h5

/-- Shared post-loop reachability for $b = 2k + 1 + d$:
$A(2k + 1, 2k + 1 + d) \to^+ 0^\infty\,1^{4k+1}\,\mathrm{A}{>}\,1\,0\,0\,1^d\,0^\infty$. -/
private theorem reach_post_loop (k d : ℕ) :
    ReachesPlus target
      (cfg_A (2 * k + 1) (2 * k + 1 + d))
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default)
        (ListBlank.append [1, 0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
  have h_b : 2 * k + 1 + d = (d + 2 * k) + 1 := by omega
  rw [h_b]
  have h1 := enter_C k (d + 2 * k)
  have h2 := loop_C k 0 0 d
  simp only [Nat.zero_add] at h2
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target (cfg_C (4 * k) 0 d)
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default)
          (ListBlank.append [1, 0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_pow_succ ([1] : List (Fin 2)) (4 * k)]
    bb_steps
  exact h12.trans h3

/-- Rule 6: $A(2k + 1, 2k + 1) \to A(4k + 1, 0)$. -/
private theorem step_R6 (k : ℕ) :
    ReachesPlus target (cfg_A (2 * k + 1) (2 * k + 1)) (cfg_A (4 * k + 1) 0) := by
  have h := reach_post_loop k 0
  have h_r :
      ListBlank.append [1, 0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2))) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default) := by
    simp
  rwa [Nat.add_zero, h_r] at h

/-- Rule 7: $A(2k + 1, 2k + 2) \to A(4k + 7, 0)$. -/
private theorem step_R7 (k : ℕ) :
    ReachesPlus target (cfg_A (2 * k + 1) (2 * k + 2)) (cfg_A (4 * k + 7) 0) := by
  have h1 := reach_post_loop k 1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default)
          (ListBlank.append [1, 0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (0 + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (2 * k + 2))) default)))
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (2 * k + 2)))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default) := by
      have h_add : 2 * (2 * k + 2) = 3 + (4 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_two : (([1] : List (Fin 2)) ^ (0 + 2)) = [1, 1] := rfl
    rw [h_l, h_two, list_pow_one]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_C_to_A (2 * k + 2) 0
  have h_out : 2 * (2 * k + 2) + 3 = 4 * k + 7 := by omega
  rw [h_out] at h3
  exact h12.trans h3

/-- Rule 8: $A(2k + 1, 2k + 3)$ reaches a halting configuration in `D` reading `0`. -/
private theorem step_R8 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A (2 * k + 1) (2 * k + 3)) cfg' ∧
      (step target cfg').isNone := by
  have h1 := reach_post_loop k 2
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default)
          (ListBlank.append [1, 0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)))
        (Cfg.headRight D
          (ListBlank.append [1, 0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default))
          default) := by
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two]
    bb_steps
  refine ⟨_, h1.trans h2, ?_⟩
  bb_halt

/-- Rule 9: $A(2k + 1, 2k + 4) \to A(4k + 5, 0)$. -/
private theorem step_R9 (k : ℕ) :
    ReachesPlus target (cfg_A (2 * k + 1) (2 * k + 4)) (cfg_A (4 * k + 5) 0) := by
  have h1 := reach_post_loop k 3
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default)
          (ListBlank.append [1, 0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)))
        (cfg_A (4 * k + 5) 0) := by
    unfold cfg_A
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 5)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default) := by
      have h_add : 4 * k + 5 = 4 + (4 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_three : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h_l, h_three, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1.trans h2

/-- Rule 10: $A(2k + 1, 2k + 5 + c) \to A(4k + 7, c)$. -/
private theorem step_R10 (k c : ℕ) :
    ReachesPlus target (cfg_A (2 * k + 1) (2 * k + 5 + c)) (cfg_A (4 * k + 7) c) := by
  have h_b : 2 * k + 5 + c = 2 * k + 1 + (c + 4) := by omega
  rw [h_b]
  have h1 := reach_post_loop k (c + 4)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default)
          (ListBlank.append [1, 0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 4)) default)))
        (cfg_A (4 * k + 7) c) := by
    unfold cfg_A
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 7)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (4 * k + 1)) default) := by
      have h_add : 4 * k + 7 = 6 + (4 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
      have h_add : c + 4 = 4 + c := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, h_r]
    bb_steps
  exact h1.trans h2

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 1 0) := by
  have h_init : ReachesPlus target (init []) (cfg_A 1 0) := by
    unfold cfg_A
    rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h_init.to_star

/-! ## Collatz-Like Acceleration (Level B) and Pattern Closure (Level A) -/

/-- Symbolic configuration state space for `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`. -/
inductive State where
  /-- $A(a, b) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^{b+1}\,0^\infty$. -/
  | A (a b : ℕ)

/-- Initial symbolic state $A(1, 0)$, reached after 7 raw TM steps. -/
def start : State := .A 1 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))

/-- Accelerated Collatz-like transition function on $A(a, b)$. -/
def next : State → Option State
  | .A a b =>
    let k := a / 2
    if a % 2 = 0 then
      match b with
      | 0 => some (.A 3 (2 * k + 1))
      | 1 => some (.A (2 * k + 1) 0)
      | c + 2 => some (.A (2 * k + 3) c)
    else if b ≤ 2 * k then
      if b % 2 = 0 then
        some (.A (4 * (b / 2) + 3) (2 * (k - b / 2) + 2))
      else
        some (.A (4 * (b / 2) + 7) (2 * (k - b / 2 - 1)))
    else if b = 2 * k + 1 then
      some (.A (4 * k + 1) 0)
    else if b = 2 * k + 2 then
      some (.A (4 * k + 7) 0)
    else if b = 2 * k + 3 then
      none
    else if b = 2 * k + 4 then
      some (.A (4 * k + 5) 0)
    else
      some (.A (4 * k + 7) (b - 2 * k - 5))

private theorem next_step_some :
    ∀ s s', next s = some s' → ReachesPlus target (encode s) (encode s') := by
  rintro ⟨a, b⟩ s' hnext
  dsimp only [next] at hnext
  split_ifs at hnext with ha hb hbe hb1 hb2 hb3 hb4
  · have hk : a = 2 * (a / 2) := by omega
    rcases b with _ | _ | c
    · simp only [Option.some.injEq] at hnext
      subst hnext
      change ReachesPlus target (cfg_A a 0) (cfg_A 3 (2 * (a / 2) + 1))
      nth_rw 1 [hk]
      exact step_R1 (a / 2)
    · simp only [Option.some.injEq] at hnext
      subst hnext
      change ReachesPlus target (cfg_A a 1) (cfg_A (2 * (a / 2) + 1) 0)
      nth_rw 1 [hk]
      exact step_R2 (a / 2)
    · simp only [Option.some.injEq] at hnext
      subst hnext
      change ReachesPlus target (cfg_A a (c + 2)) (cfg_A (2 * (a / 2) + 3) c)
      nth_rw 1 [hk]
      exact step_R3 (a / 2) c
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target (cfg_A a b)
      (cfg_A (4 * (b / 2) + 3) (2 * (a / 2 - b / 2) + 2))
    have hk : a = 2 * (a / 2) + 1 := by omega
    have hbm : b = 2 * (b / 2) := by omega
    have hmk : b / 2 ≤ a / 2 := by omega
    nth_rw 1 [hk]
    nth_rw 1 [hbm]
    exact step_R5 (a / 2) (b / 2) hmk
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target (cfg_A a b)
      (cfg_A (4 * (b / 2) + 7) (2 * (a / 2 - b / 2 - 1)))
    have hk : a = 2 * (a / 2) + 1 := by omega
    have hbm : b = 2 * (b / 2) + 1 := by omega
    have hmk : b / 2 + 1 ≤ a / 2 := by omega
    nth_rw 1 [hk]
    nth_rw 1 [hbm]
    exact step_R4 (a / 2) (b / 2) hmk
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target (cfg_A a b) (cfg_A (4 * (a / 2) + 1) 0)
    have hk : a = 2 * (a / 2) + 1 := by omega
    nth_rw 1 [hk]
    rw [hb1]
    exact step_R6 (a / 2)
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target (cfg_A a b) (cfg_A (4 * (a / 2) + 7) 0)
    have hk : a = 2 * (a / 2) + 1 := by omega
    nth_rw 1 [hk]
    rw [hb2]
    exact step_R7 (a / 2)
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target (cfg_A a b) (cfg_A (4 * (a / 2) + 5) 0)
    have hk : a = 2 * (a / 2) + 1 := by omega
    nth_rw 1 [hk]
    rw [hb4]
    exact step_R9 (a / 2)
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target (cfg_A a b)
      (cfg_A (4 * (a / 2) + 7) (b - 2 * (a / 2) - 5))
    have hk : a = 2 * (a / 2) + 1 := by omega
    have hbc : b = 2 * (a / 2) + 5 + (b - 2 * (a / 2) - 5) := by omega
    nth_rw 1 [hk]
    nth_rw 1 [hbc]
    exact step_R10 (a / 2) (b - 2 * (a / 2) - 5)

private theorem next_step_none_plus :
    ∀ s, next s = none →
      ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  rintro ⟨a, b⟩ hnext
  dsimp only [next] at hnext
  split_ifs at hnext with ha hb hbe hb1 hb2 hb3 hb4
  · rcases b with _ | _ | c <;> cases hnext
  · change ∃ cfg', ReachesPlus target (cfg_A a b) cfg' ∧ (step target cfg').isNone
    have hk : a = 2 * (a / 2) + 1 := by omega
    rw [hk, hb3]
    exact step_R8 (a / 2)

private theorem step_A (a b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h : next (.A a b) with _ | ⟨a', b'⟩
  · obtain ⟨cfg', hp, hh⟩ := next_step_none_plus (.A a b) h
    exact ⟨cfg', hp, Or.inr hh⟩
  · exact ⟨cfg_A a' b', next_step_some (.A a b) (.A a' b') h, Or.inl (in_ps_A a' b')⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 1 0, init_reaches_start, in_ps_A 1 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A (vars 0) (vars 1)

/-- `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := next_step_some
  step_none s h := by
    obtain ⟨cfg', hp, hh⟩ := next_step_none_plus s h
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE
