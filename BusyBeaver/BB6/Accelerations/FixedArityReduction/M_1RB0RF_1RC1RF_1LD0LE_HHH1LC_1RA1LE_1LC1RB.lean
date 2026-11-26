/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`
(<https://wiki.bbchallenge.org/wiki/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB>,
Parity-Collatz holdout (#668, `suspect_34`)).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$P(a, b, c) := 0^\infty\,1^a\,\mathrm{E}{>}\,0\,1^b\,0\,1^c\,0^\infty$$
at $P(0, 0, 2)$ in 5 steps, and every $P(a, b, c)$ advances in `ReachesPlus` either to another
$P(a', b', c')$ or to a halting configuration (when $a = 0$ and $b = 1$).

## Collatz-like Acceleration Rules

```text
Consider:
P(a, b, c) = 0^inf 1^a E> 0 1^b 0 1^c 0^inf

P(a, 0, 2k)       -> P(0, a+2k+1, 2)
P(a, 0, 2k+1)     -> P(0, a+2k+2, 1)
P(0, 1, c)        -> Halt
P(a+1, 1, c)      -> P(0, a, c+3)
P(a, 2k+2, 0)     -> P(a+1, 2k, 2)
P(a, 2k+2, c+1)   -> P(a+1, 2k+2, c)
P(a, 2k+3, c)     -> P(a+1, 2k+1, c+1)

Start: P(0, 0, 2), reached after 5 raw TM steps
```

Iterating the even-$b$ countdown transitions yields the 6-rule system:

```text
P(a, 0, 2k)     -> P(0, a+2k+1, 2)
P(a, 0, 2k+1)   -> P(0, a+2k+2, 1)
P(0, 1, c)      -> Halt
P(a+1, 1, c)    -> P(0, a, c+3)
P(a, 2k+2, c)   -> P(0, a+c+3k+4, 2)
P(a, 2k+3, c)   -> P(a+1, 2k+1, c+1)
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Leftward shift across `1^k` in state `E`. -/
private theorem shift_E_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight E l
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight E
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Rightward shift across `(11)^k` in state `F`. -/
private theorem shift_F_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight F (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight F (ListBlank.append [1, 1] l)
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

/-- Rightward shift across `(11)^k` in state `B`. -/
private theorem shift_B_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [1, 1] l)
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

private theorem shift_F_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  rw [← one_pow_two_mul]
  exact shift_F_11 k l r

private theorem shift_B_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight B (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  rw [← one_pow_two_mul]
  exact shift_B_11 k l r

private theorem sweep_left_E (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight E l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h1 := shift_E_1 k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [0] l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
        (Cfg.headRight E l
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_pow :
      ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
    rw [← ListBlank.append_pow_succ]
  rwa [h_pow] at h3

private theorem sweep_left_E_default (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) default)
        (ListBlank.append [1] r))
      (Cfg.headRight E default
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h := sweep_left_E k default r
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rwa [h_def] at h

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$P(a, b, c) := 0^\infty\,1^a\,\mathrm{E}{>}\,0\,1^b\,0\,1^c\,0^\infty$. -/
def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some E
    right := .sym 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 .default))) }

/-- Closed pattern set for `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

/-- Configuration $P(a, b, c)$. -/
private def cfg_P (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))

private theorem eval_pat_P (vars : ℕ → ℕ) :
    evalTapePattern pat_P vars = cfg_P (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_P (a b c : ℕ) : IsInPatternSet ps (cfg_P a b c) :=
  ⟨(pat_P, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem combine_ones_2 (a m : ℕ) :
    ListBlank.append (([1] : List (Fin 2)) ^ m)
      (ListBlank.append [1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2)))) =
      ListBlank.append [1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + m)) default) := by
  have h1 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
  rw [h1, ← ListBlank.append_pow_add, ← ListBlank.append_pow_add,
    ← ListBlank.append_pow_add]
  exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) default) (by omega)

private theorem step_P_b0_even (a k : ℕ) :
    ReachesPlus target (cfg_P a 0 (2 * k)) (cfg_P 0 (a + 2 * k + 1) 2) := by
  have h1 :
      ReachesPlus target (cfg_P a 0 (2 * k))
        (Cfg.headRight B
          (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) default)) := by
    unfold cfg_P
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_B_even k
    (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) default
  have h12 := h1.trans_star h2
  rw [combine_ones_2 a (2 * k)] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 * k)) default))
          default)
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 * k)) default)
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)))) := by
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_left_E_default (a + 2 * k)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
  exact h123.trans h4

private theorem step_P_b0_odd (a k : ℕ) :
    ReachesPlus target (cfg_P a 0 (2 * k + 1)) (cfg_P 0 (a + 2 * k + 2) 1) := by
  have h1 :
      ReachesPlus target (cfg_P a 0 (2 * k + 1))
        (Cfg.headRight B
          (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [1] default))) := by
    unfold cfg_P
    have h_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) (default : ListBlank (Fin 2)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [1] default) := by
      rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1 default]
      rfl
    rw [h_split, list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_B_even k
    (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  rw [combine_ones_2 a (2 * k)] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 * k)) default))
          (ListBlank.append [1] default))
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 * k + 1)) default)
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))) := by
    have h_l :
        ListBlank.append [1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 * k))
            (default : ListBlank (Fin 2))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 * k + 1)) default) := by
      rw [← ListBlank.append_pow_succ]
      rfl
    rw [h_l, list_pow_one]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_left_E_default (a + 2 * k + 1)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
  exact h123.trans h4

private theorem step_P_b1_a0 (c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_P 0 1 c) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_P 0 1 c)
        (Cfg.headRight D default
          (ListBlank.append [0]
            (ListBlank.append [1, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))) := by
    unfold cfg_P
    rw [list_pow_zero, list_pow_one, ListBlank.append_nil]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

private theorem step_P_b1_succ (a c : ℕ) :
    ReachesPlus target (cfg_P (a + 1) 1 c) (cfg_P 0 a (c + 3)) := by
  have h_c3 :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
    have h_add : c + 3 = 3 + c := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rcases a with _ | a'
  · unfold cfg_P
    rw [h_c3, list_pow_zero, list_pow_one, ListBlank.append_nil]
    bb_steps
  · have h1 :
        ReachesPlus target (cfg_P (a' + 1 + 1) 1 c)
          (Cfg.headRight E
            (ListBlank.append (([1] : List (Fin 2)) ^ a') default)
            (ListBlank.append [1]
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) default)))) := by
      unfold cfg_P
      have h_l :
          ListBlank.append (([1] : List (Fin 2)) ^ (a' + 1 + 1))
            (default : ListBlank (Fin 2)) =
            ListBlank.append [1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ a') default) := by
        have h_add : a' + 1 + 1 = 2 + a' := by omega
        rw [h_add, ListBlank.append_pow_add]
        rfl
      rw [h_l, h_c3, list_pow_one]
      bb_steps
    have h2 := sweep_left_E_default a'
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) default))
    exact h1.trans h2

private theorem step_P_b_odd (a k c : ℕ) :
    ReachesPlus target (cfg_P a (2 * k + 3) c) (cfg_P (a + 1) (2 * k + 1) (c + 1)) := by
  have h1 :
      ReachesPlus target (cfg_P a (2 * k + 3) c)
        (Cfg.headRight F
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [1, 1]
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))) := by
    unfold cfg_P
    have h_b :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
              (ListBlank.append [1, 1]
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))) := by
      have h_add : 2 * k + 3 = 1 + (2 * k + 2) := by omega
      rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * k + 2),
        ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 2]
      rfl
    rw [h_b, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h2 := shift_F_even k
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
    (ListBlank.append [1, 1]
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1, 1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_left_E (2 * k)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  exact h123.trans h4

private theorem step_P_b_even_succ (a k c : ℕ) :
    ReachesPlus target (cfg_P a (2 * k + 2) (c + 1)) (cfg_P (a + 1) (2 * k + 2) c) := by
  have h1 :
      ReachesPlus target (cfg_P a (2 * k + 2) (c + 1))
        (Cfg.headRight F
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [1]
              (ListBlank.append [0]
                (ListBlank.append [1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))) := by
    unfold cfg_P
    have h_b :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
              (default : ListBlank (Fin 2)))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
              (ListBlank.append [1]
                (ListBlank.append [0]
                  (ListBlank.append [1]
                    (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))) := by
      have h_add : 2 * k + 2 = 1 + (2 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * k + 1),
        ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1,
        ListBlank.append_pow_succ ([1] : List (Fin 2)) c]
      rfl
    rw [h_b, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h2 := shift_F_even k
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
    (ListBlank.append [1]
      (ListBlank.append [0]
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append [1]
                (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * k)]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_left_E (2 * k + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))
  exact h123.trans h4

private theorem step_P_b_even_zero (a k : ℕ) :
    ReachesPlus target (cfg_P a (2 * k + 2) 0) (cfg_P (a + 1) (2 * k) 2) := by
  have h1 :
      ReachesPlus target (cfg_P a (2 * k + 2) 0)
        (Cfg.headRight F
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
            (ListBlank.append [1] (ListBlank.append [0] default)))) := by
    unfold cfg_P
    have h_b :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
              (ListBlank.append [1] (ListBlank.append [0] default))) := by
      have h_add : 2 * k + 2 = 1 + (2 * k + 1) := by omega
      rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * k + 1),
        ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1]
      rfl
    rw [h_b, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h2 := shift_F_even k
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
    (ListBlank.append [1] (ListBlank.append [0] default))
  have h12 := h1.trans_star h2
  rcases k with _ | k'
  · have h3 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append (([1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
            (ListBlank.append [1] (ListBlank.append [0] default)))
          (cfg_P (a + 1) 0 2) := by
      unfold cfg_P
      have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
      rw [list_pow_zero, ListBlank.append_nil, h_two]
      bb_steps
    exact h12.trans h3
  · have h3 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k' + 1)))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
            (ListBlank.append [1] (ListBlank.append [0] default)))
          (Cfg.headRight E
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k' + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
            (ListBlank.append [1]
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)))) := by
      have h_l :
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k' + 1)))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
                (default : ListBlank (Fin 2)))) =
            ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k' + 1))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))) := by
        have h_add : 2 * (k' + 1) = (2 * k' + 1) + 1 := by omega
        rw [h_add, ListBlank.append_pow_succ]
      have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
      rw [h_l, h_two]
      bb_steps
    have h123 := h12.trans h3
    have h4 := sweep_left_E (2 * k' + 1)
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
    exact h123.trans h4

/-- Iterates `step_P_b_even_succ` `c` times, draining `c` into `a`:
`P(a, 2k + 2, c) ⊢* P(a + c, 2k + 2, 0)`. -/
private theorem drain_c (c a k : ℕ) :
    ReachesStar target (cfg_P a (2 * k + 2) c) (cfg_P (a + c) (2 * k + 2) 0) := by
  induction c generalizing a with
  | zero => exact ReachesStar.refl _ _
  | succ c ih =>
    have h1 := step_P_b_even_succ a k c
    have h2 := ih (a + 1)
    have h_eq : a + 1 + c = a + (c + 1) := by omega
    rw [h_eq] at h2
    exact (h1.trans_star h2).to_star

/-- Decrements even `b = 2k + 4` by `2` while adding `3` to `a`:
`P(a, 2k + 4, 0) ⊢⁺ P(a + 3, 2k + 2, 0)`. -/
private theorem step_b_even2 (a k : ℕ) :
    ReachesPlus target (cfg_P a (2 * k + 4) 0) (cfg_P (a + 3) (2 * k + 2) 0) := by
  have hb : 2 * k + 4 = 2 * (k + 1) + 2 := by omega
  rw [hb]
  have h1 := step_P_b_even_zero a (k + 1)
  have h2 := drain_c 2 (a + 1) k
  have ha : a + 1 + 2 = a + 3 := by omega
  rw [ha] at h2
  exact h1.trans_star h2

/-- Drains `b = 2k + 2` down to `0` while accumulating `3k + 1` into `a`:
`P(a, 2k + 2, 0) ⊢⁺ P(a + 3k + 1, 0, 2)`. -/
private theorem drain_b_even (k a : ℕ) :
    ReachesPlus target (cfg_P a (2 * k + 2) 0) (cfg_P (a + 3 * k + 1) 0 2) := by
  induction k generalizing a with
  | zero =>
    have ha : a + 3 * 0 + 1 = a + 1 := by omega
    rw [ha]
    exact step_P_b_even_zero a 0
  | succ k ih =>
    have hb : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    rw [hb]
    have h1 := step_b_even2 a k
    have h2 := ih (a + 3)
    have ha : a + 3 + 3 * k + 1 = a + 3 * (k + 1) + 1 := by omega
    rw [ha] at h2
    exact h1.trans h2

/-- Eliminates both `a` and `c` for even `b = 2k + 2` in a single macro-transition:
`P(a, 2k + 2, c) ⊢⁺ P(0, a + c + 3k + 4, 2)`. -/
private theorem accel_P_even (a k c : ℕ) :
    ReachesPlus target (cfg_P a (2 * k + 2) c) (cfg_P 0 (a + c + 3 * k + 4) 2) := by
  have h1 := drain_c c a k
  have h2 := drain_b_even k (a + c)
  have h3 := step_P_b0_even (a + c + 3 * k + 1) 1
  have hb : a + c + 3 * k + 1 + 2 * 1 + 1 = a + c + 3 * k + 4 := by omega
  rw [hb] at h3
  exact h1.trans_plus (h2.trans h3)

private theorem step_P (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_P a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | b'
  · rcases nat_even_or_odd_two_mul c with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨cfg_P 0 (a + 2 * k + 1) 2, step_P_b0_even a k,
        Or.inl (in_ps_P 0 (a + 2 * k + 1) 2)⟩
    · exact ⟨cfg_P 0 (a + 2 * k + 2) 1, step_P_b0_odd a k,
        Or.inl (in_ps_P 0 (a + 2 * k + 2) 1)⟩
  · rcases a with _ | a'
    · obtain ⟨cfg', h1, h2⟩ := step_P_b1_a0 c
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_P 0 a' (c + 3), step_P_b1_succ a' c, Or.inl (in_ps_P 0 a' (c + 3))⟩
  · rcases nat_even_or_odd_two_mul b' with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨cfg_P 0 (a + c + 3 * k + 4) 2, accel_P_even a k c,
        Or.inl (in_ps_P 0 (a + c + 3 * k + 4) 2)⟩
    · exact ⟨cfg_P (a + 1) (2 * k + 1) (c + 1), step_P_b_odd a k c,
        Or.inl (in_ps_P (a + 1) (2 * k + 1) (c + 1))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_P 0 0 2) := by
  have h_init : ReachesPlus target (init []) (cfg_P 0 0 2) := by
    unfold cfg_P
    have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [list_pow_zero, ListBlank.append_nil, h2]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P 0 0 2, init_reaches_start, in_ps_P 0 0 2⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_P]
  exact step_P (vars 0) (vars 1) (vars 2)

/-- `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`. -/
inductive State where
  /-- $P(a, b, c) := 0^\infty\,1^a\,\mathrm{E}{>}\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | P (a b c : ℕ)

/-- Initial symbolic state $P(0, 0, 2)$, reached after 5 raw TM steps. -/
def start : State := .P 0 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ b)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .P a 0 c =>
    if c % 2 = 0 then some (.P 0 (a + c + 1) 2)
    else some (.P 0 (a + c + 1) 1)
  | .P 0 1 _ => none
  | .P (a + 1) 1 c => some (.P 0 a (c + 3))
  | .P a (b + 2) c =>
    if b % 2 = 0 then some (.P 0 (a + c + 3 * (b / 2) + 4) 2)
    else some (.P (a + 1) b (c + 1))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases b with _ | _ | b'
    · rcases nat_even_or_odd_two_mul c with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod : (2 * k) % 2 = 0 := by omega
        simp only [next, hmod, ↓reduceIte, Option.some.injEq] at hnext
        subst hnext
        exact step_P_b0_even a k
      · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
        have heq : a + (2 * k + 1) + 1 = a + 2 * k + 2 := by omega
        simp only [next, hmod, ↓reduceIte, Option.some.injEq] at hnext
        subst hnext
        rw [encode, heq]
        exact step_P_b0_odd a k
    · rcases a with _ | a'
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_P_b1_succ a' c
    · rcases nat_even_or_odd_two_mul b' with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod : (2 * k) % 2 = 0 := by omega
        have hdiv : (2 * k) / 2 = k := by omega
        simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
        subst hnext
        exact accel_P_even a k c
      · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
        simp only [next, hmod, ↓reduceIte, Option.some.injEq] at hnext
        subst hnext
        exact step_P_b_odd a k c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases b with _ | _ | b'
    · simp only [next] at hnext
      split_ifs at hnext
    · rcases a with _ | a'
      · obtain ⟨cfg', hp, hh⟩ := step_P_b1_a0 c
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · simp only [next] at hnext
      split_ifs at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB
