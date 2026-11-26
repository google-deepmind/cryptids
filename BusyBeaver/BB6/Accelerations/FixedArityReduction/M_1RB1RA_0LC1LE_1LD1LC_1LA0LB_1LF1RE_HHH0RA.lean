/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` (Antihydra)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`
(see <https://wiki.bbchallenge.org/wiki/Antihydra>)
(**Antihydra**).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$P(a, b, c) := 0^\infty\,1^a\,0\,1^b\,\mathrm{F}{>}\,1\,1^c\,0^\infty$$
at $P(0, 3, 1)$ in 11 steps, and every $P(a, b, c)$ advances in `ReachesPlus` either to another
$P(a', b', c')$ or to a halting configuration (when $a = 0$ and $b = 2$).

## Collatz-like Acceleration Rules

```text
Consider:
P(a, b, c) = 0^inf 1^a 0 1^b F> 1 1^c 0^inf

P(a, b+3, c) -> P(a, b+1, c+3)
P(0, 0, c)   -> P(0, c+3, 1)
P(a+1, 0, c) -> P(0, a+c+7, 1)
P(a, 1, c)   -> P(a+2, c+3, 1)
P(0, 2, c)   -> Halt
P(a+1, 2, c) -> P(a, c+4, 1)

Start: P(0, 3, 1), reached after 11 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Rightward shift across `1^k` in state `A`. -/
private theorem shift_A_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [1] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `1^k` in state `E`. -/
private theorem shift_E_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight E (ListBlank.append [1] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `1^k` in state `C`. -/
private theorem shift_C_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight C
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

private theorem sweep_C_0 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h1 := shift_C_1 k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [0] l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
        (Cfg.headRight C l
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_pow :
      ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
    rw [← ListBlank.append_pow_succ]
  rwa [h_pow] at h3

private theorem sweep_C_default (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ k) default)
        (ListBlank.append [1] r))
      (Cfg.headRight C default
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h := sweep_C_0 k default r
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rwa [h_def] at h

private theorem sweep_F_to_C (l : ListBlank (Fin 2)) (c : ℕ) :
    ReachesPlus target
      (Cfg.headRight F l
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))
      (Cfg.headRight C l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight F l
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append (([1] : List (Fin 2)) ^ c) default)) := by
    bb_steps
  have h2 := shift_A_1 c (ListBlank.append [0] l) default
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ c) (ListBlank.append [0] l))
          default)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ c) (ListBlank.append [0] l))
          (ListBlank.append [1] default)) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_C_0 c l default
  exact h123.trans h4

private theorem sweep_E_to_F (l : ListBlank (Fin 2)) (k : ℕ) :
    ReachesPlus target
      (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default))
      (Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))) := by
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] default) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) k 1 default]
    rfl
  rw [h_split]
  have h1 := shift_E_1 k l (ListBlank.append [1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [1] default))
        (Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))) := by
    rw [list_pow_one]
    bb_steps
  exact h1.trans_plus h2

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$P(a, b, c) := 0^\infty\,1^a\,0\,1^b\,\mathrm{F}{>}\,1\,1^c\,0^\infty$. -/
def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 1 (.sym 0 (.rep [1] 0 .default))
    head := some F
    right := .sym 1 (.rep [1] 2 .default) }

/-- Closed pattern set for `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

/-- Configuration $P(a, b, c)$. -/
private def cfg_P (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

private theorem eval_pat_P (vars : ℕ → ℕ) :
    evalTapePattern pat_P vars = cfg_P (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_P (a b c : ℕ) : IsInPatternSet ps (cfg_P a b c) :=
  ⟨(pat_P, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem sweep_C_default_to_P (m : ℕ) :
    ReachesPlus target
      (Cfg.headRight C default
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
      (cfg_P 0 (m + 2) 1) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
        (Cfg.headRight E
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + 2 + 1)) default)) := by
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 2 + 1)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ m) default) := by
      have h_add : m + 2 + 1 = 3 + m := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r, list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := sweep_E_to_F
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)) (m + 2)
  exact h1.trans h2

private theorem step_P_b0_a0 (c : ℕ) :
    ReachesPlus target (cfg_P 0 0 c) (cfg_P 0 (c + 3) 1) := by
  have h1 :
      ReachesPlus target (cfg_P 0 0 c)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))) :=
    sweep_F_to_C _ c
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ 0)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2)))) =
        default := by
    simp
  rw [h_l] at h1
  have h2 := sweep_C_default_to_P (c + 1)
  exact h1.trans h2

private theorem step_P_b0_asucc (a c : ℕ) :
    ReachesPlus target (cfg_P (a + 1) 0 c) (cfg_P 0 (a + c + 7) 1) := by
  have h1 :
      ReachesPlus target (cfg_P (a + 1) 0 c)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))) :=
    sweep_F_to_C _ c
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ 0)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (default : ListBlank (Fin 2)))) =
        ListBlank.append [0]
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) := by
    rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_pow_succ]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 4)) default)) := by
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default) := by
      have h_add : c + 4 = 3 + (c + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_A_1 (c + 4) (ListBlank.append (([1] : List (Fin 2)) ^ a) default) default
  have h123 := h12.trans_star h3
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 4))
        (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (a + c + 4)) default := by
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) default) (by omega)
  rw [h_comb] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ (a + c + 4)) default) default)
        (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ (a + c + 4)) default)
          (ListBlank.append [1] default)) := by
    bb_steps
  have h1234 := h123.trans h4
  have h5 := sweep_C_default (a + c + 4) default
  have h12345 := h1234.trans h5
  have h6 := sweep_C_default_to_P (a + c + 4 + 1)
  exact h12345.trans h6

private theorem sweep_B_0 (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
        (ListBlank.append [0] r))
      (Cfg.headRight C default
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) (ListBlank.append [0] r)))) := by
  rcases a with _ | a'
  · rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  · rw [ListBlank.append_pow_succ]
    have h1 :
        ReachesPlus target
          (Cfg.headRight B
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a') default))
            (ListBlank.append [0] r))
          (Cfg.headRight C
            (ListBlank.append (([1] : List (Fin 2)) ^ a') default)
            (ListBlank.append [1] (ListBlank.append [0] r))) := by
      bb_steps
    have h2 := sweep_C_default a' (ListBlank.append [0] r)
    exact h1.trans h2

private theorem step_P_b1 (a c : ℕ) :
    ReachesPlus target (cfg_P a 1 c) (cfg_P (a + 2) (c + 3) 1) := by
  have h1 := sweep_F_to_C
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) c
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [0]
            (ListBlank.append [0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))) := by
    rw [list_pow_one]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_B_0 a
    (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  have h123 := h12.trans h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ a)
              (ListBlank.append [0]
                (ListBlank.append [0, 1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))))))
        (Cfg.headRight E (ListBlank.append [1, 1, 1] default)
          (ListBlank.append (([1] : List (Fin 2)) ^ a)
            (ListBlank.append [0]
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))))) := by
    bb_steps
  have h1234 := h123.trans h4
  have h5 := shift_E_1 a (ListBlank.append [1, 1, 1] default)
    (ListBlank.append [0]
      (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))
  have h12345 := h1234.trans_star h5
  have h_l2 :
      ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [1, 1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default) := by
    have h_3 : ([1, 1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 3 := rfl
    have h_1 : ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 1 := rfl
    rw [h_3, ← ListBlank.append_pow_add]
    nth_rw 2 [h_1]
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) default) (by omega)
  rw [h_l2] at h12345
  have h6 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default))
          (ListBlank.append [0]
            (ListBlank.append [0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))))
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)) := by
    bb_steps
  have h123456 := h12345.trans h6
  have h7 := sweep_E_to_F
    (ListBlank.append [1, 1, 1]
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default))) c
  have h_l3 :
      ListBlank.append (([1] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1, 1]
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2))
              (default : ListBlank (Fin 2))))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)) := by
    have h_3 : ([1, 1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 3 := rfl
    rw [h_3, ← ListBlank.append_pow_add]
  rw [h_l3, list_pow_one] at h7
  exact h123456.trans h7

private theorem step_P_b2_a0 (c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_P 0 2 c) cfg' ∧ (step target cfg').isNone := by
  have h1 := sweep_F_to_C
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))) c
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight F default
          (ListBlank.append [0]
            (ListBlank.append [1, 1, 0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))) := by
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two, list_pow_zero, ListBlank.append_nil]
    bb_steps
  refine ⟨_, h1.trans h2, ?_⟩
  bb_halt

private theorem step_P_b2_asucc (a c : ℕ) :
    ReachesPlus target (cfg_P (a + 1) 2 c) (cfg_P a (c + 4) 1) := by
  have h1 := sweep_F_to_C
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))) c
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)) := by
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_E_to_F
    (ListBlank.append [1, 1, 1, 1]
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) c
  have h_l2 :
      ListBlank.append (([1] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1, 1, 1]
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ a)
              (default : ListBlank (Fin 2))))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) := by
    have h_4 : ([1, 1, 1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 4 := rfl
    rw [h_4, ← ListBlank.append_pow_add]
  rw [h_l2, list_pow_one] at h3
  exact h12.trans h3

private theorem step_P_b_ge3 (a b c : ℕ) :
    ReachesPlus target (cfg_P a (b + 3) c) (cfg_P a (b + 1) (c + 3)) := by
  have h1 := sweep_F_to_C
    (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) c
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) := by
    have h_add : b + 3 = 3 + b := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b)
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)))
        (cfg_P a (b + 1) (c + 3)) := by
    unfold cfg_P
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default) := by
      have h_add : c + 3 = 2 + (c + 1) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b, h_r]
    bb_steps
  exact h1.trans h2

private theorem step_P (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_P a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | _ | b'
  · rcases a with _ | a'
    · exact ⟨cfg_P 0 (c + 3) 1, step_P_b0_a0 c, Or.inl (in_ps_P 0 (c + 3) 1)⟩
    · exact ⟨cfg_P 0 (a' + c + 7) 1, step_P_b0_asucc a' c, Or.inl (in_ps_P 0 (a' + c + 7) 1)⟩
  · exact ⟨cfg_P (a + 2) (c + 3) 1, step_P_b1 a c, Or.inl (in_ps_P (a + 2) (c + 3) 1)⟩
  · rcases a with _ | a'
    · obtain ⟨cfg', h1, h2⟩ := step_P_b2_a0 c
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_P a' (c + 4) 1, step_P_b2_asucc a' c, Or.inl (in_ps_P a' (c + 4) 1)⟩
  · exact ⟨cfg_P a (b' + 1) (c + 3), step_P_b_ge3 a b' c,
      Or.inl (in_ps_P a (b' + 1) (c + 3))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_P 0 3 1) := by
  have h_init : ReachesPlus target (init []) (cfg_P 0 3 1) := by
    unfold cfg_P
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [list_pow_zero, list_pow_one, h3]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P 0 3 1, init_reaches_start, in_ps_P 0 3 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_P]
  exact step_P (vars 0) (vars 1) (vars 2)

/-- `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`. -/
inductive State where
  /-- $P(a, b, c) := 0^\infty\,1^a\,0\,1^b\,\mathrm{F}{>}\,1\,1^c\,0^\infty$. -/
  | P (a b c : ℕ)

/-- Initial symbolic state $P(0, 3, 1)$, reached after 11 raw TM steps. -/
def start : State := .P 0 3 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P a b c =>
    Cfg.headRight SixState.F
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .P 0 0 c => some (.P 0 (c + 3) 1)
  | .P (a + 1) 0 c => some (.P 0 (a + c + 7) 1)
  | .P a 1 c => some (.P (a + 2) (c + 3) 1)
  | .P 0 2 _ => none
  | .P (a + 1) 2 c => some (.P a (c + 4) 1)
  | .P a (b + 3) c => some (.P a (b + 1) (c + 3))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases b with _ | _ | _ | b'
    · rcases a with _ | a'
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_P_b0_a0 c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_P_b0_asucc a' c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_P_b1 a c
    · rcases a with _ | a'
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_P_b2_asucc a' c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_P_b_ge3 a b' c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases b with _ | _ | _ | b'
    · rcases a with _ | a' <;> simp [next] at hnext
    · simp [next] at hnext
    · rcases a with _ | a'
      · obtain ⟨cfg', hp, hh⟩ := step_P_b2_a0 c
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA
