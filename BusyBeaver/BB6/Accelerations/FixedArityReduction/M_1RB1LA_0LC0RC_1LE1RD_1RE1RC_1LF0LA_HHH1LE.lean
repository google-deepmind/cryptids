/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`
(see <https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE>)
(`cryptid_19`, holdout #163, `suspect_83`, **The Sheep Machine**).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$P(m, k) := 0^\infty\,1^m\,\mathrm{E}{>}\,1\,1^k\,0^\infty$$
at $P(0, 2)$ in 6 steps, and every $P(m, k)$ advances in `ReachesPlus` either to another
$P(m', k')$ or to a halting configuration (when $m = 1$).

## Collatz-like Acceleration Rules

```text
Consider:
P(m, k) = 0^inf 1^m E> 1 1^k 0^inf

P(0, 0)    -> P(0, 2)
P(0, k+1)  -> P(2, k)
P(1, k)    -> Halt
P(2m+2, k) -> P(3m+k+3, 1)
P(2m+3, k) -> P(m, m+k+4)

Start: P(0, 2), reached after 6 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Leftward shift across `1^k` in state `A`. -/
private theorem shift_A_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight A
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

private theorem sweep_A_0 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h1 := shift_A_1 k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
        (Cfg.headRight A l
          (ListBlank.append [0]
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_pow :
      ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
    rw [← ListBlank.append_pow_succ]
  rwa [h_pow] at h3

/-- Rightward shift across `1^(2k)` in state `C` (alternating `C` and `D`). -/
private theorem shift_CD_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r) := by
      have h_add : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r))
          (Cfg.headRight C (ListBlank.append [1, 1] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
      rw [h_split]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l := by
      have h_two : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      rw [h_two, ← ListBlank.append_pow_add]
      exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) l) (by omega)
    rwa [h_pow] at h3

private theorem sweep_CD_odd (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C l
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) (ListBlank.append [0] r)))
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l) r) := by
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) (ListBlank.append [0] r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.append [0] r)) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1]
    rfl
  rw [h_split]
  have h1 := shift_CD_even k l (ListBlank.append [1] (ListBlank.append [0] r))
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
          (ListBlank.append [1] (ListBlank.append [0] r)))
        (Cfg.headRight E
          (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l))
          r) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_pow :
      ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l := by
    have h_two : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
    rw [h_two, ← ListBlank.append_pow_add]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) l) (by omega)
  rwa [h_pow] at h3

private theorem sweep_CD_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C l
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) (ListBlank.append [0] r)))
      (Cfg.headRight E
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) l)
        (ListBlank.append [1, 1] r)) := by
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) (ListBlank.append [0] r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1, 1] (ListBlank.append [0] r)) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 2]
    rfl
  rw [h_split]
  have h1 := shift_CD_even k l (ListBlank.append [1, 1] (ListBlank.append [0] r))
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
          (ListBlank.append [1, 1] (ListBlank.append [0] r)))
        (Cfg.headRight E
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l))
          (ListBlank.append [1, 1] r)) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_pow :
      ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) l := by
    rw [← ListBlank.append_pow_succ]
  rwa [h_pow] at h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$P(m, k) := 0^\infty\,1^m\,\mathrm{E}{>}\,1\,1^k\,0^\infty$. -/
def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

/-- Closed pattern set for `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true)]

/-- Configuration $P(m, k) := 0^\infty\,1^m\,\mathrm{E}{>}\,1\,1^k\,0^\infty$. -/
private def cfg_P (m k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))

private theorem eval_pat_P (vars : ℕ → ℕ) :
    evalTapePattern pat_P vars = cfg_P (vars 0) (vars 1) :=
  rfl

private theorem in_ps_P (m k : ℕ) : IsInPatternSet ps (cfg_P m k) :=
  ⟨(pat_P, .true), List.Mem.head _,
    fun i => match i with | 0 => m | 1 => k | _ => 0, rfl, trivial⟩

/-! ## Intermediate Configurations and Subcycles -/

private def cfg_interm_on (m i k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))

private def cfg_interm_off (m i : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
    default

private theorem subcycle_step (m i : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
        (ListBlank.append [1] r))
      (Cfg.headRight E
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (i + 1)) default)))
        r) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
          (ListBlank.append [1] r))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
          (ListBlank.append [1] (ListBlank.append [0] r))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * m + 1)]
    bb_steps
  have h2 := sweep_A_0 (2 * m + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ i) default)
    (ListBlank.append [0] r)
  have h12 := h1.trans h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ i) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
              (ListBlank.append [0] r))))
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (i + 1)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
            (ListBlank.append [0] r))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * m + 1),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) i]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_CD_odd m
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (i + 1)) default)) r
  exact h123.trans h4

private theorem subcycle (m i k : ℕ) :
    ReachesPlus target (cfg_interm_on m i (k + 1)) (cfg_interm_on m (i + 1) k) := by
  unfold cfg_interm_on
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) k]
  exact subcycle_step m i
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))

private theorem subcycle_iter (m i k : ℕ) :
    ReachesStar target (cfg_interm_on m i k) (cfg_interm_on m (i + k) 0) := by
  induction k generalizing i with
  | zero => rw [Nat.add_zero]
  | succ k ih =>
    have h1 := (subcycle m i k).to_star
    have h2 := ih (i + 1)
    have h_add : i + 1 + k = i + (k + 1) := by omega
    rw [h_add] at h2
    exact h1.trans h2

private theorem subcycle_close (m i : ℕ) :
    ReachesPlus target (cfg_interm_on m i 0) (cfg_interm_off m (i + 1)) := by
  unfold cfg_interm_on cfg_interm_off
  rw [list_pow_zero, ListBlank.append_nil]
  exact subcycle_step m i default

private theorem peel_interm (m i : ℕ) :
    ReachesPlus target (cfg_interm_off (m + 1) i) (cfg_interm_on m i 2) := by
  unfold cfg_interm_off cfg_interm_on
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (m + 1) + 2))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ i) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ i) default))) := by
    have h_add : 2 * (m + 1) + 2 = 2 + (2 * m + 2) := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h_split, h_two]
  bb_steps

private theorem finalize_m0 (i : ℕ) :
    ReachesPlus target (cfg_interm_on 0 i 0) (cfg_P (i + 3) 1) := by
  have h1 := subcycle_close 0 i
  have h2 : ReachesPlus target (cfg_interm_off 0 (i + 1)) (cfg_P (i + 3) 1) := by
    unfold cfg_interm_off cfg_P
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (i + 3)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ i) default) := by
      have h_add : i + 3 = 3 + i := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_two : (([1] : List (Fin 2)) ^ (2 * 0 + 2)) = [1, 1] := rfl
    rw [h_two, ListBlank.append_pow_succ ([1] : List (Fin 2)) i, h_l, list_pow_one]
    bb_steps
  exact h1.trans h2

private theorem drain_even (m i : ℕ) :
    ReachesPlus target (cfg_interm_on m i 0) (cfg_P (3 * m + i + 3) 1) := by
  induction m generalizing i with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add]
    exact finalize_m0 i
  | succ m ih =>
    have h1 := subcycle_close (m + 1) i
    have h2 := peel_interm m (i + 1)
    have h3 := subcycle_iter m (i + 1) 2
    have h4 := ih (i + 1 + 2)
    have h1234 := ((h1.trans h2).trans_star h3).trans h4
    have h_idx : 3 * m + (i + 1 + 2) + 3 = 3 * (m + 1) + i + 3 := by omega
    rwa [h_idx] at h1234

private def cfg_interm_odd (s i k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * s + 1))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))

private theorem descent_step (s i k : ℕ) :
    ReachesPlus target (cfg_interm_odd (s + 1) i k) (cfg_interm_odd s (i + 1) (k + 1)) := by
  unfold cfg_interm_odd
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (s + 1) + 1))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ i) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * s + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ i) default))) := by
    have h_add : 2 * (s + 1) + 1 = (2 * s + 2) + 1 := by omega
    rw [h_add, ListBlank.append_pow_succ]
  rw [h_split]
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * s + 2))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ i) default))))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * s + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ i) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))) := by
    bb_steps
  have h2 := sweep_A_0 (2 * s + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ i) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))
  have h12 := h1.trans h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ i) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * s + 2 + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))))
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (i + 1)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * s + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * s + 2),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) i]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_CD_even s
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (i + 1)) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ k) default)
  have h1234 := h123.trans h4
  have h_r :
      ListBlank.append [1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (default : ListBlank (Fin 2))) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) k]
    rfl
  rwa [h_r] at h1234

private theorem descent_iter (m i k : ℕ) :
    ReachesPlus target (cfg_interm_odd (m + 1) i k)
      (cfg_interm_odd 0 (i + m + 1) (k + m + 1)) := by
  induction m generalizing i k with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    exact descent_step 0 i k
  | succ m ih =>
    have h1 := descent_step (m + 1) i k
    have h2 := ih (i + 1) (k + 1)
    have h12 := h1.trans h2
    have h_i : i + 1 + m + 1 = i + (m + 1) + 1 := by omega
    have h_k : k + 1 + m + 1 = k + (m + 1) + 1 := by omega
    rwa [h_i, h_k] at h12

private theorem base_odd (i k : ℕ) :
    ReachesPlus target (cfg_interm_odd 0 (i + 1) k) (cfg_P i (k + 3)) := by
  unfold cfg_interm_odd cfg_P
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default) := by
    have h_add : k + 3 = 3 + k := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [list_pow_one, ListBlank.append_pow_succ ([1] : List (Fin 2)) i, h_r]
  bb_steps

/-! ## Accelerated Transition Rules -/

private theorem step_P_m0_k0 :
    ReachesPlus target (cfg_P 0 0) (cfg_P 0 2) := by
  unfold cfg_P
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [list_pow_zero, h_two]
  bb_steps

private theorem step_P_m0_ksucc (k : ℕ) :
    ReachesPlus target (cfg_P 0 (k + 1)) (cfg_P 2 k) := by
  unfold cfg_P
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [list_pow_zero, h_two, ListBlank.append_pow_succ ([1] : List (Fin 2)) k]
  bb_steps

private theorem step_P_m1 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_P 1 k) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_P 1 k)
        (Cfg.headRight F default
          (ListBlank.append [0, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ k) default))) := by
    unfold cfg_P
    rw [list_pow_one]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

private theorem step_P_even (m k : ℕ) :
    ReachesPlus target (cfg_P (2 * m + 2) k) (cfg_P (3 * m + k + 3) 1) := by
  have h_eq : cfg_P (2 * m + 2) k = cfg_interm_on m 0 k := by
    unfold cfg_P cfg_interm_on
    simp
  rw [h_eq]
  have h1 := subcycle_iter m 0 k
  rw [Nat.zero_add] at h1
  have h2 := drain_even m k
  exact h1.trans_plus h2

private theorem step_P_odd (m k : ℕ) :
    ReachesPlus target (cfg_P (2 * m + 3) k) (cfg_P m (m + k + 4)) := by
  have h_eq : cfg_P (2 * m + 3) k = cfg_interm_odd (m + 1) 0 k := by
    unfold cfg_P cfg_interm_odd
    have h_add : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    rw [h_add]
    simp
  rw [h_eq]
  have h1 := descent_iter m 0 k
  rw [Nat.zero_add] at h1
  have h2 := base_odd m (k + m + 1)
  have h12 := h1.trans h2
  have h_k : k + m + 1 + 3 = m + k + 4 := by omega
  rwa [h_k] at h12

private theorem step_P (m k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_P m k) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases m with _ | _ | m'
  · rcases k with _ | k'
    · exact ⟨cfg_P 0 2, step_P_m0_k0, Or.inl (in_ps_P 0 2)⟩
    · exact ⟨cfg_P 2 k', step_P_m0_ksucc k', Or.inl (in_ps_P 2 k')⟩
  · obtain ⟨cfg', h1, h2⟩ := step_P_m1 k
    exact ⟨cfg', h1, Or.inr h2⟩
  · rcases nat_even_or_odd_two_mul m' with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨cfg_P (3 * j + k + 3) 1, step_P_even j k,
        Or.inl (in_ps_P (3 * j + k + 3) 1)⟩
    · have h_m : 2 * j + 1 + 2 = 2 * j + 3 := by omega
      rw [h_m]
      exact ⟨cfg_P j (j + k + 4), step_P_odd j k,
        Or.inl (in_ps_P j (j + k + 4))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_P 0 2) := by
  have h_init : ReachesPlus target (init []) (cfg_P 0 2) := by
    unfold cfg_P
    have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [list_pow_zero, h2]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P 0 2, init_reaches_start, in_ps_P 0 2⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_P]
  exact step_P (vars 0) (vars 1)

/-- `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. -/
inductive State where
  /-- $P(m, k) := 0^\infty\,1^m\,\mathrm{E}{>}\,1\,1^k\,0^\infty$. -/
  | P (m k : ℕ)

/-- Initial symbolic state $P(0, 2)$, reached after 6 raw TM steps. -/
def start : State := .P 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P m k =>
    Cfg.headRight SixState.E
      (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .P 0 0 => some (.P 0 2)
  | .P 0 (k + 1) => some (.P 2 k)
  | .P 1 _ => none
  | .P (m + 2) k =>
    if m % 2 = 0 then
      some (.P (3 * (m / 2) + k + 3) 1)
    else
      some (.P (m / 2) (m / 2 + k + 4))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨m, k⟩ s' hnext
    rcases m with _ | _ | m'
    · rcases k with _ | k'
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_P_m0_k0
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_P_m0_ksucc k'
    · simp [next] at hnext
    · rcases nat_even_or_odd_two_mul m' with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have h_mod : (2 * j) % 2 = 0 := by omega
        have h_div : (2 * j) / 2 = j := by omega
        simp only [next, h_mod, h_div, ↓reduceIte, Option.some.injEq] at hnext
        subst hnext
        exact step_P_even j k
      · have h_mod : (2 * j + 1) % 2 = 1 := by omega
        have h_div : (2 * j + 1) / 2 = j := by omega
        simp only [next, h_mod, h_div, Nat.one_ne_zero, ↓reduceIte, Option.some.injEq] at hnext
        subst hnext
        have h_m : 2 * j + 1 + 2 = 2 * j + 3 := by omega
        change ReachesPlus target (cfg_P (2 * j + 1 + 2) k) (cfg_P j (j + k + 4))
        rw [h_m]
        exact step_P_odd j k
  step_none := by
    rintro ⟨m, k⟩ hnext
    rcases m with _ | _ | m'
    · rcases k with _ | k' <;> simp [next] at hnext
    · obtain ⟨cfg', hp, hh⟩ := step_P_m1 k
      exact ⟨cfg', hp.to_star, hh⟩
    · simp only [next] at hnext
      split at hnext <;> simp at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE
