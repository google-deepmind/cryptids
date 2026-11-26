/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA`
(see <https://wiki.bbchallenge.org/wiki/1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA>)
(cryptid_14 (holdout #377, suspect_56)).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$H(a, b, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^b\,(01)^c\,0^\infty$$
at $H(0, 0, 1)$ in 7 steps (and is already at $H(0, 0, 0)$ at step 0), and every $H(a, b, c)$
advances in `ReachesPlus` either to another $H(a', b', c')$ or to a halting configuration (when
$a = 0$, $c = 0$, and $b = 2k + 1$ is odd).

## Collatz-like Acceleration Rules

```text
Consider:
H(a, b, c) = 0^inf 1^a A> 1^b (01)^c 0^inf

H(0, 2k, 0)      -> H(0, 0, k+1)
H(0, 2k+1, 0)    -> Halt
H(0, b, 1)       -> H(b+2, 0, 1)
H(0, b, d+2)     -> H(b+3, 0, d+1)
H(a+1, 0, 0)     -> H(a+1, 0, 1)
H(a+1, 0, 1)     -> H(a, 4, 0)
H(a+1, 0, d+2)   -> H(a, 5, d)
H(a+1, 1, 0)     -> H(a, 0, 1)
H(1, 1, d+1)     -> H(2, 0, d+2)
H(a+2, 1, d+1)   -> H(a, 4, d+1)
H(a+1, 2, c)     -> H(a, 0, c+2)
H(1, m+3, c)     -> H(m+4, 0, c+1)
H(a+2, m+3, c)   -> H(a, m+6, c)

Start: H(0, 0, 1), reached after 7 raw TM steps (from init [] = H(0, 0, 0))
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

private theorem combine_ones_left (a n : ℕ) :
    ListBlank.append (([1] : List (Fin 2)) ^ n)
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default) =
      ListBlank.append (([1] : List (Fin 2)) ^ (a + n)) default := by
  rw [← ListBlank.append_pow_add, Nat.add_comm]

/-- `<C` shifts leftward over `1^k`, preserving `1^k` on the right tape. -/
private theorem shift_C (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft C l (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft C
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)) r)
          (Cfg.headLeft C
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] r)) := by
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

/-- `A>` reading `0 1 1^k` shifts rightward by `k` cells, placing `1^k` onto the left tape. -/
private theorem shift_ABF (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l
        (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0, 1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append [0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight A (ListBlank.append [1] l)
            (ListBlank.append [0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- `A>` with `0` to its left shifts rightward over `1^k`, placing `1^k 0` onto the left tape. -/
private theorem shift_ACD (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A (ListBlank.append [0] l)
        (ListBlank.append (([1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A (ListBlank.append [0] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A
            (ListBlank.append [0] (ListBlank.append [1] l))
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

/-- `D>` reading `1` shifts leftward over `(11)^k`, converting `(11)^k` into `(01)^k`. -/
private theorem shift_DE (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight D l
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight D
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight D
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$H(a, b, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^b\,(01)^c\,0^\infty$. -/
def pat_H : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some A
    right := .rep [1] 1 (.rep [0, 1] 2 .default) }

/-- Closed pattern set for `1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_H, .true)]

/-- Configuration $H(a, b, c)$. -/
private def cfg_H (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))

private theorem eval_pat_H (vars : ℕ → ℕ) :
    evalTapePattern pat_H vars = cfg_H (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_H (a b c : ℕ) : IsInPatternSet ps (cfg_H a b c) :=
  ⟨(pat_H, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

/-- Rule 1 (`a = 0, b = 2k, c = 0`): `H(0, 2k, 0) -> H(0, 0, k + 1)`. -/
private theorem rule_1 (k : ℕ) :
    ReachesPlus target (cfg_H 0 (2 * k) 0) (cfg_H 0 0 (k + 1)) := by
  have h_start :
      cfg_H 0 (2 * k) 0 =
        Cfg.headRight A (ListBlank.append [0] default)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) default) := by
    unfold cfg_H
    simp
  rw [h_start]
  have h1 := shift_ACD (2 * k) default default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) default))
          default)
        (Cfg.headRight D
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) default))
          (ListBlank.append [1] default)) := by
    rw [list_pow_one]
    bb_steps
  have h12 := h1.trans_plus h2
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ 1)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (default : ListBlank (Fin 2))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default) := by
    rw [one_pow_two_mul k, combine_ones_left (2 * k) 1, combine_ones_left 1 (2 * k)]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  rw [h_l] at h12
  have h3 := shift_DE k (ListBlank.append (([1] : List (Fin 2)) ^ 1) default) default
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)))
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))) := by
    rw [list_pow_one]
    bb_steps
  have h1234 := h123.trans h4
  have h_r :
      ListBlank.append [0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
          (default : ListBlank (Fin 2))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) default := by
    rw [← ListBlank.append_pow_succ]
  unfold cfg_H
  simp only [list_pow_zero, ListBlank.append_nil]
  rwa [h_r] at h1234

/-- Rule 2 (`a = 0, b = 2k + 1, c = 0`, Halts): `H(0, 2k + 1, 0)` halts. -/
private theorem rule_2_halt (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_H 0 (2 * k + 1) 0) cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headRight E default
    (ListBlank.append [0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) default)), ?_, by bb_halt⟩
  have h_start :
      cfg_H 0 (2 * k + 1) 0 =
        Cfg.headRight A (ListBlank.append [0] default)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default) := by
    unfold cfg_H
    simp
  rw [h_start]
  have h1 := shift_ACD (2 * k + 1) default default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default))
          default)
        (Cfg.headRight D
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default))
          (ListBlank.append [1] default)) := by
    rw [list_pow_one]
    bb_steps
  have h12 := h1.trans_plus h2
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ 1)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
          (default : ListBlank (Fin 2))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default := by
    rw [one_pow_two_mul (k + 1), combine_ones_left (2 * k + 1) 1]
    exact congrArg (fun x => ListBlank.append (([1] : List (Fin 2)) ^ x) default) (by omega)
  rw [h_l] at h12
  have h3 := shift_DE (k + 1) default default
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight D default
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) default)))
        (Cfg.headRight E default
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) default))) := by
    bb_steps
  exact h123.trans h4

/-- Rule 3 (`a = 0, b, c = 1`): `H(0, b, 1) -> H(b + 2, 0, 1)`. -/
private theorem rule_3 (b : ℕ) :
    ReachesPlus target (cfg_H 0 b 1) (cfg_H (b + 2) 0 1) := by
  have h_start :
      cfg_H 0 b 1 =
        Cfg.headRight A (ListBlank.append [0] default)
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1) default)) := by
    unfold cfg_H
    simp
  rw [h_start]
  have h1 := shift_ACD b default (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1) default))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1) default)) := by
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two, list_pow_one]
    bb_steps
  have h12 := h1.trans_plus h2
  have h_l := combine_ones_left b 2
  unfold cfg_H
  simp only [list_pow_zero, ListBlank.append_nil]
  rwa [h_l] at h12

/-- Rule 4 (`a = 0, b, c = d + 2`): `H(0, b, d + 2) -> H(b + 3, 0, d + 1)`. -/
private theorem rule_4 (b d : ℕ) :
    ReachesPlus target (cfg_H 0 b (d + 2)) (cfg_H (b + 3) 0 (d + 1)) := by
  have h_start :
      cfg_H 0 b (d + 2) =
        Cfg.headRight A (ListBlank.append [0] default)
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 2)) default)) := by
    unfold cfg_H
    simp
  rw [h_start]
  have h1 := shift_ACD b default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 2)) default))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default))) := by
    have h_split :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default) := by
      have h_eq : d + 2 = 2 + d := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    have h_three : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h_split, h_three]
    bb_steps
  have h12 := h1.trans_plus h2
  have h_l := combine_ones_left b 3
  have h_r :
      ListBlank.append [0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ d)
          (default : ListBlank (Fin 2))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default := by
    rw [← ListBlank.append_pow_succ]
  unfold cfg_H
  simp only [list_pow_zero, ListBlank.append_nil]
  rwa [h_l, h_r] at h12

/-- Rule 5 (`a + 1, b = 0, c = 0`): `H(a + 1, 0, 0) -> H(a + 1, 0, 1)`. -/
private theorem rule_5 (a : ℕ) :
    ReachesPlus target (cfg_H (a + 1) 0 0) (cfg_H (a + 1) 0 1) := by
  have h1 :
      ReachesPlus target (cfg_H (a + 1) 0 0)
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
          (ListBlank.append [1] default)) := by
    unfold cfg_H
    simp only [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_C (a + 1) default (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C default
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [1] default)))
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))) := by
    have h_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
          (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default) := by
      rw [ListBlank.append_pow_comm]
    rw [h_split]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_ABF (a + 1) default default
  have h1234 := h123.trans_star h4
  unfold cfg_H
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  exact h1234

/-- Rule 6 (`a + 1, b = 0, c = 1`): `H(a + 1, 0, 1) -> H(a, 4, 0)`. -/
private theorem rule_6 (a : ℕ) :
    ReachesPlus target (cfg_H (a + 1) 0 1) (cfg_H a 4 0) := by
  unfold cfg_H
  have h_four : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a, list_pow_zero, list_pow_one,
    ListBlank.append_nil, h_four]
  bb_steps

/-- Rule 7 (`a + 1, b = 0, c = d + 2`): `H(a + 1, 0, d + 2) -> H(a, 5, d)`. -/
private theorem rule_7 (a d : ℕ) :
    ReachesPlus target (cfg_H (a + 1) 0 (d + 2)) (cfg_H a 5 d) := by
  have h_r :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default) := by
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  unfold cfg_H
  have h_five : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a, h_r, list_pow_zero,
    ListBlank.append_nil, h_five]
  bb_steps

/-- Rule 8 (`a + 1, b = 1, c = 0`): `H(a + 1, 1, 0) -> H(a, 0, 1)`. -/
private theorem rule_8 (a : ℕ) :
    ReachesPlus target (cfg_H (a + 1) 1 0) (cfg_H a 0 1) := by
  have h1 :
      ReachesPlus target (cfg_H (a + 1) 1 0)
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
          default) := by
    unfold cfg_H
    rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_C (a + 1) default default
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C default
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default))
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_ABF a default default
  have h1234 := h123.trans_star h4
  unfold cfg_H
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  exact h1234

/-- Rule 9 (`a = 1, b = 1, c = d + 1`): `H(1, 1, d + 1) -> H(2, 0, d + 2)`. -/
private theorem rule_9 (d : ℕ) :
    ReachesPlus target (cfg_H 1 1 (d + 1)) (cfg_H 2 0 (d + 2)) := by
  have h_r2 :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default) := by
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  unfold cfg_H
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) d, h_r2, list_pow_one,
    list_pow_zero, ListBlank.append_nil, h_two]
  bb_steps

/-- Rule 10 (`a + 2, b = 1, c = d + 1`): `H(a + 2, 1, d + 1) -> H(a, 4, d + 1)`. -/
private theorem rule_10 (a d : ℕ) :
    ReachesPlus target (cfg_H (a + 2) 1 (d + 1)) (cfg_H a 4 (d + 1)) := by
  have h1 :
      ReachesPlus target (cfg_H (a + 2) 1 (d + 1))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
          (ListBlank.append [0]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default))) := by
    unfold cfg_H
    rw [list_pow_one]
    bb_steps
  have h2 := shift_C (a + 2) default
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C default
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [0]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default))))
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
              (ListBlank.append [0]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default))))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (a + 1)]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_ABF (a + 1) default
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default))
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
          (ListBlank.append [0, 1]
            (ListBlank.append [0]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) default))))
        (cfg_H a 4 (d + 1)) := by
    unfold cfg_H
    have h_four : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a,
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) d, h_four]
    bb_steps
  exact h1234.trans h5

/-- Rule 11 (`a + 1, b = 2, c`): `H(a + 1, 2, c) -> H(a, 0, c + 2)`. -/
private theorem rule_11 (a c : ℕ) :
    ReachesPlus target (cfg_H (a + 1) 2 c) (cfg_H a 0 (c + 2)) := by
  have h1 :
      ReachesPlus target (cfg_H (a + 1) 2 c)
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))) := by
    unfold cfg_H
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two]
    bb_steps
  have h2 := shift_C (a + 1) default
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C default
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ a)
              (ListBlank.append [0, 1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_ABF a default
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h1234 := h123.trans_star h4
  have h_r :
      ListBlank.append [0, 1]
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (default : ListBlank (Fin 2)))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2)) default := by
    have h_eq : c + 2 = 2 + c := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  unfold cfg_H
  simp only [list_pow_zero, ListBlank.append_nil]
  rwa [h_r] at h1234

/-- Rule 12 (`a = 1, b = m + 3, c`): `H(1, m + 3, c) -> H(m + 4, 0, c + 1)`. -/
private theorem rule_12 (m c : ℕ) :
    ReachesPlus target (cfg_H 1 (m + 3) c) (cfg_H (m + 4) 0 (c + 1)) := by
  have h1 :
      ReachesPlus target (cfg_H 1 (m + 3) c)
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + 4))
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))) := by
    unfold cfg_H
    have h_r1 :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 3))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (default : ListBlank (Fin 2))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)) := by
      have h_eq : m + 3 = 3 + m := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    have h_r2 :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (default : ListBlank (Fin 2))) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)) := by
      have h_eq : m + 4 = 4 + m := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r1, h_r2, list_pow_one]
    bb_steps
  have h2 := shift_ABF (m + 4) default
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)
  have h12 := h1.trans_star h2
  have h_r :
      ListBlank.append [0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
          (default : ListBlank (Fin 2))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1)) default := by
    rw [← ListBlank.append_pow_succ]
  unfold cfg_H
  simp only [list_pow_zero, ListBlank.append_nil]
  rwa [h_r] at h12

/-- Rule 13 (`a + 2, b = m + 3, c`): `H(a + 2, m + 3, c) -> H(a, m + 6, c)`. -/
private theorem rule_13 (a m c : ℕ) :
    ReachesPlus target (cfg_H (a + 2) (m + 3) c) (cfg_H a (m + 6) c) := by
  have h1 :
      ReachesPlus target (cfg_H (a + 2) (m + 3) c)
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))) := by
    unfold cfg_H
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 3))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (default : ListBlank (Fin 2))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)) := by
      have h_eq : m + 3 = 3 + m := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h2 := shift_C (a + 2) default
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1] : List (Fin 2)) ^ m)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft C default
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ m)
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))))
        (Cfg.headRight A default
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ m)
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))))) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (a + 1)]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_ABF (a + 1) default
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1] : List (Fin 2)) ^ m)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
          (ListBlank.append [0, 1]
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ m)
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))))
        (cfg_H a (m + 6) c) := by
    unfold cfg_H
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 6))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (default : ListBlank (Fin 2))) =
          ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)) := by
      have h_eq : m + 6 = 6 + m := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a, h_r]
    bb_steps
  exact h1234.trans h5

private theorem step_H (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_H a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a'
  · rcases c with _ | _ | d
    · have hb : ∃ k, b = 2 * k ∨ b = 2 * k + 1 := ⟨b / 2, by omega⟩
      rcases hb with ⟨k, rfl | rfl⟩
      · exact ⟨cfg_H 0 0 (k + 1), rule_1 k, Or.inl (in_ps_H 0 0 (k + 1))⟩
      · obtain ⟨cfg', h_plus, h_halt⟩ := rule_2_halt k
        exact ⟨cfg', h_plus, Or.inr h_halt⟩
    · exact ⟨cfg_H (b + 2) 0 1, rule_3 b, Or.inl (in_ps_H (b + 2) 0 1)⟩
    · exact ⟨cfg_H (b + 3) 0 (d + 1), rule_4 b d, Or.inl (in_ps_H (b + 3) 0 (d + 1))⟩
  · rcases b with _ | _ | _ | m
    · rcases c with _ | _ | d
      · exact ⟨cfg_H 1 0 1, rule_5 0, Or.inl (in_ps_H 1 0 1)⟩
      · exact ⟨cfg_H 0 4 0, rule_6 0, Or.inl (in_ps_H 0 4 0)⟩
      · exact ⟨cfg_H 0 5 d, rule_7 0 d, Or.inl (in_ps_H 0 5 d)⟩
    · rcases c with _ | d
      · exact ⟨cfg_H 0 0 1, rule_8 0, Or.inl (in_ps_H 0 0 1)⟩
      · exact ⟨cfg_H 2 0 (d + 2), rule_9 d, Or.inl (in_ps_H 2 0 (d + 2))⟩
    · exact ⟨cfg_H 0 0 (c + 2), rule_11 0 c, Or.inl (in_ps_H 0 0 (c + 2))⟩
    · exact ⟨cfg_H (m + 4) 0 (c + 1), rule_12 m c, Or.inl (in_ps_H (m + 4) 0 (c + 1))⟩
  · rcases b with _ | _ | _ | m
    · rcases c with _ | _ | d
      · exact ⟨cfg_H (a' + 2) 0 1, rule_5 (a' + 1), Or.inl (in_ps_H (a' + 2) 0 1)⟩
      · exact ⟨cfg_H (a' + 1) 4 0, rule_6 (a' + 1), Or.inl (in_ps_H (a' + 1) 4 0)⟩
      · exact ⟨cfg_H (a' + 1) 5 d, rule_7 (a' + 1) d, Or.inl (in_ps_H (a' + 1) 5 d)⟩
    · rcases c with _ | d
      · exact ⟨cfg_H (a' + 1) 0 1, rule_8 (a' + 1), Or.inl (in_ps_H (a' + 1) 0 1)⟩
      · exact ⟨cfg_H a' 4 (d + 1), rule_10 a' d, Or.inl (in_ps_H a' 4 (d + 1))⟩
    · exact ⟨cfg_H (a' + 1) 0 (c + 2), rule_11 (a' + 1) c,
        Or.inl (in_ps_H (a' + 1) 0 (c + 2))⟩
    · exact ⟨cfg_H a' (m + 6) c, rule_13 a' m c, Or.inl (in_ps_H a' (m + 6) c)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_H 0 0 1) := by
  have h : (init [] : Cfg (Fin 2) (Fin 6)) = cfg_H 0 0 0 := rfl
  rw [h]
  exact (rule_1 0).to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_H 0 0 1, init_reaches_start, in_ps_H 0 0 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_H]
  exact step_H (vars 0) (vars 1) (vars 2)

/-- `1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA`. -/
inductive State where
  /-- $H(a, b, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^b\,(01)^c\,0^\infty$. -/
  | H (a b c : ℕ)

/-- Initial symbolic state $H(0, 0, 1)$, reached after 7 raw TM steps. -/
def start : State := .H 0 0 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .H a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .H 0 b 0 => if b % 2 = 0 then some (.H 0 0 (b / 2 + 1)) else none
  | .H 0 b 1 => some (.H (b + 2) 0 1)
  | .H 0 b (d + 2) => some (.H (b + 3) 0 (d + 1))
  | .H (a + 1) 0 0 => some (.H (a + 1) 0 1)
  | .H (a + 1) 0 1 => some (.H a 4 0)
  | .H (a + 1) 0 (d + 2) => some (.H a 5 d)
  | .H (a + 1) 1 0 => some (.H a 0 1)
  | .H 1 1 (d + 1) => some (.H 2 0 (d + 2))
  | .H (a + 2) 1 (d + 1) => some (.H a 4 (d + 1))
  | .H (a + 1) 2 c => some (.H a 0 (c + 2))
  | .H 1 (m + 3) c => some (.H (m + 4) 0 (c + 1))
  | .H (a + 2) (m + 3) c => some (.H a (m + 6) c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases a with _ | _ | a'
    · rcases c with _ | _ | d
      · simp only [next] at hnext
        split_ifs at hnext with h_even
        simp only [Option.some.injEq] at hnext
        subst hnext
        have h := rule_1 (b / 2)
        have hb : 2 * (b / 2) = b := by omega
        rwa [hb] at h
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_3 b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_4 b d
    · rcases b with _ | _ | _ | m
      · rcases c with _ | _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_5 0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_6 0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_7 0 d
      · rcases c with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_8 0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_9 d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_11 0 c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_12 m c
    · rcases b with _ | _ | _ | m
      · rcases c with _ | _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_5 (a' + 1)
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_6 (a' + 1)
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_7 (a' + 1) d
      · rcases c with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_8 (a' + 1)
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_10 a' d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_11 (a' + 1) c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_13 a' m c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases a with _ | _ | a'
    · rcases c with _ | _ | d
      · simp only [next] at hnext
        split_ifs at hnext with h_even
        have hb : 2 * (b / 2) + 1 = b := by omega
        obtain ⟨cfg', hp, hh⟩ := rule_2_halt (b / 2)
        rw [hb] at hp
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
      · simp [next] at hnext
    · rcases b with _ | _ | _ | m
      · rcases c with _ | _ | d <;> simp [next] at hnext
      · rcases c with _ | d <;> simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext
    · rcases b with _ | _ | _ | m
      · rcases c with _ | _ | d <;> simp [next] at hnext
      · rcases c with _ | d <;> simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA
