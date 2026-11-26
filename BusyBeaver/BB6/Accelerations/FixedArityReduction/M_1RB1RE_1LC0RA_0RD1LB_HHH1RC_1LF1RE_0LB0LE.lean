/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE` (BMO1)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`
(see <https://wiki.bbchallenge.org/wiki/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE>)
(**BMO1**, holdout #508, `suspect_19`).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$A(a, b, c) := 0^\infty\,(10)^a\,0\,\mathrm{A}{>}\,(01)^b\,1^c\,0^\infty$$
at $A(0, 0, 2)$ in 8 steps, and every $A(a, b, c)$ advances in `ReachesPlus` either to another
$A(a', b', c')$ or to a halting configuration (when $a = 0$ and $c = 1$).

## Collatz-like Acceleration Rules

```text
Consider:
A(a, b, c) = 0^inf (10)^a 0 A> (01)^b 1^c 0^inf

A(a, b, 0)     -> A(a, 0, 2b+2)
A(0, b, 1)     -> Halt
A(0, b, d+2)   -> A(b+2, 0, d+1)
A(a+1, b, d+1) -> A(a, b+2, d)

Start: A(0, 0, 2), reached after 8 raw TM steps
```

Iterating the fourth rule reduces the system to the 2-parameter slice $S(a, c) := A(a, 0, c)$:

```text
Consider:
S(a, c) = 0^inf (10)^a 0 A> 1^c 0^inf

S(a+c, c)     -> S(a, 4c+2)
S(a, a+1)     -> Halt
S(a, a+d+2)   -> S(2a+2, d+1)

Start: S(0, 2), reached after 8 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Bounce Lemmas -/

private theorem default_append_10_succ (k : ℕ) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (default : ListBlank (Fin 2)) =
      ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default) := by
  have h1 :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
          (ListBlank.append [1] (ListBlank.append [0] default)) := by
    rw [list_pow_succ', ListBlank.append_assoc]
    rfl
  rw [h1, ListBlank.default_eq_append_zero.symm, append_10_pow_one]

/-- `A>` shifts rightward over `(01)^k`, writing `(10)^k` (`[0, 1]^k` on the left stack). -/
private theorem shift_AB (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [0, 1] l)
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

/-- `C>` scanning `1` shifts leftward over `(10)^k`, turning each `(10)` into `11` on the right. -/
private theorem shift_CB (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [1] r))) := by
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
            (ListBlank.append [1] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.append [1, 1] r)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.append [1] r) := by
      have h_eq1 :
          ListBlank.append [1] (ListBlank.append [1, 1] r) =
            ListBlank.append (([1] : List (Fin 2)) ^ 2) (ListBlank.append [1] r) :=
        rfl
      have h_eq2 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h_eq1, h_eq2, ListBlank.append_pow_add]
    rwa [h_pow_l, h_pow_r] at h3

/-- `E>` shifts rightward over `1^k`, preserving `1^k` on the left. -/
private theorem shift_E_right (k : ℕ) (l r : ListBlank (Fin 2)) :
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

/-- `F>` scanning `1` shifts leftward over `1^k`, preserving `1^k` on the right. -/
private theorem shift_FE_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight F l
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight F
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
        ListBlank.append (([1] : List (Fin 2)) ^ k)
          (ListBlank.append [1] (ListBlank.append [1] r)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r) := by
      rw [ListBlank.append_pow_add ([1] : List (Fin 2)) k 1]
      rfl
    rwa [h_pow_l, h_pow_r] at h3

/-- `F>` scanning `11` shifts leftward over `(10)^k`, turning it into `11 (01)^k` on the right. -/
private theorem shift_FE_10 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1, 1] r))
      (Cfg.headRight F l
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1] r))
          (Cfg.headRight F
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] (ListBlank.append [0, 1] r))) := by
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

/-- `C>` shifts rightward over `(01)^k`, writing `(01)^k` (`[1, 0]^k` on the left stack). -/
private theorem shift_CD (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight C (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight C (ListBlank.append [1, 0] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 0] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem bounce_CB_00 (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [1] r))
      (Cfg.headRight A
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [1] r)) := by
  rcases a with _ | a'
  · rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  · rw [ListBlank.append_pow_succ]
    bb_steps

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$A(a, b, c) := 0^\infty\,(10)^a\,0\,\mathrm{A}{>}\,(01)^b\,1^c\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.rep [0, 1] 0 .default)
    head := some A
    right := .rep [0, 1] 1 (.rep [1] 2 .default) }

/-- Closed pattern set for `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

/-- Configuration $A(a, b, c)$. -/
private def cfg_A (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_A (a b c : ℕ) : IsInPatternSet ps (cfg_A a b c) :=
  ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

/-- Rule 1 (`c = 0`): `A(a, b, 0) -> A(a, 0, 2b + 2)`. -/
private theorem step_A_c0 (a b : ℕ) :
    ReachesPlus target (cfg_A a b 0) (cfg_A a 0 (2 * b + 2)) := by
  have h1 := shift_AB b
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)) default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)))
          default)
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    bb_steps
  have h12 :
      ReachesPlus target (cfg_A a b 0)
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    unfold cfg_A
    rw [list_pow_zero, ListBlank.append_nil]
    exact h1.trans_plus h2
  have h3 := shift_CB b
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1] default)
  have h123 := h12.trans_star h3
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * b))
        (ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 1)) default) := by
    have h_eq :
        ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append (([1] : List (Fin 2)) ^ 2) default :=
      rfl
    rw [h_eq, ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * b) 2 default]
    have h_add : 2 * b + 2 = 1 + (2 * b + 1) := by omega
    rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * b + 1) default]
    rfl
  rw [h_r] at h123
  have h4 := bounce_CB_00 a (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 1)) default)
  have h1234 := h123.trans h4
  unfold cfg_A
  rw [list_pow_zero, ListBlank.append_nil]
  have h_r2 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 1)) default) := by
    have h_add : 2 * b + 2 = 1 + (2 * b + 1) := by omega
    rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * b + 1) default]
    rfl
  rwa [h_r2]

/-- Rule 2 (`a = 0, c = 1`): `A(0, b, 1)` reaches a halting configuration. -/
private theorem step_A_a0_c1 (b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 0 b 1) cfg' ∧ (step target cfg').isNone := by
  have h1 := shift_AB b (ListBlank.append [0] default)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
        (Cfg.headRight F
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))
          (ListBlank.append [1, 1] default)) := by
    rw [list_pow_one]
    bb_steps
  have h12 :
      ReachesPlus target (cfg_A 0 b 1)
        (Cfg.headRight F
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))
          (ListBlank.append [1, 1] default)) := by
    unfold cfg_A
    rw [list_pow_zero, ListBlank.append_nil]
    exact h1.trans_plus h2
  have h3 := shift_FE_10 b (ListBlank.append [0] default) default
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight F (ListBlank.append [0] default)
          (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default)))
        (Cfg.headRight C default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 3)) default)) := by
    have h_eq : b + 3 = 3 + b := by omega
    rw [h_eq, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 3 b default]
    have h_three : (([0, 1] : List (Fin 2)) ^ 3) = [0, 1, 0, 1, 0, 1] := rfl
    rw [h_three]
    bb_steps
  have h1234 := h123.trans h4
  have h5 := shift_CD (b + 3) default default
  have h12345 := h1234.trans_star h5
  have h6 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 3)) default) default)
        (Cfg.headRight D
          (ListBlank.append [0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 3)) default))
          default) := by
    bb_steps
  refine ⟨_, h12345.trans h6, ?_⟩
  bb_halt

/-- Rule 3 (`a = 0, c = d + 2`): `A(0, b, d + 2) -> A(b + 2, 0, d + 1)`. -/
private theorem step_A_a0_c_ge2 (b d : ℕ) :
    ReachesPlus target (cfg_A 0 b (d + 2)) (cfg_A (b + 2) 0 (d + 1)) := by
  have h1 := shift_AB b (ListBlank.append [0] default)
    (ListBlank.append (([1] : List (Fin 2)) ^ (d + 2)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 2)) default))
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (d + 1) default]
    bb_steps
  have h12 :
      ReachesPlus target (cfg_A 0 b (d + 2))
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)) := by
    unfold cfg_A
    rw [list_pow_zero, ListBlank.append_nil]
    exact h1.trans_plus h2
  have h3 := shift_E_right (d + 1)
    (ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default)))
    default
  have h123 := h12.trans_star h3
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (default : ListBlank (Fin 2))))) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))) := by
    rw [ListBlank.append_pow_comm ([1] : List (Fin 2)) (d + 1)]
  rw [h_l] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))))
          default)
        (Cfg.headRight F
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default)))
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    bb_steps
  have h1234 := h123.trans h4
  have h5 := shift_FE_1 (d + 1)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [0] default))
    (ListBlank.append [1] default)
  have h12345 := h1234.trans_star h5
  have h_r1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default) := by
    have h_eq1 :
        ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append (([1] : List (Fin 2)) ^ 2) default :=
      rfl
    rw [h_eq1, ← ListBlank.append_pow_add ([1] : List (Fin 2)) (d + 1) 2 default]
    have h_eq2 : d + 1 + 2 = 2 + (d + 1) := by omega
    rw [h_eq2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (d + 1) default]
    rfl
  rw [h_r1] at h12345
  have h6 := shift_FE_10 b (ListBlank.append [0] default)
    (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
  have h123456 := h12345.trans_star h6
  have h7 :
      ReachesPlus target
        (Cfg.headRight F (ListBlank.append [0] default)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))))
        (Cfg.headRight C default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 3))
            (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))) := by
    have h_eq : b + 3 = 3 + b := by omega
    rw [h_eq, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 3 b]
    have h_three : (([0, 1] : List (Fin 2)) ^ 3) = [0, 1, 0, 1, 0, 1] := rfl
    rw [h_three]
    bb_steps
  have h1234567 := h123456.trans h7
  have h8 := shift_CD (b + 3) default (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
  have h12345678 := h1234567.trans_star h8
  rw [default_append_10_succ (b + 2)] at h12345678
  have h9 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default))
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))
        (cfg_A (b + 2) 0 (d + 1)) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d default,
      list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h12345678.trans h9

/-- Rule 4 (`a = a' + 1, c = d + 1`): `A(a' + 1, b, d + 1) -> A(a', b + 2, d)`. -/
private theorem step_A_asucc_csucc (a' b d : ℕ) :
    ReachesPlus target (cfg_A (a' + 1) b (d + 1)) (cfg_A a' (b + 2) d) := by
  have h1 := shift_AB b
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))))
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default)) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d default]
    bb_steps
  have h12 :
      ReachesPlus target (cfg_A (a' + 1) b (d + 1))
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))))
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default)) := by
    unfold cfg_A
    exact h1.trans_plus h2
  have h3 := shift_E_right d
    (ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))))
    default
  have h123 := h12.trans_star h3
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ d)
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1))
                (default : ListBlank (Fin 2)))))) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default)))) := by
    rw [ListBlank.append_pow_comm ([1] : List (Fin 2)) d]
  rw [h_l] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
                (ListBlank.append [0]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default)))))
          default)
        (Cfg.headRight F
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))))
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    bb_steps
  have h1234 := h123.trans h4
  have h5 := shift_FE_1 d
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default)))
    (ListBlank.append [1] default)
  have h12345 := h1234.trans_star h5
  have h_r1 :
      ListBlank.append (([1] : List (Fin 2)) ^ d)
        (ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
    have h_eq1 :
        ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append (([1] : List (Fin 2)) ^ 2) default :=
      rfl
    rw [h_eq1, ← ListBlank.append_pow_add ([1] : List (Fin 2)) d 2 default]
    have h_eq2 : d + 2 = 2 + d := by omega
    rw [h_eq2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d default]
    rfl
  rw [h_r1] at h12345
  have h6 := shift_FE_10 b
    (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
  have h123456 := h12345.trans_star h6
  have h7 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a' + 1)) default))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (cfg_A a' (b + 2) d) := by
    unfold cfg_A
    have h_r2 :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (default : ListBlank (Fin 2))) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default)) := by
      have h_eq : b + 2 = 2 + b := by omega
      rw [h_eq, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 b]
      rfl
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a' default, h_r2]
    bb_steps
  exact h123456.trans h7

private theorem step_A (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | d
  · exact ⟨cfg_A a 0 (2 * b + 2), step_A_c0 a b, Or.inl (in_ps_A a 0 (2 * b + 2))⟩
  · rcases a with _ | a'
    · rcases d with _ | d'
      · obtain ⟨cfg', h_plus, h_halt⟩ := step_A_a0_c1 b
        exact ⟨cfg', h_plus, Or.inr h_halt⟩
      · exact ⟨cfg_A (b + 2) 0 (d' + 1), step_A_a0_c_ge2 b d',
          Or.inl (in_ps_A (b + 2) 0 (d' + 1))⟩
    · exact ⟨cfg_A a' (b + 2) d, step_A_asucc_csucc a' b d,
        Or.inl (in_ps_A a' (b + 2) d)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 0 0 2) := by
  have h : (init [] : Cfg (Fin 2) (Fin 6)) = cfg_A 0 0 0 := by
    rw [init_nil_eq_headRight]
    unfold cfg_A
    simp
  rw [h]
  exact (step_A_c0 0 0).to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 0 2, init_reaches_start, in_ps_A 0 0 2⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A (vars 0) (vars 1) (vars 2)

/-- `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`. -/
inductive State where
  /-- $A(a, b, c) := 0^\infty\,(10)^a\,0\,\mathrm{A}{>}\,(01)^b\,1^c\,0^\infty$. -/
  | A (a b c : ℕ)

/-- Initial symbolic state $A(0, 0, 2)$, reached after 8 raw TM steps. -/
def start : State := .A 0 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A a b 0 => some (.A a 0 (2 * b + 2))
  | .A 0 _ 1 => none
  | .A 0 b (d + 2) => some (.A (b + 2) 0 (d + 1))
  | .A (a + 1) b (d + 1) => some (.A a (b + 2) d)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases c with _ | d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_A_c0 a b
    · rcases a with _ | a'
      · rcases d with _ | d'
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_A_a0_c_ge2 b d'
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_A_asucc_csucc a' b d
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases c with _ | d
    · simp [next] at hnext
    · rcases a with _ | a'
      · rcases d with _ | d'
        · obtain ⟨cfg', hp, hh⟩ := step_A_a0_c1 b
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE
