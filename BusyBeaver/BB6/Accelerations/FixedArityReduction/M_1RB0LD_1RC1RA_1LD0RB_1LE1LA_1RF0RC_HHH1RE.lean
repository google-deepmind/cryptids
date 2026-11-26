/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`
(`cryptid_17`, holdout #710, `suspect_54`; see
<https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE>).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$A(a, b, c) := 0^\infty\,1^a\,0\,(10)^b\,0\,(11)^{c+1}\,\mathrm{B}{>}\,0^\infty$$
at $A(3, 0, 0)$ in 17 steps, and every $A(a, b, c)$ advances in `ReachesPlus` either to another
$A(a', b', c')$ or to a halting configuration (when $a = 0$ and $b = 0$).

## Collatz-like Acceleration Rules

```text
Consider:
A(a, b, c) = 0^inf 1^a 0 (10)^b 0 (11)^{c+1} B> 0^inf

A(a, b+2, c) -> A(a, b, c+3)
A(a+1, 0, c) -> A(a, c, 2)
A(a+1, 1, c) -> A(a, c, 6)
A(0, 1, c)   -> A(2c+9, 0, 0)
A(0, 0, c)   -> Halt

Start: A(3, 0, 0), reached after 17 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

/-- `<A` shifts leftward across `(11)^n`, producing `(10)^n` on the right. -/
private theorem shift_A_left_11 (l r : ListBlank (Fin 2)) (n : ℕ) :
    ReachesStar target
      (Cfg.headLeft A (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) l) r)
      (Cfg.headLeft A l (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) r)) := by
  induction n generalizing l r with
  | zero => bb_refl
  | succ n ih =>
    rw [list_pow_add, ListBlank.append_assoc]
    refine (ih _ _).trans ?_
    simp only [list_pow_one]
    bb_steps

/-- `B>` shifts rightward across `(10)^n`, producing `(11)^n` on the left. -/
private theorem shift_B_right_10 (l r : ListBlank (Fin 2)) (n : ℕ) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) r))
      (Cfg.headRight B (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) l) r) := by
  induction n generalizing l r with
  | zero => bb_refl
  | succ n ih =>
    rw [list_pow_add, ListBlank.append_assoc]
    refine (ih _ _).trans ?_
    simp only [list_pow_one]
    bb_steps

/-- `F>` shifts rightward across `(10)^n`, producing `(11)^n` on the left. -/
private theorem shift_F_right_10 (l r : ListBlank (Fin 2)) (n : ℕ) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) r))
      (Cfg.headRight F (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) l) r) := by
  induction n generalizing l r with
  | zero => bb_refl
  | succ n ih =>
    rw [list_pow_add, ListBlank.append_assoc]
    refine (ih _ _).trans ?_
    simp only [list_pow_one]
    bb_steps

/-- `C>` shifts rightward across `(10)^n`, producing `(10)^n` on the left. -/
private theorem shift_C_right_10 (l r : ListBlank (Fin 2)) (n : ℕ) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) r))
      (Cfg.headRight C (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) l) r) := by
  induction n generalizing l r with
  | zero => bb_refl
  | succ n ih =>
    rw [list_pow_add, ListBlank.append_assoc, ← list_pow_add]
    refine (ih _ _).trans ?_
    simp only [list_pow_one]
    bb_steps

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$A(a, b, c) := 0^\infty\,1^a\,0\,(10)^b\,0\,(11)^{c+1}\,\mathrm{B}{>}\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left :=
      .sym 1 (.sym 1 (.rep [1, 1] 2 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.rep [1] 0 .default))))))
    head := some B
    right := .default }

/-- Closed pattern set for `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

/-- Configuration $A(a, b, c)$. -/
private def cfg_A (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
      (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
          (ListBlank.cons 0
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
    default

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_A (a b c : ℕ) : IsInPatternSet ps (cfg_A a b c) :=
  ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

/-- Rule 1: $A(a, b + 2, c) \to A(a, b, c + 3)$. -/
private theorem step_A_b_ge2 (a b c : ℕ) :
    ReachesPlus target (cfg_A a (b + 2) c) (cfg_A a b (c + 3)) := by
  unfold cfg_A
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step
  simp_rw [Nat.add_comm b 2, (by omega : c + 3 + 1 = 2 + c + 2),
    list_pow_add, ListBlank.append_assoc]
  have h2_10 : ([1, 0] : List (Fin 2)) ^ 2 = [1, 0, 1, 0] := rfl
  have h2_11 : ([1, 1] : List (Fin 2)) ^ 2 = [1, 1, 1, 1] := rfl
  rw [h2_10, h2_11]
  bb_steps
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_steps

/-- Rule 2: $A(a + 1, 0, c) \to A(a, c, 2)$. -/
private theorem step_A_b0_asucc (a c : ℕ) :
    ReachesPlus target (cfg_A (a + 1) 0 c) (cfg_A a c 2) := by
  unfold cfg_A
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  rw [list_pow_zero, Nat.add_comm a 1, list_pow_add, list_pow_one]
  simp_rw [ListBlank.append_assoc, ListBlank.append]
  bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_C_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  rw [Nat.add_comm c 1, list_pow_add, list_pow_one]
  simp_rw [ListBlank.append_assoc, ListBlank.append]
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  have h (s : ListBlank (Fin 2)) (n : ℕ) :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) s =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
          (ListBlank.cons 1 (ListBlank.cons 0 s)) := by
    rw [list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl
  rw [← h]
  bb_refl

/-- Intermediate rule for $A(a + 1, 1, c) \to A(a, c + 4, 0)$. -/
private theorem step_A_b1_asucc_aux (a c : ℕ) :
    ReachesPlus target (cfg_A (a + 1) 1 c) (cfg_A a (c + 4) 0) := by
  unfold cfg_A
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  rw [list_pow_one, Nat.add_comm a 1, list_pow_add, list_pow_one]
  simp_rw [ListBlank.append_assoc, ListBlank.append]
  bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_C_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step
  have h (s : ListBlank (Fin 2)) (n : ℕ) :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) s =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
          (ListBlank.cons 1 (ListBlank.cons 0 s)) := by
    rw [list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl
  rw [← h, ← h, list_pow_one]
  bb_refl

/-- Rule 3: $A(a + 1, 1, c) \to A(a, c, 6)$. -/
private theorem step_A_b1_asucc (a c : ℕ) :
    ReachesPlus target (cfg_A (a + 1) 1 c) (cfg_A a c 6) :=
  ((step_A_b1_asucc_aux a c).trans (step_A_b_ge2 a (c + 2) 0)).trans (step_A_b_ge2 a c 3)

/-- Rule 4: $A(0, 1, c) \to A(2c + 9, 0, 0)$. -/
private theorem step_A_b1_a0 (c : ℕ) :
    ReachesPlus target (cfg_A 0 1 c) (cfg_A (2 * c + 9) 0 0) := by
  unfold cfg_A
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  rw [list_pow_zero, list_pow_zero, list_pow_one]
  simp_rw [ListBlank.append]
  bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_F_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step; bb_step
  rw [one_pow_two_mul, Nat.mul_add, (by omega : 2 * c + 9 = 2 + 2 * c + 7)]
  simp_rw [list_pow_add, ListBlank.append_assoc]
  have h2 : ([1] : List (Fin 2)) ^ 2 = [1, 1] := rfl
  have h7 : ([1] : List (Fin 2)) ^ 7 = [1, 1, 1, 1, 1, 1, 1] := rfl
  rw [h2, h7, list_pow_one]
  bb_refl

/-- Rule 5: $A(0, 0, c)$ halts. -/
private theorem step_A_b0_a0 (c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 0 0 c) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F
    (ListBlank.cons 1
      (ListBlank.cons 1
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 default))))))
    default, ?_, by bb_halt⟩
  unfold cfg_A
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  bb_step
  refine (shift_B_right_10 _ _ _).trans ?_
  bb_step; bb_step; bb_step
  refine (shift_A_left_11 _ _ _).trans ?_
  rw [list_pow_zero, list_pow_zero]
  simp_rw [ListBlank.append]
  bb_step; bb_step; bb_step; bb_step; bb_step
  refine (shift_F_right_10 _ _ _).trans ?_
  bb_steps

private theorem step_A_all (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | b'
  · rcases a with _ | a'
    · obtain ⟨cfg', h_plus, h_halt⟩ := step_A_b0_a0 c
      exact ⟨cfg', h_plus, Or.inr h_halt⟩
    · exact ⟨cfg_A a' c 2, step_A_b0_asucc a' c, Or.inl (in_ps_A a' c 2)⟩
  · rcases a with _ | a'
    · exact ⟨cfg_A (2 * c + 9) 0 0, step_A_b1_a0 c, Or.inl (in_ps_A (2 * c + 9) 0 0)⟩
    · exact ⟨cfg_A a' c 6, step_A_b1_asucc a' c, Or.inl (in_ps_A a' c 6)⟩
  · exact ⟨cfg_A a b' (c + 3), step_A_b_ge2 a b' c, Or.inl (in_ps_A a b' (c + 3))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 3 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_A 3 0 0) := by
    unfold cfg_A
    have h3 : ([1] : List (Fin 2)) ^ 3 = [1, 1, 1] := rfl
    rw [list_pow_zero, list_pow_one, h3]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 3 0 0, init_reaches_start, in_ps_A 3 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A_all (vars 0) (vars 1) (vars 2)

/-- `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. -/
inductive State where
  /-- $A(a, b, c) := 0^\infty\,1^a\,0\,(10)^b\,0\,(11)^{c+1}\,\mathrm{B}{>}\,0^\infty$. -/
  | A (a b c : ℕ)

/-- Initial symbolic state $A(3, 0, 0)$, reached after 17 raw TM steps. -/
def start : State := .A 3 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c =>
    Cfg.headRight SixState.B
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
        (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
            (ListBlank.cons 0
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
      default

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A 0 0 _ => none
  | .A (a + 1) 0 c => some (.A a c 2)
  | .A 0 1 c => some (.A (2 * c + 9) 0 0)
  | .A (a + 1) 1 c => some (.A a c 6)
  | .A a (b + 2) c => some (.A a b (c + 3))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases b with _ | _ | b'
    · rcases a with _ | a'
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_A_b0_asucc a' c
    · rcases a with _ | a'
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_A_b1_a0 c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_A_b1_asucc a' c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_A_b_ge2 a b' c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases b with _ | _ | b'
    · rcases a with _ | a'
      · obtain ⟨cfg', hp, hh⟩ := step_A_b0_a0 c
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · rcases a with _ | a' <;> simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE
