/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`
(holdout #417, `suspect_15`; see
<https://wiki.bbchallenge.org/wiki/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB>).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$D(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,1^b\,0\,1^c\,0^\infty$$
at $D(0, 0, 1)$ in 4 steps and $D(0, 3, 1)$ in 13 steps, and every $D(a, b, c)$ advances in
`ReachesPlus` either to another $D(a', b', c')$ or to a halting configuration (when $b \equiv 0
\pmod 3$ and $c = 0$).

## Collatz-like Acceleration Rules

```text
Consider:
D(a, b, c) = 0^inf 1^{a+1} D> 1^b 0 1^c 0^inf

D(a, 0, 1)       -> D(0, a+3, 1)
D(a, 0, 2)       -> D(0, a+2, 2)
D(a, 0, c+3)     -> D(a+3, 0, c)
D(a, 2, c)       -> D(0, a, c+3)
D(a, 3k, 0)      -> Halt
D(a, 3k+3, c+1)  -> D(a+1, 3k+1, c+2)
D(a, 3k+1, 0)    -> D(a+1, 3k, 1)
D(a, 3k+1, c+1)  -> D(a+1, 3k+1, c)
D(a, 3k+5, c)    -> D(a+1, 3k+2, c+2)

Start: D(0, 3, 1), reached after 13 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

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

private theorem sweep_left_C (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight D
        (ListBlank.append [1] l)
        (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r)) := by
  have h1 := shift_C_1 k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [0] l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
        (Cfg.headRight D (ListBlank.append [1] l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
    bb_steps
  have h3 := h1.trans_plus h2
  have h_pow :
      ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
    rw [← ListBlank.append_pow_succ]
  rwa [h_pow] at h3

private theorem sweep_left_C_default (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ k) default)
        (ListBlank.append [1] r))
      (Cfg.headRight D (ListBlank.append [1] default)
        (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r)) := by
  have h := sweep_left_C k default r
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rwa [h_def] at h

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$D(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,1^b\,0\,1^c\,0^\infty$. -/
def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .rep [1] 1 (.sym 0 (.rep [1] 2 .default)) }

/-- Closed pattern set for `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .true)]

/-- Configuration $D(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,1^b\,0\,1^c\,0^\infty$. -/
private def cfg_D (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

/-- Intermediate configuration
$E(a, d, b, c) := 0^\infty\,1^{a+1}\,0\,1^{d+2}\,\mathrm{E}{>}\,1^b\,0\,1^c\,0^\infty$. -/
private def cfg_E (a d b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append [1, 1]
      (ListBlank.append (([1] : List (Fin 2)) ^ d)
        (ListBlank.append [0]
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
    (ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

private theorem eval_pat_D (vars : ℕ → ℕ) :
    evalTapePattern pat_D vars = cfg_D (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_D (a b c : ℕ) : IsInPatternSet ps (cfg_D a b c) :=
  ⟨(pat_D, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem step_D_b0_c0 (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D a 0 0) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_D a 0 0)
        (Cfg.headRight F
          (ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          default) := by
    unfold cfg_D
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

private theorem step_D_b0_c1 (a : ℕ) :
    ReachesPlus target (cfg_D a 0 1) (cfg_D 0 (a + 3) 1) := by
  have h1 :
      ReachesPlus target (cfg_D a 0 1)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
          (ListBlank.append [1]
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))) := by
    unfold cfg_D
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
      have h_add : a + 2 = 2 + a := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, list_pow_zero, list_pow_one, ListBlank.append_nil]
    bb_steps
  have h2 := sweep_left_C_default (a + 2)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
  exact h1.trans h2

private theorem step_D_b0_c2 (a : ℕ) :
    ReachesPlus target (cfg_D a 0 2) (cfg_D 0 (a + 2) 2) := by
  have h1 :
      ReachesPlus target (cfg_D a 0 2)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
          (ListBlank.append [1]
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)))) := by
    unfold cfg_D
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
      rw [ListBlank.append_pow_succ]
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_l, list_pow_zero, h_two, ListBlank.append_nil]
    bb_steps
  have h2 := sweep_left_C_default (a + 1)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
  exact h1.trans h2

private theorem step_D_b0_add3 (a c : ℕ) :
    ReachesPlus target (cfg_D a 0 (c + 3)) (cfg_D (a + 3) 0 c) := by
  unfold cfg_D
  have h_c :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
    have h_add : c + 3 = 3 + c := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h_l :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    have h_add : a + 3 = 3 + a := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_c, h_l, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_D_b1_c0 (a : ℕ) :
    ReachesPlus target (cfg_D a 1 0) (cfg_D (a + 1) 0 1) := by
  unfold cfg_D
  have h_l :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rw [h_l, list_pow_zero, list_pow_one, ListBlank.append_nil]
  bb_steps

private theorem step_D_b1_succ (a c : ℕ) :
    ReachesPlus target (cfg_D a 1 (c + 1)) (cfg_D (a + 1) 1 c) := by
  unfold cfg_D
  have h_c :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
    rw [ListBlank.append_pow_succ]
  have h_l :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rw [h_c, h_l, list_pow_one]
  bb_steps

private theorem step_D_b2 (a c : ℕ) :
    ReachesPlus target (cfg_D a 2 c) (cfg_D 0 a (c + 3)) := by
  have h_c :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
    have h_add : c + 3 = 3 + c := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rcases a with _ | a'
  · unfold cfg_D
    rw [h_c, h_two, list_pow_zero, ListBlank.append_nil]
    bb_steps
  · have h1 :
        ReachesPlus target (cfg_D (a' + 1) 2 c)
          (Cfg.headRight C
            (ListBlank.append (([1] : List (Fin 2)) ^ a') default)
            (ListBlank.append [1]
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) default)))) := by
      unfold cfg_D
      rw [h_c, h_two, ListBlank.append_pow_succ ([1] : List (Fin 2)) a']
      bb_steps
    have h2 := sweep_left_C_default a'
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3)) default))
    exact h1.trans h2

private theorem step_D_b_add3 (a b c : ℕ) :
    ReachesPlus target (cfg_D a (b + 3) c) (cfg_E a 0 b c) := by
  unfold cfg_D cfg_E
  have h_b :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ c) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))) := by
    have h_add : b + 3 = 3 + b := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_b, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_E_b0_c0 (a d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_E a d 0 0) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_E a d 0 0)
        (Cfg.headRight F
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d)
              (ListBlank.append [0, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ a) default))))
          default) := by
    unfold cfg_E
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

private theorem step_E_b0_succ (a d c : ℕ) :
    ReachesPlus target (cfg_E a d 0 (c + 1)) (cfg_D (a + 1) (d + 1) (c + 2)) := by
  have h1 :
      ReachesPlus target (cfg_E a d 0 (c + 1))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 2)) default)))) := by
    unfold cfg_E
    have h_c1 :
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
      rw [ListBlank.append_pow_succ]
    have h_c2 :
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
      have h_add : c + 2 = 2 + c := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a, h_c1, h_c2,
      list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := sweep_left_C d
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 2)) default))
  exact h1.trans h2

private theorem step_E_b1_c0 (a d : ℕ) :
    ReachesPlus target (cfg_E a d 1 0) (cfg_D (a + 1) (d + 3) 1) := by
  have h1 :
      ReachesPlus target (cfg_E a d 1 0)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 2))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)))) := by
    unfold cfg_E
    have h_d :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
              (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d)
              (ListBlank.append [0]
                (ListBlank.append [1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))) := by
      have h_add : d + 2 = 2 + d := by omega
      rw [h_add, ListBlank.append_pow_add, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
      rfl
    rw [h_d, list_pow_zero, list_pow_one, ListBlank.append_nil]
    bb_steps
  have h2 := sweep_left_C (d + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) default))
  exact h1.trans h2

private theorem step_E_b1_succ (a d c : ℕ) :
    ReachesPlus target (cfg_E a d 1 (c + 1)) (cfg_D (a + 1) (d + 4) c) := by
  have h1 :
      ReachesPlus target (cfg_E a d 1 (c + 1))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))) := by
    unfold cfg_E
    have h_d :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
              (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d)
              (ListBlank.append [0]
                (ListBlank.append [1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))) := by
      have h_add : d + 3 = 3 + d := by omega
      rw [h_add, ListBlank.append_pow_add, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
      rfl
    rw [h_d, ListBlank.append_pow_succ ([1] : List (Fin 2)) c, list_pow_one]
    bb_steps
  have h2 := sweep_left_C (d + 3)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))
  exact h1.trans h2

private theorem step_E_b2 (a d c : ℕ) :
    ReachesPlus target (cfg_E a d 2 c) (cfg_D (a + 1) (d + 2) (c + 2)) := by
  have h1 :
      ReachesPlus target (cfg_E a d 2 c)
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)))
          (ListBlank.append [1]
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (c + 2)) default)))) := by
    unfold cfg_E
    have h_d :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
              (default : ListBlank (Fin 2)))) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d)
              (ListBlank.append [0]
                (ListBlank.append [1]
                  (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))) := by
      rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d,
        ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    have h_c :
        ListBlank.append (([1] : List (Fin 2)) ^ (c + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
      have h_add : c + 2 = 2 + c := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_d, h_c, h_two]
    bb_steps
  have h2 := sweep_left_C (d + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 2)) default))
  exact h1.trans h2

private theorem step_E_b_add3 (a d b c : ℕ) :
    ReachesPlus target (cfg_E a d (b + 3) c) (cfg_E a (d + 3) b c) := by
  unfold cfg_E
  have h_b :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ c) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))) := by
    have h_add : b + 3 = 3 + b := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h_d :
      ListBlank.append [1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (d + 3))
          (ListBlank.append [0]
            (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2)))))) =
        ListBlank.append [1, 1, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append [0]
              (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))) := by
    have h_add : d + 3 = 3 + d := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_b, h_d]
  bb_steps

private theorem shift_E_b_mul3 (k a d r c : ℕ) :
    ReachesStar target (cfg_E a d (3 * k + r) c) (cfg_E a (d + 3 * k) r c) := by
  induction k generalizing d with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h_b : 3 * (k + 1) + r = (3 * k + r) + 3 := by omega
    have h_d : d + 3 * (k + 1) = (d + 3) + 3 * k := by omega
    rw [h_b, h_d]
    exact ((step_E_b_add3 a d (3 * k + r) c).trans_star (ih (d + 3))).to_star

private theorem step_D_b_3k3_c0 (a k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D a (3 * k + 3) 0) cfg' ∧ (step target cfg').isNone := by
  have h1 := step_D_b_add3 a (3 * k + 0) 0
  have h2 := shift_E_b_mul3 k a 0 0 0
  rw [Nat.zero_add] at h2
  obtain ⟨cfg', h3, h4⟩ := step_E_b0_c0 a (3 * k)
  exact ⟨cfg', (h1.trans_star h2).trans h3, h4⟩

private theorem step_D_b_3k3_succ (a k c : ℕ) :
    ReachesPlus target (cfg_D a (3 * k + 3) (c + 1)) (cfg_D (a + 1) (3 * k + 1) (c + 2)) := by
  have h1 := step_D_b_add3 a (3 * k + 0) (c + 1)
  have h2 := shift_E_b_mul3 k a 0 0 (c + 1)
  rw [Nat.zero_add] at h2
  have h3 := step_E_b0_succ a (3 * k) c
  exact (h1.trans_star h2).trans h3

private theorem step_D_b_3k4_c0 (a k : ℕ) :
    ReachesPlus target (cfg_D a (3 * k + 1 + 3) 0) (cfg_D (a + 1) (3 * k + 3) 1) := by
  have h1 := step_D_b_add3 a (3 * k + 1) 0
  have h2 := shift_E_b_mul3 k a 0 1 0
  rw [Nat.zero_add] at h2
  have h3 := step_E_b1_c0 a (3 * k)
  exact (h1.trans_star h2).trans h3

private theorem step_D_b_3k4_succ (a k c : ℕ) :
    ReachesPlus target (cfg_D a (3 * k + 1 + 3) (c + 1)) (cfg_D (a + 1) (3 * k + 4) c) := by
  have h1 := step_D_b_add3 a (3 * k + 1) (c + 1)
  have h2 := shift_E_b_mul3 k a 0 1 (c + 1)
  rw [Nat.zero_add] at h2
  have h3 := step_E_b1_succ a (3 * k) c
  exact (h1.trans_star h2).trans h3

private theorem step_D_b_3k5 (a k c : ℕ) :
    ReachesPlus target (cfg_D a (3 * k + 2 + 3) c) (cfg_D (a + 1) (3 * k + 2) (c + 2)) := by
  have h1 := step_D_b_add3 a (3 * k + 2) c
  have h2 := shift_E_b_mul3 k a 0 2 c
  rw [Nat.zero_add] at h2
  have h3 := step_E_b2 a (3 * k) c
  exact (h1.trans_star h2).trans h3

private theorem nat_mod_three (n : ℕ) :
    (∃ k, n = 3 * k) ∨ (∃ k, n = 3 * k + 1) ∨ (∃ k, n = 3 * k + 2) := by
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · exact Or.inl ⟨n / 3, by omega⟩
  · exact Or.inr (Or.inl ⟨n / 3, by omega⟩)
  · exact Or.inr (Or.inr ⟨n / 3, by omega⟩)

private theorem step_D (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | _ | b'
  · rcases c with _ | _ | _ | c'
    · obtain ⟨cfg', h1, h2⟩ := step_D_b0_c0 a
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_D 0 (a + 3) 1, step_D_b0_c1 a, Or.inl (in_ps_D 0 (a + 3) 1)⟩
    · exact ⟨cfg_D 0 (a + 2) 2, step_D_b0_c2 a, Or.inl (in_ps_D 0 (a + 2) 2)⟩
    · exact ⟨cfg_D (a + 3) 0 c', step_D_b0_add3 a c', Or.inl (in_ps_D (a + 3) 0 c')⟩
  · rcases c with _ | c'
    · exact ⟨cfg_D (a + 1) 0 1, step_D_b1_c0 a, Or.inl (in_ps_D (a + 1) 0 1)⟩
    · exact ⟨cfg_D (a + 1) 1 c', step_D_b1_succ a c', Or.inl (in_ps_D (a + 1) 1 c')⟩
  · exact ⟨cfg_D 0 a (c + 3), step_D_b2 a c, Or.inl (in_ps_D 0 a (c + 3))⟩
  · rcases nat_mod_three b' with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rcases c with _ | c'
      · obtain ⟨cfg', h1, h2⟩ := step_D_b_3k3_c0 a k
        exact ⟨cfg', h1, Or.inr h2⟩
      · exact ⟨cfg_D (a + 1) (3 * k + 1) (c' + 2), step_D_b_3k3_succ a k c',
          Or.inl (in_ps_D (a + 1) (3 * k + 1) (c' + 2))⟩
    · rcases c with _ | c'
      · exact ⟨cfg_D (a + 1) (3 * k + 3) 1, step_D_b_3k4_c0 a k,
          Or.inl (in_ps_D (a + 1) (3 * k + 3) 1)⟩
      · exact ⟨cfg_D (a + 1) (3 * k + 4) c', step_D_b_3k4_succ a k c',
          Or.inl (in_ps_D (a + 1) (3 * k + 4) c')⟩
    · exact ⟨cfg_D (a + 1) (3 * k + 2) (c + 2), step_D_b_3k5 a k c,
        Or.inl (in_ps_D (a + 1) (3 * k + 2) (c + 2))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_D 0 3 1) := by
  have h_init : ReachesPlus target (init []) (cfg_D 0 3 1) := by
    unfold cfg_D
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [list_pow_zero, list_pow_one, h3]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_D 0 3 1, init_reaches_start, in_ps_D 0 3 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_D]
  exact step_D (vars 0) (vars 1) (vars 2)

/-- `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`. -/
inductive State where
  /-- $D(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,1^b\,0\,1^c\,0^\infty$. -/
  | D (a b c : ℕ)

/-- Initial symbolic state $D(0, 3, 1)$, reached after 13 raw TM steps. -/
def start : State := .D 0 3 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b c =>
    Cfg.headRight SixState.D
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .D _ 0 0 => none
  | .D a 0 1 => some (.D 0 (a + 3) 1)
  | .D a 0 2 => some (.D 0 (a + 2) 2)
  | .D a 0 (c + 3) => some (.D (a + 3) 0 c)
  | .D a 1 0 => some (.D (a + 1) 0 1)
  | .D a 1 (c + 1) => some (.D (a + 1) 1 c)
  | .D a 2 c => some (.D 0 a (c + 3))
  | .D a (b + 3) 0 =>
    if b % 3 = 0 then none
    else if b % 3 = 1 then some (.D (a + 1) (b + 2) 1)
    else some (.D (a + 1) b 2)
  | .D a (b + 3) (c + 1) =>
    if b % 3 = 0 then some (.D (a + 1) (b + 1) (c + 2))
    else if b % 3 = 1 then some (.D (a + 1) (b + 3) c)
    else some (.D (a + 1) b (c + 3))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases b with _ | _ | _ | b'
    · rcases c with _ | _ | _ | c'
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_D_b0_c1 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_D_b0_c2 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_D_b0_add3 a c'
    · rcases c with _ | c'
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_D_b1_c0 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_D_b1_succ a c'
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_D_b2 a c
    · rcases nat_mod_three b' with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hm0 : (3 * k) % 3 = 0 := by omega
        rcases c with _ | c'
        · simp [next, hm0] at hnext
        · simp only [next, hm0, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_3k3_succ a k c'
      · have hm0 : (3 * k + 1) % 3 ≠ 0 := by omega
        have hm1 : (3 * k + 1) % 3 = 1 := by omega
        rcases c with _ | c'
        · simp only [next, hm0, ↓reduceIte] at hnext
          simp only [hm1, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_3k4_c0 a k
        · simp only [next, hm0, ↓reduceIte] at hnext
          simp only [hm1, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_3k4_succ a k c'
      · have hm0 : (3 * k + 2) % 3 ≠ 0 := by omega
        have hm1 : (3 * k + 2) % 3 ≠ 1 := by omega
        rcases c with _ | c'
        · simp only [next, hm0, hm1, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_3k5 a k 0
        · simp only [next, hm0, hm1, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_3k5 a k (c' + 1)
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases b with _ | _ | _ | b'
    · rcases c with _ | _ | _ | c'
      · obtain ⟨cfg', hp, hh⟩ := step_D_b0_c0 a
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext
    · rcases c with _ | c' <;> simp [next] at hnext
    · simp [next] at hnext
    · rcases nat_mod_three b' with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hm : (3 * k) % 3 = 0 := by omega
        rcases c with _ | c'
        · obtain ⟨cfg', hp, hh⟩ := step_D_b_3k3_c0 a k
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next, hm] at hnext
      · have hm : (3 * k + 1) % 3 = 1 := by omega
        rcases c with _ | c' <;> simp [next, hm] at hnext
      · have hm : (3 * k + 2) % 3 = 2 := by omega
        rcases c with _ | c' <;> simp [next, hm] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB
