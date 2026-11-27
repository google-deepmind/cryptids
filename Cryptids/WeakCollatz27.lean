/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz41
public import Cryptids.Semantics.WeakCollatz75

/-!
# WeakCollatz27 (`weak_collatz_27`)

The 27-state, 2-symbol Turing machine `weak_collatz_27` compresses `weak_collatz_41` (`41 → 27`
states, `-14` states / `-34.15%`; `75 → 41 → 27` overall, `-48` states / `-64.00%`) while
constructively preserving blank-tape halting equivalence (`candidate_equivalent`, proved without
`Classical.choice`).

## Compression Ideas (`41 → 27` states)

At canonical checkpoint `stageCfg x y` (`x ≥ 1`, `y ≥ 1`), the tape holds only **two** unary
blocks `0^∞  1^x  0  [1] 1^(y - 1)  0^∞` in state `24`, with **no step-counter block `1^c`**:
1. **Zero-Counter Cycle-Maximum Dovetailing**: Instead of maintaining and copying a third unary
   counter block `1^c` (`tripleCfg` + `postDecCfg` = 19 states in `weak_collatz_41`), stage `x`
   aborts and advances to `x + 1` whenever `y = 1` (exiting the trivial `{1, 2}` basin) or
   `terras y > x` (exceeding the candidate cycle maximum). Constructive finite pigeonhole shows:
   - Every nontrivial cycle `C` attains a maximum `M = max C ≥ 3` whose orbit stays inside
     `[3, M]` (`3 ≤ terras^[t] M ≤ M` for all `t`) and returns in `1 ≤ j ≤ M - 2` steps, so the
     smallest such cycle maximum halts;
   - Conversely, if stage `x ≥ 3` stayed inside `[2, x - 1]` for `x` rounds without hitting `1`,
     its iterates would repeat a periodic point `u ≥ 3` (`u = 2` hits `1` next) whose entire cycle
     lies below `x`, contradicting absence of an earlier halting cycle maximum, even if divergent
     Collatz trajectories existed.
2. **Shared `restCfg` Stage-Advance Splitter**: Both abort paths (`y = 1` via 3-state doubler
   `dblCfg`, and `z > x` via rightward `0^∞` erasure of `1^(z - x)` onto the `1^(2x)` block already
   built during `cmpCfg`) feed `0^∞ [0] 1^(2(x + 1)) 0^∞` directly into `restCfg 0 0 (x + 1)`,
   splitting `1^(2(x + 1))` into `stageCfg (x + 1) (x + 1)` with zero copy states.
3. **Zero-State Blank-Tape Warm-Up (`53/53` Active Transitions Visited)**: Starting in state `0`
   on the blank tape enters `restCfg 0 0 1` in 5 steps and naturally steps through `stageCfg 1 1`
   (`t = 18`) and `stageCfg 2 2` (`t = 56`, where `2 ↦ 1 ≠ 2` aborts at `y = 1`) into
   `stageCfg 3 3` (`t = 148`) without dedicated boot states, visiting all 53 non-halting cells by
   step 507.
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz27

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_zero nSteps_succ nSteps_reaches
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- 41-state Weak Collatz reference machine (`weak_collatz_41`). -/
abbrev reference : BundledMachine 2 := Machines.weakCollatz41.bundle

/-- 27-state Weak Collatz candidate machine (`weak_collatz_27`). -/
abbrev candidate : BundledMachine 2 := Machines.weakCollatz27.bundle

/-- The candidate as a `Machine 27 2`. -/
abbrev weakCollatz27 : Machine 27 2 := Machines.weakCollatz27

private theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

private theorem ones_zero (X : ListBlank (Fin 2)) : ones 0 X = X := rfl

private theorem ones_succ (k : ℕ) (X : ListBlank (Fin 2)) : ones (k + 1) X = (ones k X).cons 1 :=
  rfl

private theorem stepR {q q' : Fin 27} {a b : Fin 2}
    (h : weakCollatz27.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz27 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

private theorem stepL {q q' : Fin 27} {a b : Fin 2}
    (h : weakCollatz27.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz27 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table -/

private theorem tr0_0 (L R) :
    step weakCollatz27 ⟨0, ⟨0, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr0_1 (L R) :
    step weakCollatz27 ⟨0, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr1_0 (L R) :
    step weakCollatz27 ⟨1, ⟨0, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr1_1 (L R) :
    step weakCollatz27 ⟨1, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr2_0 (L R) : step weakCollatz27 ⟨2, ⟨0, L, R⟩⟩ = some ⟨3, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr2_1 (L R) :
    step weakCollatz27 ⟨2, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr3_0 (L R) : step weakCollatz27 ⟨3, ⟨0, L, R⟩⟩ = some ⟨1, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr3_1 (L R) : step weakCollatz27 ⟨3, ⟨1, L, R⟩⟩ = some ⟨3, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr4_0 (L R) :
    step weakCollatz27 ⟨4, ⟨0, L, R⟩⟩ = some ⟨22, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr4_1 (L R) : step weakCollatz27 ⟨4, ⟨1, L, R⟩⟩ = some ⟨4, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr5_0 (L R) :
    step weakCollatz27 ⟨5, ⟨0, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr5_1 (L R) :
    step weakCollatz27 ⟨5, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr6_0 (L R) : step weakCollatz27 ⟨6, ⟨0, L, R⟩⟩ = some ⟨19, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr6_1 (L R) :
    step weakCollatz27 ⟨6, ⟨1, L, R⟩⟩ = some ⟨23, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr7_0 (L R) :
    step weakCollatz27 ⟨7, ⟨0, L, R⟩⟩ = some ⟨24, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr7_1 (L R) : step weakCollatz27 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr8_0 (L R) : step weakCollatz27 ⟨8, ⟨0, L, R⟩⟩ = some ⟨3, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr8_1 (L R) :
    step weakCollatz27 ⟨8, ⟨1, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr9_0 (L R) : step weakCollatz27 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr9_1 (L R) :
    step weakCollatz27 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr10_0 (L R) : step weakCollatz27 ⟨10, ⟨0, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr10_1 (L R) : step weakCollatz27 ⟨10, ⟨1, L, R⟩⟩ = some ⟨11, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr11_0 (L R) :
    step weakCollatz27 ⟨11, ⟨0, L, R⟩⟩ = some ⟨25, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr11_1 (L R) : step weakCollatz27 ⟨11, ⟨1, L, R⟩⟩ = some ⟨12, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr12_0 (L R) :
    step weakCollatz27 ⟨12, ⟨0, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr12_1 (L R) : step weakCollatz27 ⟨12, ⟨1, L, R⟩⟩ = some ⟨12, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr13_0 (L R) :
    step weakCollatz27 ⟨13, ⟨0, L, R⟩⟩ = some ⟨26, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr13_1 (L R) :
    step weakCollatz27 ⟨13, ⟨1, L, R⟩⟩ = some ⟨24, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr14_0 (L R) :
    step weakCollatz27 ⟨14, ⟨0, L, R⟩⟩ = some ⟨25, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr14_1 (L R) :
    step weakCollatz27 ⟨14, ⟨1, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr15_0 (L R) : step weakCollatz27 ⟨15, ⟨0, L, R⟩⟩ = some ⟨13, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr15_1 (L R) : step weakCollatz27 ⟨15, ⟨1, L, R⟩⟩ = some ⟨15, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr16_0 (L R) : step weakCollatz27 ⟨16, ⟨0, L, R⟩⟩ = some ⟨18, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr16_1 (L R) : step weakCollatz27 ⟨16, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr17_0 (L R) : step weakCollatz27 ⟨17, ⟨0, L, R⟩⟩ = some ⟨20, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr17_1 (L R) : step weakCollatz27 ⟨17, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr18_0 (L R : ListBlank (Fin 2)) : step weakCollatz27 ⟨18, ⟨0, L, R⟩⟩ = none := rfl
private theorem tr18_1 (L R) :
    step weakCollatz27 ⟨18, ⟨1, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr19_0 (L R) :
    step weakCollatz27 ⟨19, ⟨0, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr19_1 (L R) : step weakCollatz27 ⟨19, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr20_0 (L R) :
    step weakCollatz27 ⟨20, ⟨0, L, R⟩⟩ = some ⟨22, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr20_1 (L R) :
    step weakCollatz27 ⟨20, ⟨1, L, R⟩⟩ = some ⟨23, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr21_0 (L R) : step weakCollatz27 ⟨21, ⟨0, L, R⟩⟩ = some ⟨25, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr21_1 (L R) :
    step weakCollatz27 ⟨21, ⟨1, L, R⟩⟩ = some ⟨21, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr22_0 (L R) :
    step weakCollatz27 ⟨22, ⟨0, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr22_1 (L R) :
    step weakCollatz27 ⟨22, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr23_0 (L R) :
    step weakCollatz27 ⟨23, ⟨0, L, R⟩⟩ = some ⟨21, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr23_1 (L R) : step weakCollatz27 ⟨23, ⟨1, L, R⟩⟩ = some ⟨4, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr24_0 (L R) :
    step weakCollatz27 ⟨24, ⟨0, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr24_1 (L R) :
    step weakCollatz27 ⟨24, ⟨1, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr25_0 (L R) : step weakCollatz27 ⟨25, ⟨0, L, R⟩⟩ = some ⟨15, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr25_1 (L R) : step weakCollatz27 ⟨25, ⟨1, L, R⟩⟩ = some ⟨26, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr26_0 (L R) : step weakCollatz27 ⟨26, ⟨0, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr26_1 (L R) : step weakCollatz27 ⟨26, ⟨1, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R

/-! ## Sweep & Reachability Combinators -/

private def reachPos (c₁ c₂ : Cfg 27 2) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ nSteps weakCollatz27 s c₁ = some c₂

private theorem reachPos_step {c₁ c₂ : Cfg 27 2}
    (h : step weakCollatz27 c₁ = some c₂) : reachPos c₁ c₂ :=
  ⟨1, le_rfl, step_one h⟩

private theorem reachPos_trans {c₁ c₂ c₃ : Cfg 27 2}
    (h₁ : reachPos c₁ c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s₁, hs₁, heq₁⟩ := h₁
  obtain ⟨s₂, hs₂, heq₂⟩ := h₂
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq heq₁ heq₂⟩

private theorem step_then_reachPos {c₁ c₂ c₃ : Cfg 27 2}
    (h₁ : step weakCollatz27 c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ :=
  reachPos_trans (reachPos_step h₁) h₂

private theorem nSteps_then_reachPos {k : ℕ} {c₁ c₂ c₃ : Cfg 27 2}
    (h₁ : nSteps weakCollatz27 k c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₂
  exact ⟨k + s, by omega, nSteps_bind_eq h₁ heq⟩

private theorem reachPos_then_nSteps {k : ℕ} {c₁ c₂ c₃ : Cfg 27 2}
    (h₁ : reachPos c₁ c₂) (h₂ : nSteps weakCollatz27 k c₂ = some c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₁
  exact ⟨s + k, by omega, nSteps_bind_eq heq h₂⟩

private theorem sweep1R {q : Fin 27}
    (h : ∀ L R, step weakCollatz27 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz27 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweep1L {q : Fin 27}
    (h : ∀ L R, step weakCollatz27 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz27 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

private theorem erase1R {q : Fin 27}
    (h : ∀ L R, step weakCollatz27 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 0) R⟩)
    (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps weakCollatz27 k ⟨q, Tape.mk' B0 (ones k R)⟩ = some ⟨q, Tape.mk' B0 R⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, B0_cons_zero, Option.bind_some, ih]

/-! ## Canonical 2-Block Checkpoint, Restoration Splitter & Doubler -/

/-- Canonical stage checkpoint: `0^∞ 1^x 0 [1] 1^(y - 1) 0^∞` in state `24`. -/
private def stageCfg (x y : ℕ) : Cfg 27 2 :=
  ⟨24, Tape.mk' ((ones x B0).cons 0) (ones y B0)⟩

/-- Restoration / even-block splitter configuration: `0^∞ 1^u 0 1^v [0] 1^(2p) 0^∞` in state `5`. -/
private def restCfg (u v p : ℕ) : Cfg 27 2 :=
  ⟨5, Tape.mk' (ones v ((ones u B0).cons 0)) ((ones (2 * p) B0).cons 0)⟩

private theorem rest_step (u v p : ℕ) :
    reachPos (restCfg u v (p + 1)) (restCfg (u + 1) (v + 1) p) := by
  unfold restCfg
  let Lu := (ones u B0).cons 0
  change reachPos ⟨5, Tape.mk' (ones v Lu) ((ones (2 * (p + 1)) B0).cons 0)⟩ _
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr5_0 _ _) ?_
  rw [show (ones v Lu).cons 1 = ones (v + 1) Lu from rfl,
    show 2 * (p + 1) = (2 * p + 1) + 1 by omega, ones_succ (2 * p + 1) B0,
    ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr6_1 _ _) ?_
  rw [show (ones (v + 1) Lu).cons 1 = ones (v + 2) Lu from rfl,
    ones_succ (2 * p) B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr23_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr4_1 (v + 2) Lu _) ?_
  dsimp only [Lu]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr4_0 _ _) ?_
  rw [← ones_succ u B0, show v + 2 = (v + 1) + 1 by omega, ones_succ (v + 1) _,
    ErdosTernary15.Tape.mk'_cons]
  have h22 : reachPos ⟨22, ⟨1, ones (u + 1) B0, ones (v + 1) ((ones (2 * p) B0).cons 0)⟩⟩
      ⟨5, Tape.mk' ((ones (u + 1) B0).cons 0) (ones (v + 1) ((ones (2 * p) B0).cons 0))⟩ :=
    reachPos_step (tr22_1 (ones (u + 1) B0) (ones (v + 1) ((ones (2 * p) B0).cons 0)))
  exact reachPos_then_nSteps h22
    (sweep1R tr5_1 (v + 1) ((ones (u + 1) B0).cons 0) ((ones (2 * p) B0).cons 0))

private theorem rest_many (u v p k : ℕ) :
    k = 0 ∨ reachPos (restCfg u v (p + k)) (restCfg (u + k) (v + k) p) := by
  induction k generalizing u v with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ?_
    rw [show p + (k + 1) = (p + k) + 1 by omega]
    have hfirst := rest_step u v (p + k)
    rcases ih (u + 1) (v + 1) with rfl | hrest
    · rw [Nat.add_zero]
      exact hfirst
    · rw [show u + (k + 1) = u + 1 + k by omega, show v + (k + 1) = v + 1 + k by omega]
      exact reachPos_trans hfirst hrest

private theorem rest_exit (x z : ℕ) :
    reachPos (restCfg x z 0) (stageCfg x z) := by
  unfold restCfg stageCfg
  let Lx := (ones x B0).cons 0
  change reachPos ⟨5, Tape.mk' (ones z Lx) ((ones (2 * 0) B0).cons 0)⟩
    ⟨24, Tape.mk' Lx (ones z B0)⟩
  rw [Nat.mul_zero, ones_zero, B0_cons_zero, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr5_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr6_0 _ _) ?_
  rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr19_1 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (sweep1L tr7_1 z Lx B0) ?_
  dsimp only [Lx]
  rw [ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr7_0 _ _)

private theorem rest_from_zero (A : ℕ) (hA : 1 ≤ A) :
    reachPos (restCfg 0 0 A) (stageCfg A A) := by
  rcases rest_many 0 0 0 A with rfl | hmany
  · exfalso; omega
  · rw [Nat.zero_add] at hmany
    exact reachPos_trans hmany (rest_exit A A)

private def dblCfg (m p : ℕ) : Cfg 27 2 :=
  ⟨1, mkL (ones m B0) ((ones (2 * p) B0).cons 0)⟩

private theorem dbl_step (m p : ℕ) :
    reachPos (dblCfg (m + 1) p) (dblCfg m (p + 1)) := by
  unfold dblCfg
  rw [ones_succ m B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr1_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr0_0 _ _) ?_
  change reachPos ⟨2, Tape.mk' (ones 1 ((ones m B0).cons 0)) (ones (2 * p) B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr2_1 (2 * p) _ B0) ?_
  rw [← ones_add (2 * p) 1 ((ones m B0).cons 0), ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr2_0 _ _) ?_
  change reachPos ⟨3, mkL (ones (2 * p + 1) ((ones m B0).cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr3_1 (2 * p + 1) _ (ones 1 B0)) ?_
  rw [← ones_add (2 * p + 1) 1 B0, show 2 * p + 1 + 1 = 2 * (p + 1) by omega,
    ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr3_0 _ _)

private theorem dbl_many (m p : ℕ) :
    m = 0 ∨ reachPos (dblCfg m p) (dblCfg 0 (p + m)) := by
  induction m generalizing p with
  | zero => exact Or.inl rfl
  | succ m ih =>
    refine Or.inr ?_
    rcases ih (p + 1) with rfl | hrest
    · rw [Nat.add_zero]
      exact dbl_step 0 p
    · rw [show p + (m + 1) = p + 1 + m by omega]
      exact reachPos_trans (dbl_step m p) hrest

private theorem stage_y1_advance (x : ℕ) (hx : 1 ≤ x) :
    reachPos (stageCfg x 1) (stageCfg (x + 1) (x + 1)) := by
  unfold stageCfg
  rw [ones_succ 0 B0, ones_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr24_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr8_0 _ _) ?_
  change reachPos ⟨3, mkL (ones 1 ((ones x B0).cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr3_1 1 ((ones x B0).cons 0) (ones 1 B0)) ?_
  rw [show ones 1 (ones 1 B0) = ones (2 * 1) B0 from rfl, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr3_0 _ _) ?_
  change reachPos (dblCfg x 1) _
  rcases dbl_many x 1 with rfl | hmany
  · exfalso; omega
  · rw [show 1 + x = x + 1 by omega] at hmany
    refine reachPos_trans hmany ?_
    unfold dblCfg
    rw [ones_zero, mkL_B0]
    refine step_then_reachPos (tr1_0 _ _) ?_
    have hrest_eq : (⟨5, Tape.mk' (B0.cons 0) ((ones (2 * (x + 1)) B0).cons 0)⟩ : Cfg 27 2) =
        restCfg 0 0 (x + 1) := by
      simp only [restCfg, ones_zero, B0_cons_zero]
    rw [hrest_eq]
    exact rest_from_zero (x + 1) (by omega)

/-! ## Zero-Gap In-Place `terras` Evaluation (`y ≥ 2`) -/

private def evenCfg (L0 : ListBlank (Fin 2)) (a b : ℕ) : Cfg 27 2 :=
  ⟨9, Tape.mk' ((ones a L0).cons 0) (ones b B0)⟩

private theorem even_step (L0 : ListBlank (Fin 2)) (a b : ℕ) :
    reachPos (evenCfg L0 a (b + 2)) (evenCfg L0 (a + 1) b) := by
  unfold evenCfg
  refine nSteps_then_reachPos (sweep1R tr9_1 (b + 2) _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr9_0 _ _) ?_
  rw [B0_cons_zero, ones_succ (b + 1) _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_1 _ _) ?_
  rw [B0_cons_zero, ones_succ b _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr11_1 _ _) ?_
  change reachPos ⟨12, mkL (ones b ((ones a L0).cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr12_1 b _ _) ?_
  rw [← ones_add b 1 B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr12_0 _ _) ?_
  rw [← ones_succ a L0, ones_succ b B0, ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr8_1 _ _)

private theorem even_many (L0 : ListBlank (Fin 2)) (a k r : ℕ) :
    k = 0 ∨ reachPos (evenCfg L0 a (2 * k + r)) (evenCfg L0 (a + k) r) := by
  induction k generalizing a with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ?_
    rw [show 2 * (k + 1) + r = (2 * k + r) + 2 by omega]
    rcases ih (a + 1) with rfl | hrest
    · rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add]
      exact even_step L0 a r
    · rw [show a + (k + 1) = (a + 1) + k by omega]
      exact reachPos_trans (even_step L0 a (2 * k + r)) hrest

private def oddCfg (L0 : ListBlank (Fin 2)) (m r : ℕ) : Cfg 27 2 :=
  ⟨13, mkL (ones m L0) ((ones r B0).cons 0)⟩

private theorem odd_step (L0 : ListBlank (Fin 2)) (m r : ℕ) :
    reachPos (oddCfg L0 (m + 1) r) (oddCfg L0 m (r + 3)) := by
  unfold oddCfg
  rw [ones_succ m L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr13_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr24_0 _ _) ?_
  change reachPos ⟨14, Tape.mk' (ones 1 ((ones m L0).cons 0)) (ones r B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr14_1 r _ B0) ?_
  rw [← ones_add r 1 ((ones m L0).cons 0), ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr14_0 _ _) ?_
  rw [← ones_succ (r + 1) _, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr25_0 _ _) ?_
  change reachPos ⟨15, mkL (ones (r + 2) ((ones m L0).cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr15_1 (r + 2) _ _) ?_
  rw [← ones_add (r + 2) 1 B0, show r + 2 + 1 = r + 3 by omega, ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr15_0 _ _)

private theorem odd_many (L0 : ListBlank (Fin 2)) (m r : ℕ) :
    m = 0 ∨ reachPos (oddCfg L0 m r) (oddCfg L0 0 (r + 3 * m)) := by
  induction m generalizing r with
  | zero => exact Or.inl rfl
  | succ m ih =>
    refine Or.inr ?_
    rcases ih (r + 3) with rfl | hrest
    · rw [Nat.zero_add, Nat.mul_one]
      exact odd_step L0 0 r
    · rw [show r + 3 * (m + 1) = r + 3 + 3 * m by omega]
      exact reachPos_trans (odd_step L0 m r) hrest

private theorem terras_pos_of_pos {y : ℕ} (hy : 1 ≤ y) : 1 ≤ terras y := by
  unfold terras
  split_ifs <;> omega

private theorem terras_eval (x y : ℕ) (hy : 2 ≤ y) :
    reachPos (stageCfg x y) ⟨17, mkL ((ones x B0).cons 0) (ones (terras y) B0)⟩ := by
  let L0 := (ones x B0).cons 0
  rcases Nat.mod_two_eq_zero_or_one y with hev | hodd
  · let k := y / 2 - 1
    have hy_eq : y = 2 * k + 2 := by dsimp [k]; omega
    have hty : terras y = k + 1 := by unfold terras; simp [hev]; dsimp [k]; omega
    rw [hty, hy_eq]
    unfold stageCfg
    change reachPos ⟨24, Tape.mk' L0 (ones (2 * k + 2) B0)⟩ ⟨17, mkL L0 (ones (k + 1) B0)⟩
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, ones_succ (2 * k + 1) B0,
      ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr24_1 _ _) ?_
    rw [ones_succ (2 * k) B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr8_1 _ _) ?_
    change reachPos (evenCfg L0 1 (2 * k + 0)) _
    have hev_end : reachPos (evenCfg L0 (k + 1) 0) ⟨17, mkL L0 (ones (k + 1) B0)⟩ := by
      unfold evenCfg
      rw [ones_zero, ErdosTernary15.Tape.mk'_B0]
      refine step_then_reachPos (tr9_0 _ _) ?_
      rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
      refine step_then_reachPos (tr10_0 _ _) ?_
      rw [B0_cons_zero, ones_succ k L0, ErdosTernary15.Tape.mkL_cons]
      have h16 : reachPos ⟨16, ⟨1, ones k L0, B0⟩⟩ ⟨17, mkL (ones k L0) (ones 1 B0)⟩ :=
        reachPos_step (tr16_1 (ones k L0) B0)
      have hsw := sweep1L tr17_1 k L0 (ones 1 B0)
      rw [← ones_add k 1 B0] at hsw
      exact reachPos_then_nSteps h16 hsw
    rcases even_many L0 1 k 0 with hk0 | hmany
    · rw [hk0] at hev_end ⊢
      exact hev_end
    · rw [show 1 + k = k + 1 by omega] at hmany
      exact reachPos_trans hmany hev_end
  · let k' := y / 2 - 1
    have hy_eq : y = 2 * (k' + 1) + 1 := by dsimp [k']; omega
    have hty : terras y = 3 * (k' + 1) + 2 := by
      unfold terras
      have hne : ¬ (y % 2 = 0) := by omega
      simp [hne]; dsimp [k']; omega
    rw [hty, hy_eq]
    unfold stageCfg
    change reachPos ⟨24, Tape.mk' L0 (ones (2 * (k' + 1) + 1) B0)⟩
      ⟨17, mkL L0 (ones (3 * (k' + 1) + 2) B0)⟩
    rw [show 2 * (k' + 1) + 1 = (2 * k' + 2) + 1 by omega,
      ones_succ (2 * k' + 2) B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr24_1 _ _) ?_
    rw [show 2 * k' + 2 = (2 * k' + 1) + 1 by omega,
      ones_succ (2 * k' + 1) B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr8_1 _ _) ?_
    change reachPos (evenCfg L0 1 (2 * k' + 1)) _
    have hto_odd : reachPos (evenCfg L0 (k' + 1) 1) (oddCfg L0 (k' + 1) 1) := by
      unfold evenCfg oddCfg
      refine nSteps_then_reachPos (sweep1R tr9_1 1 _ B0) ?_
      rw [ErdosTernary15.Tape.mk'_B0]
      refine step_then_reachPos (tr9_0 _ _) ?_
      rw [B0_cons_zero, ones_succ 0 _, ErdosTernary15.Tape.mkL_cons]
      refine step_then_reachPos (tr10_1 _ _) ?_
      rw [B0_cons_zero, ones_zero, ErdosTernary15.Tape.mkL_cons]
      refine step_then_reachPos (tr11_0 _ _) ?_
      rw [ErdosTernary15.Tape.mk'_B0]
      refine step_then_reachPos (tr25_0 _ _) ?_
      rw [ErdosTernary15.Tape.mkL_cons]
      exact reachPos_step (tr15_0 _ _)
    have hev_part : reachPos (evenCfg L0 1 (2 * k' + 1)) (oddCfg L0 (k' + 1) 1) := by
      rcases even_many L0 1 k' 1 with hk0 | hmany
      · rw [hk0] at hto_odd ⊢
        exact hto_odd
      · rw [show 1 + k' = k' + 1 by omega] at hmany
        exact reachPos_trans hmany hto_odd
    refine reachPos_trans hev_part ?_
    rcases odd_many L0 (k' + 1) 1 with h0 | hmany
    · exfalso; omega
    · refine reachPos_trans hmany ?_
      unfold oddCfg
      rw [ones_zero]
      dsimp only [L0]
      rw [ErdosTernary15.Tape.mkL_cons]
      refine step_then_reachPos (tr13_0 _ _) ?_
      rw [ErdosTernary15.Tape.mk'_cons]
      have hstep := tr26_0 ((ones x B0).cons 0) (ones (1 + 3 * (k' + 1)) B0)
      rw [← ones_succ (1 + 3 * (k' + 1)) B0,
        show 1 + 3 * (k' + 1) + 1 = 3 * (k' + 1) + 2 by omega] at hstep
      exact reachPos_step hstep

/-! ## Local `2p` Comparison, Cycle Halt & `z > x` Stage Advance -/

private def cmpCfg (u v p : ℕ) : Cfg 27 2 :=
  ⟨16, mkL (ones v ((ones u B0).cons 0)) ((ones (2 * p) B0).cons 0)⟩

private theorem cmpFrom17 (u v p : ℕ) :
    reachPos ⟨17, mkL ((ones (u + 1) B0).cons 0) (ones (v + 1) ((ones (2 * p) B0).cons 0))⟩
      (cmpCfg u v (p + 1)) := by
  let Lu := (ones u B0).cons 0
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr17_0 _ _) ?_
  rw [ones_succ u B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr20_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr23_0 _ _) ?_
  change reachPos ⟨21, Tape.mk' (ones 1 Lu) (ones (v + 1) ((ones (2 * p) B0).cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr21_1 (v + 1) (ones 1 Lu) _) ?_
  rw [← ones_add (v + 1) 1 Lu, show v + 1 + 1 = v + 2 by omega, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr21_0 _ _) ?_
  rw [show (ones (2 * p) B0).cons 1 = ones (2 * p + 1) B0 from rfl,
    show v + 2 = (v + 1) + 1 by omega, ones_succ (v + 1) Lu, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr25_1 _ _) ?_
  rw [← ones_succ (2 * p + 1) B0, ones_succ v Lu, ErdosTernary15.Tape.mkL_cons]
  have h26 := tr26_1 (ones v Lu) (ones (2 * p + 2) B0)
  rw [show 2 * p + 2 = 2 * (p + 1) by omega] at h26
  exact reachPos_step h26

private theorem terras_to_cmp1 (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    reachPos (stageCfg x y) (cmpCfg (x - 1) (terras y - 1) 1) := by
  have hz : 1 ≤ terras y := terras_pos_of_pos (by omega)
  have heval := terras_eval x y hy
  have htarget : (⟨17, mkL ((ones x B0).cons 0) (ones (terras y) B0)⟩ : Cfg 27 2) =
      ⟨17, mkL ((ones ((x - 1) + 1) B0).cons 0)
        (ones ((terras y - 1) + 1) ((ones (2 * 0) B0).cons 0))⟩ := by
    rw [show (x - 1) + 1 = x by omega, show (terras y - 1) + 1 = terras y by omega,
      Nat.mul_zero, ones_zero, B0_cons_zero]
  rw [htarget] at heval
  exact reachPos_trans heval (cmpFrom17 (x - 1) (terras y - 1) 0)

private theorem cmp_step (u v p : ℕ) :
    reachPos (cmpCfg (u + 1) (v + 1) p) (cmpCfg u v (p + 1)) := by
  unfold cmpCfg
  let Lu1 := (ones (u + 1) B0).cons 0
  let Rp := (ones (2 * p) B0).cons 0
  change reachPos ⟨16, mkL (ones (v + 1) Lu1) Rp⟩ _
  rw [ones_succ v Lu1, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr16_1 _ _) ?_
  change reachPos ⟨17, mkL (ones v Lu1) (ones 1 Rp)⟩ _
  refine nSteps_then_reachPos (sweep1L tr17_1 v Lu1 (ones 1 Rp)) ?_
  rw [← ones_add v 1 Rp]
  exact cmpFrom17 u v p

private theorem cmp_many (u v p k : ℕ) :
    k = 0 ∨ reachPos (cmpCfg (u + k) (v + k) p) (cmpCfg u v (p + k)) := by
  induction k generalizing u v p with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ?_
    rw [show u + (k + 1) = (u + k) + 1 by omega, show v + (k + 1) = (v + k) + 1 by omega]
    rcases ih u v (p + 1) with rfl | hrest
    · rw [Nat.add_zero]
      exact cmp_step u v p
    · rw [show p + 1 + k = p + (k + 1) by omega] at hrest
      exact reachPos_trans (cmp_step (u + k) (v + k) p) hrest

private theorem cmp_halt_eq (p : ℕ) :
    ∃ s cfg, nSteps weakCollatz27 s (cmpCfg 0 0 p) = some cfg ∧
      step weakCollatz27 cfg = none := by
  unfold cmpCfg
  rw [ones_zero, ones_zero, B0_cons_zero, mkL_B0]
  have h1 := tr16_0 B0 ((ones (2 * p) B0).cons 0)
  rw [mkL_B0] at h1
  exact ⟨1, _, step_one h1, tr18_0 _ _⟩

private theorem cmp_lt_to_rest (u p : ℕ) :
    reachPos (cmpCfg (u + 1) 0 p) (restCfg (u + 1) 0 p) := by
  unfold cmpCfg restCfg
  rw [ones_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr16_0 _ _) ?_
  rw [ones_succ u B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr18_1 _ _) ?_
  rw [← ones_succ u B0, ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr19_0 _ _)

private theorem cmp_gt_advance (v x : ℕ) (hx : 1 ≤ x) :
    reachPos (cmpCfg 0 (v + 1) x) (stageCfg (x + 1) (x + 1)) := by
  unfold cmpCfg
  let Rx := (ones (2 * x) B0).cons 0
  change reachPos ⟨16, mkL (ones (v + 1) ((ones 0 B0).cons 0)) Rx⟩ _
  rw [ones_zero, B0_cons_zero, ones_succ v B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr16_1 _ _) ?_
  change reachPos ⟨17, mkL (ones v B0) (ones 1 Rx)⟩ _
  refine nSteps_then_reachPos (sweep1L tr17_1 v B0 (ones 1 Rx)) ?_
  rw [← ones_add v 1 Rx, mkL_B0]
  refine step_then_reachPos (tr17_0 _ _) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr20_0 _ _) ?_
  rw [B0_cons_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr22_0 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (erase1R tr0_1 (v + 1) Rx) ?_
  dsimp only [Rx]
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr0_0 _ _) ?_
  change reachPos ⟨2, Tape.mk' (ones 1 B0) (ones (2 * x) B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr2_1 (2 * x) (ones 1 B0) B0) ?_
  rw [← ones_add (2 * x) 1 B0, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr2_0 _ _) ?_
  change reachPos ⟨3, mkL (ones (2 * x + 1) B0) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr3_1 (2 * x + 1) B0 (ones 1 B0)) ?_
  rw [← ones_add (2 * x + 1) 1 B0, show 2 * x + 1 + 1 = 2 * (x + 1) by omega, mkL_B0]
  refine step_then_reachPos (tr3_0 _ _) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr1_0 _ _) ?_
  have hrest_eq : (⟨5, Tape.mk' (B0.cons 0) ((ones (2 * (x + 1)) B0).cons 0)⟩ : Cfg 27 2) =
      restCfg 0 0 (x + 1) := by
    simp only [restCfg, ones_zero, B0_cons_zero]
  rw [hrest_eq]
  exact rest_from_zero (x + 1) (by omega)

/-! ## Blank-Tape Warm-Up & Round Outcomes -/

private theorem stage_round_halt (x y : ℕ) (hx : 3 ≤ x) (hy : 2 ≤ y) (hhit : terras y = x) :
    ∃ s cfg, nSteps weakCollatz27 s (stageCfg x y) = some cfg ∧
      step weakCollatz27 cfg = none := by
  have hcmp1 := terras_to_cmp1 x y (by omega) hy
  rw [hhit] at hcmp1
  have hmany : reachPos (cmpCfg (x - 1) (x - 1) 1) (cmpCfg 0 0 x) := by
    rcases cmp_many 0 0 1 (x - 1) with h0 | hp
    · exfalso; omega
    · rw [Nat.zero_add, show 1 + (x - 1) = x by omega] at hp
      exact hp
  obtain ⟨s₁, _, hs₁⟩ := reachPos_trans hcmp1 hmany
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := cmp_halt_eq x
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

private theorem stage_round_lt (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hlt : terras y < x) :
    reachPos (stageCfg x y) (stageCfg x (terras y)) := by
  let z := terras y
  have hz : 1 ≤ z := terras_pos_of_pos (by omega)
  refine reachPos_trans (terras_to_cmp1 x y hx hy) ?_
  let q := z - 1
  let uRem := x - z - 1
  have hsub_x : x - 1 = (uRem + 1) + q := by dsimp [uRem, q]; omega
  have hsub_z : z - 1 = 0 + q := by dsimp [q]; omega
  rw [hsub_x, hsub_z]
  have hmid : reachPos (cmpCfg ((uRem + 1) + q) (0 + q) 1) (restCfg (uRem + 1) 0 (q + 1)) := by
    rcases cmp_many (uRem + 1) 0 1 q with hq0 | hp
    · rw [hq0, Nat.add_zero, Nat.add_zero]
      exact cmp_lt_to_rest uRem 1
    · rw [show 1 + q = q + 1 by omega] at hp
      exact reachPos_trans hp (cmp_lt_to_rest uRem (q + 1))
  rcases rest_many (uRem + 1) 0 0 (q + 1) with h0 | hrm
  · exfalso; omega
  · have hrm' : reachPos (restCfg (uRem + 1) 0 (q + 1)) (restCfg x z 0) := by
      have heq1 : 0 + (q + 1) = q + 1 := Nat.zero_add (q + 1)
      have heq2 : uRem + 1 + (q + 1) = x := by dsimp [uRem, q]; omega
      have heq3 : q + 1 = z := by dsimp [q]; omega
      rw [heq1, heq2] at hrm
      have hfin_eq : restCfg x (q + 1) 0 = restCfg x z 0 := by rw [heq3]
      rw [← hfin_eq]
      exact hrm
    exact reachPos_trans hmid (reachPos_trans hrm' (rest_exit x z))

private theorem stage_round_gt (x y : ℕ) (hx : 3 ≤ x) (hy : 2 ≤ y) (hgt : x < terras y) :
    reachPos (stageCfg x y) (stageCfg (x + 1) (x + 1)) := by
  let z := terras y
  refine reachPos_trans (terras_to_cmp1 x y (by omega) hy) ?_
  let q := x - 1
  let vRem := z - x - 1
  have hsub_x : x - 1 = 0 + q := by dsimp [q]; omega
  have hsub_z : z - 1 = (vRem + 1) + q := by dsimp [vRem, q]; omega
  rw [hsub_x, hsub_z]
  rcases cmp_many 0 (vRem + 1) 1 q with hq0 | hp
  · exfalso; dsimp [q] at hq0; omega
  · rw [show 1 + q = x by dsimp [q]; omega] at hp
    exact reachPos_trans hp (cmp_gt_advance vRem x (by omega))

private theorem boot_to_rest1 : reachPos init (restCfg 0 0 1) := by
  refine ⟨5, by decide, ?_⟩
  change nSteps weakCollatz27 5 ⟨0, ⟨0, B0, B0⟩⟩ = some (restCfg 0 0 1)
  simp only [restCfg, Nat.mul_one, ones_succ, ones_zero, nSteps_succ, nSteps_zero,
    Option.bind_some, tr0_0, tr2_0, tr3_1, tr3_0, tr1_0,
    ErdosTernary15.Tape.mkL_cons, ErdosTernary15.Tape.mk'_B0, B0_cons_zero, mkL_B0]

private theorem init_reaches_stage3 : reachPos init (stageCfg 3 3) := by
  have h1 : reachPos init (stageCfg 1 1) :=
    reachPos_trans boot_to_rest1 (rest_from_zero 1 le_rfl)
  have h2 : reachPos (stageCfg 1 1) (stageCfg 2 2) := stage_y1_advance 1 le_rfl
  have ht2 : terras 2 = 1 := rfl
  have h21 : reachPos (stageCfg 2 2) (stageCfg 2 1) := by
    have hlt := stage_round_lt 2 2 le_rfl le_rfl (by rw [ht2]; decide)
    rw [ht2] at hlt
    exact hlt
  have h3 : reachPos (stageCfg 2 1) (stageCfg 3 3) := stage_y1_advance 2 (by decide)
  exact reachPos_trans h1 (reachPos_trans h2 (reachPos_trans h21 h3))

/-! ## Cycle-Maximum Dovetailing & Halting Equivalence -/

private theorem terras_iterate_pos {y : ℕ} (hy : 1 ≤ y) (m : ℕ) : 1 ≤ terras^[m] y := by
  induction m generalizing y with
  | zero => exact hy
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (terras_pos_of_pos hy)

private def StepContinues (x t : ℕ) : Prop :=
  2 ≤ terras^[t] x ∧ terras^[t] x < x

private def StayIn (x m : ℕ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ m → StepContinues x t

private theorem stayIn_or_first_exit (x m : ℕ) :
    StayIn x m ∨ ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ StayIn x (t - 1) ∧ ¬ StepContinues x t := by
  induction m with
  | zero => exact Or.inl fun t ht1 ht0 => absurd (le_trans ht1 ht0) (by decide)
  | succ m ih =>
    rcases ih with hstay | ⟨t, ht1, htm, hprev, hexit⟩
    · by_cases hstep : 2 ≤ terras^[m + 1] x ∧ terras^[m + 1] x < x
      · refine Or.inl fun t ht1 htm1 => ?_
        rcases Nat.lt_or_ge t (m + 1) with hlt | hge
        · exact hstay t ht1 (by omega)
        · rw [show t = m + 1 by omega]; exact hstep
      · exact Or.inr ⟨m + 1, by omega, le_rfl, hstay, hstep⟩
    · exact Or.inr ⟨t, ht1, by omega, hprev, hexit⟩

private theorem stage_stay_reach (x : ℕ) (hx : 3 ≤ x) (m : ℕ) (hstay : StayIn x m) :
    m = 0 ∨ (1 ≤ m ∧ reachPos (stageCfg x x) (stageCfg x (terras^[m] x))) := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    refine Or.inr ⟨by omega, ?_⟩
    have hstep : StepContinues x (m + 1) := hstay (m + 1) (by omega) le_rfl
    rcases ih (fun t ht1 htm => hstay t ht1 (by omega)) with rfl | ⟨hm1, hprev⟩
    · have hlt1 : terras x < x := by
        have h1 : terras x = terras^[1] x := rfl
        rw [h1]
        exact hstep.2
      rw [Function.iterate_one]
      exact stage_round_lt x x (by omega) (by omega) hlt1
    · have hym : 2 ≤ terras^[m] x := (hstay m hm1 (by omega)).1
      have hlt : terras (terras^[m] x) < x := by
        rw [← Function.iterate_succ_apply' terras m x]
        exact hstep.2
      rw [Function.iterate_succ_apply']
      exact reachPos_trans hprev (stage_round_lt x (terras^[m] x) (by omega) hym hlt)

private def StageHalts (x : ℕ) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ t ≤ x ∧ StayIn x (t - 1) ∧ terras^[t] x = x

private theorem stageHalts_decidable (x : ℕ) : StageHalts x ∨ ¬ StageHalts x := by
  rcases stayIn_or_first_exit x x with hstay | ⟨t, ht1, htx, hprev, hexit⟩
  · refine Or.inr ?_
    rintro ⟨t, ht1, htx, _, hhit⟩
    have hlt := (hstay t ht1 htx).2
    omega
  · by_cases hhit : terras^[t] x = x
    · exact Or.inl ⟨t, ht1, htx, hprev, hhit⟩
    · refine Or.inr ?_
      rintro ⟨t', ht'1, ht'x, hprev', hhit'⟩
      rcases Nat.lt_trichotomy t' t with hlt | rfl | hgt
      · have hlt_x := (hprev t' ht'1 (by omega)).2
        omega
      · exact hhit hhit'
      · have hcont : StepContinues x t := hprev' t ht1 (by omega)
        exact hexit hcont

private theorem stageHalts_of_cycle_max {M j : ℕ} (_hM3 : 3 ≤ M) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (hcyc : terras^[j] M = M) (hbnd : ∀ t : ℕ, 3 ≤ terras^[t] M ∧ terras^[t] M ≤ M) :
    StageHalts M := by
  rcases stayIn_or_first_exit M j with hstay | ⟨t, ht1, htj, hprev, hexit⟩
  · exfalso
    have hlt := (hstay j hj1 le_rfl).2
    omega
  · refine ⟨t, ht1, by omega, hprev, ?_⟩
    have ht_bnd := hbnd t
    by_cases hhit : terras^[t] M = M
    · exact hhit
    · exfalso
      exact hexit ⟨by omega, by omega⟩

private def NoStageHalts (X : ℕ) : Prop :=
  ∀ w : ℕ, 3 ≤ w → w ≤ X → ¬ StageHalts w

private theorem noStageHalts_or_first (X : ℕ) :
    NoStageHalts X ∨
      ∃ w : ℕ, 3 ≤ w ∧ w ≤ X ∧ NoStageHalts (w - 1) ∧ StageHalts w := by
  induction X with
  | zero => exact Or.inl fun w hw3 hw0 => absurd (le_trans hw3 hw0) (by decide)
  | succ X ih =>
    rcases ih with hno | ⟨w, hw3, hwX, hprev, hhalt⟩
    · by_cases hw3 : 3 ≤ X + 1
      · rcases stageHalts_decidable (X + 1) with hhalt | hnhalt
        · exact Or.inr ⟨X + 1, hw3, le_rfl, hno, hhalt⟩
        · refine Or.inl fun w hw_ge3 hw_le => ?_
          rcases Nat.lt_or_ge w (X + 1) with hlt | hge
          · exact hno w hw_ge3 (by omega)
          · rw [show w = X + 1 by omega]; exact hnhalt
      · exact Or.inl fun w hw_ge3 hw_le => absurd (le_trans hw_ge3 hw_le) hw3
    · exact Or.inr ⟨w, hw3, by omega, hprev, hhalt⟩

private theorem not_stayIn_self_of_noStageHalts {x : ℕ} (hx : 3 ≤ x)
    (hno : NoStageHalts (x - 1)) : ¬ StayIn x x := by
  intro hstay
  let N := x - 3
  let f : ℕ → ℕ := fun i => terras^[i + 1] x - 2
  have hf_lt : ∀ i : ℕ, i ≤ N + 1 → f i < N + 1 := by
    intro i hi
    have hs : StepContinues x (i + 1) := hstay (i + 1) (by omega) (by dsimp only [N] at hi; omega)
    have hge2 := hs.1
    have hlt_x := hs.2
    dsimp only [f, N]
    omega
  rcases WeakCollatz75.nat_pigeonhole_constructive N f hf_lt with ⟨a, b, hab, hb_le, hfab⟩
  have ha_step : StepContinues x (a + 1) :=
    hstay (a + 1) (by omega) (by dsimp only [N] at hb_le; omega)
  have hb_step : StepContinues x (b + 1) :=
    hstay (b + 1) (by omega) (by dsimp only [N] at hb_le; omega)
  have hab_eq : terras^[a + 1] x = terras^[b + 1] x := by
    have ha2 := ha_step.1
    have hb2 := hb_step.1
    dsimp only [f] at hfab
    omega
  let u := terras^[a + 1] x
  have hu3 : 3 ≤ u := by
    have ha2_step : StepContinues x (a + 2) :=
      hstay (a + 2) (by omega) (by dsimp only [N] at hb_le; omega)
    have hnext : terras u = terras^[a + 2] x :=
      (Function.iterate_succ_apply' terras (a + 1) x).symm
    have hge2 : 2 ≤ terras u := by rw [hnext]; exact ha2_step.1
    have hu_ge2 : 2 ≤ u := ha_step.1
    by_cases hu_eq2 : u = 2
    · exfalso
      rw [hu_eq2, show terras 2 = 1 from rfl] at hge2
      omega
    · omega
  let k := b - a
  have hk1 : 1 ≤ k := by dsimp only [k]; omega
  have hu_cyc : terras^[k] u = u := by
    dsimp only [u]
    rw [← Function.iterate_add_apply, show k + (a + 1) = b + 1 by dsimp only [k]; omega]
    exact hab_eq.symm
  rcases WeakCollatz75.exists_bounded_cycle_max hu3 hk1 hu_cyc with
    ⟨M, j, hM3, hj1, hjM, hj_cyc, hbnd, ⟨i, hik, hi_M⟩⟩
  have hM_lt_x : M < x := by
    have hidx_le : i + (a + 1) ≤ x := by dsimp only [k, N] at hik hb_le; omega
    have hM_eq : M = terras^[i + (a + 1)] x := by
      rw [← hi_M]
      dsimp only [u]
      rw [← Function.iterate_add_apply]
    rw [hM_eq]
    exact (hstay (i + (a + 1)) (by omega) hidx_le).2
  have hM_halts : StageHalts M := stageHalts_of_cycle_max hM3 hj1 (by omega) hj_cyc hbnd
  exact hno M hM3 (by omega) hM_halts

private theorem stage_advance_of_noStageHalts (x : ℕ) (hx : 3 ≤ x) (hno : NoStageHalts x) :
    reachPos (stageCfg x x) (stageCfg (x + 1) (x + 1)) := by
  rcases stayIn_or_first_exit x x with hstay | ⟨t, ht1, htx, hprev, hexit⟩
  · exfalso
    exact not_stayIn_self_of_noStageHalts hx (fun w hw3 hwx => hno w hw3 (by omega)) hstay
  · have hnot_halt : ¬ StageHalts x := hno x hx le_rfl
    have hne_x : terras^[t] x ≠ x := fun hhit => hnot_halt ⟨t, ht1, htx, hprev, hhit⟩
    have ht_pos : 1 ≤ terras^[t] x := terras_iterate_pos (by omega) t
    have hor : terras^[t] x = 1 ∨ x < terras^[t] x := by
      by_cases h1 : terras^[t] x = 1
      · exact Or.inl h1
      · refine Or.inr ?_
        by_cases hlt : terras^[t] x < x
        · exfalso; exact hexit ⟨by omega, hlt⟩
        · omega
    rcases stage_stay_reach x hx (t - 1) hprev with ht0 | ⟨ht1_pos, hreach_prev⟩
    · have ht_eq1 : t = 1 := by omega
      subst ht_eq1
      rw [Function.iterate_one] at hor
      rcases hor with h1 | hgt
      · have hlt := stage_round_lt x x (by omega) (by omega) (by omega)
        rw [h1] at hlt
        exact reachPos_trans hlt (stage_y1_advance x (by omega))
      · exact stage_round_gt x x hx (by omega) hgt
    · have hy_prev : 2 ≤ terras^[t - 1] x := (hprev (t - 1) ht1_pos le_rfl).1
      have hnext : terras (terras^[t - 1] x) = terras^[t] x := by
        rw [← Function.iterate_succ_apply' terras (t - 1) x, show (t - 1).succ = t by omega]
      rcases hor with h1 | hgt
      · have hlt := stage_round_lt x (terras^[t - 1] x) (by omega) hy_prev (by rw [hnext]; omega)
        rw [hnext, h1] at hlt
        exact reachPos_trans hreach_prev (reachPos_trans hlt (stage_y1_advance x (by omega)))
      · rw [← hnext] at hgt
        exact reachPos_trans hreach_prev (stage_round_gt x (terras^[t - 1] x) hx hy_prev hgt)

private theorem reach_stage_from_init (X : ℕ) (hX : 3 ≤ X) (hno : NoStageHalts (X - 1)) :
    ∃ s : ℕ, X - 2 ≤ s ∧ nSteps weakCollatz27 s init = some (stageCfg X X) := by
  induction X, hX using Nat.le_induction with
  | base =>
    obtain ⟨s, hs1, hs⟩ := init_reaches_stage3
    exact ⟨s, by omega, hs⟩
  | succ X hX ih =>
    obtain ⟨s₁, hs₁_ge, hs₁⟩ := ih fun w hw3 hw_le => hno w hw3 (by omega)
    obtain ⟨s₂, hs₂_pos, hs₂⟩ :=
      stage_advance_of_noStageHalts X hX fun w hw3 hw_le => hno w hw3 (by omega)
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

private theorem stage_halt_of_stageHalts (x : ℕ) (hx : 3 ≤ x) (hhalt : StageHalts x) :
    ∃ s cfg, nSteps weakCollatz27 s (stageCfg x x) = some cfg ∧
      step weakCollatz27 cfg = none := by
  obtain ⟨t, ht1, _, hprev, hhit⟩ := hhalt
  rcases stage_stay_reach x hx (t - 1) hprev with ht0 | ⟨ht1_pos, hreach_prev⟩
  · have ht_eq1 : t = 1 := by omega
    subst ht_eq1
    rw [Function.iterate_one] at hhit
    exact stage_round_halt x x hx (by omega) hhit
  · obtain ⟨s₁, _, hs₁⟩ := hreach_prev
    have hy_prev : 2 ≤ terras^[t - 1] x := (hprev (t - 1) ht1_pos le_rfl).1
    have hhit' : terras (terras^[t - 1] x) = x := by
      rw [← Function.iterate_succ_apply' terras (t - 1) x, show (t - 1).succ = t by omega]
      exact hhit
    obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_round_halt x (terras^[t - 1] x) hx hy_prev hhit'
    exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-- The 27-state machine `weakCollatz27` (`weak_collatz_27`) halts on the blank tape if and only if
there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(constructive, zero `Classical.choice`). -/
theorem halts_weakCollatz27_iff_bounded_cycle :
    ConjectureMachines.Halts weakCollatz27 ↔
      ∃ x j : ℕ, 3 ≤ x ∧ 1 ≤ j ∧ j ≤ x ∧ terras^[j] x = x := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases noStageHalts_or_first (k + 3) with hno | ⟨w, hw3, -, -, ⟨t, ht1, htw, -, hhit⟩⟩
    · obtain ⟨s, hks, hs⟩ := reach_stage_from_init (k + 3) (by omega)
        (fun w hw3 hw_le => hno w hw3 (by omega))
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
    · exact ⟨w, t, hw3, ht1, htw, hhit⟩
  · rintro ⟨x, j, hx3, hj1, _, hhit⟩
    rcases WeakCollatz75.exists_bounded_cycle_max hx3 hj1 hhit with
      ⟨M, jM, hM3, hjM1, hjMM, hjM_cyc, hbnd, -⟩
    have hM_halts : StageHalts M :=
      stageHalts_of_cycle_max hM3 hjM1 (by omega) hjM_cyc hbnd
    rcases noStageHalts_or_first M with hno | ⟨w₀, hw₀3, -, hprev₀, hhalt₀⟩
    · exfalso
      exact hno M hM3 le_rfl hM_halts
    · obtain ⟨s₁, -, hs₁⟩ := reach_stage_from_init w₀ hw₀3 hprev₀
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt_of_stageHalts w₀ hw₀3 hhalt₀
      rw [Part.dom_iff_mem]
      exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches (nSteps_bind_eq hs₁ hs₂), hnone⟩⟩

/-- The 27-state candidate machine halts on the blank tape if and only if the 41-state reference
machine does (constructive, zero `Classical.choice`). -/
theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  halts_weakCollatz27_iff_bounded_cycle.trans
    WeakCollatz41.halts_weakCollatz41_iff_bounded_cycle.symm

/-- The candidate has 14 fewer states than the 41-state reference (`27 < 41`). -/
theorem candidate_fewer_states : candidate.states < reference.states := by
  decide +kernel

end ConjectureMachines.WeakCollatz27
