/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz16
public import Cryptids.Semantics.WeakCollatz75

/-!
# WeakCollatz15 (`weak_collatz_15`)

The 15-state, 2-symbol Turing machine `weak_collatz_15` compresses `weak_collatz_16` (`16 → 15`
states, `-1` state / `-6.25%`; `75 → 41 → 27 → 17 → 16 → 15` overall, `-60` states / `-80.00%`)
while constructively preserving blank-tape halting equivalence (`candidate_equivalent`, proved
without `Classical.choice`).

## Compression Ideas (`16 → 15` states)

`weak_collatz_15` replaces `weak_collatz_16`'s inward parity-squeeze + 2-step odd decrement with a
**Parity-Back + Left-to-Right Pair-Eater** architecture under the shifted conservation law
`d + n = x - 1` (`n = y - 1`, `0^∞ 1^d 0 1^n 0^∞`):
1. **Shifted Encoding (`n = y - 1`) & Zero-State `y = 2` Abort**: Every `terras` step from `y ≥ 3`
   satisfies `terras y ≥ 2`, so aborting at `y = 2` (`n = 1`) makes `y = 1` unreachable. Under
   `n = y - 1`, `y = 2` is the unique input where `L1` (state `1`) reads `0`, jumping directly into
   `GT_SW` (`1(0) = 1R12`) to advance `x ↦ x + 2` with zero abort-detection state.
2. **Parity-Back Sweep (`states 5, 6`)**: Alternating states `5` (`PAR_E`) and `6` (`PAR_O`) sweep
   left across `1^n` after every step, computing `n mod 2` while returning to the separator `0`.
   For even `x`, a cycle return `z = x` has odd `n = x - 1` and `d = 0`, halting at `6 → 14(0)`.
3. **Left-to-Right Pair-Eater & 1-Step Odd Decrement**: The even loop (`states 0–4`,
   `L += 1, M += 1, R -= 2`) leaves `1^(d + k) 0 1^(k - 1)` in place with no shift-back sweeper,
   while the odd loop (`states 7–11`, `L -= 1, M += 3, R -= 2`) needs only a single decrement state
   `O_P1` (state `10`).
4. **6-Step Blank-Tape Boot**: Starting in state `0` (`L_SW`) on the all-blank tape enters
   `stageCfg 4` (`0^∞ 0 [1] 1 1 0^∞` in state `3`) at `t = 6` (`29/29` active cells visited by
   step `93`).
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz15

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_succ nSteps_reaches
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- 16-state Weak Collatz reference machine (`weak_collatz_16`). -/
abbrev reference : BundledMachine 2 := Machines.weakCollatz16.bundle

/-- 15-state Weak Collatz candidate machine (`weak_collatz_15`). -/
abbrev candidate : BundledMachine 2 := Machines.weakCollatz15.bundle

/-- The candidate as a `Machine 15 2`. -/
abbrev weakCollatz15 : Machine 15 2 := Machines.weakCollatz15

private theorem mk'_B0 (L : ListBlank (Fin 2)) : Tape.mk' L B0 = ⟨0, L, B0⟩ := rfl

private theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

private theorem ones_zero (X : ListBlank (Fin 2)) : ones 0 X = X := rfl

private theorem ones_succ (k : ℕ) (X : ListBlank (Fin 2)) : ones (k + 1) X = (ones k X).cons 1 :=
  rfl

private theorem stepR {q q' : Fin 15} {a b : Fin 2}
    (h : weakCollatz15.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz15 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

private theorem stepL {q q' : Fin 15} {a b : Fin 2}
    (h : weakCollatz15.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz15 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table -/

private theorem tr0_0 (L R) :
    step weakCollatz15 ⟨0, ⟨0, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr0_1 (L R) : step weakCollatz15 ⟨0, ⟨1, L, R⟩⟩ = some ⟨0, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr1_0 (L R) :
    step weakCollatz15 ⟨1, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr1_1 (L R) :
    step weakCollatz15 ⟨1, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr2_0 (L R) :
    step weakCollatz15 ⟨2, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr2_1 (L R) :
    step weakCollatz15 ⟨2, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr3_0 (L R) : step weakCollatz15 ⟨3, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr3_1 (L R) :
    step weakCollatz15 ⟨3, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr4_0 (L R) : step weakCollatz15 ⟨4, ⟨0, L, R⟩⟩ = some ⟨4, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr4_1 (L R) : step weakCollatz15 ⟨4, ⟨1, L, R⟩⟩ = some ⟨0, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr5_0 (L R) : step weakCollatz15 ⟨5, ⟨0, L, R⟩⟩ = some ⟨7, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr5_1 (L R) : step weakCollatz15 ⟨5, ⟨1, L, R⟩⟩ = some ⟨6, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr6_0 (L R) : step weakCollatz15 ⟨6, ⟨0, L, R⟩⟩ = some ⟨14, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr6_1 (L R) : step weakCollatz15 ⟨6, ⟨1, L, R⟩⟩ = some ⟨5, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr7_0 (L R) : step weakCollatz15 ⟨7, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr7_1 (L R) :
    step weakCollatz15 ⟨7, ⟨1, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr8_0 (L R) : step weakCollatz15 ⟨8, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr8_1 (L R) : step weakCollatz15 ⟨8, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr9_0 (L R) : step weakCollatz15 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr9_1 (L R) : step weakCollatz15 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr10_0 (L R) :
    step weakCollatz15 ⟨10, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr10_1 (L R) :
    step weakCollatz15 ⟨10, ⟨1, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr11_0 (L R) :
    step weakCollatz15 ⟨11, ⟨0, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr11_1 (L R) :
    step weakCollatz15 ⟨11, ⟨1, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr12_0 (L R) : step weakCollatz15 ⟨12, ⟨0, L, R⟩⟩ = some ⟨13, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr12_1 (L R) :
    step weakCollatz15 ⟨12, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr13_0 (L R) :
    step weakCollatz15 ⟨13, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr13_1 (L R) : step weakCollatz15 ⟨13, ⟨1, L, R⟩⟩ = some ⟨13, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr14_0 (L R : ListBlank (Fin 2)) : step weakCollatz15 ⟨14, ⟨0, L, R⟩⟩ = none := rfl
private theorem tr14_1 (L R) :
    step weakCollatz15 ⟨14, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R

/-! ## Sweep & Reachability Combinators -/

private def reachPos (c₁ c₂ : Cfg 15 2) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ nSteps weakCollatz15 s c₁ = some c₂

private theorem reachPos_step {c₁ c₂ : Cfg 15 2}
    (h : step weakCollatz15 c₁ = some c₂) : reachPos c₁ c₂ :=
  ⟨1, le_rfl, step_one h⟩

private theorem reachPos_trans {c₁ c₂ c₃ : Cfg 15 2}
    (h₁ : reachPos c₁ c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s₁, hs₁, heq₁⟩ := h₁
  obtain ⟨s₂, hs₂, heq₂⟩ := h₂
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq heq₁ heq₂⟩

private theorem step_then_reachPos {c₁ c₂ c₃ : Cfg 15 2}
    (h₁ : step weakCollatz15 c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ :=
  reachPos_trans (reachPos_step h₁) h₂

private theorem nSteps_then_reachPos {k : ℕ} {c₁ c₂ c₃ : Cfg 15 2}
    (h₁ : nSteps weakCollatz15 k c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₂
  exact ⟨k + s, by omega, nSteps_bind_eq h₁ heq⟩

private theorem sweep1R {q : Fin 15}
    (h : ∀ L R, step weakCollatz15 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz15 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweep1L {q : Fin 15}
    (h : ∀ L R, step weakCollatz15 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz15 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweepParEven (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz15 (2 * k) ⟨5, mkL (ones (2 * k) L) R⟩ =
      some ⟨5, mkL L (ones (2 * k) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, nSteps_succ, ones_succ,
      ErdosTernary15.Tape.mkL_cons, tr5_1, Option.bind_some, nSteps_succ, ones_succ,
      ErdosTernary15.Tape.mkL_cons, tr6_1, Option.bind_some, ih]
    rw [ones_succ', ones_succ']

private theorem sweepParOdd (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz15 (2 * k + 1) ⟨5, mkL (ones (2 * k + 1) L) R⟩ =
      some ⟨6, mkL L (ones (2 * k + 1) R)⟩ := by
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  have h1 : nSteps weakCollatz15 (2 * k) ⟨5, mkL (ones (2 * k) (L.cons 1)) R⟩ =
      some ⟨5, mkL (L.cons 1) (ones (2 * k) R)⟩ := sweepParEven k (L.cons 1) R
  rw [← ones_succ' (2 * k) L] at h1
  have h2 : step weakCollatz15 ⟨5, mkL (L.cons 1) (ones (2 * k) R)⟩ =
      some ⟨6, mkL L (ones (2 * k + 1) R)⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons, tr5_1, ones_succ]
  exact nSteps_bind_eq h1 (step_one h2)

/-! ## Canonical Configurations & Stage Advance -/

/-- Canonical round checkpoint (`d + n = x - 1`, `n = y - 1`, `d ≥ 1`, `n ≥ 1`):
`0^∞ 1^d 0 1^(n - 1) [1] 0^∞` in state `5` (`PAR_E`). -/
private def roundCfg (d n : ℕ) : Cfg 15 2 :=
  ⟨5, mkL (ones n ((ones d B0).cons 0)) B0⟩

/-- Left-to-right even pair-eater configuration (`L + M + R = x - 1`):
`0^∞ 1^L 0 1^M [1] 1^(R - 1) 0^∞` in state `3` (`ER1`). -/
private def evCfg (L M R : ℕ) : Cfg 15 2 :=
  ⟨3, Tape.mk' (ones M ((ones L B0).cons 0)) (ones R B0)⟩

/-- Canonical even stage start (`x ≥ 4`, `d = 0`, `n = x - 1`):
`0^∞ 0 [1] 1^(x - 2) 0^∞` in state `3` (`ER1`). -/
private def stageCfg (x : ℕ) : Cfg 15 2 :=
  evCfg 0 0 (x - 1)

/-- Left-to-right odd pair-eater configuration (`L + M + R = x - 1`):
`0^∞ 1^L 0 1^M [?] 1^(R - 1) 0^∞` in state `7` (`OR1`). -/
private def oddCfg (L M R : ℕ) : Cfg 15 2 :=
  ⟨7, Tape.mk' (ones M ((ones L B0).cons 0)) (ones R B0)⟩

/-- Stage-advance merge from `GT_SW` (state `12`): given `0^∞ 1^a [0] 1^b 0^∞` in state `12`,
fills the separator `0` to `1^(a + b + 1)`, sweeps left in `GT_L` (`13`), and enters
`stageCfg (a + b + 2)`. -/
private theorem gtsw_to_stage (a b : ℕ) :
    reachPos ⟨12, ⟨0, ones a B0, ones b B0⟩⟩ (stageCfg (a + b + 2)) := by
  refine step_then_reachPos (tr12_0 _ _) ?_
  rw [← ones_succ b B0]
  refine nSteps_then_reachPos (sweep1L tr13_1 a B0 (ones (b + 1) B0)) ?_
  rw [← ones_add a (b + 1) B0, mkL_B0]
  refine reachPos_step ?_
  rw [tr13_0, B0_cons_zero]
  unfold stageCfg evCfg
  rw [ones_zero, ones_zero, B0_cons_zero, show a + b + 2 - 1 = a + (b + 1) by omega]

/-! ## Even Halving Loop & Zero-State `y = 2` Abort -/

private theorem ev_step (L M r : ℕ) :
    reachPos (evCfg L M (r + 2)) (evCfg (L + 1) (M + 1) r) := by
  unfold evCfg
  let DL := (ones L B0).cons 0
  let Rr := ones r B0
  change reachPos ⟨3, Tape.mk' (ones M DL) (ones (r + 2) B0)⟩ _
  rw [show r + 2 = (r + 1) + 1 by omega, ones_succ (r + 1) B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  rw [← ones_succ M DL, ones_succ r B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr4_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr0_1 (M + 1) DL (Rr.cons 0)) ?_
  dsimp only [DL]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr0_0 _ _) ?_
  rw [← ones_succ L B0, ones_succ M (Rr.cons 0), ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr1_1 _ _) ?_
  let DL1 := (ones (L + 1) B0).cons 0
  change reachPos ⟨2, Tape.mk' DL1 (ones M (Rr.cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr2_1 M DL1 (Rr.cons 0)) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine reachPos_step ?_
  rw [tr2_0, ← ones_succ M DL1]

private theorem ev_loop (j L M r : ℕ) :
    j = 0 ∨ reachPos (evCfg L M (r + 2 * j)) (evCfg (L + j) (M + j) r) := by
  induction j generalizing L M with
  | zero => exact Or.inl rfl
  | succ j ih =>
    refine Or.inr ?_
    have h1 : reachPos (evCfg L M (r + 2 * (j + 1))) (evCfg (L + 1) (M + 1) (r + 2 * j)) := by
      rw [show r + 2 * (j + 1) = (r + 2 * j) + 2 by omega]
      exact ev_step L M (r + 2 * j)
    rcases ih (L + 1) (M + 1) with rfl | h2
    · simpa [Nat.add_assoc] using h1
    · rw [show L + 1 + j = L + (j + 1) by omega, show M + 1 + j = M + (j + 1) by omega] at h2
      exact reachPos_trans h1 h2

private theorem ev_finish_ge2 (L m : ℕ) :
    reachPos (evCfg L (m + 1) 1) (roundCfg (L + 1) (m + 1)) := by
  unfold evCfg
  let DL := (ones L B0).cons 0
  change reachPos ⟨3, Tape.mk' (ones (m + 1) DL) (ones 1 B0)⟩ _
  rw [ones_succ 0 B0, ones_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  rw [← ones_succ (m + 1) DL, mk'_B0]
  refine step_then_reachPos (tr4_0 _ _) ?_
  rw [B0_cons_zero, ones_succ (m + 1) DL, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr4_1 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (sweep1L tr0_1 (m + 1) DL B0) ?_
  dsimp only [DL]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr0_0 _ _) ?_
  rw [← ones_succ L B0, ones_succ m B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr1_1 _ _) ?_
  let DL1 := (ones (L + 1) B0).cons 0
  change reachPos ⟨2, Tape.mk' DL1 (ones m B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr2_1 m DL1 B0) ?_
  rw [mk'_B0]
  refine step_then_reachPos (tr2_0 _ _) ?_
  rw [← ones_succ m DL1, mk'_B0]
  refine reachPos_step ?_
  rw [tr3_0, B0_cons_zero]
  rfl

private theorem ev_finish_y2 (L : ℕ) :
    reachPos (evCfg L 0 1) (stageCfg (L + 4)) := by
  unfold evCfg
  let DL := (ones L B0).cons 0
  change reachPos ⟨3, Tape.mk' DL (ones 1 B0)⟩ _
  rw [ones_succ 0 B0, ones_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  rw [mk'_B0]
  refine step_then_reachPos (tr4_0 _ _) ?_
  rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr4_1 _ _) ?_
  rw [B0_cons_zero]
  dsimp only [DL]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr0_0 _ _) ?_
  rw [← ones_succ L B0, mk'_B0]
  refine step_then_reachPos (tr1_0 _ _) ?_
  rw [← ones_succ (L + 1) B0, mk'_B0]
  have h := gtsw_to_stage (L + 2) 0
  simpa [ones_zero, Nat.add_assoc] using h

private theorem stage_first_step (m : ℕ) (hm : 2 ≤ m) :
    reachPos (stageCfg (2 * m)) (roundCfg m (m - 1)) := by
  unfold stageCfg
  have hlen : 2 * m - 1 = 1 + 2 * (m - 1) := by omega
  rw [hlen]
  have hloop := ev_loop (m - 1) 0 0 1
  rcases hloop with h0 | hreach
  · exfalso; omega
  · have hfin : reachPos (evCfg (0 + (m - 1)) (0 + (m - 1)) 1) (roundCfg m (m - 1)) := by
      have hm1 : 0 + (m - 1) = (m - 2) + 1 := by omega
      rw [hm1]
      have h := ev_finish_ge2 (m - 1) (m - 2)
      rw [show m - 1 + 1 = m by omega, show m - 2 + 1 = m - 1 by omega] at h
      simpa [show m - 1 = m - 2 + 1 by omega] using h
    exact reachPos_trans hreach hfin

private theorem round_even_enter (d k : ℕ) :
    reachPos (roundCfg (d + 1) (2 * k + 1)) (evCfg (d + 1) 0 (2 * k + 1)) := by
  unfold roundCfg
  refine nSteps_then_reachPos (sweepParOdd k ((ones (d + 1) B0).cons 0) B0) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr6_0 _ _) ?_
  rw [ones_succ d B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr14_1 _ _) ?_
  rw [← ones_succ d B0, ErdosTernary15.Tape.mk'_cons]
  refine reachPos_step ?_
  rw [tr13_0]
  unfold evCfg
  rw [ones_zero]

private theorem round_even_ge4 (d k : ℕ) (hk : 2 ≤ k) :
    reachPos (roundCfg (d + 1) (2 * k - 1)) (roundCfg (d + 1 + k) (k - 1)) := by
  have heq : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [heq]
  refine reachPos_trans (round_even_enter d (k - 1)) ?_
  have hloop := ev_loop (k - 1) (d + 1) 0 1
  rw [show 1 + 2 * (k - 1) = 2 * (k - 1) + 1 by omega] at hloop
  rcases hloop with h0 | hreach
  · exfalso; omega
  · have hfin : reachPos (evCfg (d + 1 + (k - 1)) (0 + (k - 1)) 1)
        (roundCfg (d + 1 + k) (k - 1)) := by
      rw [Nat.zero_add]
      have h := ev_finish_ge2 (d + 1 + (k - 1)) (k - 2)
      rwa [show d + 1 + (k - 1) + 1 = d + 1 + k by omega,
        show k - 2 + 1 = k - 1 by omega] at h
    exact reachPos_trans hreach hfin

private theorem round_y2_abort (d : ℕ) :
    reachPos (roundCfg (d + 1) 1) (stageCfg (d + 5)) := by
  have h1 := round_even_enter d 0
  rw [show 2 * 0 + 1 = 1 by omega] at h1
  have h2 := ev_finish_y2 (d + 1)
  rw [show d + 1 + 4 = d + 5 by omega] at h2
  exact reachPos_trans h1 h2

/-! ## Odd `3k + 2` Loop, Cycle Halt & `z > x` Abort -/

private theorem round_odd_enter (d k : ℕ) :
    reachPos (roundCfg (d + 1) (2 * k)) (oddCfg d 1 (2 * k)) := by
  unfold roundCfg
  refine nSteps_then_reachPos (sweepParEven k ((ones (d + 1) B0).cons 0) B0) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr5_0 _ _) ?_
  rw [ones_succ d B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr7_1 _ _) ?_
  rw [← ones_succ d B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr8_0 _ _) ?_
  rw [ones_succ d B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine reachPos_step ?_
  rw [tr11_0]
  unfold oddCfg
  rw [ones_succ 0, ones_zero]

private theorem odd_step (L M r : ℕ) :
    reachPos (oddCfg (L + 1) (M + 1) (r + 2)) (oddCfg L (M + 4) r) := by
  unfold oddCfg
  let DL1 := (ones (L + 1) B0).cons 0
  let Rr := ones r B0
  change reachPos ⟨7, Tape.mk' (ones (M + 1) DL1) (ones (r + 2) B0)⟩ _
  rw [show r + 2 = (r + 1) + 1 by omega, ones_succ (r + 1) B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr7_1 _ _) ?_
  rw [← ones_succ (M + 1) DL1, ones_succ r B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr8_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr9_1 (M + 2) DL1 (Rr.cons 0)) ?_
  dsimp only [DL1]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr9_0 _ _) ?_
  rw [ones_succ L B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_1 _ _) ?_
  let DL := (ones L B0).cons 0
  change reachPos ⟨11, Tape.mk' DL (ones (M + 3) (Rr.cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr11_1 (M + 3) DL (Rr.cons 0)) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine reachPos_step ?_
  rw [tr11_0, ← ones_succ (M + 3) DL]

private theorem odd_loop (j L M r : ℕ) :
    j = 0 ∨ reachPos (oddCfg (L + j) (M + 1) (r + 2 * j)) (oddCfg L (M + 1 + 3 * j) r) := by
  induction j generalizing M with
  | zero => exact Or.inl rfl
  | succ j ih =>
    refine Or.inr ?_
    have h1 : reachPos (oddCfg (L + (j + 1)) (M + 1) (r + 2 * (j + 1)))
        (oddCfg (L + j) (M + 4) (r + 2 * j)) := by
      rw [show L + (j + 1) = (L + j) + 1 by omega,
        show r + 2 * (j + 1) = (r + 2 * j) + 2 by omega]
      exact odd_step (L + j) M (r + 2 * j)
    rcases ih (M + 3) with rfl | h2
    · simpa [Nat.add_assoc] using h1
    · rw [show M + 3 + 1 = M + 4 by omega,
        show M + 4 + 3 * j = M + 1 + 3 * (j + 1) by omega] at h2
      exact reachPos_trans h1 h2

private theorem odd_done_lt (d m : ℕ) :
    reachPos (oddCfg d (m + 1) 0) (roundCfg d (m + 1)) := by
  unfold oddCfg
  rw [ones_zero, mk'_B0]
  refine reachPos_step ?_
  rw [tr7_0, B0_cons_zero]
  rfl

private theorem odd_done_halt (q : ℕ) :
    ∃ s cfg, nSteps weakCollatz15 s (oddCfg 0 (2 * q + 1) 0) = some cfg ∧
      step weakCollatz15 cfg = none := by
  obtain ⟨s₁, _, hs₁⟩ := odd_done_lt 0 (2 * q)
  have hpar : nSteps weakCollatz15 (2 * q + 1) (roundCfg 0 (2 * q + 1)) =
      some ⟨6, ⟨0, B0, ones (2 * q + 1) B0⟩⟩ := by
    unfold roundCfg
    rw [ones_zero, B0_cons_zero]
    have h := sweepParOdd q B0 B0
    rw [mkL_B0] at h
    exact h
  have hhalt : step weakCollatz15 ⟨6, ⟨0, B0, ones (2 * q + 1) B0⟩⟩ =
      some ⟨14, ⟨0, B0, (ones (2 * q + 1) B0).cons 0⟩⟩ := by
    rw [tr6_0, mkL_B0]
  exact ⟨s₁ + (2 * q + 1) + 1, ⟨14, ⟨0, B0, (ones (2 * q + 1) B0).cons 0⟩⟩,
    nSteps_bind_eq (nSteps_bind_eq hs₁ hpar) (step_one hhalt), tr14_0 _ _⟩

private theorem odd_abort_gt (M r : ℕ) :
    reachPos (oddCfg 0 (M + 1) (2 * r + 2)) (stageCfg (M + 2 * r + 6)) := by
  unfold oddCfg
  rw [ones_zero, B0_cons_zero]
  let R2r := ones (2 * r) B0
  change reachPos ⟨7, Tape.mk' (ones (M + 1) B0) (ones (2 * r + 2) B0)⟩ _
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, ones_succ (2 * r + 1) B0,
    ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr7_1 _ _) ?_
  rw [← ones_succ (M + 1) B0, ones_succ (2 * r) B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr8_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr9_1 (M + 2) B0 (R2r.cons 0)) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr9_0 _ _) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr10_0 _ _) ?_
  change reachPos ⟨12, Tape.mk' (ones 1 B0) (ones (M + 3) (R2r.cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr12_1 (M + 3) (ones 1 B0) (R2r.cons 0)) ?_
  rw [← ones_add (M + 3) 1 B0, ErdosTernary15.Tape.mk'_cons]
  have h := gtsw_to_stage (M + 3 + 1) (2 * r)
  rw [show M + 3 + 1 + 2 * r + 2 = M + 2 * r + 6 by omega] at h
  exact h

/-! ## Blank-Tape Warm-Up (`init → stageCfg 4` in 6 Steps) -/

private theorem init_reaches_stage4 :
    ∃ s : ℕ, 1 ≤ s ∧ nSteps weakCollatz15 s init = some (stageCfg 4) :=
  ⟨6, by omega, rfl⟩

/-! ## One-Step `terras` Dispatch on Even Stages -/

private theorem even_or_odd_constructive (n : ℕ) : ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 := by
  induction n with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, rfl | rfl⟩
    · exact ⟨k, Or.inr rfl⟩
    · exact ⟨k + 1, Or.inl (by omega)⟩

private theorem terras_ge2_of_ge3 {y : ℕ} (hy : 3 ≤ y) : 2 ≤ terras y := by
  unfold terras
  split <;> omega

private theorem stage_round_lt (x y : ℕ) (hy3 : 3 ≤ y) (hyx : y < x) (hlt : terras y < x) :
    reachPos (roundCfg (x - y) (y - 1)) (roundCfg (x - terras y) (terras y - 1)) := by
  rcases even_or_odd_constructive y with ⟨k, rfl | rfl⟩
  · have hk2 : 2 ≤ k := by omega
    have hte : terras (2 * k) = k := by unfold terras; split <;> omega
    have hd : x - 2 * k = (x - 2 * k - 1) + 1 := by omega
    have h := round_even_ge4 (x - 2 * k - 1) k hk2
    rw [show x - 2 * k - 1 + 1 = x - 2 * k by omega,
      show x - 2 * k + k = x - k by omega] at h
    simpa [hte] using h
  · have hk1 : 1 ≤ k := by omega
    have hto : terras (2 * k + 1) = 3 * k + 2 := by unfold terras; split <;> omega
    have hd1 : x - (2 * k + 1) = (x - (2 * k + 1) - 1) + 1 := by omega
    have h1 : reachPos (roundCfg (x - (2 * k + 1)) (2 * k))
        (oddCfg (x - (2 * k + 1) - 1) 1 (2 * k)) := by
      rw [hd1]; exact round_odd_enter (x - (2 * k + 1) - 1) k
    have hloop := odd_loop k (x - (3 * k + 2)) 0 0
    rw [show x - (3 * k + 2) + k = x - (2 * k + 1) - 1 by omega,
      show 0 + 1 = 1 by omega, show 0 + 2 * k = 2 * k by omega,
      show 1 + 3 * k = 3 * k + 1 by omega] at hloop
    rcases hloop with h0 | h2
    · exfalso; omega
    · have h3 := odd_done_lt (x - (3 * k + 2)) (3 * k)
      have htot := reachPos_trans h1 (reachPos_trans h2 h3)
      simpa [hto, show 2 * k + 1 - 1 = 2 * k by omega,
        show 3 * k + 2 - 1 = 3 * k + 1 by omega] using htot

private theorem stage_round_gt (x y : ℕ) (hy3 : 3 ≤ y) (hyx : y < x) (hgt : x < terras y) :
    reachPos (roundCfg (x - y) (y - 1)) (stageCfg (x + 2)) := by
  rcases even_or_odd_constructive y with ⟨k, rfl | rfl⟩
  · exfalso
    have hte : terras (2 * k) = k := by unfold terras; split <;> omega
    omega
  · have hk1 : 1 ≤ k := by omega
    have hto : terras (2 * k + 1) = 3 * k + 2 := by unfold terras; split <;> omega
    let d' := x - (2 * k + 1) - 1
    have hd1 : x - (2 * k + 1) = d' + 1 := by dsimp only [d']; omega
    have hk_gt : d' < k := by dsimp only [d']; omega
    let r := k - d' - 1
    have h1 : reachPos (roundCfg (x - (2 * k + 1)) (2 * k)) (oddCfg d' 1 (2 * k)) := by
      rw [hd1]; exact round_odd_enter d' k
    have hloop := odd_loop d' 0 0 (2 * r + 2)
    rw [Nat.zero_add, show 0 + 1 = 1 by omega,
      show 2 * r + 2 + 2 * d' = 2 * k by dsimp only [r, d']; omega,
      show 1 + 3 * d' = 3 * d' + 1 by omega] at hloop
    have h3 : reachPos (oddCfg 0 (3 * d' + 1) (2 * r + 2)) (stageCfg (x + 2)) := by
      have h := odd_abort_gt (3 * d') r
      rw [show 3 * d' + 2 * r + 6 = x + 2 by dsimp only [r, d']; omega] at h
      exact h
    rcases hloop with hd0 | h2
    · rw [show 2 * k + 1 - 1 = 2 * k by omega]
      rw [hd0] at h1 h3
      rw [show 3 * 0 + 1 = 1 by omega,
        show 2 * r + 2 = 2 * k by dsimp only [r]; omega] at h3
      exact reachPos_trans h1 h3
    · rw [show 2 * k + 1 - 1 = 2 * k by omega]
      exact reachPos_trans h1 (reachPos_trans h2 h3)

private theorem stage_round_halt (m y : ℕ) (hy3 : 3 ≤ y) (hyx : y < 2 * m)
    (heq : terras y = 2 * m) :
    ∃ s cfg, nSteps weakCollatz15 s (roundCfg (2 * m - y) (y - 1)) = some cfg ∧
      step weakCollatz15 cfg = none := by
  rcases even_or_odd_constructive y with ⟨k, rfl | rfl⟩
  · exfalso
    have hte : terras (2 * k) = k := by unfold terras; split <;> omega
    omega
  · have hto : terras (2 * k + 1) = 3 * k + 2 := by unfold terras; split <;> omega
    let q := k / 2
    have hkq : k = 2 * q := by dsimp only [q]; omega
    have hq1 : 1 ≤ q := by dsimp only [q]; omega
    have h1 : reachPos (roundCfg (2 * m - (2 * k + 1)) (2 * k))
        (oddCfg (2 * q) 1 (2 * (2 * q))) := by
      rw [show 2 * m - (2 * k + 1) = 2 * q + 1 by omega, hkq]
      exact round_odd_enter (2 * q) (2 * q)
    have hloop := odd_loop (2 * q) 0 0 0
    rw [Nat.zero_add, show 0 + 1 = 1 by omega, show 0 + 2 * (2 * q) = 2 * (2 * q) by omega,
      show 1 + 3 * (2 * q) = 2 * (3 * q) + 1 by omega] at hloop
    rcases hloop with h0 | h2
    · exfalso; omega
    · obtain ⟨s₁, _, hs₁⟩ := reachPos_trans h1 h2
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := odd_done_halt (3 * q)
      rw [show 2 * k + 1 - 1 = 2 * k by omega]
      exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-! ## Constructive Cycle-Maximum Reduction (`16 → 15`) -/

private def StepContinues (x i : ℕ) : Prop :=
  3 ≤ terras^[i] x ∧ terras^[i] x < x

private def StayIn (x m : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ m → StepContinues x i

private theorem stayIn_or_first_exit (x m : ℕ) :
    StayIn x m ∨
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ StayIn x (t - 1) ∧ ¬ StepContinues x t := by
  induction m with
  | zero => exact Or.inl fun i hi1 hi0 => absurd (le_trans hi1 hi0) (by decide)
  | succ m ih =>
    rcases ih with hstay | ⟨t, ht1, htm, hprev, hexit⟩
    · by_cases hcont : 3 ≤ terras^[m + 1] x ∧ terras^[m + 1] x < x
      · refine Or.inl fun i hi1 hi_le => ?_
        rcases Nat.lt_or_ge i (m + 1) with hlt | hge
        · exact hstay i hi1 (by omega)
        · rw [show i = m + 1 by omega]; exact hcont
      · exact Or.inr ⟨m + 1, by omega, le_rfl, hstay, hcont⟩
    · exact Or.inr ⟨t, ht1, by omega, hprev, hexit⟩

private theorem stage_stay_reach (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hstay : StayIn (2 * m) k) :
    k = 0 ∨
      (1 ≤ k ∧ reachPos (stageCfg (2 * m))
        (roundCfg (2 * m - terras^[k] (2 * m)) (terras^[k] (2 * m) - 1))) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ⟨by omega, ?_⟩
    have hstep : StepContinues (2 * m) (k + 1) := hstay (k + 1) (by omega) le_rfl
    rcases ih fun i hi1 hik => hstay i hi1 (by omega) with rfl | ⟨hk1, hprev⟩
    · have ht1 : terras^[1] (2 * m) = m := by
        rw [Function.iterate_one]; unfold terras; split <;> omega
      rw [ht1, show 2 * m - m = m by omega]
      exact stage_first_step m hm
    · have hyk := hstay k hk1 (by omega)
      have hlt : terras (terras^[k] (2 * m)) < 2 * m := by
        rw [← Function.iterate_succ_apply' terras k (2 * m)]
        exact hstep.2
      rw [Function.iterate_succ_apply']
      exact reachPos_trans hprev (stage_round_lt (2 * m) (terras^[k] (2 * m)) hyk.1 hyk.2 hlt)

private def StageHalts (x : ℕ) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ t ≤ x ∧ StayIn x (t - 1) ∧ terras^[t] x = x

private theorem even_of_stageHalts {w : ℕ} (hw3 : 3 ≤ w) (hh : StageHalts w) :
    ∃ m : ℕ, 2 ≤ m ∧ w = 2 * m := by
  obtain ⟨t, ht1, _, hprev, hhit⟩ := hh
  rcases even_or_odd_constructive w with ⟨m, rfl | rfl⟩
  · exact ⟨m, by omega, rfl⟩
  · exfalso
    have hto : terras (2 * m + 1) = 3 * m + 2 := by unfold terras; split <;> omega
    by_cases ht_eq1 : t = 1
    · subst ht_eq1
      rw [Function.iterate_one, hto] at hhit
      omega
    · have hs1 : StepContinues (2 * m + 1) 1 := hprev 1 le_rfl (by omega)
      have hlt1 : terras (2 * m + 1) < 2 * m + 1 := by
        have h1 : terras (2 * m + 1) = terras^[1] (2 * m + 1) := rfl
        rw [h1]
        exact hs1.2
      omega

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
      · exact hexit (hprev' t ht1 (by omega))

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
      exact hexit ⟨ht_bnd.1, by omega⟩

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

private theorem not_stayIn_self_of_noStageHalts {x : ℕ} (hx : 4 ≤ x)
    (hno : NoStageHalts (x - 1)) : ¬ StayIn x x := by
  intro hstay
  let N := x - 4
  let f : ℕ → ℕ := fun i => terras^[i + 1] x - 3
  have hf_lt : ∀ i : ℕ, i ≤ N + 1 → f i < N + 1 := by
    intro i hi
    have hs : StepContinues x (i + 1) := hstay (i + 1) (by omega) (by dsimp only [N] at hi; omega)
    dsimp only [f, N]
    have hge3 := hs.1
    have hlt_x := hs.2
    omega
  rcases WeakCollatz75.nat_pigeonhole_constructive N f hf_lt with ⟨a, b, hab, hb_le, hfab⟩
  have ha_step : StepContinues x (a + 1) :=
    hstay (a + 1) (by omega) (by dsimp only [N] at hb_le; omega)
  have hb_step : StepContinues x (b + 1) :=
    hstay (b + 1) (by omega) (by dsimp only [N] at hb_le; omega)
  have hab_eq : terras^[a + 1] x = terras^[b + 1] x := by
    have ha3 := ha_step.1
    have hb3 := hb_step.1
    dsimp only [f] at hfab
    omega
  let u := terras^[a + 1] x
  have hu3 : 3 ≤ u := ha_step.1
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

private theorem stage_advance_of_noStageHalts (m : ℕ) (hm : 2 ≤ m)
    (hno : NoStageHalts (2 * m)) :
    reachPos (stageCfg (2 * m)) (stageCfg (2 * m + 2)) := by
  rcases stayIn_or_first_exit (2 * m) (2 * m) with hstay | ⟨t, ht1, htx, hprev, hexit⟩
  · exfalso
    exact not_stayIn_self_of_noStageHalts (by omega)
      (fun w hw3 hwx => hno w hw3 (by omega)) hstay
  · have hnot_halt : ¬ StageHalts (2 * m) := hno (2 * m) (by omega) le_rfl
    have hne_x : terras^[t] (2 * m) ≠ 2 * m := fun hhit => hnot_halt ⟨t, ht1, htx, hprev, hhit⟩
    rcases stage_stay_reach m hm (t - 1) hprev with ht0 | ⟨ht1_pos, hreach_prev⟩
    · have ht_eq1 : t = 1 := by omega
      subst ht_eq1
      have ht1_val : terras^[1] (2 * m) = m := by
        rw [Function.iterate_one]; unfold terras; split <;> omega
      have hm_eq2 : m = 2 := by
        by_cases hm2 : m = 2
        · exact hm2
        · exfalso; exact hexit ⟨by rw [ht1_val]; omega, by rw [ht1_val]; omega⟩
      subst hm_eq2
      have h1 := stage_first_step 2 le_rfl
      have h2 := round_y2_abort 1
      exact reachPos_trans h1 h2
    · have hy_prev := hprev (t - 1) ht1_pos le_rfl
      have hnext : terras (terras^[t - 1] (2 * m)) = terras^[t] (2 * m) := by
        rw [← Function.iterate_succ_apply' terras (t - 1) (2 * m), show (t - 1).succ = t by omega]
      have hge2 : 2 ≤ terras^[t] (2 * m) := by
        rw [← hnext]; exact terras_ge2_of_ge3 hy_prev.1
      have hor : terras^[t] (2 * m) = 2 ∨ 2 * m < terras^[t] (2 * m) := by
        by_cases h2 : terras^[t] (2 * m) = 2
        · exact Or.inl h2
        · refine Or.inr ?_
          by_cases hlt : terras^[t] (2 * m) < 2 * m
          · exfalso; exact hexit ⟨by omega, hlt⟩
          · omega
      rcases hor with h2 | hgt
      · have hlt := stage_round_lt (2 * m) (terras^[t - 1] (2 * m)) hy_prev.1 hy_prev.2
          (by rw [hnext, h2]; omega)
        rw [hnext, h2] at hlt
        have habort := round_y2_abort (2 * m - 3)
        rw [show 2 * m - 3 + 1 = 2 * m - 2 by omega,
          show 2 * m - 3 + 5 = 2 * m + 2 by omega] at habort
        exact reachPos_trans hreach_prev (reachPos_trans hlt habort)
      · rw [← hnext] at hgt
        exact reachPos_trans hreach_prev
          (stage_round_gt (2 * m) (terras^[t - 1] (2 * m)) hy_prev.1 hy_prev.2 hgt)

private theorem reach_even_stage_from_init (m : ℕ) (hm : 2 ≤ m)
    (hno : NoStageHalts (2 * m - 1)) :
    ∃ s : ℕ, m - 1 ≤ s ∧ nSteps weakCollatz15 s init = some (stageCfg (2 * m)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨s, hs1, hs⟩ := init_reaches_stage4
    exact ⟨s, by omega, hs⟩
  | succ m hm ih =>
    obtain ⟨s₁, hs₁_ge, hs₁⟩ := ih fun w hw3 hw_le => hno w hw3 (by omega)
    obtain ⟨s₂, hs₂_pos, hs₂⟩ :=
      stage_advance_of_noStageHalts m hm fun w hw3 hw_le => hno w hw3 (by omega)
    rw [show 2 * m + 2 = 2 * (m + 1) by omega] at hs₂
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

private theorem stage_halt_of_stageHalts (m : ℕ) (hm : 2 ≤ m) (hhalt : StageHalts (2 * m)) :
    ∃ s cfg, nSteps weakCollatz15 s (stageCfg (2 * m)) = some cfg ∧
      step weakCollatz15 cfg = none := by
  obtain ⟨t, ht1, _, hprev, hhit⟩ := hhalt
  rcases stage_stay_reach m hm (t - 1) hprev with ht0 | ⟨ht1_pos, hreach_prev⟩
  · exfalso
    have ht_eq1 : t = 1 := by omega
    subst ht_eq1
    have ht1_val : terras^[1] (2 * m) = m := by
      rw [Function.iterate_one]; unfold terras; split <;> omega
    omega
  · obtain ⟨s₁, _, hs₁⟩ := hreach_prev
    have hy_prev := hprev (t - 1) ht1_pos le_rfl
    have hhit' : terras (terras^[t - 1] (2 * m)) = 2 * m := by
      rw [← Function.iterate_succ_apply' terras (t - 1) (2 * m), show (t - 1).succ = t by omega]
      exact hhit
    obtain ⟨s₂, cfg, hs₂, hnone⟩ :=
      stage_round_halt m (terras^[t - 1] (2 * m)) hy_prev.1 hy_prev.2 hhit'
    exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-- The 15-state machine `weakCollatz15` (`weak_collatz_15`) halts on the blank tape if and only if
there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(constructive, zero `Classical.choice`). -/
theorem halts_weakCollatz15_iff_bounded_cycle :
    ConjectureMachines.Halts weakCollatz15 ↔
      ∃ x j : ℕ, 3 ≤ x ∧ 1 ≤ j ∧ j ≤ x ∧ terras^[j] x = x := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases noStageHalts_or_first (2 * (k + 2) - 1) with
      hno | ⟨w, hw3, -, -, ⟨t, ht1, htw, -, hhit⟩⟩
    · obtain ⟨s, hks, hs⟩ := reach_even_stage_from_init (k + 2) (by omega) hno
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
    · exact ⟨w, t, hw3, ht1, htw, hhit⟩
  · rintro ⟨x, j, hx3, hj1, _, hhit⟩
    rcases WeakCollatz75.exists_bounded_cycle_max hx3 hj1 hhit with
      ⟨M, jM, hM3, hjM1, _hjMM, hjM_cyc, hbnd, -⟩
    have hM_halts : StageHalts M :=
      stageHalts_of_cycle_max hM3 hjM1 (by omega) hjM_cyc hbnd
    rcases noStageHalts_or_first M with hno | ⟨w₀, hw₀3, -, hprev₀, hhalt₀⟩
    · exfalso
      exact hno M hM3 le_rfl hM_halts
    · obtain ⟨m₀, hm₀2, rfl⟩ := even_of_stageHalts hw₀3 hhalt₀
      obtain ⟨s₁, -, hs₁⟩ := reach_even_stage_from_init m₀ hm₀2 hprev₀
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt_of_stageHalts m₀ hm₀2 hhalt₀
      rw [Part.dom_iff_mem]
      exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches (nSteps_bind_eq hs₁ hs₂), hnone⟩⟩

/-- The 15-state candidate machine halts on the blank tape if and only if the 16-state reference
machine does (constructive, zero `Classical.choice`). -/
theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  halts_weakCollatz15_iff_bounded_cycle.trans
    WeakCollatz16.halts_weakCollatz16_iff_bounded_cycle.symm

/-- The candidate has 1 fewer state than the 16-state reference (`15 < 16`). -/
theorem candidate_fewer_states : candidate.states < reference.states := by
  decide +kernel

end ConjectureMachines.WeakCollatz15
