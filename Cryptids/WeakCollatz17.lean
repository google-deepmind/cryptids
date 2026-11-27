/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz27
public import Cryptids.Semantics.WeakCollatz75

/-!
# WeakCollatz17 (`weak_collatz_17`)

The 17-state, 2-symbol Turing machine `weak_collatz_17` compresses `weak_collatz_27` (`27 → 17`
states, `-10` states / `-37.04%`; `75 → 41 → 27 → 17` overall, `-58` states / `-77.33%`) while
constructively preserving blank-tape halting equivalence (`candidate_equivalent`, proved without
`Classical.choice`).

## Compression Ideas (`27 → 17` states)

Instead of storing `x` and `y` in separate unary blocks `1^x 0 1^y` (which required dedicated
comparison, restoration, and stage-doubling loops in `weak_collatz_27`), `weak_collatz_17`
maintains the **popcount conservation law** `d + y = x` (`d = x - y ≥ 0`, `y ≥ 1`) at canonical
round checkpoint `roundCfg d y`: `0^∞  1^d  [0]  1^y  0^∞` in state `1`:
1. **Single-Block Stage Start & 1-Step Blank-Tape Boot**: At stage start (`d = 0`, `y = x`),
   `stageCfg x = roundCfg 0 x` is a single unary block `0^∞ [0] 1^x 0^∞`. State `0` on the blank
   tape writes `1` and steps left into `stageCfg 1` at `t = 1` (`stageCfg 3` at `t = 29`, with all
   `33/33` active transitions visited by step `238`).
2. **Inward Parity Squeeze (`sqzCfg`)**: Each pass shifts a left `0` right by 1 (`d ↦ d + 1`) and
   carves a right `0` left by 1 (`b ↦ b - 2`, `a ↦ a + 1`), conserving `d + b + a = x` for both
   even `y = 2k + 2` (finishing at `roundCfg (d + k + 1) (k + 1)`) and odd `y = 2k + 1` (leaving
   `0^∞ 1^(d + k + 1) 0 [0] 1^k 0^∞`).
3. **Conservation-Preserving Odd Pass & Cycle-Max Halt (`oddCfg`)**: For `y = 1`, filling the single
   `0` next to `1^x` yields `1^(x + 1)` directly. For odd `y = 2k + 1 ≥ 3` (`z = 3k + 2`), each pass
   locally peels two `1`s from `1^L` and one `1` from `1^m` into `1^r` (`(L, r, m) ↦
   (L - 2, r + 3, m - 1)`): if `L` runs out early (`z > x`), filling the single `0` between `1^r`
   and `1^m` merges `1^r 1 1^m = 1^(x + 1)` in place; if all `k + 1` peels succeed (`z ≤ x`), state
   `16` halts iff `x - z = 0` (`z = x`; every predecessor `y ≤ M` of a cycle maximum `M ≥ 3` must be
   odd since `2M > M`) and otherwise enters `roundCfg (x - z) z`.
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz17

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_succ nSteps_reaches
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- 27-state Weak Collatz reference machine (`weak_collatz_27`). -/
abbrev reference : BundledMachine 2 := Machines.weakCollatz27.bundle

/-- 17-state Weak Collatz candidate machine (`weak_collatz_17`). -/
abbrev candidate : BundledMachine 2 := Machines.weakCollatz17.bundle

/-- The candidate as a `Machine 17 2`. -/
abbrev weakCollatz17 : Machine 17 2 := Machines.weakCollatz17

private theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

private theorem ones_zero (X : ListBlank (Fin 2)) : ones 0 X = X := rfl

private theorem ones_succ (k : ℕ) (X : ListBlank (Fin 2)) : ones (k + 1) X = (ones k X).cons 1 :=
  rfl

private theorem stepR {q q' : Fin 17} {a b : Fin 2}
    (h : weakCollatz17.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz17 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

private theorem stepL {q q' : Fin 17} {a b : Fin 2}
    (h : weakCollatz17.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz17 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table -/

private theorem tr0_0 (L R) : step weakCollatz17 ⟨0, ⟨0, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr0_1 (L R) :
    step weakCollatz17 ⟨0, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr1_0 (L R) :
    step weakCollatz17 ⟨1, ⟨0, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr1_1 (L R) : step weakCollatz17 ⟨1, ⟨1, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr2_0 (L R) :
    step weakCollatz17 ⟨2, ⟨0, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr2_1 (L R) :
    step weakCollatz17 ⟨2, ⟨1, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr3_0 (L R) :
    step weakCollatz17 ⟨3, ⟨0, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr3_1 (L R) :
    step weakCollatz17 ⟨3, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr4_0 (L R) : step weakCollatz17 ⟨4, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr4_1 (L R) :
    step weakCollatz17 ⟨4, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr5_0 (L R) : step weakCollatz17 ⟨5, ⟨0, L, R⟩⟩ = some ⟨0, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr5_1 (L R) : step weakCollatz17 ⟨5, ⟨1, L, R⟩⟩ = some ⟨6, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr6_0 (L R) :
    step weakCollatz17 ⟨6, ⟨0, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr6_1 (L R) : step weakCollatz17 ⟨6, ⟨1, L, R⟩⟩ = some ⟨15, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr7_0 (L R) : step weakCollatz17 ⟨7, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr7_1 (L R) :
    step weakCollatz17 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr8_0 (L R) : step weakCollatz17 ⟨8, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr8_1 (L R) : step weakCollatz17 ⟨8, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr9_0 (L R) : step weakCollatz17 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr9_1 (L R) :
    step weakCollatz17 ⟨9, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr10_0 (L R) : step weakCollatz17 ⟨10, ⟨0, L, R⟩⟩ = some ⟨11, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr10_1 (L R) : step weakCollatz17 ⟨10, ⟨1, L, R⟩⟩ = some ⟨10, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr11_0 (L R) :
    step weakCollatz17 ⟨11, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr11_1 (L R) : step weakCollatz17 ⟨11, ⟨1, L, R⟩⟩ = some ⟨12, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr12_0 (L R) :
    step weakCollatz17 ⟨12, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr12_1 (L R) :
    step weakCollatz17 ⟨12, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr13_0 (L R) :
    step weakCollatz17 ⟨13, ⟨0, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr13_1 (L R) :
    step weakCollatz17 ⟨13, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr14_0 (L R) : step weakCollatz17 ⟨14, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr14_1 (L R) : step weakCollatz17 ⟨14, ⟨1, L, R⟩⟩ = some ⟨10, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr15_0 (L R) : step weakCollatz17 ⟨15, ⟨0, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr15_1 (L R) : step weakCollatz17 ⟨15, ⟨1, L, R⟩⟩ = some ⟨15, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr16_0 (L R : ListBlank (Fin 2)) : step weakCollatz17 ⟨16, ⟨0, L, R⟩⟩ = none := rfl
private theorem tr16_1 (L R) :
    step weakCollatz17 ⟨16, ⟨1, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R

/-! ## Sweep & Reachability Combinators -/

private def reachPos (c₁ c₂ : Cfg 17 2) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ nSteps weakCollatz17 s c₁ = some c₂

private theorem reachPos_step {c₁ c₂ : Cfg 17 2}
    (h : step weakCollatz17 c₁ = some c₂) : reachPos c₁ c₂ :=
  ⟨1, le_rfl, step_one h⟩

private theorem reachPos_trans {c₁ c₂ c₃ : Cfg 17 2}
    (h₁ : reachPos c₁ c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s₁, hs₁, heq₁⟩ := h₁
  obtain ⟨s₂, hs₂, heq₂⟩ := h₂
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq heq₁ heq₂⟩

private theorem step_then_reachPos {c₁ c₂ c₃ : Cfg 17 2}
    (h₁ : step weakCollatz17 c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ :=
  reachPos_trans (reachPos_step h₁) h₂

private theorem nSteps_then_reachPos {k : ℕ} {c₁ c₂ c₃ : Cfg 17 2}
    (h₁ : nSteps weakCollatz17 k c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₂
  exact ⟨k + s, by omega, nSteps_bind_eq h₁ heq⟩

private theorem reachPos_then_nSteps {k : ℕ} {c₁ c₂ c₃ : Cfg 17 2}
    (h₁ : reachPos c₁ c₂) (h₂ : nSteps weakCollatz17 k c₂ = some c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₁
  exact ⟨s + k, by omega, nSteps_bind_eq heq h₂⟩

private theorem sweep1R {q : Fin 17}
    (h : ∀ L R, step weakCollatz17 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz17 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweep1L {q : Fin 17}
    (h : ∀ L R, step weakCollatz17 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz17 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

/-! ## Conservation-Law Checkpoints & Inward Parity Squeeze -/

/-- Canonical round checkpoint (`d + y = x`): `0^∞ 1^d [0] 1^y 0^∞` in state `1`. -/
private def roundCfg (d y : ℕ) : Cfg 17 2 :=
  ⟨1, ⟨0, ones d B0, ones y B0⟩⟩

/-- Canonical stage start (`d = 0, y = x`): `0^∞ [0] 1^x 0^∞` in state `1`. -/
private def stageCfg (x : ℕ) : Cfg 17 2 :=
  roundCfg 0 x

/-- Inward parity-squeeze configuration (`d + b + a = x`): `0^∞ 1^d [0] 1^b 0 1^a 0^∞` in state
`1` (at `a = 0`, `(ones 0 B0).cons 0 = B0`, coinciding with `roundCfg d b`). -/
private def sqzCfg (d b a : ℕ) : Cfg 17 2 :=
  ⟨1, ⟨0, ones d B0, ones b ((ones a B0).cons 0)⟩⟩

private theorem roundCfg_eq_sqzCfg (d y : ℕ) : roundCfg d y = sqzCfg d y 0 := by
  simp only [roundCfg, sqzCfg, ones_zero, B0_cons_zero]

private theorem sqz_to_eback (d b a : ℕ) :
    reachPos (sqzCfg d (b + 2) a)
      ⟨6, mkL (ones b ((ones (d + 1) B0).cons 0)) ((ones (a + 1) B0).cons 0)⟩ := by
  unfold sqzCfg
  let Ra := (ones a B0).cons 0
  change reachPos ⟨1, ⟨0, ones d B0, ones (b + 2) Ra⟩⟩ _
  refine step_then_reachPos (tr1_0 _ _) ?_
  rw [← ones_succ d B0, show b + 2 = (b + 1) + 1 by omega, ones_succ (b + 1) Ra,
    ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr2_1 _ _) ?_
  rw [ones_succ b Ra, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  let Ld := (ones (d + 1) B0).cons 0
  change reachPos ⟨4, Tape.mk' (ones 1 Ld) (ones b Ra)⟩ _
  refine nSteps_then_reachPos (sweep1R tr4_1 b (ones 1 Ld) Ra) ?_
  rw [← ones_add b 1 Ld]
  dsimp only [Ra]
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr4_0 _ _) ?_
  rw [ones_succ b Ld, ErdosTernary15.Tape.mkL_cons, ← ones_succ a B0]
  exact reachPos_step (tr5_1 _ _)

private theorem eback_to_haltchk (L : ListBlank (Fin 2)) (m : ℕ) :
    reachPos ⟨6, ⟨1, ones m (L.cons 0), B0⟩⟩ ⟨16, mkL L ((ones (m + 1) B0).cons 0)⟩ := by
  refine step_then_reachPos (tr6_1 _ _) ?_
  change reachPos ⟨15, mkL (ones m (L.cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr15_1 m (L.cons 0) (ones 1 B0)) ?_
  rw [← ones_add m 1 B0, ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr15_0 _ _)

private theorem sqz_step (d b₀ a : ℕ) :
    reachPos (sqzCfg d (b₀ + 3) a) (sqzCfg (d + 1) (b₀ + 1) (a + 1)) := by
  rw [show b₀ + 3 = (b₀ + 1) + 2 by omega]
  refine reachPos_trans (sqz_to_eback d (b₀ + 1) a) ?_
  let Ld := (ones (d + 1) B0).cons 0
  let Ra1 := (ones (a + 1) B0).cons 0
  change reachPos ⟨6, mkL (ones (b₀ + 1) Ld) Ra1⟩ _
  rw [ones_succ b₀ Ld, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr6_1 _ _) ?_
  change reachPos ⟨15, mkL (ones b₀ Ld) (ones 1 Ra1)⟩ _
  refine nSteps_then_reachPos (sweep1L tr15_1 b₀ Ld (ones 1 Ra1)) ?_
  rw [← ones_add b₀ 1 Ra1]
  dsimp only [Ld]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr15_0 _ _) ?_
  rw [ones_succ d B0, ErdosTernary15.Tape.mkL_cons]
  have h16 := tr16_1 (ones d B0) ((ones (b₀ + 1) Ra1).cons 0)
  rw [← ones_succ d B0, ErdosTernary15.Tape.mk'_cons] at h16
  exact reachPos_step h16

private theorem sqz_many (d b₀ a k : ℕ) :
    ∃ s : ℕ, nSteps weakCollatz17 s (sqzCfg d ((b₀ + 1) + 2 * k) a) =
      some (sqzCfg (d + k) (b₀ + 1) (a + k)) := by
  induction k generalizing d a with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [show (b₀ + 1) + 2 * (k + 1) = (b₀ + 2 * k) + 3 by omega]
    obtain ⟨s₁, _, hs₁⟩ := sqz_step d (b₀ + 2 * k) a
    rw [show (b₀ + 2 * k) + 1 = (b₀ + 1) + 2 * k by omega] at hs₁
    obtain ⟨s₂, hs₂⟩ := ih (d + 1) (a + 1)
    rw [show d + 1 + k = d + (k + 1) by omega, show a + 1 + k = a + (k + 1) by omega] at hs₂
    exact ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩

private theorem sqz_even_exit (d a : ℕ) :
    reachPos (sqzCfg d 2 a) (roundCfg (d + 1) (a + 1)) := by
  refine reachPos_trans (sqz_to_eback d 0 a) ?_
  rw [ones_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr6_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr2_0 _ _) ?_
  let Ld := (ones (d + 1) B0).cons 0
  change reachPos ⟨7, Tape.mk' (ones 1 Ld) (ones (a + 1) B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr7_1 (a + 1) (ones 1 Ld) B0) ?_
  rw [← ones_add (a + 1) 1 Ld, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr7_0 _ _) ?_
  rw [B0_cons_zero, show a + 1 + 1 = (a + 1) + 1 from rfl, ones_succ (a + 1) Ld,
    ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr5_1 _ _) ?_
  rw [B0_cons_zero, ones_succ a Ld, ErdosTernary15.Tape.mkL_cons]
  refine reachPos_trans (eback_to_haltchk (ones (d + 1) B0) a) ?_
  rw [ones_succ d B0, ErdosTernary15.Tape.mkL_cons]
  have h16 := tr16_1 (ones d B0) ((ones (a + 1) B0).cons 0)
  rw [← ones_succ d B0, ErdosTernary15.Tape.mk'_cons] at h16
  exact reachPos_step h16

private theorem round_even (d k : ℕ) :
    reachPos (roundCfg d (2 * k + 2)) (roundCfg (d + k + 1) (k + 1)) := by
  rw [roundCfg_eq_sqzCfg, show 2 * k + 2 = (1 + 1) + 2 * k by omega]
  obtain ⟨s, hs⟩ := sqz_many d 1 0 k
  rw [Nat.zero_add] at hs
  exact nSteps_then_reachPos hs (sqz_even_exit (d + k) k)

private theorem round_y1 (d : ℕ) : reachPos (roundCfg d 1) (stageCfg (d + 2)) := by
  unfold stageCfg roundCfg
  refine step_then_reachPos (tr1_0 _ _) ?_
  rw [← ones_succ d B0, ones_succ 0 B0, ones_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr2_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr3_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr8_0 _ _) ?_
  rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr5_0 _ _) ?_
  rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
  have h0 : reachPos ⟨0, ⟨0, ones (d + 1) B0, B0⟩⟩
      ⟨1, mkL (ones (d + 1) B0) (ones 1 B0)⟩ :=
    reachPos_step (tr0_0 (ones (d + 1) B0) B0)
  have hsw := sweep1L tr1_1 (d + 1) B0 (ones 1 B0)
  rw [← ones_add (d + 1) 1 B0, mkL_B0] at hsw
  exact reachPos_then_nSteps h0 hsw

/-! ## Odd `3k + 2` Conservation Loop, `z > x` Merge & `z = x` Halt -/

/-- Odd conservation configuration (`L + r + m = x`): `0^∞ 1^L 0 1^(r - 1) [1] 0 1^m 0^∞` in
state `10` (for `r = 0`, `0^∞ 1^L [0] 0 1^m 0^∞`). -/
private def oddCfg (L r m : ℕ) : Cfg 17 2 :=
  ⟨10, mkL (ones r ((ones L B0).cons 0)) ((ones m B0).cons 0)⟩

private theorem sqz_odd_enter (d k' : ℕ) :
    reachPos (sqzCfg d 1 (k' + 1)) (oddCfg (d + 1) 0 (k' + 1)) := by
  unfold sqzCfg oddCfg
  let Rk := (ones (k' + 1) B0).cons 0
  change reachPos ⟨1, ⟨0, ones d B0, ones 1 Rk⟩⟩ _
  refine step_then_reachPos (tr1_0 _ _) ?_
  rw [← ones_succ d B0, ones_succ 0 Rk, ones_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr2_1 _ _) ?_
  dsimp only [Rk]
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_0 _ _) ?_
  rw [ones_succ k' B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr8_1 _ _) ?_
  rw [← ones_succ k' B0, ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr9_0 _ _)

private theorem odd_peel_to_14 (L r m : ℕ) :
    reachPos (oddCfg (L + 2) r m)
      ⟨14, Tape.mk' (ones (r + 3) ((ones L B0).cons 0)) (ones m B0)⟩ := by
  unfold oddCfg
  let LL2 := (ones (L + 2) B0).cons 0
  let Rm := (ones m B0).cons 0
  change reachPos ⟨10, mkL (ones r LL2) Rm⟩ _
  refine nSteps_then_reachPos (sweep1L tr10_1 r LL2 Rm) ?_
  dsimp only [LL2]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_0 _ _) ?_
  rw [show L + 2 = (L + 1) + 1 by omega, ones_succ (L + 1) B0, ErdosTernary15.Tape.mkL_cons,
    ← ones_succ r Rm]
  refine step_then_reachPos (tr11_1 _ _) ?_
  rw [ones_succ L B0, ErdosTernary15.Tape.mkL_cons, ← ones_succ (r + 1) Rm]
  refine step_then_reachPos (tr12_1 _ _) ?_
  let LL := (ones L B0).cons 0
  change reachPos ⟨13, Tape.mk' LL (ones (r + 2) Rm)⟩ _
  refine nSteps_then_reachPos (sweep1R tr13_1 (r + 2) LL Rm) ?_
  dsimp only [Rm]
  rw [ErdosTernary15.Tape.mk'_cons]
  have h13 := tr13_0 (ones (r + 2) LL) (ones m B0)
  rw [← ones_succ (r + 2) LL] at h13
  exact reachPos_step h13

private theorem odd_pass (L r m : ℕ) :
    reachPos (oddCfg (L + 2) r (m + 1)) (oddCfg L (r + 3) m) := by
  refine reachPos_trans (odd_peel_to_14 L r (m + 1)) ?_
  rw [ones_succ m B0, ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr14_1 _ _)

private theorem odd_many (L r m j : ℕ) :
    ∃ s : ℕ, nSteps weakCollatz17 s (oddCfg (L + 2 * j) r (m + j)) =
      some (oddCfg L (r + 3 * j) m) := by
  induction j generalizing L r with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ j ih =>
    rw [show L + 2 * (j + 1) = (L + 2 * j) + 2 by omega,
      show m + (j + 1) = (m + j) + 1 by omega]
    obtain ⟨s₁, _, hs₁⟩ := odd_pass (L + 2 * j) r (m + j)
    obtain ⟨s₂, hs₂⟩ := ih L (r + 3)
    rw [show r + 3 + 3 * j = r + 3 * (j + 1) by omega] at hs₂
    exact ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩

private theorem odd_done_to_16 (L r : ℕ) :
    reachPos (oddCfg (L + 2) r 0) ⟨16, mkL (ones L B0) ((ones (r + 2) B0).cons 0)⟩ := by
  refine reachPos_trans (odd_peel_to_14 L r 0) ?_
  rw [ones_zero, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr14_0 _ _) ?_
  let LL := (ones L B0).cons 0
  rw [B0_cons_zero, show r + 3 = (r + 2) + 1 by omega, ones_succ (r + 2) LL,
    ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr5_1 _ _) ?_
  rw [B0_cons_zero, show r + 2 = (r + 1) + 1 by omega, ones_succ (r + 1) LL,
    ErdosTernary15.Tape.mkL_cons]
  exact eback_to_haltchk (ones L B0) (r + 1)

private theorem odd_done_lt (d' r : ℕ) :
    reachPos (oddCfg (d' + 3) r 0) (roundCfg (d' + 1) (r + 2)) := by
  rw [show d' + 3 = (d' + 1) + 2 by omega]
  refine reachPos_trans (odd_done_to_16 (d' + 1) r) ?_
  rw [ones_succ d' B0, ErdosTernary15.Tape.mkL_cons]
  have h16 := tr16_1 (ones d' B0) ((ones (r + 2) B0).cons 0)
  rw [← ones_succ d' B0, ErdosTernary15.Tape.mk'_cons] at h16
  exact reachPos_step h16

private theorem odd_done_halt (r : ℕ) :
    ∃ s cfg, nSteps weakCollatz17 s (oddCfg 2 r 0) = some cfg ∧
      step weakCollatz17 cfg = none := by
  obtain ⟨s, _, hs⟩ := odd_done_to_16 0 r
  rw [ones_zero, mkL_B0] at hs
  exact ⟨s, _, hs, tr16_0 B0 ((ones (r + 2) B0).cons 0)⟩

private theorem gt_merge (r m : ℕ) :
    reachPos ⟨9, ⟨1, B0, ones r ((ones m B0).cons 0)⟩⟩ (stageCfg (r + m + 1)) := by
  unfold stageCfg roundCfg
  refine step_then_reachPos (tr9_1 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (sweep1R tr0_1 r B0 ((ones m B0).cons 0)) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  have h0 : reachPos ⟨0, ⟨0, ones r B0, ones m B0⟩⟩
      ⟨1, mkL (ones r B0) (ones (m + 1) B0)⟩ :=
    reachPos_step (tr0_0 (ones r B0) (ones m B0))
  have hsw := sweep1L tr1_1 r B0 (ones (m + 1) B0)
  rw [← ones_add r (m + 1) B0, mkL_B0, show r + (m + 1) = r + m + 1 by omega] at hsw
  exact reachPos_then_nSteps h0 hsw

private theorem odd_abort_L0 (r m : ℕ) :
    reachPos (oddCfg 0 r m) (stageCfg (r + m + 1)) := by
  unfold oddCfg
  rw [ones_zero, B0_cons_zero]
  let Rm := (ones m B0).cons 0
  change reachPos ⟨10, mkL (ones r B0) Rm⟩ _
  refine nSteps_then_reachPos (sweep1L tr10_1 r B0 Rm) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr10_0 _ _) ?_
  rw [mkL_B0, ← ones_succ r Rm]
  refine step_then_reachPos (tr11_0 _ _) ?_
  rw [B0_cons_zero, ones_succ r Rm, ErdosTernary15.Tape.mk'_cons]
  exact gt_merge r m

private theorem odd_abort_L1 (r m : ℕ) :
    reachPos (oddCfg 1 r m) (stageCfg (1 + r + m + 1)) := by
  unfold oddCfg
  let L1 := (ones 1 B0).cons 0
  let Rm := (ones m B0).cons 0
  change reachPos ⟨10, mkL (ones r L1) Rm⟩ _
  refine nSteps_then_reachPos (sweep1L tr10_1 r L1 Rm) ?_
  dsimp only [L1]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_0 _ _) ?_
  rw [ones_succ 0 B0, ones_zero, ErdosTernary15.Tape.mkL_cons, ← ones_succ r Rm]
  refine step_then_reachPos (tr11_1 _ _) ?_
  rw [mkL_B0, ← ones_succ (r + 1) Rm]
  refine step_then_reachPos (tr12_0 _ _) ?_
  rw [B0_cons_zero, ones_succ (r + 1) Rm, ErdosTernary15.Tape.mk'_cons]
  rw [show 1 + r + m + 1 = (r + 1) + m + 1 by omega]
  exact gt_merge (r + 1) m

/-! ## Round Dispatch (`z < x`, `z > x`, `z = x`, `y = 1`) & Blank-Tape Boot -/

private theorem round_to_odd (d k : ℕ) (hk : 1 ≤ k) :
    reachPos (roundCfg d (2 * k + 1)) (oddCfg (d + k + 1) 0 k) := by
  rw [roundCfg_eq_sqzCfg, show 2 * k + 1 = (0 + 1) + 2 * k by omega]
  obtain ⟨s, hs⟩ := sqz_many d 0 0 k
  have hsqz : sqzCfg (d + k) (0 + 1) (0 + k) = sqzCfg (d + k) 1 ((k - 1) + 1) := by
    congr 1; omega
  rw [hsqz] at hs
  have hent := sqz_odd_enter (d + k) (k - 1)
  have hodd : oddCfg (d + k + 1) 0 ((k - 1) + 1) = oddCfg (d + k + 1) 0 k := by
    congr 1; omega
  rw [hodd] at hent
  exact nSteps_then_reachPos hs hent

private theorem even_or_odd_constructive (y : ℕ) : ∃ m : ℕ, y = 2 * m ∨ y = 2 * m + 1 :=
  ⟨y / 2, by omega⟩

private theorem stage_round_lt (x y : ℕ) (hy2 : 2 ≤ y) (hyle : y ≤ x) (hlt : terras y < x) :
    reachPos (roundCfg (x - y) y) (roundCfg (x - terras y) (terras y)) := by
  rcases even_or_odd_constructive y with ⟨m, rfl | rfl⟩
  · have hm1 : 1 ≤ m := by omega
    have hte : terras (2 * m) = m := by unfold terras; split <;> omega
    rw [hte]
    let k := m - 1
    have hy_eq : 2 * m = 2 * k + 2 := by dsimp only [k]; omega
    rw [hy_eq]
    have hrev := round_even (x - (2 * k + 2)) k
    have hd_eq : x - (2 * k + 2) + k + 1 = x - m := by dsimp only [k]; omega
    have hk_eq : k + 1 = m := by dsimp only [k]; omega
    rw [hd_eq, hk_eq] at hrev
    exact hrev
  · have hm1 : 1 ≤ m := by omega
    have hto : terras (2 * m + 1) = 3 * m + 2 := by unfold terras; split <;> omega
    rw [hto] at hlt ⊢
    have h1 := round_to_odd (x - (2 * m + 1)) m hm1
    let d' := x - (3 * m + 2) - 1
    have hL : x - (2 * m + 1) + m + 1 = (d' + 3) + 2 * m := by dsimp only [d']; omega
    rw [hL] at h1
    obtain ⟨s, hs⟩ := odd_many (d' + 3) 0 0 m
    simp only [Nat.zero_add] at hs
    have hfin := odd_done_lt d' (3 * m)
    rw [show d' + 1 = x - (3 * m + 2) by dsimp only [d']; omega] at hfin
    exact reachPos_trans h1 (nSteps_then_reachPos hs hfin)

private theorem stage_round_gt (x y : ℕ) (hx : 3 ≤ x) (hy2 : 2 ≤ y) (hyle : y ≤ x)
    (hgt : x < terras y) :
    reachPos (roundCfg (x - y) y) (stageCfg (x + 1)) := by
  rcases even_or_odd_constructive y with ⟨m, rfl | rfl⟩
  · exfalso
    have hte : terras (2 * m) = m := by unfold terras; split <;> omega
    omega
  · have hm1 : 1 ≤ m := by omega
    have hto : terras (2 * m + 1) = 3 * m + 2 := by unfold terras; split <;> omega
    rw [hto] at hgt
    have h1 := round_to_odd (x - (2 * m + 1)) m hm1
    let L₀ := x - m
    have hL₀_eq : x - (2 * m + 1) + m + 1 = L₀ := by dsimp only [L₀]; omega
    rw [hL₀_eq] at h1
    let j := L₀ / 2
    let rem := L₀ % 2
    have hj_le : j ≤ m := by dsimp only [j, L₀]; omega
    have hL_split : L₀ = rem + 2 * j := by dsimp only [j, rem]; omega
    have hm_split : m = (m - j) + j := by omega
    obtain ⟨s, hs⟩ := odd_many rem 0 (m - j) j
    have hin : oddCfg (rem + 2 * j) 0 ((m - j) + j) = oddCfg L₀ 0 m := by
      rw [← hL_split, ← hm_split]
    rw [hin, Nat.zero_add] at hs
    have hrem01 : rem = 0 ∨ rem = 1 := by dsimp only [rem]; omega
    rcases hrem01 with hrem0 | hrem1
    · rw [hrem0] at hs
      have hab := odd_abort_L0 (3 * j) (m - j)
      have hsum : 3 * j + (m - j) + 1 = x + 1 := by
        have : rem = 0 := hrem0
        dsimp only [j, rem, L₀] at this hj_le ⊢
        omega
      rw [hsum] at hab
      exact reachPos_trans h1 (nSteps_then_reachPos hs hab)
    · rw [hrem1] at hs
      have hab := odd_abort_L1 (3 * j) (m - j)
      have hsum : 1 + 3 * j + (m - j) + 1 = x + 1 := by
        have : rem = 1 := hrem1
        dsimp only [j, rem, L₀] at this hj_le ⊢
        omega
      rw [hsum] at hab
      exact reachPos_trans h1 (nSteps_then_reachPos hs hab)

private theorem stage_round_halt (x y : ℕ) (hx : 3 ≤ x) (hy2 : 2 ≤ y) (hyle : y ≤ x)
    (heq : terras y = x) :
    ∃ s cfg, nSteps weakCollatz17 s (roundCfg (x - y) y) = some cfg ∧
      step weakCollatz17 cfg = none := by
  rcases even_or_odd_constructive y with ⟨m, rfl | rfl⟩
  · exfalso
    have hte : terras (2 * m) = m := by unfold terras; split <;> omega
    omega
  · have hm1 : 1 ≤ m := by omega
    have hto : terras (2 * m + 1) = 3 * m + 2 := by unfold terras; split <;> omega
    rw [hto] at heq
    obtain ⟨s₁, _, hs₁⟩ := round_to_odd (x - (2 * m + 1)) m hm1
    have hL : x - (2 * m + 1) + m + 1 = 2 + 2 * m := by omega
    rw [hL] at hs₁
    obtain ⟨s₂, hs₂⟩ := odd_many 2 0 0 m
    simp only [Nat.zero_add] at hs₂
    obtain ⟨s₃, cfg, hs₃, hnone⟩ := odd_done_halt (3 * m)
    exact ⟨s₁ + s₂ + s₃, cfg, nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃, hnone⟩

private theorem stage_y1_advance (x : ℕ) (hx : 1 ≤ x) :
    reachPos (roundCfg (x - 1) 1) (stageCfg (x + 1)) := by
  have h := round_y1 (x - 1)
  rw [show x - 1 + 2 = x + 1 by omega] at h
  exact h

private theorem init_reaches_stage3 : reachPos init (stageCfg 3) := by
  have h01 : reachPos init (stageCfg 1) := reachPos_step (tr0_0 B0 B0)
  exact reachPos_trans h01 (reachPos_trans (round_y1 0)
    (reachPos_trans (round_even 0 0) (round_y1 1)))

/-! ## Cycle-Maximum Dovetailing & Halting Equivalence -/

private theorem terras_pos_of_pos {y : ℕ} (hy : 1 ≤ y) : 1 ≤ terras y := by
  unfold terras; split <;> omega

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
    m = 0 ∨ (1 ≤ m ∧ reachPos (stageCfg x) (roundCfg (x - terras^[m] x) (terras^[m] x))) := by
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
      have h0 : stageCfg x = roundCfg (x - x) x := by unfold stageCfg; rw [Nat.sub_self]
      rw [h0]
      exact stage_round_lt x x (by omega) le_rfl hlt1
    · have hym := hstay m hm1 (by omega)
      have hlt : terras (terras^[m] x) < x := by
        rw [← Function.iterate_succ_apply' terras m x]
        exact hstep.2
      rw [Function.iterate_succ_apply']
      exact reachPos_trans hprev
        (stage_round_lt x (terras^[m] x) hym.1 (le_of_lt hym.2) hlt)

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
    reachPos (stageCfg x) (stageCfg (x + 1)) := by
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
      have h0 : stageCfg x = roundCfg (x - x) x := by unfold stageCfg; rw [Nat.sub_self]
      rw [h0]
      rcases hor with h1 | hgt
      · have hlt := stage_round_lt x x (by omega) le_rfl (by omega)
        rw [h1] at hlt
        exact reachPos_trans hlt (stage_y1_advance x (by omega))
      · exact stage_round_gt x x hx (by omega) le_rfl hgt
    · have hy_prev := hprev (t - 1) ht1_pos le_rfl
      have hnext : terras (terras^[t - 1] x) = terras^[t] x := by
        rw [← Function.iterate_succ_apply' terras (t - 1) x, show (t - 1).succ = t by omega]
      rcases hor with h1 | hgt
      · have hlt :=
          stage_round_lt x (terras^[t - 1] x) hy_prev.1 (le_of_lt hy_prev.2)
            (by rw [hnext]; omega)
        rw [hnext, h1] at hlt
        exact reachPos_trans hreach_prev (reachPos_trans hlt (stage_y1_advance x (by omega)))
      · rw [← hnext] at hgt
        exact reachPos_trans hreach_prev
          (stage_round_gt x (terras^[t - 1] x) hx hy_prev.1 (le_of_lt hy_prev.2) hgt)

private theorem reach_stage_from_init (X : ℕ) (hX : 3 ≤ X) (hno : NoStageHalts (X - 1)) :
    ∃ s : ℕ, X - 2 ≤ s ∧ nSteps weakCollatz17 s init = some (stageCfg X) := by
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
    ∃ s cfg, nSteps weakCollatz17 s (stageCfg x) = some cfg ∧
      step weakCollatz17 cfg = none := by
  obtain ⟨t, ht1, _, hprev, hhit⟩ := hhalt
  rcases stage_stay_reach x hx (t - 1) hprev with ht0 | ⟨ht1_pos, hreach_prev⟩
  · have ht_eq1 : t = 1 := by omega
    subst ht_eq1
    rw [Function.iterate_one] at hhit
    have h0 : stageCfg x = roundCfg (x - x) x := by unfold stageCfg; rw [Nat.sub_self]
    rw [h0]
    exact stage_round_halt x x hx (by omega) le_rfl hhit
  · obtain ⟨s₁, _, hs₁⟩ := hreach_prev
    have hy_prev := hprev (t - 1) ht1_pos le_rfl
    have hhit' : terras (terras^[t - 1] x) = x := by
      rw [← Function.iterate_succ_apply' terras (t - 1) x, show (t - 1).succ = t by omega]
      exact hhit
    obtain ⟨s₂, cfg, hs₂, hnone⟩ :=
      stage_round_halt x (terras^[t - 1] x) hx hy_prev.1 (le_of_lt hy_prev.2) hhit'
    exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-- The 17-state machine `weakCollatz17` (`weak_collatz_17`) halts on the blank tape if and only if
there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(constructive, zero `Classical.choice`). -/
theorem halts_weakCollatz17_iff_bounded_cycle :
    ConjectureMachines.Halts weakCollatz17 ↔
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
      ⟨M, jM, hM3, hjM1, _hjMM, hjM_cyc, hbnd, -⟩
    have hM_halts : StageHalts M :=
      stageHalts_of_cycle_max hM3 hjM1 (by omega) hjM_cyc hbnd
    rcases noStageHalts_or_first M with hno | ⟨w₀, hw₀3, -, hprev₀, hhalt₀⟩
    · exfalso
      exact hno M hM3 le_rfl hM_halts
    · obtain ⟨s₁, -, hs₁⟩ := reach_stage_from_init w₀ hw₀3 hprev₀
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt_of_stageHalts w₀ hw₀3 hhalt₀
      rw [Part.dom_iff_mem]
      exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches (nSteps_bind_eq hs₁ hs₂), hnone⟩⟩

/-- The 17-state candidate machine halts on the blank tape if and only if the 27-state reference
machine does (constructive, zero `Classical.choice`). -/
theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  halts_weakCollatz17_iff_bounded_cycle.trans
    WeakCollatz27.halts_weakCollatz27_iff_bounded_cycle.symm

/-- The candidate has 10 fewer states than the 27-state reference (`17 < 27`). -/
theorem candidate_fewer_states : candidate.states < reference.states := by
  decide +kernel

end ConjectureMachines.WeakCollatz17
