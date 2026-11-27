/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz75

/-!
# WeakCollatz41 (`weak_collatz_41`)

The 41-state, 2-symbol Turing machine `weak_collatz_41` compresses `weak_collatz_75` (`75 → 41`
states, `-34` states / `-45.33%`) while constructively preserving blank-tape halting equivalence:
it halts on the blank tape if and only if there exist `x ≥ 3` and `1 ≤ j ≤ x` with
`terras^[j] x = x` (`halts_weakCollatz41_iff_bounded_cycle`), and hence if and only if
`weak_collatz_75` halts (`candidate_equivalent`, proved without `Classical.choice`).

Notice why **Tao's Weak Collatz Conjecture** (absence of nontrivial positive cycles) is the exact
blank-tape halting ($\Sigma_1^0$) half of the Collatz problem: existence of a divergent trajectory
($\exists x,\; \forall k,\; T^k(x) \neq 1$) is $\Sigma_2^0$ and cannot be semi-decided by blank-tape
halting without an oracle, whereas existence of a nontrivial cycle
($\exists x \ge 3,\; \exists j \ge 1,\; T^j(x) = x$) is $\Sigma_1^0$.

## Compression Ideas (`75 → 41` states)

At canonical checkpoint `stageCfg c x y` (`c ≥ 1`, `x ≥ 3`, `y ≥ 1`), the tape holds
`0^∞  1^c  0  1^x  0  [1] 1^(y - 1)  0^∞` in state `12` with **single-zero** delimiters and
**zero unbounded blank gaps**:
1. **Adjacent `1^x 0 1^y` Layout & Left-End Counter Decrement**: placing `1^c` on the outer left
   (`1^c 0 1^x 0 1^y` instead of `1^x 00 1^c 0^(g + 2) 1^y`) makes `1^x` and `1^z` directly
   adjacent during comparison and lets counter decrements erase the leftmost `1` of `1^c` into `0^∞`
   without creating a growing `0^(g + 2)` gap.
2. **In-Place Zero-Gap `terras` Engine (`states 12–22`)**: moves a single `0`-hole right across
   `1^y` while peeling `1`s from the right end; even `y = 2k + 2` finishes directly as `1^(k + 1)`
   when the right suffix vanishes into `0^∞`, while odd `y = 2k + 1` reverses the hole leftward to
   expand `1^k` into `1^(3k + 2)` in place.
3. **Local `2p` Comparison & Unified Restoration (`states 0, 1, 20, 22, 23–31`)**: compares
   `1^x 0 1^z` in place as `1^u 0 1^v 0 1^(2p)` (`u + p = x`, `v + p = z`) without ever sweeping
   across `1^c` or `1^(2p)`, halting at `(25, 0)` iff `u = v = 0`, and otherwise restoring
   `1^x 0 1^z` via a single shared reverse loop for both `z < x` and `z > x`.
4. **Right-to-Left 1-Pass Triple-Build & 6-Step Boot (`states 0–11, 34–40`)**: builds all three
   blocks `1^A 0 1^A 0 1^A` from `1^A` in a single pass rather than two sequential copy passes, and
   uses the sole remaining `0`-transition `(1, 0)` for a 6-step blank-tape entry into
   `tripleCfg 0 3`, achieving `81/81` active transition coverage (`82/82` cells including halt).
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz41

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_zero nSteps_succ nSteps_reaches
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- 75-state Weak Collatz reference machine (`weak_collatz_75`). -/
abbrev reference : BundledMachine 2 := Machines.weakCollatz75.bundle

/-- 41-state Weak Collatz candidate machine (`weak_collatz_41`). -/
abbrev candidate : BundledMachine 2 := Machines.weakCollatz41.bundle

/-- The candidate as a `Machine 41 2`. -/
abbrev weakCollatz41 : Machine 41 2 := Machines.weakCollatz41

private theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

private theorem ones_zero (X : ListBlank (Fin 2)) : ones 0 X = X := rfl

private theorem ones_succ (k : ℕ) (X : ListBlank (Fin 2)) : ones (k + 1) X = (ones k X).cons 1 :=
  rfl

private theorem stepR {q q' : Fin 41} {a b : Fin 2}
    (h : weakCollatz41.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz41 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

private theorem stepL {q q' : Fin 41} {a b : Fin 2}
    (h : weakCollatz41.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz41 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table -/

private theorem tr0_0 (L R) :
    step weakCollatz41 ⟨0, ⟨0, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr0_1 (L R) : step weakCollatz41 ⟨0, ⟨1, L, R⟩⟩ = some ⟨0, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr1_0 (L R) :
    step weakCollatz41 ⟨1, ⟨0, L, R⟩⟩ = some ⟨35, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr1_1 (L R) :
    step weakCollatz41 ⟨1, ⟨1, L, R⟩⟩ = some ⟨30, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr2_0 (L R) : step weakCollatz41 ⟨2, ⟨0, L, R⟩⟩ = some ⟨34, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr2_1 (L R) :
    step weakCollatz41 ⟨2, ⟨1, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr3_0 (L R) :
    step weakCollatz41 ⟨3, ⟨0, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr3_1 (L R) :
    step weakCollatz41 ⟨3, ⟨1, L, R⟩⟩ = some ⟨35, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr4_0 (L R) :
    step weakCollatz41 ⟨4, ⟨0, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr4_1 (L R) :
    step weakCollatz41 ⟨4, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr5_0 (L R) : step weakCollatz41 ⟨5, ⟨0, L, R⟩⟩ = some ⟨6, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr5_1 (L R) :
    step weakCollatz41 ⟨5, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr6_0 (L R) : step weakCollatz41 ⟨6, ⟨0, L, R⟩⟩ = some ⟨7, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr6_1 (L R) : step weakCollatz41 ⟨6, ⟨1, L, R⟩⟩ = some ⟨6, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr7_0 (L R) : step weakCollatz41 ⟨7, ⟨0, L, R⟩⟩ = some ⟨8, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr7_1 (L R) : step weakCollatz41 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr8_0 (L R) : step weakCollatz41 ⟨8, ⟨0, L, R⟩⟩ = some ⟨9, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr8_1 (L R) : step weakCollatz41 ⟨8, ⟨1, L, R⟩⟩ = some ⟨8, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr9_0 (L R) :
    step weakCollatz41 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr9_1 (L R) : step weakCollatz41 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr10_0 (L R) :
    step weakCollatz41 ⟨10, ⟨0, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr10_1 (L R) :
    step weakCollatz41 ⟨10, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr11_0 (L R) : step weakCollatz41 ⟨11, ⟨0, L, R⟩⟩ = some ⟨2, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr11_1 (L R) :
    step weakCollatz41 ⟨11, ⟨1, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr12_0 (L R) :
    step weakCollatz41 ⟨12, ⟨0, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr12_1 (L R) :
    step weakCollatz41 ⟨12, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr13_0 (L R) : step weakCollatz41 ⟨13, ⟨0, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr13_1 (L R) :
    step weakCollatz41 ⟨13, ⟨1, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr14_0 (L R) : step weakCollatz41 ⟨14, ⟨0, L, R⟩⟩ = some ⟨15, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr14_1 (L R) :
    step weakCollatz41 ⟨14, ⟨1, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr15_0 (L R) : step weakCollatz41 ⟨15, ⟨0, L, R⟩⟩ = some ⟨23, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr15_1 (L R) : step weakCollatz41 ⟨15, ⟨1, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr16_0 (L R) :
    step weakCollatz41 ⟨16, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr16_1 (L R) : step weakCollatz41 ⟨16, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr17_0 (L R) :
    step weakCollatz41 ⟨17, ⟨0, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr17_1 (L R) : step weakCollatz41 ⟨17, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr18_0 (L R) :
    step weakCollatz41 ⟨18, ⟨0, L, R⟩⟩ = some ⟨22, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr18_1 (L R) :
    step weakCollatz41 ⟨18, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr19_0 (L R) :
    step weakCollatz41 ⟨19, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr19_1 (L R) :
    step weakCollatz41 ⟨19, ⟨1, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr20_0 (L R) : step weakCollatz41 ⟨20, ⟨0, L, R⟩⟩ = some ⟨21, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr20_1 (L R) : step weakCollatz41 ⟨20, ⟨1, L, R⟩⟩ = some ⟨22, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr21_0 (L R) : step weakCollatz41 ⟨21, ⟨0, L, R⟩⟩ = some ⟨18, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr21_1 (L R) : step weakCollatz41 ⟨21, ⟨1, L, R⟩⟩ = some ⟨21, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr22_0 (L R) : step weakCollatz41 ⟨22, ⟨0, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr22_1 (L R) : step weakCollatz41 ⟨22, ⟨1, L, R⟩⟩ = some ⟨23, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr23_0 (L R) : step weakCollatz41 ⟨23, ⟨0, L, R⟩⟩ = some ⟨25, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr23_1 (L R) : step weakCollatz41 ⟨23, ⟨1, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr24_0 (L R) : step weakCollatz41 ⟨24, ⟨0, L, R⟩⟩ = some ⟨27, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr24_1 (L R) : step weakCollatz41 ⟨24, ⟨1, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr25_0 (L R : ListBlank (Fin 2)) : step weakCollatz41 ⟨25, ⟨0, L, R⟩⟩ = none := rfl
private theorem tr25_1 (L R) :
    step weakCollatz41 ⟨25, ⟨1, L, R⟩⟩ = some ⟨26, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr26_0 (L R) :
    step weakCollatz41 ⟨26, ⟨0, L, R⟩⟩ = some ⟨30, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr26_1 (L R) : step weakCollatz41 ⟨26, ⟨1, L, R⟩⟩ = some ⟨32, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr27_0 (L R) :
    step weakCollatz41 ⟨27, ⟨0, L, R⟩⟩ = some ⟨26, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr27_1 (L R) :
    step weakCollatz41 ⟨27, ⟨1, L, R⟩⟩ = some ⟨28, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr28_0 (L R) :
    step weakCollatz41 ⟨28, ⟨0, L, R⟩⟩ = some ⟨29, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr28_1 (L R) : step weakCollatz41 ⟨28, ⟨1, L, R⟩⟩ = some ⟨0, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr29_0 (L R) : step weakCollatz41 ⟨29, ⟨0, L, R⟩⟩ = some ⟨20, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr29_1 (L R) :
    step weakCollatz41 ⟨29, ⟨1, L, R⟩⟩ = some ⟨29, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr30_0 (L R) :
    step weakCollatz41 ⟨30, ⟨0, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr30_1 (L R) :
    step weakCollatz41 ⟨30, ⟨1, L, R⟩⟩ = some ⟨30, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr31_0 (L R) : step weakCollatz41 ⟨31, ⟨0, L, R⟩⟩ = some ⟨26, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr31_1 (L R) :
    step weakCollatz41 ⟨31, ⟨1, L, R⟩⟩ = some ⟨28, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr32_0 (L R) : step weakCollatz41 ⟨32, ⟨0, L, R⟩⟩ = some ⟨33, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr32_1 (L R) : step weakCollatz41 ⟨32, ⟨1, L, R⟩⟩ = some ⟨32, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr33_0 (L R) : step weakCollatz41 ⟨33, ⟨0, L, R⟩⟩ = some ⟨34, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr33_1 (L R) : step weakCollatz41 ⟨33, ⟨1, L, R⟩⟩ = some ⟨33, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr34_0 (L R) :
    step weakCollatz41 ⟨34, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr34_1 (L R) : step weakCollatz41 ⟨34, ⟨1, L, R⟩⟩ = some ⟨34, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr35_0 (L R) :
    step weakCollatz41 ⟨35, ⟨0, L, R⟩⟩ = some ⟨38, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr35_1 (L R) :
    step weakCollatz41 ⟨35, ⟨1, L, R⟩⟩ = some ⟨36, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr36_0 (L R) :
    step weakCollatz41 ⟨36, ⟨0, L, R⟩⟩ = some ⟨37, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr36_1 (L R) :
    step weakCollatz41 ⟨36, ⟨1, L, R⟩⟩ = some ⟨36, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr37_0 (L R) :
    step weakCollatz41 ⟨37, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr37_1 (L R) :
    step weakCollatz41 ⟨37, ⟨1, L, R⟩⟩ = some ⟨37, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr38_0 (L R) :
    step weakCollatz41 ⟨38, ⟨0, L, R⟩⟩ = some ⟨39, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr38_1 (L R) :
    step weakCollatz41 ⟨38, ⟨1, L, R⟩⟩ = some ⟨38, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr39_0 (L R) : step weakCollatz41 ⟨39, ⟨0, L, R⟩⟩ = some ⟨40, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr39_1 (L R) :
    step weakCollatz41 ⟨39, ⟨1, L, R⟩⟩ = some ⟨39, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr40_0 (L R) : step weakCollatz41 ⟨40, ⟨0, L, R⟩⟩ = some ⟨2, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr40_1 (L R) : step weakCollatz41 ⟨40, ⟨1, L, R⟩⟩ = some ⟨40, mkL L (R.cons 0)⟩ :=
  stepL rfl L R

/-! ## Sweep & Reachability Combinators -/

private def reachPos (c₁ c₂ : Cfg 41 2) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ nSteps weakCollatz41 s c₁ = some c₂

private theorem reachPos_step {c₁ c₂ : Cfg 41 2}
    (h : step weakCollatz41 c₁ = some c₂) : reachPos c₁ c₂ :=
  ⟨1, le_rfl, step_one h⟩

private theorem reachPos_trans {c₁ c₂ c₃ : Cfg 41 2}
    (h₁ : reachPos c₁ c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s₁, hs₁, heq₁⟩ := h₁
  obtain ⟨s₂, hs₂, heq₂⟩ := h₂
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq heq₁ heq₂⟩

private theorem step_then_reachPos {c₁ c₂ c₃ : Cfg 41 2}
    (h₁ : step weakCollatz41 c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ :=
  reachPos_trans (reachPos_step h₁) h₂

private theorem nSteps_then_reachPos {k : ℕ} {c₁ c₂ c₃ : Cfg 41 2}
    (h₁ : nSteps weakCollatz41 k c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₂
  exact ⟨k + s, by omega, nSteps_bind_eq h₁ heq⟩

private theorem reachPos_then_nSteps {k : ℕ} {c₁ c₂ c₃ : Cfg 41 2}
    (h₁ : reachPos c₁ c₂) (h₂ : nSteps weakCollatz41 k c₂ = some c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₁
  exact ⟨s + k, by omega, nSteps_bind_eq heq h₂⟩

private theorem sweep1R {q : Fin 41}
    (h : ∀ L R, step weakCollatz41 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz41 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweep1L {q : Fin 41}
    (h : ∀ L R, step weakCollatz41 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz41 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

private theorem erase1L {q : Fin 41}
    (h : ∀ L R, step weakCollatz41 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 0)⟩)
    (k : ℕ) (L : ListBlank (Fin 2)) :
    nSteps weakCollatz41 k ⟨q, mkL (ones k L) B0⟩ = some ⟨q, mkL L B0⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mkL_cons, h, B0_cons_zero, Option.bind_some, ih]

/-! ## Canonical Stage Checkpoint & 1-Pass Triple-Build -/

private def baseCX (c x : ℕ) : ListBlank (Fin 2) :=
  ones x ((ones c B0).cons 0)

/-- Canonical stage checkpoint: `0^∞ 1^c 0 1^x 0 [1] 1^(y - 1) 0^∞` in state `12`. -/
private def stageCfg (c x y : ℕ) : Cfg 41 2 :=
  ⟨12, Tape.mk' ((baseCX c x).cons 0) (ones y B0)⟩

private def tripleCfg (p rem : ℕ) : Cfg 41 2 :=
  ⟨2, mkL (ones rem ((ones p B0).cons 0)) ((ones p ((ones p B0).cons 0)).cons 0)⟩

private theorem boot_to_triple : reachPos init (tripleCfg 0 3) := by
  refine ⟨6, by decide, ?_⟩
  change nSteps weakCollatz41 6 ⟨0, ⟨0, B0, B0⟩⟩ = some (tripleCfg 0 3)
  simp only [tripleCfg, ones_succ, ones_zero, nSteps_succ, nSteps_zero, Option.bind_some,
    tr0_0, tr1_0, tr35_0, tr38_0, tr39_0, tr40_0,
    ErdosTernary15.Tape.mkL_cons, ErdosTernary15.Tape.mk'_B0, B0_cons_zero]

private theorem triple_step (p rem : ℕ) :
    reachPos (tripleCfg p (rem + 1)) (tripleCfg (p + 1) rem) := by
  unfold tripleCfg
  let Lp := (ones p B0).cons 0
  let Rp := (ones p Lp).cons 0
  change reachPos ⟨2, mkL (ones (rem + 1) Lp) Rp⟩ _
  rw [ones_succ rem Lp, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr2_1 _ _) ?_
  dsimp only [Rp]
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_0 _ _) ?_
  change reachPos ⟨4, Tape.mk' (ones 1 ((ones rem Lp).cons 0)) (ones p Lp)⟩ _
  refine nSteps_then_reachPos (sweep1R tr4_1 p _ Lp) ?_
  rw [← ones_add p 1 ((ones rem Lp).cons 0)]
  dsimp only [Lp]
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr4_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr5_1 p _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr5_0 _ _) ?_
  change reachPos ⟨6, mkL (ones p _) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr6_1 p _ _) ?_
  rw [← ones_add p 1 B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr6_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr7_1 (p + 1) _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr7_0 _ _) ?_
  let Rn := (ones (p + 1) ((ones (p + 1) B0).cons 0)).cons 0
  change reachPos ⟨8, mkL (ones rem ((ones p B0).cons 0)) Rn⟩ _
  refine nSteps_then_reachPos (sweep1L tr8_1 rem _ Rn) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr8_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr9_1 p B0 _) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr9_0 _ _) ?_
  change reachPos ⟨10, Tape.mk' (ones 1 B0) (ones p ((ones rem Rn).cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr10_1 p _ _) ?_
  rw [← ones_add p 1 B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr10_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr11_1 rem _ Rn) ?_
  dsimp only [Rn]
  rw [ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr11_0 _ _)

private theorem triple_many (p rem : ℕ) :
    rem = 0 ∨ reachPos (tripleCfg p rem) (tripleCfg (p + rem) 0) := by
  induction rem generalizing p with
  | zero => exact Or.inl rfl
  | succ rem ih =>
    refine Or.inr ?_
    rcases ih (p + 1) with rfl | hrest
    · rw [Nat.add_zero]
      exact triple_step p 0
    · rw [show p + (rem + 1) = (p + 1) + rem by omega]
      exact reachPos_trans (triple_step p rem) hrest

private theorem triple_finish (a : ℕ) :
    reachPos (tripleCfg (a + 2) 0) (stageCfg (a + 2) (a + 2) (a + 2)) := by
  let A := a + 2
  unfold tripleCfg stageCfg baseCX
  change reachPos ⟨2, mkL (ones 0 ((ones A B0).cons 0)) ((ones A ((ones A B0).cons 0)).cons 0)⟩
    ⟨12, Tape.mk' ((ones A ((ones A B0).cons 0)).cons 0) (ones A B0)⟩
  rw [ones_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr2_0 _ _) ?_
  let Rtail := ((ones A ((ones A B0).cons 0)).cons 0)
  change reachPos ⟨34, mkL (ones A B0) (ones 1 Rtail)⟩ _
  refine nSteps_then_reachPos (sweep1L tr34_1 A B0 _) ?_
  rw [← ones_add A 1 Rtail, mkL_B0]
  refine step_then_reachPos (tr34_0 _ _) ?_
  rw [B0_cons_zero, show A + 1 = A.succ from rfl, ones_succ A Rtail, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  rw [B0_cons_zero, show A = (a + 1) + 1 from rfl, ones_succ (a + 1) Rtail,
    ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr35_1 _ _) ?_
  change reachPos ⟨36, Tape.mk' (ones 1 B0) (ones (a + 1) Rtail)⟩ _
  refine nSteps_then_reachPos (sweep1R tr36_1 (a + 1) _ Rtail) ?_
  rw [← ones_add (a + 1) 1 B0, show (a + 1) + 1 = A from rfl]
  dsimp only [Rtail]
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr36_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr37_1 A _ ((ones A B0).cons 0)) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr37_0 _ _)

private theorem triple_from_zero (a : ℕ) :
    reachPos (tripleCfg 0 (a + 2)) (stageCfg (a + 2) (a + 2) (a + 2)) := by
  rcases triple_many 0 (a + 2) with h0 | hmany
  · exfalso; omega
  · rw [Nat.zero_add] at hmany
    exact reachPos_trans hmany (triple_finish a)

private theorem init_reaches_stage3 : reachPos init (stageCfg 3 3 3) :=
  reachPos_trans boot_to_triple (triple_from_zero 1)

/-! ## Zero-Gap In-Place `terras` Evaluation -/

private def evenCfg (L0 : ListBlank (Fin 2)) (a b : ℕ) : Cfg 41 2 :=
  ⟨14, Tape.mk' ((ones a L0).cons 0) (ones b B0)⟩

private theorem even_step (L0 : ListBlank (Fin 2)) (a b : ℕ) :
    reachPos (evenCfg L0 a (b + 2)) (evenCfg L0 (a + 1) b) := by
  unfold evenCfg
  refine nSteps_then_reachPos (sweep1R tr14_1 (b + 2) _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr14_0 _ _) ?_
  rw [B0_cons_zero, ones_succ (b + 1) _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr15_1 _ _) ?_
  rw [B0_cons_zero, ones_succ b _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr16_1 _ _) ?_
  change reachPos ⟨17, mkL (ones b ((ones a L0).cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr17_1 b _ _) ?_
  rw [← ones_add b 1 B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr17_0 _ _) ?_
  rw [← ones_succ a L0, ones_succ b B0, ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr13_1 _ _)

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

private def oddCfg (L0 : ListBlank (Fin 2)) (m r : ℕ) : Cfg 41 2 :=
  ⟨18, mkL (ones m L0) ((ones r B0).cons 0)⟩

private theorem odd_step (L0 : ListBlank (Fin 2)) (m r : ℕ) :
    reachPos (oddCfg L0 (m + 1) r) (oddCfg L0 m (r + 3)) := by
  unfold oddCfg
  rw [ones_succ m L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr18_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr12_0 _ _) ?_
  change reachPos ⟨19, Tape.mk' (ones 1 ((ones m L0).cons 0)) (ones r B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr19_1 r _ B0) ?_
  rw [← ones_add r 1 ((ones m L0).cons 0), ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr19_0 _ _) ?_
  rw [← ones_succ (r + 1) _, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr20_0 _ _) ?_
  change reachPos ⟨21, mkL (ones (r + 2) ((ones m L0).cons 0)) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr21_1 (r + 2) _ _) ?_
  rw [← ones_add (r + 2) 1 B0, show r + 2 + 1 = r + 3 by omega, ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr21_0 _ _)

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

private theorem terras_eval (c x y : ℕ) (hy : 1 ≤ y) :
    reachPos (stageCfg c x y) ⟨24, mkL ((baseCX c x).cons 0) (ones (terras y) B0)⟩ := by
  let L0 := (baseCX c x).cons 0
  rcases Nat.mod_two_eq_zero_or_one y with hev | hodd
  · let k := y / 2 - 1
    have hy_eq : y = 2 * k + 2 := by dsimp [k]; omega
    have hty : terras y = k + 1 := by unfold terras; simp [hev]; dsimp [k]; omega
    rw [hty, hy_eq]
    unfold stageCfg
    change reachPos ⟨12, Tape.mk' L0 (ones (2 * k + 2) B0)⟩ ⟨24, mkL L0 (ones (k + 1) B0)⟩
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, ones_succ (2 * k + 1) B0,
      ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr12_1 _ _) ?_
    rw [ones_succ (2 * k) B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr13_1 _ _) ?_
    change reachPos (evenCfg L0 1 (2 * k + 0)) _
    have hev_end : reachPos (evenCfg L0 (k + 1) 0) ⟨24, mkL L0 (ones (k + 1) B0)⟩ := by
      unfold evenCfg
      rw [ones_zero, ErdosTernary15.Tape.mk'_B0]
      refine step_then_reachPos (tr14_0 _ _) ?_
      rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
      refine step_then_reachPos (tr15_0 _ _) ?_
      rw [B0_cons_zero, ones_succ k L0, ErdosTernary15.Tape.mkL_cons]
      have h23 : reachPos ⟨23, ⟨1, ones k L0, B0⟩⟩ ⟨24, mkL (ones k L0) (ones 1 B0)⟩ :=
        reachPos_step (tr23_1 (ones k L0) B0)
      have hsw := sweep1L tr24_1 k L0 (ones 1 B0)
      rw [← ones_add k 1 B0] at hsw
      exact reachPos_then_nSteps h23 hsw
    rcases even_many L0 1 k 0 with hk0 | hmany
    · rw [hk0] at hev_end ⊢
      exact hev_end
    · rw [show 1 + k = k + 1 by omega] at hmany
      exact reachPos_trans hmany hev_end
  · let k := y / 2
    have hy_eq : y = 2 * k + 1 := by dsimp [k]; omega
    have hty : terras y = 3 * k + 2 := by
      unfold terras
      have hne : ¬ (y % 2 = 0) := by omega
      simp [hne]; dsimp [k]; omega
    rw [hty, hy_eq]
    cases k with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add]
      unfold stageCfg
      change reachPos ⟨12, Tape.mk' L0 (ones 1 B0)⟩ ⟨24, mkL L0 (ones 2 B0)⟩
      rw [ones_succ 0 B0, ones_zero, ErdosTernary15.Tape.mk'_cons]
      refine step_then_reachPos (tr12_1 _ _) ?_
      rw [ErdosTernary15.Tape.mk'_B0]
      have h13 : reachPos ⟨13, ⟨0, ones 1 L0, B0⟩⟩ ⟨24, mkL (ones 1 L0) (ones 1 B0)⟩ :=
        reachPos_step (tr13_0 (ones 1 L0) B0)
      have hsw : nSteps weakCollatz41 1 ⟨24, mkL (ones 1 L0) (ones 1 B0)⟩ =
          some ⟨24, mkL L0 (ones 2 B0)⟩ := sweep1L tr24_1 1 L0 (ones 1 B0)
      exact reachPos_then_nSteps h13 hsw
    | succ k' =>
      unfold stageCfg
      change reachPos ⟨12, Tape.mk' L0 (ones (2 * (k' + 1) + 1) B0)⟩
        ⟨24, mkL L0 (ones (3 * (k' + 1) + 2) B0)⟩
      rw [show 2 * (k' + 1) + 1 = (2 * k' + 2) + 1 by omega,
        ones_succ (2 * k' + 2) B0, ErdosTernary15.Tape.mk'_cons]
      refine step_then_reachPos (tr12_1 _ _) ?_
      rw [show 2 * k' + 2 = (2 * k' + 1) + 1 by omega,
        ones_succ (2 * k' + 1) B0, ErdosTernary15.Tape.mk'_cons]
      refine step_then_reachPos (tr13_1 _ _) ?_
      change reachPos (evenCfg L0 1 (2 * k' + 1)) _
      have hto_odd : reachPos (evenCfg L0 (k' + 1) 1) (oddCfg L0 (k' + 1) 1) := by
        unfold evenCfg oddCfg
        refine nSteps_then_reachPos (sweep1R tr14_1 1 _ B0) ?_
        rw [ErdosTernary15.Tape.mk'_B0]
        refine step_then_reachPos (tr14_0 _ _) ?_
        rw [B0_cons_zero, ones_succ 0 _, ErdosTernary15.Tape.mkL_cons]
        refine step_then_reachPos (tr15_1 _ _) ?_
        rw [B0_cons_zero, ones_zero, ErdosTernary15.Tape.mkL_cons]
        refine step_then_reachPos (tr16_0 _ _) ?_
        rw [ErdosTernary15.Tape.mk'_B0]
        refine step_then_reachPos (tr20_0 _ _) ?_
        rw [ErdosTernary15.Tape.mkL_cons]
        exact reachPos_step (tr21_0 _ _)
      have hev_part : reachPos (evenCfg L0 1 (2 * k' + 1)) (oddCfg L0 (k' + 1) 1) := by
        rcases even_many L0 1 k' 1 with rfl | hmany
        · exact hto_odd
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
        refine step_then_reachPos (tr18_0 _ _) ?_
        rw [ErdosTernary15.Tape.mk'_cons]
        have hstep := tr22_0 ((baseCX c x).cons 0) (ones (1 + 3 * (k' + 1)) B0)
        rw [← ones_succ (1 + 3 * (k' + 1)) B0,
          show 1 + 3 * (k' + 1) + 1 = 3 * (k' + 1) + 2 by omega] at hstep
        exact reachPos_step hstep

/-! ## Adjacent Comparison, Cycle Halt & Unified Restoration -/

private def cmpCfg (c u v p : ℕ) : Cfg 41 2 :=
  ⟨23, mkL (ones v ((ones u ((ones c B0).cons 0)).cons 0)) ((ones (2 * p) B0).cons 0)⟩

private theorem cmpFrom24 (c u v p : ℕ) :
    reachPos ⟨24, mkL ((ones (u + 1) ((ones c B0).cons 0)).cons 0)
        (ones (v + 1) ((ones (2 * p) B0).cons 0))⟩
      (cmpCfg c u v (p + 1)) := by
  let Lc := (ones c B0).cons 0
  let Lu := (ones u Lc).cons 0
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr24_0 _ _) ?_
  rw [ones_succ u Lc, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr27_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr28_0 _ _) ?_
  change reachPos ⟨29, Tape.mk' (ones 1 Lu) (ones (v + 1) ((ones (2 * p) B0).cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr29_1 (v + 1) (ones 1 Lu) _) ?_
  rw [← ones_add (v + 1) 1 Lu, show v + 1 + 1 = v + 2 by omega, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr29_0 _ _) ?_
  rw [show (ones (2 * p) B0).cons 1 = ones (2 * p + 1) B0 from rfl,
    show v + 2 = (v + 1) + 1 by omega, ones_succ (v + 1) Lu, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr20_1 _ _) ?_
  rw [← ones_succ (2 * p + 1) B0, ones_succ v Lu, ErdosTernary15.Tape.mkL_cons]
  have h22 := tr22_1 (ones v Lu) (ones (2 * p + 2) B0)
  rw [show 2 * p + 2 = 2 * (p + 1) by omega] at h22
  exact reachPos_step h22

private theorem terras_to_cmp1 (c x y : ℕ) (hx : 3 ≤ x) (hy : 1 ≤ y) :
    reachPos (stageCfg c x y) (cmpCfg c (x - 1) (terras y - 1) 1) := by
  have hz : 1 ≤ terras y := terras_pos_of_pos hy
  have heval := terras_eval c x y hy
  have htarget : (⟨24, mkL ((baseCX c x).cons 0) (ones (terras y) B0)⟩ : Cfg 41 2) =
      ⟨24, mkL ((ones ((x - 1) + 1) ((ones c B0).cons 0)).cons 0)
        (ones ((terras y - 1) + 1) ((ones (2 * 0) B0).cons 0))⟩ := by
    unfold baseCX
    rw [show (x - 1) + 1 = x by omega, show (terras y - 1) + 1 = terras y by omega,
      Nat.mul_zero, ones_zero, B0_cons_zero]
  rw [htarget] at heval
  exact reachPos_trans heval (cmpFrom24 c (x - 1) (terras y - 1) 0)

private theorem cmp_step (c u v p : ℕ) :
    reachPos (cmpCfg c (u + 1) (v + 1) p) (cmpCfg c u v (p + 1)) := by
  unfold cmpCfg
  let Lu1 := (ones (u + 1) ((ones c B0).cons 0)).cons 0
  let Rp := (ones (2 * p) B0).cons 0
  change reachPos ⟨23, mkL (ones (v + 1) Lu1) Rp⟩ _
  rw [ones_succ v Lu1, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr23_1 _ _) ?_
  change reachPos ⟨24, mkL (ones v Lu1) (ones 1 Rp)⟩ _
  refine nSteps_then_reachPos (sweep1L tr24_1 v Lu1 (ones 1 Rp)) ?_
  rw [← ones_add v 1 Rp]
  exact cmpFrom24 c u v p

private theorem cmp_many (c u v p k : ℕ) :
    k = 0 ∨ reachPos (cmpCfg c (u + k) (v + k) p) (cmpCfg c u v (p + k)) := by
  induction k generalizing u v p with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ?_
    rw [show u + (k + 1) = (u + k) + 1 by omega, show v + (k + 1) = (v + k) + 1 by omega]
    rcases ih u v (p + 1) with rfl | hrest
    · rw [Nat.add_zero]
      exact cmp_step c u v p
    · rw [show p + 1 + k = p + (k + 1) by omega] at hrest
      exact reachPos_trans (cmp_step c (u + k) (v + k) p) hrest

private theorem cmp_halt_eq (c p : ℕ) :
    ∃ s cfg, nSteps weakCollatz41 s (cmpCfg c 0 0 p) = some cfg ∧
      step weakCollatz41 cfg = none := by
  unfold cmpCfg
  rw [ones_zero, ones_zero, ErdosTernary15.Tape.mkL_cons]
  have h1 := tr23_0 (((ones c B0).cons 0)) ((ones (2 * p) B0).cons 0)
  rw [ErdosTernary15.Tape.mkL_cons] at h1
  exact ⟨1, _, step_one h1, tr25_0 _ _⟩

private def restCfg (c u v p : ℕ) : Cfg 41 2 :=
  ⟨30, Tape.mk' (ones v ((ones u ((ones c B0).cons 0)).cons 0)) ((ones (2 * p) B0).cons 0)⟩

private theorem cmp_lt_to_rest (c u p : ℕ) :
    reachPos (cmpCfg c (u + 1) 0 p) (restCfg c (u + 1) 0 p) := by
  unfold cmpCfg restCfg
  rw [ones_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr23_0 _ _) ?_
  rw [ones_succ u _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr25_1 _ _) ?_
  rw [← ones_succ u _, ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr26_0 _ _)

private theorem cmp_gt_to_rest (c v p : ℕ) :
    reachPos (cmpCfg c 0 (v + 1) p) (restCfg c 0 (v + 1) p) := by
  unfold cmpCfg restCfg
  let L0 := (ones 0 ((ones c B0).cons 0)).cons 0
  let Rp := (ones (2 * p) B0).cons 0
  change reachPos ⟨23, mkL (ones (v + 1) L0) Rp⟩ _
  rw [ones_succ v L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr23_1 _ _) ?_
  change reachPos ⟨24, mkL (ones v L0) (ones 1 Rp)⟩ _
  refine nSteps_then_reachPos (sweep1L tr24_1 v L0 (ones 1 Rp)) ?_
  rw [← ones_add v 1 Rp]
  dsimp only [L0]
  rw [ones_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr24_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr27_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  have h26 : reachPos ⟨26, ⟨0, (ones c B0).cons 0, ones (v + 1) Rp⟩⟩
      ⟨30, Tape.mk' (((ones c B0).cons 0).cons 0) (ones (v + 1) Rp)⟩ :=
    reachPos_step (tr26_0 ((ones c B0).cons 0) (ones (v + 1) Rp))
  exact reachPos_then_nSteps h26 (sweep1R tr30_1 (v + 1) (((ones c B0).cons 0).cons 0) Rp)

private theorem rest_step (c u v p : ℕ) :
    reachPos (restCfg c u v (p + 1)) (restCfg c (u + 1) (v + 1) p) := by
  unfold restCfg
  let Lc := (ones c B0).cons 0
  let Lu := (ones u Lc).cons 0
  change reachPos ⟨30, Tape.mk' (ones v Lu) ((ones (2 * (p + 1)) B0).cons 0)⟩ _
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr30_0 _ _) ?_
  rw [show (ones v Lu).cons 1 = ones (v + 1) Lu from rfl,
    show 2 * (p + 1) = (2 * p + 1) + 1 by omega, ones_succ (2 * p + 1) B0,
    ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr31_1 _ _) ?_
  rw [show (ones (v + 1) Lu).cons 1 = ones (v + 2) Lu from rfl,
    ones_succ (2 * p) B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr28_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr0_1 (v + 2) Lu _) ?_
  dsimp only [Lu]
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr0_0 _ _) ?_
  rw [← ones_succ u Lc, show v + 2 = (v + 1) + 1 by omega, ones_succ (v + 1) _,
    ErdosTernary15.Tape.mk'_cons]
  have h1 : reachPos ⟨1, ⟨1, ones (u + 1) Lc, ones (v + 1) ((ones (2 * p) B0).cons 0)⟩⟩
      ⟨30, Tape.mk' ((ones (u + 1) Lc).cons 0) (ones (v + 1) ((ones (2 * p) B0).cons 0))⟩ :=
    reachPos_step (tr1_1 (ones (u + 1) Lc) (ones (v + 1) ((ones (2 * p) B0).cons 0)))
  exact reachPos_then_nSteps h1
    (sweep1R tr30_1 (v + 1) ((ones (u + 1) Lc).cons 0) ((ones (2 * p) B0).cons 0))

private theorem rest_many (c u v p k : ℕ) :
    k = 0 ∨ reachPos (restCfg c u v (p + k)) (restCfg c (u + k) (v + k) p) := by
  induction k generalizing u v with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ?_
    rw [show p + (k + 1) = (p + k) + 1 by omega]
    have hfirst := rest_step c u v (p + k)
    rcases ih (u + 1) (v + 1) with rfl | hrest
    · rw [Nat.add_zero]
      exact hfirst
    · rw [show u + (k + 1) = u + 1 + k by omega, show v + (k + 1) = v + 1 + k by omega]
      exact reachPos_trans hfirst hrest

/-! ## Counter Decrement, Stage Advance & Halting Equivalence -/

private def postDecCfg (c' x z : ℕ) : Cfg 41 2 :=
  ⟨35, Tape.mk' B0 (ones c' ((ones x ((ones z B0).cons 0)).cons 0))⟩

private theorem rest_exit (c' x z : ℕ) :
    reachPos (restCfg (c' + 1) x z 0) (postDecCfg c' x z) := by
  unfold restCfg postDecCfg
  rw [Nat.mul_zero, ones_zero, B0_cons_zero, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr30_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr31_0 _ _) ?_
  rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr26_1 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (sweep1L tr32_1 z _ B0) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr32_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr33_1 x _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr33_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr34_1 (c' + 1) B0 _) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr34_0 _ _) ?_
  rw [B0_cons_zero, ones_succ c' _, ErdosTernary15.Tape.mk'_cons]
  have h3 := tr3_1 B0 (ones c' ((ones x ((ones z B0).cons 0)).cons 0))
  rw [B0_cons_zero] at h3
  exact reachPos_step h3

private theorem postDec_continue (c'' x z : ℕ) :
    reachPos (postDecCfg (c'' + 1) x z) (stageCfg (c'' + 1) x z) := by
  unfold postDecCfg stageCfg baseCX
  rw [ones_succ c'' _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr35_1 _ _) ?_
  change reachPos ⟨36, Tape.mk' (ones 1 B0) (ones c'' ((ones x ((ones z B0).cons 0)).cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr36_1 c'' _ _) ?_
  rw [← ones_add c'' 1 B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr36_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr37_1 x _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr37_0 _ _)

private theorem postDec_advance (x z : ℕ) (hx : 3 ≤ x) :
    reachPos (postDecCfg 0 x z) (stageCfg (x + 1) (x + 1) (x + 1)) := by
  unfold postDecCfg
  rw [ones_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr35_0 _ _) ?_
  change reachPos ⟨38, Tape.mk' (ones 1 B0) (ones x ((ones z B0).cons 0))⟩ _
  refine nSteps_then_reachPos (sweep1R tr38_1 x _ _) ?_
  rw [← ones_add x 1 B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr38_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr39_1 z _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr39_0 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (erase1L tr40_1 z ((ones (x + 1) B0).cons 0)) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr40_0 _ _) ?_
  rw [B0_cons_zero]
  have htr : (⟨2, mkL (ones (x + 1) B0) B0⟩ : Cfg 41 2) = tripleCfg 0 (x + 1) := by
    simp only [tripleCfg, ones_zero, B0_cons_zero]
  rw [htr]
  have hfin := triple_from_zero (x - 1)
  rw [show (x - 1) + 2 = x + 1 by omega] at hfin
  exact hfin

private theorem stage_round_halt (c x y : ℕ) (_hc : 1 ≤ c) (hx : 3 ≤ x) (hy : 1 ≤ y)
    (hhit : terras y = x) :
    ∃ s cfg, nSteps weakCollatz41 s (stageCfg c x y) = some cfg ∧
      step weakCollatz41 cfg = none := by
  have hcmp1 := terras_to_cmp1 c x y hx hy
  rw [hhit] at hcmp1
  have hmany : reachPos (cmpCfg c (x - 1) (x - 1) 1) (cmpCfg c 0 0 x) := by
    have heq := cmp_many c 0 0 1 (x - 1)
    rcases heq with h0 | hp
    · exfalso; omega
    · rw [Nat.zero_add, show 1 + (x - 1) = x by omega] at hp
      exact hp
  obtain ⟨s₁, _, hs₁⟩ := reachPos_trans hcmp1 hmany
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := cmp_halt_eq c x
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

private theorem stage_round_mismatch (c' x y : ℕ) (hx : 3 ≤ x) (hy : 1 ≤ y)
    (hne : terras y ≠ x) :
    reachPos (stageCfg (c' + 1) x y) (postDecCfg c' x (terras y)) := by
  let z := terras y
  have hz : 1 ≤ z := terras_pos_of_pos hy
  refine reachPos_trans (terras_to_cmp1 (c' + 1) x y hx hy) ?_
  have hto_rest0 : reachPos (cmpCfg (c' + 1) (x - 1) (z - 1) 1) (restCfg (c' + 1) x z 0) := by
    rcases Nat.lt_or_ge z x with hlt | hge
    · let q := z - 1
      let uRem := x - z - 1
      have hsub_x : x - 1 = (uRem + 1) + q := by dsimp [uRem, q]; omega
      have hsub_z : z - 1 = 0 + q := by dsimp [q]; omega
      rw [hsub_x, hsub_z]
      have hmid : reachPos (cmpCfg (c' + 1) ((uRem + 1) + q) (0 + q) 1)
          (restCfg (c' + 1) (uRem + 1) 0 (q + 1)) := by
        rcases cmp_many (c' + 1) (uRem + 1) 0 1 q with hq0 | hp
        · rw [hq0, Nat.add_zero, Nat.add_zero]
          exact cmp_lt_to_rest (c' + 1) uRem 1
        · rw [show 1 + q = q + 1 by omega] at hp
          exact reachPos_trans hp (cmp_lt_to_rest (c' + 1) uRem (q + 1))
      rcases rest_many (c' + 1) (uRem + 1) 0 0 (q + 1) with h0 | hrm
      · exfalso; omega
      · have hrm' : reachPos (restCfg (c' + 1) (uRem + 1) 0 (q + 1)) (restCfg (c' + 1) x z 0) := by
          have heq1 : 0 + (q + 1) = q + 1 := Nat.zero_add (q + 1)
          have heq2 : uRem + 1 + (q + 1) = x := by dsimp [uRem, q]; omega
          have heq3 : q + 1 = z := by dsimp [q]; omega
          rw [heq1, heq2] at hrm
          have hfin_eq : restCfg (c' + 1) x (q + 1) 0 = restCfg (c' + 1) x z 0 := by rw [heq3]
          rw [← hfin_eq]
          exact hrm
        exact reachPos_trans hmid hrm'
    · have hgt : x < z := by omega
      let q := x - 1
      let vRem := z - x - 1
      have hsub_x : x - 1 = 0 + q := by dsimp [q]; omega
      have hsub_z : z - 1 = (vRem + 1) + q := by dsimp [vRem, q]; omega
      rw [hsub_x, hsub_z]
      have hmid : reachPos (cmpCfg (c' + 1) (0 + q) ((vRem + 1) + q) 1)
          (restCfg (c' + 1) 0 (vRem + 1) (q + 1)) := by
        rcases cmp_many (c' + 1) 0 (vRem + 1) 1 q with hq0 | hp
        · exfalso; dsimp [q] at hq0; omega
        · rw [show 1 + q = q + 1 by omega] at hp
          exact reachPos_trans hp (cmp_gt_to_rest (c' + 1) vRem (q + 1))
      rcases rest_many (c' + 1) 0 (vRem + 1) 0 (q + 1) with h0 | hrm
      · exfalso; omega
      · have hrm' : reachPos (restCfg (c' + 1) 0 (vRem + 1) (q + 1)) (restCfg (c' + 1) x z 0) := by
          have heq1 : 0 + (q + 1) = q + 1 := Nat.zero_add (q + 1)
          have heq2 : vRem + 1 + (q + 1) = z := by dsimp [vRem, q]; omega
          have heq3 : q + 1 = x := by dsimp [q]; omega
          rw [heq1, heq2] at hrm
          have hfin_eq : restCfg (c' + 1) (q + 1) z 0 = restCfg (c' + 1) x z 0 := by rw [heq3]
          rw [← hfin_eq]
          exact hrm
        exact reachPos_trans hmid hrm'
  exact reachPos_trans hto_rest0 (rest_exit c' x z)

private theorem terras_iterate_pos {y : ℕ} (hy : 1 ≤ y) (m : ℕ) : 1 ≤ terras^[m] y := by
  induction m generalizing y with
  | zero => exact hy
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (terras_pos_of_pos hy)

private def StageClear (x m : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ m → terras^[j] x ≠ x

private theorem stage_within_reach (x : ℕ) (hx : 3 ≤ x) (m : ℕ) (hm : m < x)
    (hcl : StageClear x m) :
    m = 0 ∨ reachPos (stageCfg x x x) (stageCfg (x - m) x (terras^[m] x)) := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    refine Or.inr ?_
    rcases ih (by omega) (fun j hj1 hjm => hcl j hj1 (by omega)) with rfl | hprev
    · have hne1 : terras x ≠ x := hcl 1 le_rfl le_rfl
      have hchk := stage_round_mismatch (x - 1) x x hx (by omega) hne1
      rw [show x - 1 + 1 = x by omega] at hchk
      have hcont := postDec_continue (x - 2) x (terras x)
      rw [show x - 2 + 1 = x - 1 by omega] at hcont
      rw [Nat.sub_one, Function.iterate_one]
      exact reachPos_trans hchk hcont
    · have hne : terras (terras^[m] x) ≠ x := by
        have hit : terras (terras^[m] x) = terras^[m + 1] x :=
          (Function.iterate_succ_apply' terras m x).symm
        rw [hit]
        exact hcl (m + 1) (by omega) le_rfl
      have hy_pos : 1 ≤ terras^[m] x := terras_iterate_pos (by omega) m
      have hxm_eq : x - m = (x - (m + 1)) + 1 := by omega
      have hxm1_eq : x - (m + 1) = (x - (m + 2)) + 1 := by omega
      rw [hxm_eq] at hprev
      have hchk := stage_round_mismatch (x - (m + 1)) x (terras^[m] x) hx hy_pos hne
      rw [hxm1_eq] at hprev hchk ⊢
      have hcont := postDec_continue (x - (m + 2)) x (terras (terras^[m] x))
      rw [Function.iterate_succ_apply']
      exact reachPos_trans hprev (reachPos_trans hchk hcont)

private theorem stage_full_advance (x : ℕ) (hx : 3 ≤ x) (hcl : StageClear x x) :
    reachPos (stageCfg x x x) (stageCfg (x + 1) (x + 1) (x + 1)) := by
  rcases stage_within_reach x hx (x - 1) (by omega)
      (fun j hj1 hjm => hcl j hj1 (by omega)) with h0 | hprev
  · exfalso; omega
  · rw [show x - (x - 1) = 1 by omega] at hprev
    have hne : terras (terras^[x - 1] x) ≠ x := by
      have hit : terras (terras^[x - 1] x) = terras^[x] x := by
        rw [← Function.iterate_succ_apply' terras (x - 1) x, show (x - 1).succ = x by omega]
      rw [hit]
      exact hcl x (by omega) le_rfl
    have hy_pos : 1 ≤ terras^[x - 1] x := terras_iterate_pos (by omega) (x - 1)
    have hchk := stage_round_mismatch 0 x (terras^[x - 1] x) hx hy_pos hne
    exact reachPos_trans hprev (reachPos_trans hchk (postDec_advance x _ hx))

private theorem stage_first_hit_halt (x j : ℕ) (hx : 3 ≤ x) (hj1 : 1 ≤ j) (hjx : j ≤ x)
    (hcl : StageClear x (j - 1)) (hhit : terras^[j] x = x) :
    ∃ s cfg, nSteps weakCollatz41 s (stageCfg x x x) = some cfg ∧
      step weakCollatz41 cfg = none := by
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj_gt1
  · exact stage_round_halt x x x (by omega) hx (by omega) hhit
  · rcases stage_within_reach x hx (j - 1) (by omega) hcl with h0 | hprev
    · exfalso; omega
    · obtain ⟨s₁, _, hs₁⟩ := hprev
      have hhit' : terras (terras^[j - 1] x) = x := by
        rw [← Function.iterate_succ_apply' terras (j - 1) x, show (j - 1).succ = j by omega]
        exact hhit
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_round_halt (x - (j - 1)) x (terras^[j - 1] x)
        (by omega) hx (terras_iterate_pos (by omega) (j - 1)) hhit'
      exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

private theorem stageClear_or_first_hit (x m : ℕ) :
    StageClear x m ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧ StageClear x (j - 1) ∧ terras^[j] x = x := by
  induction m with
  | zero => exact Or.inl fun j hj1 hj0 => absurd (le_trans hj1 hj0) (by decide)
  | succ m ih =>
    rcases ih with hcl | ⟨j, hj1, hjm, hcj, hhit⟩
    · by_cases hhit : terras^[m + 1] x = x
      · exact Or.inr ⟨m + 1, by omega, le_rfl, hcl, hhit⟩
      · refine Or.inl fun j hj1 hjm1 => ?_
        rcases Nat.lt_or_ge j (m + 1) with hlt | hge
        · exact hcl j hj1 (by omega)
        · rw [show j = m + 1 by omega]; exact hhit
    · exact Or.inr ⟨j, hj1, by omega, hcj, hhit⟩

private def AllClear (X : ℕ) : Prop :=
  ∀ x : ℕ, 3 ≤ x → x ≤ X → StageClear x x

private theorem allClear_or_first_witness (X : ℕ) :
    AllClear X ∨
      ∃ x j : ℕ, 3 ≤ x ∧ x ≤ X ∧ 1 ≤ j ∧ j ≤ x ∧
        AllClear (x - 1) ∧ StageClear x (j - 1) ∧ terras^[j] x = x := by
  induction X with
  | zero => exact Or.inl fun x hx3 hx0 => absurd (le_trans hx3 hx0) (by decide)
  | succ X ih =>
    rcases ih with hAll | ⟨x, j, hx3, hxX, hj1, hjx, hAllX, hStg, hhit⟩
    · by_cases hx3 : 3 ≤ X + 1
      · rcases stageClear_or_first_hit (X + 1) (X + 1) with hStg | ⟨j, hj1, hjx, hcj, hhit⟩
        · refine Or.inl fun x hx_ge3 hx_le => ?_
          rcases Nat.lt_or_ge x (X + 1) with hlt | hge
          · exact hAll x hx_ge3 (by omega)
          · rw [show x = X + 1 by omega]; exact hStg
        · exact Or.inr ⟨X + 1, j, hx3, le_rfl, hj1, hjx, hAll, hcj, hhit⟩
      · exact Or.inl fun x hx_ge3 hx_le => absurd (le_trans hx_ge3 hx_le) hx3
    · exact Or.inr ⟨x, j, hx3, by omega, hj1, hjx, hAllX, hStg, hhit⟩

private theorem reach_stage_from_init (X : ℕ) (hX : 3 ≤ X) (hAll : AllClear (X - 1)) :
    ∃ s : ℕ, X - 2 ≤ s ∧ nSteps weakCollatz41 s init = some (stageCfg X X X) := by
  induction X, hX using Nat.le_induction with
  | base =>
    obtain ⟨s, hs1, hs⟩ := init_reaches_stage3
    exact ⟨s, by omega, hs⟩
  | succ X hX ih =>
    obtain ⟨s₁, hs₁_ge, hs₁⟩ := ih fun x hx3 hx_le => hAll x hx3 (by omega)
    have hclX : StageClear X X := hAll X hX (by omega)
    obtain ⟨s₂, hs₂_pos, hs₂⟩ := stage_full_advance X hX hclX
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- The 41-state machine `weakCollatz41` (`weak_collatz_41`) halts on the blank tape if and only if
there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(constructive, zero `Classical.choice`). -/
theorem halts_weakCollatz41_iff_bounded_cycle :
    ConjectureMachines.Halts weakCollatz41 ↔
      ∃ x j : ℕ, 3 ≤ x ∧ 1 ≤ j ∧ j ≤ x ∧ terras^[j] x = x := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases allClear_or_first_witness (k + 3) with hAll | ⟨x, j, hx3, -, hj1, hjx, -, -, hhit⟩
    · obtain ⟨s, hks, hs⟩ := reach_stage_from_init (k + 3) (by omega)
        (fun x hx3 hx_le => hAll x hx3 (by omega))
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
    · exact ⟨x, j, hx3, hj1, hjx, hhit⟩
  · rintro ⟨x, j, hx3, hj1, hjx, hhit⟩
    rcases allClear_or_first_witness x with
        hAll | ⟨x₀, j₀, hx₀3, -, hj₀1, hj₀x, hAll₀, hStg₀, hhit₀⟩
    · exfalso
      exact hAll x hx3 le_rfl j hj1 hjx hhit
    · obtain ⟨s₁, -, hs₁⟩ := reach_stage_from_init x₀ hx₀3 hAll₀
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_first_hit_halt x₀ j₀ hx₀3 hj₀1 hj₀x hStg₀ hhit₀
      rw [Part.dom_iff_mem]
      exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches (nSteps_bind_eq hs₁ hs₂), hnone⟩⟩

/-- The 41-state candidate machine halts on the blank tape if and only if the 75-state reference
machine does (constructive, zero `Classical.choice`). -/
theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  halts_weakCollatz41_iff_bounded_cycle.trans
    WeakCollatz75.halts_weakCollatz75_iff_bounded_cycle.symm

/-- The candidate has 34 fewer states than the 75-state reference (`41 < 75`). -/
theorem candidate_fewer_states : candidate.states < reference.states := by
  decide +kernel

end ConjectureMachines.WeakCollatz41
