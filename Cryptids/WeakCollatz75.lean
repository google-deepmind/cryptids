/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ErdosTernary14
public import Cryptids.Propositions

/-!
# WeakCollatz75 (`weak_collatz_75`)

The 75-state, 2-symbol Turing machine `weak_collatz_75` halts on the blank tape if and only if
there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(`halts_weakCollatz75_iff_bounded_cycle`),
and hence (by `Cryptids.Semantics.WeakCollatz75`) if and only if **Tao's Weak Collatz Conjecture**
is false (`¬ WeakCollatzConjecture`). Neither the machine proof nor the Böhm–Sontacchi (1978) /
bounded-period cycle reduction uses `Classical.choice`.

This improves on the previously published 124-state unverified Weak Collatz Turing machine listed on
the `bbchallenge` wiki (`124 → 75` states, `-49` states / `-39.5%`) by eliminating Cantor pairing
via finite pigeonhole on the cycle maximum `M ≥ 3` (whose minimal period satisfies `1 ≤ j ≤ M - 2`)
and sharing both the even/odd `Terras` evaluation loop (`0` vs `00` separator) and the mismatch
restoration pass across `z < x` and `z > x`.

## Tape Layout

At canonical checkpoint `stageCfg x c g y` (`x ≥ 3`, `c ≥ 1`, `g ≥ 0`, `y ≥ 1`), the tape holds
`0^∞  1^x  00  1^c  0^(g + 2)  [1] 1^(y - 1)  0^∞` in state `20` on the leftmost `1` of `1^y`:
1. **Boot & Double-Copy (`states 0–19`)**: writes `x = 3` and duplicates `1^A` twice to initialize
   `stageCfg A A 0 A`.
2. **Unified `terras` Step (`states 0, 2, 4, 10, 14, 20–32`)**: scans `1^y` mod `2` (`20, 21, 2`),
   leaves a single `0` separator with `z₀ = 1` for even `y = 2k + 2` or double `00` with `z₀ = 2`
   for odd `y = 2k + 1`, and peels pairs of `1`s while appending `+1` or `+3` to form
   `1^(terras y)`.
3. **Non-Destructive Comparison & Restoration (`states 7, 22, 33–69`)**: compares `z = terras y`
   against `x` via `0`-hole shuttling. If `z = x`, state `56` reading `0` halts (`---`); otherwise
   both `1^x` and `1^z` are restored and `1^c` is decremented into state `70`.
4. **Counter Check & Stage Increment (`states 11, 70–74`)**: if `c ≥ 2`, returns to state `20` on
   `1^z`; if `c = 1`, erases `1^z`, increments `1^x → 1^(x + 1)`, and runs Double-Copy.
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz75

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_zero nSteps_succ nSteps_reaches nSteps_add
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- The 75-state Weak Collatz machine (`weak_collatz_75`), loaded from
`artifacts/weak_collatz_75/machine.txt` in `Machines.lean`. -/
abbrev weakCollatz75 : Machine 75 2 := Machines.weakCollatz75

private theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

private theorem stepR {q q' : Fin 75} {a b : Fin 2}
    (h : weakCollatz75.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz75 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

private theorem stepL {q q' : Fin 75} {a b : Fin 2}
    (h : weakCollatz75.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step weakCollatz75 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table Lemmas -/

private theorem tr0_0 (L R) : step weakCollatz75 ⟨0, ⟨0, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr0_1 (L R) : step weakCollatz75 ⟨0, ⟨1, L, R⟩⟩ = some ⟨28, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr1_0 (L R) : step weakCollatz75 ⟨1, ⟨0, L, R⟩⟩ = some ⟨2, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr2_0 (L R) : step weakCollatz75 ⟨2, ⟨0, L, R⟩⟩ = some ⟨4, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr2_1 (L R) :
    step weakCollatz75 ⟨2, ⟨1, L, R⟩⟩ = some ⟨21, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr3_0 (L R) : step weakCollatz75 ⟨3, ⟨0, L, R⟩⟩ = some ⟨12, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr3_1 (L R) : step weakCollatz75 ⟨3, ⟨1, L, R⟩⟩ = some ⟨4, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr4_0 (L R) :
    step weakCollatz75 ⟨4, ⟨0, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr4_1 (L R) :
    step weakCollatz75 ⟨4, ⟨1, L, R⟩⟩ = some ⟨23, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr5_0 (L R) :
    step weakCollatz75 ⟨5, ⟨0, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr6_0 (L R) :
    step weakCollatz75 ⟨6, ⟨0, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr6_1 (L R) :
    step weakCollatz75 ⟨6, ⟨1, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr7_0 (L R) :
    step weakCollatz75 ⟨7, ⟨0, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr7_1 (L R) :
    step weakCollatz75 ⟨7, ⟨1, L, R⟩⟩ = some ⟨59, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr8_0 (L R) : step weakCollatz75 ⟨8, ⟨0, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr8_1 (L R) :
    step weakCollatz75 ⟨8, ⟨1, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr9_0 (L R) : step weakCollatz75 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr9_1 (L R) : step weakCollatz75 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr10_0 (L R) : step weakCollatz75 ⟨10, ⟨0, L, R⟩⟩ = some ⟨11, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr10_1 (L R) :
    step weakCollatz75 ⟨10, ⟨1, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr11_0 (L R) :
    step weakCollatz75 ⟨11, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr11_1 (L R) : step weakCollatz75 ⟨11, ⟨1, L, R⟩⟩ = some ⟨11, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr12_0 (L R) : step weakCollatz75 ⟨12, ⟨0, L, R⟩⟩ = some ⟨13, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr12_1 (L R) : step weakCollatz75 ⟨12, ⟨1, L, R⟩⟩ = some ⟨14, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr13_0 (L R) :
    step weakCollatz75 ⟨13, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr13_1 (L R) : step weakCollatz75 ⟨13, ⟨1, L, R⟩⟩ = some ⟨13, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr14_0 (L R) : step weakCollatz75 ⟨14, ⟨0, L, R⟩⟩ = some ⟨15, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr14_1 (L R) :
    step weakCollatz75 ⟨14, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr15_0 (L R) :
    step weakCollatz75 ⟨15, ⟨0, L, R⟩⟩ = some ⟨16, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr15_1 (L R) :
    step weakCollatz75 ⟨15, ⟨1, L, R⟩⟩ = some ⟨18, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr16_0 (L R) :
    step weakCollatz75 ⟨16, ⟨0, L, R⟩⟩ = some ⟨16, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr16_1 (L R) :
    step weakCollatz75 ⟨16, ⟨1, L, R⟩⟩ = some ⟨17, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr17_0 (L R) :
    step weakCollatz75 ⟨17, ⟨0, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr17_1 (L R) :
    step weakCollatz75 ⟨17, ⟨1, L, R⟩⟩ = some ⟨17, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr18_0 (L R) :
    step weakCollatz75 ⟨18, ⟨0, L, R⟩⟩ = some ⟨18, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr18_1 (L R) :
    step weakCollatz75 ⟨18, ⟨1, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr19_0 (L R) :
    step weakCollatz75 ⟨19, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr19_1 (L R) :
    step weakCollatz75 ⟨19, ⟨1, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr20_0 (L R) :
    step weakCollatz75 ⟨20, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr20_1 (L R) :
    step weakCollatz75 ⟨20, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr21_0 (L R) : step weakCollatz75 ⟨21, ⟨0, L, R⟩⟩ = some ⟨22, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr21_1 (L R) :
    step weakCollatz75 ⟨21, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr22_0 (L R) :
    step weakCollatz75 ⟨22, ⟨0, L, R⟩⟩ = some ⟨44, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr22_1 (L R) : step weakCollatz75 ⟨22, ⟨1, L, R⟩⟩ = some ⟨0, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr23_0 (L R) :
    step weakCollatz75 ⟨23, ⟨0, L, R⟩⟩ = some ⟨25, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr24_0 (L R) :
    step weakCollatz75 ⟨24, ⟨0, L, R⟩⟩ = some ⟨25, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr24_1 (L R) :
    step weakCollatz75 ⟨24, ⟨1, L, R⟩⟩ = some ⟨24, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr25_0 (L R) :
    step weakCollatz75 ⟨25, ⟨0, L, R⟩⟩ = some ⟨26, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr26_0 (L R) : step weakCollatz75 ⟨26, ⟨0, L, R⟩⟩ = some ⟨27, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr26_1 (L R) :
    step weakCollatz75 ⟨26, ⟨1, L, R⟩⟩ = some ⟨26, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr27_0 (L R) : step weakCollatz75 ⟨27, ⟨0, L, R⟩⟩ = some ⟨28, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr27_1 (L R) : step weakCollatz75 ⟨27, ⟨1, L, R⟩⟩ = some ⟨27, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr28_0 (L R) : step weakCollatz75 ⟨28, ⟨0, L, R⟩⟩ = some ⟨29, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr28_1 (L R) : step weakCollatz75 ⟨28, ⟨1, L, R⟩⟩ = some ⟨30, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr29_0 (L R) :
    step weakCollatz75 ⟨29, ⟨0, L, R⟩⟩ = some ⟨33, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr29_1 (L R) : step weakCollatz75 ⟨29, ⟨1, L, R⟩⟩ = some ⟨30, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr30_0 (L R) :
    step weakCollatz75 ⟨30, ⟨0, L, R⟩⟩ = some ⟨14, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr30_1 (L R) : step weakCollatz75 ⟨30, ⟨1, L, R⟩⟩ = some ⟨30, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr31_0 (L R) :
    step weakCollatz75 ⟨31, ⟨0, L, R⟩⟩ = some ⟨32, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr31_1 (L R) :
    step weakCollatz75 ⟨31, ⟨1, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr32_0 (L R) :
    step weakCollatz75 ⟨32, ⟨0, L, R⟩⟩ = some ⟨24, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr32_1 (L R) :
    step weakCollatz75 ⟨32, ⟨1, L, R⟩⟩ = some ⟨26, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr33_0 (L R) :
    step weakCollatz75 ⟨33, ⟨0, L, R⟩⟩ = some ⟨33, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr33_1 (L R) :
    step weakCollatz75 ⟨33, ⟨1, L, R⟩⟩ = some ⟨34, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr34_0 (L R) : step weakCollatz75 ⟨34, ⟨0, L, R⟩⟩ = some ⟨35, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr34_1 (L R) :
    step weakCollatz75 ⟨34, ⟨1, L, R⟩⟩ = some ⟨34, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr35_0 (L R) : step weakCollatz75 ⟨35, ⟨0, L, R⟩⟩ = some ⟨53, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr35_1 (L R) :
    step weakCollatz75 ⟨35, ⟨1, L, R⟩⟩ = some ⟨36, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr36_0 (L R) : step weakCollatz75 ⟨36, ⟨0, L, R⟩⟩ = some ⟨37, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr37_0 (L R) : step weakCollatz75 ⟨37, ⟨0, L, R⟩⟩ = some ⟨38, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr37_1 (L R) : step weakCollatz75 ⟨37, ⟨1, L, R⟩⟩ = some ⟨22, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr38_0 (L R) : step weakCollatz75 ⟨38, ⟨0, L, R⟩⟩ = some ⟨39, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr38_1 (L R) : step weakCollatz75 ⟨38, ⟨1, L, R⟩⟩ = some ⟨38, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr39_0 (L R) : step weakCollatz75 ⟨39, ⟨0, L, R⟩⟩ = some ⟨39, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr39_1 (L R) : step weakCollatz75 ⟨39, ⟨1, L, R⟩⟩ = some ⟨40, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr40_0 (L R) : step weakCollatz75 ⟨40, ⟨0, L, R⟩⟩ = some ⟨41, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr40_1 (L R) : step weakCollatz75 ⟨40, ⟨1, L, R⟩⟩ = some ⟨40, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr41_0 (L R) : step weakCollatz75 ⟨41, ⟨0, L, R⟩⟩ = some ⟨42, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr42_0 (L R) : step weakCollatz75 ⟨42, ⟨0, L, R⟩⟩ = some ⟨58, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr42_1 (L R) : step weakCollatz75 ⟨42, ⟨1, L, R⟩⟩ = some ⟨43, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr43_0 (L R) :
    step weakCollatz75 ⟨43, ⟨0, L, R⟩⟩ = some ⟨37, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr43_1 (L R) : step weakCollatz75 ⟨43, ⟨1, L, R⟩⟩ = some ⟨43, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr44_0 (L R) :
    step weakCollatz75 ⟨44, ⟨0, L, R⟩⟩ = some ⟨45, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr45_0 (L R) :
    step weakCollatz75 ⟨45, ⟨0, L, R⟩⟩ = some ⟨46, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr45_1 (L R) :
    step weakCollatz75 ⟨45, ⟨1, L, R⟩⟩ = some ⟨45, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr46_0 (L R) :
    step weakCollatz75 ⟨46, ⟨0, L, R⟩⟩ = some ⟨46, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr46_1 (L R) :
    step weakCollatz75 ⟨46, ⟨1, L, R⟩⟩ = some ⟨47, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr47_0 (L R) :
    step weakCollatz75 ⟨47, ⟨0, L, R⟩⟩ = some ⟨48, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr47_1 (L R) :
    step weakCollatz75 ⟨47, ⟨1, L, R⟩⟩ = some ⟨47, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr48_0 (L R) :
    step weakCollatz75 ⟨48, ⟨0, L, R⟩⟩ = some ⟨48, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr48_1 (L R) :
    step weakCollatz75 ⟨48, ⟨1, L, R⟩⟩ = some ⟨49, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr49_0 (L R) :
    step weakCollatz75 ⟨49, ⟨0, L, R⟩⟩ = some ⟨50, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr49_1 (L R) :
    step weakCollatz75 ⟨49, ⟨1, L, R⟩⟩ = some ⟨49, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr50_0 (L R) : step weakCollatz75 ⟨50, ⟨0, L, R⟩⟩ = some ⟨51, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr50_1 (L R) :
    step weakCollatz75 ⟨50, ⟨1, L, R⟩⟩ = some ⟨49, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr51_0 (L R) : step weakCollatz75 ⟨51, ⟨0, L, R⟩⟩ = some ⟨52, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr52_0 (L R) : step weakCollatz75 ⟨52, ⟨0, L, R⟩⟩ = some ⟨35, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr52_1 (L R) : step weakCollatz75 ⟨52, ⟨1, L, R⟩⟩ = some ⟨52, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr53_0 (L R) : step weakCollatz75 ⟨53, ⟨0, L, R⟩⟩ = some ⟨53, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr53_1 (L R) : step weakCollatz75 ⟨53, ⟨1, L, R⟩⟩ = some ⟨54, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr54_0 (L R) : step weakCollatz75 ⟨54, ⟨0, L, R⟩⟩ = some ⟨55, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr54_1 (L R) : step weakCollatz75 ⟨54, ⟨1, L, R⟩⟩ = some ⟨54, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr55_0 (L R) : step weakCollatz75 ⟨55, ⟨0, L, R⟩⟩ = some ⟨56, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr55_1 (L R) : step weakCollatz75 ⟨55, ⟨1, L, R⟩⟩ = some ⟨68, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr56_0 (L R : ListBlank (Fin 2)) : step weakCollatz75 ⟨56, ⟨0, L, R⟩⟩ = none := rfl
private theorem tr56_1 (L R) : step weakCollatz75 ⟨56, ⟨1, L, R⟩⟩ = some ⟨57, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr57_0 (L R) : step weakCollatz75 ⟨57, ⟨0, L, R⟩⟩ = some ⟨58, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr57_1 (L R) : step weakCollatz75 ⟨57, ⟨1, L, R⟩⟩ = some ⟨57, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr58_0 (L R) :
    step weakCollatz75 ⟨58, ⟨0, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr58_1 (L R) : step weakCollatz75 ⟨58, ⟨1, L, R⟩⟩ = some ⟨58, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr59_0 (L R) :
    step weakCollatz75 ⟨59, ⟨0, L, R⟩⟩ = some ⟨60, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr59_1 (L R) :
    step weakCollatz75 ⟨59, ⟨1, L, R⟩⟩ = some ⟨59, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr60_0 (L R) :
    step weakCollatz75 ⟨60, ⟨0, L, R⟩⟩ = some ⟨60, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr60_1 (L R) :
    step weakCollatz75 ⟨60, ⟨1, L, R⟩⟩ = some ⟨61, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr61_0 (L R) :
    step weakCollatz75 ⟨61, ⟨0, L, R⟩⟩ = some ⟨62, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr61_1 (L R) :
    step weakCollatz75 ⟨61, ⟨1, L, R⟩⟩ = some ⟨61, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr62_0 (L R) :
    step weakCollatz75 ⟨62, ⟨0, L, R⟩⟩ = some ⟨62, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr62_1 (L R) :
    step weakCollatz75 ⟨62, ⟨1, L, R⟩⟩ = some ⟨63, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr63_0 (L R) :
    step weakCollatz75 ⟨63, ⟨0, L, R⟩⟩ = some ⟨64, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr63_1 (L R) :
    step weakCollatz75 ⟨63, ⟨1, L, R⟩⟩ = some ⟨63, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr64_0 (L R) : step weakCollatz75 ⟨64, ⟨0, L, R⟩⟩ = some ⟨65, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr64_1 (L R) :
    step weakCollatz75 ⟨64, ⟨1, L, R⟩⟩ = some ⟨63, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr65_0 (L R) : step weakCollatz75 ⟨65, ⟨0, L, R⟩⟩ = some ⟨66, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr66_0 (L R) :
    step weakCollatz75 ⟨66, ⟨0, L, R⟩⟩ = some ⟨67, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr66_1 (L R) : step weakCollatz75 ⟨66, ⟨1, L, R⟩⟩ = some ⟨66, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr67_0 (L R) : step weakCollatz75 ⟨67, ⟨0, L, R⟩⟩ = some ⟨55, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr67_1 (L R) :
    step weakCollatz75 ⟨67, ⟨1, L, R⟩⟩ = some ⟨67, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr68_0 (L R) : step weakCollatz75 ⟨68, ⟨0, L, R⟩⟩ = some ⟨69, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr68_1 (L R) : step weakCollatz75 ⟨68, ⟨1, L, R⟩⟩ = some ⟨68, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
private theorem tr69_0 (L R) : step weakCollatz75 ⟨69, ⟨0, L, R⟩⟩ = some ⟨69, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr69_1 (L R) : step weakCollatz75 ⟨69, ⟨1, L, R⟩⟩ = some ⟨70, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr70_0 (L R) :
    step weakCollatz75 ⟨70, ⟨0, L, R⟩⟩ = some ⟨71, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr70_1 (L R) :
    step weakCollatz75 ⟨70, ⟨1, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr71_0 (L R) :
    step weakCollatz75 ⟨71, ⟨0, L, R⟩⟩ = some ⟨71, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr71_1 (L R) :
    step weakCollatz75 ⟨71, ⟨1, L, R⟩⟩ = some ⟨72, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr72_0 (L R) : step weakCollatz75 ⟨72, ⟨0, L, R⟩⟩ = some ⟨73, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr72_1 (L R) :
    step weakCollatz75 ⟨72, ⟨1, L, R⟩⟩ = some ⟨72, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
private theorem tr73_0 (L R) : step weakCollatz75 ⟨73, ⟨0, L, R⟩⟩ = some ⟨73, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
private theorem tr73_1 (L R) :
    step weakCollatz75 ⟨73, ⟨1, L, R⟩⟩ = some ⟨74, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
private theorem tr74_0 (L R) : step weakCollatz75 ⟨74, ⟨0, L, R⟩⟩ = some ⟨11, mkL L (R.cons 1)⟩ :=
  stepL rfl L R

/-! ## Tape Block & Reachability Combinators -/

private def zeros : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, X => X
  | k + 1, X => (zeros k X).cons 0

private theorem ones_zero (X : ListBlank (Fin 2)) : ones 0 X = X := rfl
private theorem ones_succ (k : ℕ) (X : ListBlank (Fin 2)) : ones (k + 1) X = (ones k X).cons 1 :=
  rfl
private theorem zeros_zero (X : ListBlank (Fin 2)) : zeros 0 X = X := rfl
private theorem zeros_succ (k : ℕ) (X : ListBlank (Fin 2)) :
    zeros (k + 1) X = (zeros k X).cons 0 := rfl

private theorem zeros_succ' (k : ℕ) (X : ListBlank (Fin 2)) :
    zeros (k + 1) X = zeros k (X.cons 0) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (·.cons 0) ih

private theorem zeros_add (a b : ℕ) (X : ListBlank (Fin 2)) :
    zeros (a + b) X = zeros a (zeros b X) := by
  induction a with
  | zero => rw [Nat.zero_add, zeros_zero]
  | succ a ih =>
    rw [Nat.succ_add, zeros_succ, zeros_succ, ih]

private theorem zeros_B0 (k : ℕ) : zeros k B0 = B0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zeros_succ, ih, B0_cons_zero]

private def reachPos (c₁ c₂ : Cfg 75 2) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ nSteps weakCollatz75 s c₁ = some c₂

private theorem reachPos_step {c₁ c₂ : Cfg 75 2}
    (h : step weakCollatz75 c₁ = some c₂) : reachPos c₁ c₂ :=
  ⟨1, le_rfl, step_one h⟩

private theorem reachPos_trans {c₁ c₂ c₃ : Cfg 75 2}
    (h₁ : reachPos c₁ c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s₁, hs₁, heq₁⟩ := h₁
  obtain ⟨s₂, hs₂, heq₂⟩ := h₂
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq heq₁ heq₂⟩

private theorem step_then_reachPos {c₁ c₂ c₃ : Cfg 75 2}
    (h₁ : step weakCollatz75 c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ :=
  reachPos_trans (reachPos_step h₁) h₂

private theorem nSteps_then_reachPos {k : ℕ} {c₁ c₂ c₃ : Cfg 75 2}
    (h₁ : nSteps weakCollatz75 k c₁ = some c₂) (h₂ : reachPos c₂ c₃) : reachPos c₁ c₃ := by
  obtain ⟨s, hs, heq⟩ := h₂
  exact ⟨k + s, by omega, nSteps_bind_eq h₁ heq⟩

private theorem sweep1R {q : Fin 75}
    (h : ∀ L R, step weakCollatz75 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweep1L {q : Fin 75}
    (h : ∀ L R, step weakCollatz75 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

private theorem sweep0R {q : Fin 75}
    (h : ∀ L R, step weakCollatz75 ⟨q, ⟨0, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 0) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 k ⟨q, Tape.mk' L (zeros k R)⟩ = some ⟨q, Tape.mk' (zeros k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, zeros_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih,
      zeros_succ']

private theorem sweep0L {q : Fin 75}
    (h : ∀ L R, step weakCollatz75 ⟨q, ⟨0, L, R⟩⟩ = some ⟨q, mkL L (R.cons 0)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 k ⟨q, mkL (zeros k L) R⟩ = some ⟨q, mkL L (zeros k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, zeros_succ, ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih,
      zeros_succ']

private theorem erase1R {q : Fin 75}
    (h : ∀ L R, step weakCollatz75 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 0) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (zeros k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, ones_succ, ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, zeros_succ']

/-! ## Canonical Stage Checkpoint & Subroutine 1: Boot + Double-Copy -/

private def baseXC (x c : ℕ) : ListBlank (Fin 2) :=
  ones c (zeros 2 (ones x B0))

/-- Canonical stage checkpoint: `0^∞ 1^x 00 1^c 0^(g + 2) [1] 1^(y - 1) 0^∞` in state `20`. -/
private def stageCfg (x c g y : ℕ) : Cfg 75 2 :=
  ⟨20, Tape.mk' (zeros (g + 2) (baseXC x c)) (ones y B0)⟩

private def cpStartCfg (X : ListBlank (Fin 2)) (A : ℕ) : Cfg 75 2 :=
  ⟨3, Tape.mk' (zeros 2 X) (ones A B0)⟩

private def cpLoopCfg (X : ListBlank (Fin 2)) (p rem : ℕ) : Cfg 75 2 :=
  ⟨3, Tape.mk' ((ones p (X.cons 0)).cons 0) (ones rem (zeros 2 (ones p B0)))⟩

private theorem boot_to_cpLoop : reachPos init (cpLoopCfg B0 1 2) := by
  refine ⟨15, by decide, ?_⟩
  change nSteps weakCollatz75 15 ⟨0, ⟨0, B0, B0⟩⟩ = some (cpLoopCfg B0 1 2)
  simp only [cpLoopCfg, ones_succ, ones_zero, zeros_succ, zeros_zero, nSteps_succ,
    nSteps_zero, Option.bind_some, tr0_0, tr1_0, tr2_0, tr4_0, tr5_0, tr6_0, tr6_1, tr7_0, tr8_0,
    tr9_0, tr10_0, tr11_0, tr11_1, ErdosTernary15.Tape.mk'_cons, ErdosTernary15.Tape.mkL_cons,
    ErdosTernary15.Tape.mk'_B0, mkL_B0, B0_cons_zero]

private theorem cpStart_first_pass (X : ListBlank (Fin 2)) (rem : ℕ) :
    reachPos (cpStartCfg X (rem + 1)) (cpLoopCfg X 1 rem) := by
  unfold cpStartCfg cpLoopCfg
  rw [zeros_succ, zeros_succ, zeros_zero, ones_succ rem B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr4_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr5_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr6_1 rem _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr6_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr7_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr8_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr9_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_0 _ _) ?_
  change reachPos ⟨11, mkL (ones rem ((ones 1 (X.cons 0)).cons 0)) (zeros 2 (ones 1 B0))⟩ _
  refine nSteps_then_reachPos (sweep1L tr11_1 rem _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr11_0 _ _)

private theorem cpLoop_step (X : ListBlank (Fin 2)) (p rem : ℕ) :
    reachPos (cpLoopCfg X p (rem + 1)) (cpLoopCfg X (p + 1) rem) := by
  unfold cpLoopCfg
  rw [ones_succ rem _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_1 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr4_0 _ _) ?_
  rw [ ← ones_succ p (X.cons 0), ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr5_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr6_1 rem _ _) ?_
  rw [zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr6_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr7_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr8_1 p _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr8_0 _ _) ?_
  change reachPos ⟨9, mkL (ones p _) (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr9_1 p _ _) ?_
  rw [← ones_add p 1 B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr9_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr10_0 _ _) ?_
  change reachPos ⟨11, mkL (ones rem ((ones (p + 1) (X.cons 0)).cons 0))
    (zeros 2 (ones (p + 1) B0))⟩ _
  refine nSteps_then_reachPos (sweep1L tr11_1 rem _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr11_0 _ _)

private theorem cpLoop_many (X : ListBlank (Fin 2)) (p rem : ℕ) :
    rem = 0 ∨ reachPos (cpLoopCfg X p rem) (cpLoopCfg X (p + rem) 0) := by
  induction rem generalizing p with
  | zero => exact Or.inl rfl
  | succ rem ih =>
    refine Or.inr ?_
    rcases ih (p + 1) with rfl | hrest
    · simpa [Nat.add_zero] using cpLoop_step X p 0
    · rw [show p + (rem + 1) = (p + 1) + rem by omega]
      exact reachPos_trans (cpLoop_step X p rem) hrest

private theorem cpLoop_finish_common (X : ListBlank (Fin 2)) (A : ℕ) :
    reachPos (cpLoopCfg X A 0)
      ⟨15, mkL X (zeros 2 (ones A (zeros 2 (ones A B0))))⟩ := by
  unfold cpLoopCfg
  rw [ones_zero, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr3_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr12_0 _ _) ?_
  change reachPos ⟨13, mkL (ones A (X.cons 0)) (ones 1 (zeros 2 (ones A B0)))⟩ _
  refine nSteps_then_reachPos (sweep1L tr13_1 A _ _) ?_
  rw [← ones_add A 1 (zeros 2 (ones A B0)), ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr13_0 _ _) ?_
  rw [ones_succ A (zeros 2 (ones A B0)), ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr12_1 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr14_0 _ _)

private theorem double_copy_to_stage (a : ℕ) :
    reachPos (cpLoopCfg B0 1 (a + 2)) (stageCfg (a + 3) (a + 3) 0 (a + 3)) := by
  let A := a + 3
  have h1 : reachPos (cpLoopCfg B0 1 (a + 2)) (cpLoopCfg B0 A 0) := by
    rcases cpLoop_many B0 1 (a + 2) with h0 | hpos
    · exfalso; omega
    · rw [show 1 + (a + 2) = A by dsimp [A]; omega] at hpos
      exact hpos
  refine reachPos_trans h1 ?_
  refine reachPos_trans (cpLoop_finish_common B0 A) ?_
  rw [mkL_B0]
  refine step_then_reachPos (tr15_0 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (sweep0R tr16_0 2 B0 _) ?_
  rw [zeros_B0, show ones A (zeros 2 (ones A B0)) =
    (ones (a + 2) (zeros 2 (ones A B0))).cons 1 from rfl, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr16_1 _ _) ?_
  change reachPos ⟨17, Tape.mk' (ones 1 B0) (ones (a + 2) (zeros 2 (ones A B0)))⟩ _
  refine nSteps_then_reachPos (sweep1R tr17_1 (a + 2) _ _) ?_
  rw [← ones_add (a + 2) 1 B0, show a + 2 + 1 = A from rfl, zeros_succ, zeros_succ, zeros_zero,
    ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr17_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr11_0 _ _) ?_
  change reachPos (cpStartCfg (ones A B0) (a + 2 + 1)) _
  refine reachPos_trans (cpStart_first_pass (ones A B0) (a + 2)) ?_
  have h2 : reachPos (cpLoopCfg (ones A B0) 1 (a + 2)) (cpLoopCfg (ones A B0) A 0) := by
    rcases cpLoop_many (ones A B0) 1 (a + 2) with h0 | hpos
    · exfalso; omega
    · rw [show 1 + (a + 2) = A by dsimp [A]; omega] at hpos
      exact hpos
  refine reachPos_trans h2 ?_
  refine reachPos_trans (cpLoop_finish_common (ones A B0) A) ?_
  rw [show ones A B0 = (ones (a + 2) B0).cons 1 from rfl, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr15_1 _ _) ?_
  rw [← ones_succ (a + 2) B0]
  change reachPos ⟨18, Tape.mk' (ones A B0)
    (zeros 2 (ones A (zeros 2 (ones A B0))))⟩ _
  refine nSteps_then_reachPos (sweep0R tr18_0 2 _ _) ?_
  rw [show ones A (zeros 2 (ones A B0)) =
    (ones (a + 2) (zeros 2 (ones A B0))).cons 1 from rfl, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr18_1 _ _) ?_
  change reachPos ⟨19, Tape.mk' (ones 1 (zeros 2 (ones A B0)))
    (ones (a + 2) (zeros 2 (ones A B0)))⟩ _
  refine nSteps_then_reachPos (sweep1R tr19_1 (a + 2) _ _) ?_
  rw [← ones_add (a + 2) 1 (zeros 2 (ones A B0)), show a + 2 + 1 = A from rfl,
    zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr19_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  exact reachPos_step (tr20_0 _ _)

private theorem init_reaches_stage3 : reachPos init (stageCfg 3 3 0 3) :=
  reachPos_trans boot_to_cpLoop (double_copy_to_stage 0)

/-! ## Subroutine 2: Unified `terras` Evaluation (`stageCfg` → `cmpLoopCfg`) -/

private theorem parity_scan_p1 (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 (2 * k) ⟨2, Tape.mk' L (ones (2 * k) R)⟩ =
      some ⟨2, Tape.mk' (ones (2 * k) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have hpre : nSteps weakCollatz75 2
        ⟨2, Tape.mk' L (((ones (2 * k) R).cons 1).cons 1)⟩ =
        some ⟨2, Tape.mk' (ones 2 L) (ones (2 * k) R)⟩ := by
      rw [nSteps_succ, ErdosTernary15.Tape.mk'_cons, tr2_1, Option.bind_some,
        nSteps_succ, ErdosTernary15.Tape.mk'_cons, tr21_1, Option.bind_some, nSteps_zero]
      rfl
    have hpost : nSteps weakCollatz75 (2 * k) ⟨2, Tape.mk' (ones 2 L) (ones (2 * k) R)⟩ =
        some ⟨2, Tape.mk' (ones (2 * k + 2) L) R⟩ := by
      rw [ih (ones 2 L), ← ones_add (2 * k) 2 L]
    have htot := nSteps_bind_eq hpre hpost
    simpa only [show 2 * (k + 1) = 2 * k + 2 by omega, Nat.add_comm 2 (2 * k), ones_succ] using htot

private theorem parity_scan_p0 (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps weakCollatz75 (2 * k) ⟨21, Tape.mk' L (ones (2 * k) R)⟩ =
      some ⟨21, Tape.mk' (ones (2 * k) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have hpre : nSteps weakCollatz75 2
        ⟨21, Tape.mk' L (((ones (2 * k) R).cons 1).cons 1)⟩ =
        some ⟨21, Tape.mk' (ones 2 L) (ones (2 * k) R)⟩ := by
      rw [nSteps_succ, ErdosTernary15.Tape.mk'_cons, tr21_1, Option.bind_some,
        nSteps_succ, ErdosTernary15.Tape.mk'_cons, tr2_1, Option.bind_some, nSteps_zero]
      rfl
    have hpost : nSteps weakCollatz75 (2 * k) ⟨21, Tape.mk' (ones 2 L) (ones (2 * k) R)⟩ =
        some ⟨21, Tape.mk' (ones (2 * k + 2) L) R⟩ := by
      rw [ih (ones 2 L), ← ones_add (2 * k) 2 L]
    have htot := nSteps_bind_eq hpre hpost
    simpa only [show 2 * (k + 1) = 2 * k + 2 by omega, Nat.add_comm 2 (2 * k), ones_succ] using htot

private def oddBackCfg (L0 : ListBlank (Fin 2)) (g0 m r : ℕ) : Cfg 75 2 :=
  ⟨27, mkL (ones r (zeros 2 (ones (2 * m) (zeros (g0 + 2) L0)))) (ones 1 B0)⟩

private theorem oddBack_step (L0 : ListBlank (Fin 2)) (g0 m r : ℕ) :
    reachPos (oddBackCfg L0 g0 (m + 1) r) (oddBackCfg L0 (g0 + 2) m (r + 3)) := by
  unfold oddBackCfg
  refine nSteps_then_reachPos (sweep1L tr27_1 r _ _) ?_
  rw [← ones_add r 1 B0, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr27_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr28_0 _ _) ?_
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, ones_succ (2 * m + 1) _,
    ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr29_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr30_1 (2 * m + 1) _ _) ?_
  rw [zeros_succ (g0 + 1) L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr30_0 _ _) ?_
  rw [← ones_succ' (2 * m + 1) _, show 2 * m + 1 + 1 = 2 * m + 2 by omega,
    ones_succ (2 * m + 1) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr14_1 _ _) ?_
  rw [ones_succ (2 * m) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr10_1 _ _) ?_
  have hL4 : (((zeros (g0 + 1) L0).cons 0).cons 0).cons 0 = zeros (g0 + 2 + 2) L0 := rfl
  rw [hL4]
  refine nSteps_then_reachPos (sweep1R tr31_1 (2 * m) _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr31_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr32_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr24_1 (r + 1) _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr24_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr25_0 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  exact reachPos_step (tr26_0 _ _)

private theorem oddBack_many (L0 : ListBlank (Fin 2)) (g0 m r : ℕ) :
    m = 0 ∨ reachPos (oddBackCfg L0 g0 m r) (oddBackCfg L0 (g0 + 2 * m) 0 (r + 3 * m)) := by
  induction m generalizing g0 r with
  | zero => exact Or.inl rfl
  | succ m ih =>
    refine Or.inr ?_
    rcases ih (g0 + 2) (r + 3) with rfl | hrest
    · simpa [Nat.add_zero] using oddBack_step L0 g0 0 r
    · have hg : g0 + 2 + 2 * m = g0 + 2 * (m + 1) := by omega
      have hr : r + 3 + 3 * m = r + 3 * (m + 1) := by omega
      rw [hg, hr] at hrest
      exact reachPos_trans (oddBack_step L0 g0 m r) hrest

private theorem oddBack_exit (L0 : ListBlank (Fin 2)) (g0 r : ℕ) :
    reachPos (oddBackCfg L0 g0 0 r) ⟨35, mkL (ones (r + 1) (zeros (g0 + 4) L0)) B0⟩ := by
  unfold oddBackCfg
  rw [Nat.mul_zero, ones_zero]
  refine nSteps_then_reachPos (sweep1L tr27_1 r _ _) ?_
  rw [← ones_add r 1 B0, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr27_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr28_0 _ _) ?_
  rw [zeros_succ (g0 + 1) L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr29_0 _ _) ?_
  have hL : (zeros (g0 + 1) L0).cons 0 = zeros (g0 + 2) L0 := rfl
  have hR : ((ones (r + 1) B0).cons 0).cons 0 = zeros 2 (ones (r + 1) B0) := rfl
  rw [hL, hR]
  refine nSteps_then_reachPos (sweep0R tr33_0 2 _ _) ?_
  have hL2 : zeros 2 (zeros (g0 + 2) L0) = zeros (g0 + 4) L0 := by
    rw [← zeros_add 2 (g0 + 2) L0, show 2 + (g0 + 2) = g0 + 4 by omega]
  rw [hL2, ones_succ r B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr33_1 _ _) ?_
  change reachPos ⟨34, Tape.mk' (ones 1 (zeros (g0 + 4) L0)) (ones r B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr34_1 r _ B0) ?_
  rw [← ones_add r 1 (zeros (g0 + 4) L0), ErdosTernary15.Tape.mk'_B0]
  have hstep := tr34_0 (ones (r + 1) (zeros (g0 + 4) L0)) B0
  rw [B0_cons_zero] at hstep
  exact reachPos_step hstep

private def evenChkCfg (L0 : ListBlank (Fin 2)) (g0 m r : ℕ) : Cfg 75 2 :=
  ⟨28, mkL (ones (2 * m) (zeros (g0 + 2) L0)) ((ones (r + 1) B0).cons 0)⟩

private theorem evenChk_step (L0 : ListBlank (Fin 2)) (g0 m r : ℕ) :
    reachPos (evenChkCfg L0 g0 (m + 1) r) (evenChkCfg L0 (g0 + 2) m (r + 1)) := by
  unfold evenChkCfg
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, ones_succ (2 * m + 1) _,
    ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr28_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr30_1 (2 * m + 1) _ _) ?_
  rw [zeros_succ (g0 + 1) L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr30_0 _ _) ?_
  rw [← ones_succ' (2 * m + 1) _, show 2 * m + 1 + 1 = 2 * m + 2 by omega,
    ones_succ (2 * m + 1) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr14_1 _ _) ?_
  rw [ones_succ (2 * m) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr10_1 _ _) ?_
  have hL : (((zeros (g0 + 1) L0).cons 0).cons 0).cons 0 = zeros (g0 + 2 + 2) L0 := rfl
  rw [hL]
  refine nSteps_then_reachPos (sweep1R tr31_1 (2 * m) _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr31_0 _ _) ?_
  rw [ones_succ r B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr32_1 _ _) ?_
  change reachPos ⟨26, Tape.mk' (ones 1 ((ones (2 * m) (zeros (g0 + 2 + 2) L0)).cons 0))
    (ones r B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr26_1 r _ B0) ?_
  rw [← ones_add r 1 _, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr26_0 _ _) ?_
  change reachPos ⟨27, mkL (ones (r + 1) ((ones (2 * m) (zeros (g0 + 2 + 2) L0)).cons 0))
    (ones 1 B0)⟩ _
  refine nSteps_then_reachPos (sweep1L tr27_1 (r + 1) _ _) ?_
  rw [← ones_add (r + 1) 1 B0, ErdosTernary15.Tape.mkL_cons]
  exact reachPos_step (tr27_0 _ _)

private theorem evenChk_many (L0 : ListBlank (Fin 2)) (g0 m r : ℕ) :
    m = 0 ∨ reachPos (evenChkCfg L0 g0 m r) (evenChkCfg L0 (g0 + 2 * m) 0 (r + m)) := by
  induction m generalizing g0 r with
  | zero => exact Or.inl rfl
  | succ m ih =>
    refine Or.inr ?_
    rcases ih (g0 + 2) (r + 1) with rfl | hrest
    · simpa [Nat.add_zero] using evenChk_step L0 g0 0 r
    · have hg : g0 + 2 + 2 * m = g0 + 2 * (m + 1) := by omega
      have hr : r + 1 + m = r + (m + 1) := by omega
      rw [hg, hr] at hrest
      exact reachPos_trans (evenChk_step L0 g0 m r) hrest

private theorem evenChk_exit (L0 : ListBlank (Fin 2)) (g0 r : ℕ) :
    reachPos (evenChkCfg L0 g0 0 r) ⟨35, mkL (ones (r + 1) (zeros (g0 + 3) L0)) B0⟩ := by
  unfold evenChkCfg
  rw [Nat.mul_zero, ones_zero, zeros_succ (g0 + 1) L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr28_0 _ _) ?_
  rw [zeros_succ g0 L0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr29_0 _ _) ?_
  have hL : (zeros g0 L0).cons 0 = zeros (g0 + 1) L0 := rfl
  have hR : ((ones (r + 1) B0).cons 0).cons 0 = zeros 2 (ones (r + 1) B0) := rfl
  rw [hL, hR]
  refine nSteps_then_reachPos (sweep0R tr33_0 2 _ _) ?_
  have hL2 : zeros 2 (zeros (g0 + 1) L0) = zeros (g0 + 3) L0 := by
    rw [← zeros_add 2 (g0 + 1) L0, show 2 + (g0 + 1) = g0 + 3 by omega]
  rw [hL2, ones_succ r B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr33_1 _ _) ?_
  change reachPos ⟨34, Tape.mk' (ones 1 (zeros (g0 + 3) L0)) (ones r B0)⟩ _
  refine nSteps_then_reachPos (sweep1R tr34_1 r _ B0) ?_
  rw [← ones_add r 1 (zeros (g0 + 3) L0), ErdosTernary15.Tape.mk'_B0]
  have hstep := tr34_0 (ones (r + 1) (zeros (g0 + 3) L0)) B0
  rw [B0_cons_zero] at hstep
  exact reachPos_step hstep

private theorem terras_pos_of_pos {y : ℕ} (hy : 1 ≤ y) : 1 ≤ terras y := by
  unfold terras
  split_ifs <;> omega

private theorem terras_eval (x c g y : ℕ) (hy : 1 ≤ y) :
    ∃ g0 : ℕ, reachPos (stageCfg x c g y)
      ⟨35, mkL (ones (terras y) (zeros (g0 + 3) (baseXC x c))) B0⟩ := by
  rcases Nat.mod_two_eq_zero_or_one y with hev | hodd
  · let k := y / 2 - 1
    have hy_eq : y = 2 * k + 2 := by dsimp [k]; omega
    have hty : terras y = k + 1 := by unfold terras; simp [hev]; dsimp [k]; omega
    refine ⟨g + 2 * k, ?_⟩
    rw [hty, hy_eq]
    unfold stageCfg
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, ones_succ (2 * k + 1) B0,
      ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr20_1 _ _) ?_
    rw [ones_succ (2 * k) B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr2_1 _ _) ?_
    change reachPos ⟨21, Tape.mk' (ones 2 (zeros (g + 2) (baseXC x c))) (ones (2 * k) B0)⟩ _
    refine nSteps_then_reachPos (parity_scan_p0 k _ B0) ?_
    rw [← ones_add (2 * k) 2 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr21_0 _ _) ?_
    rw [B0_cons_zero, show 2 * k + 2 = (2 * k + 1) + 1 by omega,
      ones_succ (2 * k + 1) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr22_1 _ _) ?_
    rw [ones_succ (2 * k) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr0_1 _ _) ?_
    change reachPos (evenChkCfg (baseXC x c) g k 0) _
    rcases evenChk_many (baseXC x c) g k 0 with hk0 | hmany
    · rw [hk0, Nat.mul_zero, Nat.add_zero]
      exact evenChk_exit (baseXC x c) g 0
    · rw [Nat.zero_add] at hmany
      exact reachPos_trans hmany (evenChk_exit (baseXC x c) (g + 2 * k) k)
  · let k := y / 2
    have hy_eq : y = 2 * k + 1 := by dsimp [k]; omega
    have hty : terras y = 3 * k + 2 := by
      unfold terras
      have hne : ¬ (y % 2 = 0) := by omega
      simp [hne]; dsimp [k]; omega
    refine ⟨g + 2 * k + 1, ?_⟩
    rw [hty, hy_eq, show g + 2 * k + 1 + 3 = (g + 2 * k) + 4 by omega]
    unfold stageCfg
    rw [ones_succ (2 * k) B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr20_1 _ _) ?_
    change reachPos ⟨2, Tape.mk' (ones 1 (zeros (g + 2) (baseXC x c))) (ones (2 * k) B0)⟩ _
    refine nSteps_then_reachPos (parity_scan_p1 k _ B0) ?_
    rw [← ones_add (2 * k) 1 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr2_0 _ _) ?_
    rw [B0_cons_zero, ones_succ (2 * k) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr4_1 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr23_0 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr25_0 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr26_0 _ _) ?_
    change reachPos (oddBackCfg (baseXC x c) g k 1) _
    rcases oddBack_many (baseXC x c) g k 1 with hk0 | hmany
    · rw [hk0, Nat.mul_zero, Nat.add_zero]
      exact oddBack_exit (baseXC x c) g 1
    · have hr : 1 + 3 * k + 1 = 3 * k + 2 := by omega
      exact reachPos_trans hmany (by rw [← hr]; exact oddBack_exit (baseXC x c) (g + 2 * k) _)

/-! ## Subroutine 3: Comparison, Cycle Halt & Unified Restoration -/

private def cmpLoopCfg (xRem c G zRem p : ℕ) : Cfg 75 2 :=
  ⟨35, mkL (ones zRem (zeros G (ones c (zeros 2 (ones xRem ((ones p B0).cons 0))))))
    ((ones p B0).cons 0)⟩

private theorem cmpLoopCfg_zero (x c G z : ℕ) :
    cmpLoopCfg x c G z 0 = ⟨35, mkL (ones z (zeros G (baseXC x c))) B0⟩ := by
  simp only [cmpLoopCfg, baseXC, ones_zero, B0_cons_zero]

private theorem cmpLoop_step (xRem c' g0 zRem p : ℕ) :
    reachPos (cmpLoopCfg (xRem + 1) (c' + 1) (g0 + 3) (zRem + 1) p)
      (cmpLoopCfg xRem (c' + 1) (g0 + 3) zRem (p + 1)) := by
  unfold cmpLoopCfg
  rw [ones_succ zRem _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr35_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr36_0 _ _) ?_
  rw [← ones_succ p B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr37_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr38_1 zRem _ _) ?_
  rw [zeros_succ (g0 + 2) _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr38_0 _ _) ?_
  refine nSteps_then_reachPos (sweep0L tr39_0 (g0 + 2) _ _) ?_
  have hR0 : zeros (g0 + 2) ((ones zRem ((ones (p + 1) B0).cons 0)).cons 0) =
      zeros (g0 + 3) (ones zRem ((ones (p + 1) B0).cons 0)) := by
    rw [← zeros_succ' (g0 + 2) _]
  rw [hR0, ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr39_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr40_1 c' _ _) ?_
  rw [← ones_succ' c' _, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr40_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr41_0 _ _) ?_
  rw [ones_succ xRem _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr42_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr43_1 xRem _ _) ?_
  rw [← ones_succ' xRem _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr43_0 _ _) ?_
  rw [ones_succ xRem _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr37_1 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr22_0 _ _) ?_
  rw [← ones_succ p B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr44_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1R tr45_1 xRem _ _) ?_
  have hR2 :
      ((ones (c' + 1) (zeros (g0 + 3) (ones zRem ((ones (p + 1) B0).cons 0)))).cons 0).cons 0 =
        zeros 2 (ones (c' + 1) (zeros (g0 + 3) (ones zRem ((ones (p + 1) B0).cons 0)))) := rfl
  rw [hR2]
  have h45 : step weakCollatz75 ⟨45, Tape.mk' (ones xRem ((ones (p + 1) B0).cons 0))
      (zeros 2 (ones (c' + 1) (zeros (g0 + 3) (ones zRem ((ones (p + 1) B0).cons 0)))))⟩ =
      some ⟨46, Tape.mk' ((ones xRem ((ones (p + 1) B0).cons 0)).cons 0)
        (zeros 1 (ones (c' + 1) (zeros (g0 + 3) (ones zRem ((ones (p + 1) B0).cons 0)))))⟩ := by
    rw [zeros_succ 1 _, ErdosTernary15.Tape.mk'_cons]
    exact tr45_0 _ _
  refine step_then_reachPos h45 ?_
  refine nSteps_then_reachPos (sweep0R tr46_0 1 _ _) ?_
  have hL2 : zeros 1 ((ones xRem ((ones (p + 1) B0).cons 0)).cons 0) =
      zeros 2 (ones xRem ((ones (p + 1) B0).cons 0)) := rfl
  rw [hL2, ones_succ c' _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr46_1 _ _) ?_
  change reachPos ⟨47, Tape.mk' (ones 1 (zeros 2 (ones xRem ((ones (p + 1) B0).cons 0))))
    (ones c' (zeros (g0 + 3) (ones zRem ((ones (p + 1) B0).cons 0))))⟩ _
  refine nSteps_then_reachPos (sweep1R tr47_1 c' _ _) ?_
  rw [← ones_add c' 1 _, zeros_succ (g0 + 2) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr47_0 _ _) ?_
  cases zRem with
  | zero =>
    rw [ones_zero]
    have hz : zeros (g0 + 2) ((ones (p + 1) B0).cons 0) = zeros (g0 + 3) (ones (p + 1) B0) := by
      rw [← zeros_succ' (g0 + 2) (ones (p + 1) B0)]
    rw [hz]
    refine nSteps_then_reachPos (sweep0R tr48_0 (g0 + 3) _ _) ?_
    rw [← zeros_succ' (g0 + 3) _, ones_succ p B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr48_1 _ _) ?_
    change reachPos ⟨49, Tape.mk' (ones 1 _) (ones p B0)⟩ _
    refine nSteps_then_reachPos (sweep1R tr49_1 p _ B0) ?_
    rw [← ones_add p 1 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr49_0 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr50_0 _ _) ?_
    rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr51_0 _ _) ?_
    rw [B0_cons_zero]
    refine nSteps_then_reachPos (sweep1L tr52_1 (p + 1) _ B0) ?_
    rw [ErdosTernary15.Tape.mkL_cons]
    exact reachPos_step (tr52_0 _ _)
  | succ z' =>
    let L48 := zeros (g0 + 3) (ones (c' + 1) (zeros 2 (ones xRem ((ones (p + 1) B0).cons 0))))
    refine nSteps_then_reachPos (sweep0R tr48_0 (g0 + 2) _ _) ?_
    rw [← zeros_succ' (g0 + 2) _, ones_succ z' _, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr48_1 _ _) ?_
    change reachPos ⟨49, Tape.mk' (ones 1 L48) (ones z' ((ones (p + 1) B0).cons 0))⟩ _
    refine nSteps_then_reachPos (sweep1R tr49_1 z' _ _) ?_
    rw [← ones_add z' 1 _, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr49_0 _ _) ?_
    rw [ones_succ p B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr50_1 _ _) ?_
    change reachPos ⟨49, Tape.mk' (ones 1 ((ones (z' + 1) L48).cons 0)) (ones p B0)⟩ _
    refine nSteps_then_reachPos (sweep1R tr49_1 p _ B0) ?_
    rw [← ones_add p 1 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr49_0 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr50_0 _ _) ?_
    rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr51_0 _ _) ?_
    rw [B0_cons_zero]
    refine nSteps_then_reachPos (sweep1L tr52_1 (p + 1) _ B0) ?_
    rw [ErdosTernary15.Tape.mkL_cons]
    exact reachPos_step (tr52_0 _ _)

private theorem cmpLoop_many (xRem c' g0 zRem p k : ℕ) :
    k = 0 ∨ reachPos (cmpLoopCfg (xRem + k) (c' + 1) (g0 + 3) (zRem + k) p)
      (cmpLoopCfg xRem (c' + 1) (g0 + 3) zRem (p + k)) := by
  induction k generalizing xRem zRem p with
  | zero => exact Or.inl rfl
  | succ k ih =>
    refine Or.inr ?_
    have hx : xRem + (k + 1) = (xRem + k) + 1 := by omega
    have hz : zRem + (k + 1) = (zRem + k) + 1 := by omega
    rw [hx, hz]
    rcases ih xRem zRem (p + 1) with rfl | hrest
    · simpa [Nat.add_zero] using cmpLoop_step xRem c' g0 zRem p
    · have hp : p + 1 + k = p + (k + 1) := by omega
      rw [hp] at hrest
      exact reachPos_trans (cmpLoop_step (xRem + k) c' g0 (zRem + k) p) hrest

private theorem cmpLoop_halt_eq (c' g0 p : ℕ) :
    ∃ s cfg, nSteps weakCollatz75 s (cmpLoopCfg 0 (c' + 1) (g0 + 3) 0 p) = some cfg ∧
      step weakCollatz75 cfg = none := by
  let Rfin : ListBlank (Fin 2) :=
    ((ones (c' + 1) (zeros (g0 + 2) (((ones p B0).cons 0).cons 0))).cons 0).cons 0
  have hreach :
      reachPos (cmpLoopCfg 0 (c' + 1) (g0 + 3) 0 p) ⟨56, ⟨0, ones p B0, Rfin⟩⟩ := by
    unfold cmpLoopCfg
    rw [ones_zero, ones_zero, zeros_succ (g0 + 2) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr35_0 _ _) ?_
    refine nSteps_then_reachPos (sweep0L tr53_0 (g0 + 2) _ _) ?_
    rw [ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr53_1 _ _) ?_
    change reachPos ⟨54, mkL (ones c' (zeros 2 ((ones p B0).cons 0)))
      (ones 1 (zeros (g0 + 2) (((ones p B0).cons 0).cons 0)))⟩ _
    refine nSteps_then_reachPos (sweep1L tr54_1 c' _ _) ?_
    rw [← ones_add c' 1 _, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr54_0 _ _) ?_
    rw [ErdosTernary15.Tape.mkL_cons]
    have hs55 := tr55_0 ((ones p B0).cons 0)
      ((ones (c' + 1) (zeros (g0 + 2) (((ones p B0).cons 0).cons 0))).cons 0)
    rw [ErdosTernary15.Tape.mkL_cons] at hs55
    exact reachPos_step hs55
  obtain ⟨s, _, hs⟩ := hreach
  exact ⟨s, ⟨56, ⟨0, ones p B0, Rfin⟩⟩, hs, tr56_0 _ _⟩

private theorem gt_restore_to_chkC (xRest c' G0 zRem p q : ℕ) :
    reachPos ⟨58, mkL (ones p B0)
        (ones (xRest + 1) (zeros 2 (ones (c' + 1)
          (zeros (G0 + 2) (ones zRem ((ones (q + 1) B0).cons 0))))))⟩
      ⟨70, mkL (ones c' (zeros 2 (ones (p + xRest) B0)))
        (zeros (G0 + 3) (ones (zRem + (q + 1)) B0))⟩ := by
  refine nSteps_then_reachPos (sweep1L tr58_1 p B0 _) ?_
  rw [← ones_add p (xRest + 1) _, mkL_B0]
  refine step_then_reachPos (tr58_0 _ _) ?_
  rw [B0_cons_zero, show p + (xRest + 1) = (p + xRest) + 1 by omega,
    ones_succ (p + xRest) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr7_1 _ _) ?_
  rw [B0_cons_zero]
  refine nSteps_then_reachPos (sweep1R tr59_1 (p + xRest) B0 _) ?_
  rw [zeros_succ 1 _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr59_0 _ _) ?_
  refine nSteps_then_reachPos (sweep0R tr60_0 1 _ _) ?_
  have hL2 : zeros 1 ((ones (p + xRest) B0).cons 0) = zeros 2 (ones (p + xRest) B0) := rfl
  rw [hL2, ones_succ c' _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr60_1 _ _) ?_
  change reachPos ⟨61, Tape.mk' (ones 1 (zeros 2 (ones (p + xRest) B0)))
    (ones c' (zeros (G0 + 2) (ones zRem ((ones (q + 1) B0).cons 0))))⟩ _
  refine nSteps_then_reachPos (sweep1R tr61_1 c' _ _) ?_
  rw [← ones_add c' 1 _, zeros_succ (G0 + 1) _, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr61_0 _ _) ?_
  cases zRem with
  | zero =>
    rw [ones_zero, Nat.zero_add]
    have hz : zeros (G0 + 1) ((ones (q + 1) B0).cons 0) = zeros (G0 + 2) (ones (q + 1) B0) := by
      rw [← zeros_succ' (G0 + 1) _]
    rw [hz]
    refine nSteps_then_reachPos (sweep0R tr62_0 (G0 + 2) _ _) ?_
    rw [← zeros_succ' (G0 + 2) _, ones_succ q B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr62_1 _ _) ?_
    change reachPos ⟨63, Tape.mk' (ones 1 _) (ones q B0)⟩ _
    refine nSteps_then_reachPos (sweep1R tr63_1 q _ B0) ?_
    rw [← ones_add q 1 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr63_0 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr64_0 _ _) ?_
    rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr65_0 _ _) ?_
    rw [B0_cons_zero]
    refine nSteps_then_reachPos (sweep1L tr66_1 (q + 1) _ B0) ?_
    rw [zeros_succ (G0 + 2) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr66_0 _ _) ?_
    change reachPos ⟨67, Tape.mk' (ones 1 _) (ones (q + 1) B0)⟩ _
    refine nSteps_then_reachPos (sweep1R tr67_1 (q + 1) _ B0) ?_
    rw [← ones_add (q + 1) 1 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr67_0 _ _) ?_
    rw [B0_cons_zero, show q + 1 + 1 = (q + 1) + 1 from rfl, ones_succ (q + 1) _,
      ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr55_1 _ _) ?_
    rw [B0_cons_zero]
    refine nSteps_then_reachPos (sweep1L tr68_1 (q + 1) _ B0) ?_
    rw [zeros_succ (G0 + 1) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr68_0 _ _) ?_
    refine nSteps_then_reachPos (sweep0L tr69_0 (G0 + 1) _ _) ?_
    rw [← zeros_succ' (G0 + 1) _, ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
    exact reachPos_step (tr69_1 _ _)
  | succ z' =>
    let Lbase := zeros (G0 + 2) (ones (c' + 1) (zeros 2 (ones (p + xRest) B0)))
    refine nSteps_then_reachPos (sweep0R tr62_0 (G0 + 1) _ _) ?_
    rw [← zeros_succ' (G0 + 1) _, ones_succ z' _, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr62_1 _ _) ?_
    change reachPos ⟨63, Tape.mk' (ones 1 Lbase) (ones z' ((ones (q + 1) B0).cons 0))⟩ _
    refine nSteps_then_reachPos (sweep1R tr63_1 z' _ _) ?_
    rw [← ones_add z' 1 _, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr63_0 _ _) ?_
    rw [ones_succ q B0, ErdosTernary15.Tape.mk'_cons]
    refine step_then_reachPos (tr64_1 _ _) ?_
    change reachPos ⟨63, Tape.mk' (ones 1 ((ones (z' + 1) Lbase).cons 0)) (ones q B0)⟩ _
    refine nSteps_then_reachPos (sweep1R tr63_1 q _ B0) ?_
    rw [← ones_add q 1 _, ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr63_0 _ _) ?_
    rw [ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr64_0 _ _) ?_
    rw [B0_cons_zero, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr65_0 _ _) ?_
    rw [B0_cons_zero]
    refine nSteps_then_reachPos (sweep1L tr66_1 (q + 1) _ B0) ?_
    rw [ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr66_0 _ _) ?_
    change reachPos ⟨67, Tape.mk' (ones 1 (ones (z' + 1) Lbase)) (ones (q + 1) B0)⟩ _
    rw [← ones_add 1 (z' + 1) _]
    refine nSteps_then_reachPos (sweep1R tr67_1 (q + 1) _ B0) ?_
    rw [← ones_add (q + 1) (1 + (z' + 1)) _,
      show q + 1 + (1 + (z' + 1)) = (z' + 1 + (q + 1)) + 1 by omega,
      ErdosTernary15.Tape.mk'_B0]
    refine step_then_reachPos (tr67_0 _ _) ?_
    rw [B0_cons_zero, ones_succ (z' + 1 + (q + 1)) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr55_1 _ _) ?_
    rw [B0_cons_zero]
    refine nSteps_then_reachPos (sweep1L tr68_1 (z' + 1 + (q + 1)) _ B0) ?_
    dsimp only [Lbase]
    rw [zeros_succ (G0 + 1) _, ErdosTernary15.Tape.mkL_cons]
    refine step_then_reachPos (tr68_0 _ _) ?_
    refine nSteps_then_reachPos (sweep0L tr69_0 (G0 + 1) _ _) ?_
    rw [← zeros_succ' (G0 + 1) _, ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
    exact reachPos_step (tr69_1 _ _)

private theorem cmp_mismatch_lt (xRem c' g0 q : ℕ) :
    reachPos (cmpLoopCfg (xRem + 1) (c' + 1) (g0 + 3) 0 (q + 1))
      ⟨70, mkL (ones c' (zeros 2 (ones ((q + 1) + (xRem + 1)) B0)))
        (zeros (g0 + 4) (ones (q + 1) B0))⟩ := by
  unfold cmpLoopCfg
  rw [ones_zero, zeros_succ (g0 + 2) _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr35_0 _ _) ?_
  refine nSteps_then_reachPos (sweep0L tr53_0 (g0 + 2) _ _) ?_
  rw [← zeros_succ' (g0 + 2) _, ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr53_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr54_1 c' _ _) ?_
  rw [← ones_succ' c' _, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr54_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr55_0 _ _) ?_
  rw [ones_succ xRem _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr56_1 _ _) ?_
  have hR2 : ((ones (c' + 1) (zeros (g0 + 3) ((ones (q + 1) B0).cons 0))).cons 0).cons 0 =
      zeros 2 (ones (c' + 1) (zeros (g0 + 3) ((ones (q + 1) B0).cons 0))) := rfl
  rw [hR2]
  refine nSteps_then_reachPos (sweep1L tr57_1 xRem _ _) ?_
  rw [← ones_succ' xRem _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr57_0 _ _) ?_
  have heq : reachPos ⟨58, mkL (ones (q + 1) B0)
      (ones ((xRem + 1) + 1) (zeros 2 (ones (c' + 1)
        (zeros ((g0 + 1) + 2) (ones 0 ((ones (q + 1) B0).cons 0))))))⟩
      ⟨70, mkL (ones c' (zeros 2 (ones ((q + 1) + (xRem + 1)) B0)))
        (zeros (g0 + 4) (ones (0 + (q + 1)) B0))⟩ :=
    gt_restore_to_chkC (xRem + 1) c' (g0 + 1) 0 (q + 1) q
  rw [Nat.zero_add] at heq
  exact heq

private theorem cmp_mismatch_gt (c' g0 zRem q : ℕ) :
    reachPos (cmpLoopCfg 0 (c' + 1) (g0 + 3) (zRem + 1) (q + 1))
      ⟨70, mkL (ones c' (zeros 2 (ones (q + 1) B0)))
        (zeros (g0 + 4) (ones (zRem + 1 + (q + 1)) B0))⟩ := by
  unfold cmpLoopCfg
  rw [ones_zero, ones_succ zRem _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr35_1 _ _) ?_
  rw [ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr36_0 _ _) ?_
  rw [← ones_succ (q + 1) B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr37_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr38_1 zRem _ _) ?_
  rw [zeros_succ (g0 + 2) _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr38_0 _ _) ?_
  refine nSteps_then_reachPos (sweep0L tr39_0 (g0 + 2) _ _) ?_
  rw [← zeros_succ' (g0 + 2) _, ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr39_1 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr40_1 c' _ _) ?_
  rw [← ones_succ' c' _, zeros_succ, zeros_succ, zeros_zero, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr40_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr41_0 _ _) ?_
  rw [ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr42_0 _ _) ?_
  have heq : reachPos ⟨58, mkL (ones (q + 1) B0)
      (ones (0 + 1) (zeros 2 (ones (c' + 1)
        (zeros ((g0 + 1) + 2) (ones zRem ((ones ((q + 1) + 1) B0).cons 0))))))⟩
      ⟨70, mkL (ones c' (zeros 2 (ones ((q + 1) + 0) B0)))
        (zeros (g0 + 4) (ones (zRem + ((q + 1) + 1)) B0))⟩ :=
    gt_restore_to_chkC 0 c' (g0 + 1) zRem (q + 1) (q + 1)
  rw [Nat.add_zero, show zRem + ((q + 1) + 1) = zRem + 1 + (q + 1) by omega] at heq
  exact heq

/-! ## Subroutine 4: Counter Check, Stage Advance & Halting Equivalence -/

private theorem chkC_continue (x c' g0 z : ℕ) :
    reachPos ⟨70, mkL (ones (c' + 1) (zeros 2 (ones x B0))) (zeros (g0 + 4) (ones z B0))⟩
      (stageCfg x (c' + 1) (g0 + 2) z) := by
  unfold stageCfg baseXC
  rw [ones_succ c' _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr70_1 _ _) ?_
  rw [← ones_succ c' _]
  exact ⟨g0 + 4, by omega, sweep0R tr20_0 (g0 + 4) _ (ones z B0)⟩

private theorem chkC_next_stage (a g0 z : ℕ) (hz : 1 ≤ z) :
    reachPos ⟨70, mkL (ones 0 (zeros 2 (ones (a + 3) B0))) (zeros (g0 + 4) (ones z B0))⟩
      (stageCfg (a + 4) (a + 4) 0 (a + 4)) := by
  rw [ones_zero, zeros_succ 1 _, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr70_0 _ _) ?_
  refine nSteps_then_reachPos (sweep0R tr71_0 (g0 + 4) (zeros 2 (ones (a + 3) B0)) _) ?_
  rw [← zeros_add (g0 + 4) 2 (ones (a + 3) B0), show z = (z - 1) + 1 by omega,
    ones_succ (z - 1) B0, ErdosTernary15.Tape.mk'_cons]
  refine step_then_reachPos (tr71_1 _ _) ?_
  refine nSteps_then_reachPos (erase1R tr72_1 (z - 1) _ B0) ?_
  rw [ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr72_0 _ _) ?_
  have hzerosL : zeros (z - 1) ((zeros (g0 + 4 + 2) (ones (a + 3) B0)).cons 0) =
      zeros (z - 1 + (g0 + 7)) (ones (a + 3) B0) := by
    have h1 : (zeros (g0 + 4 + 2) (ones (a + 3) B0)).cons 0 =
        zeros (g0 + 7) (ones (a + 3) B0) := rfl
    rw [h1, ← zeros_add (z - 1) (g0 + 7) _]
  rw [B0_cons_zero, hzerosL]
  refine nSteps_then_reachPos (sweep0L tr73_0 (z - 1 + (g0 + 7)) _ B0) ?_
  rw [zeros_B0, ones_succ (a + 2) B0, ErdosTernary15.Tape.mkL_cons]
  refine step_then_reachPos (tr73_1 _ _) ?_
  rw [← ones_succ (a + 2) B0, ErdosTernary15.Tape.mk'_B0]
  refine step_then_reachPos (tr74_0 _ _) ?_
  refine nSteps_then_reachPos (sweep1L tr11_1 (a + 3) B0 (ones 1 B0)) ?_
  rw [← ones_add (a + 3) 1 B0, mkL_B0]
  refine step_then_reachPos (tr11_0 _ _) ?_
  have hcp0 : Tape.mk' (B0.cons 0) (ones (a + 3 + 1) B0) =
      Tape.mk' (zeros 2 B0) (ones ((a + 3) + 1) B0) := by
    rw [B0_cons_zero, zeros_B0]
  rw [hcp0]
  exact reachPos_trans (cpStart_first_pass B0 (a + 3)) (double_copy_to_stage (a + 1))

private theorem stage_round_halt (x c g y : ℕ) (hx : 3 ≤ x) (hc : 1 ≤ c) (hy : 1 ≤ y)
    (hhit : terras y = x) :
    ∃ s cfg, nSteps weakCollatz75 s (stageCfg x c g y) = some cfg ∧
      step weakCollatz75 cfg = none := by
  obtain ⟨g0, heval⟩ := terras_eval x c g y hy
  rw [hhit, ← cmpLoopCfg_zero] at heval
  have hc_eq : c = (c - 1) + 1 := by omega
  rw [hc_eq] at heval
  have hmany : reachPos (cmpLoopCfg x ((c - 1) + 1) (g0 + 3) x 0)
      (cmpLoopCfg 0 ((c - 1) + 1) (g0 + 3) 0 x) := by
    rcases cmpLoop_many 0 (c - 1) g0 0 0 x with h0 | hp
    · exfalso; omega
    · rw [Nat.zero_add] at hp
      exact hp
  obtain ⟨s₁, _, hs₁⟩ := reachPos_trans heval hmany
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := cmpLoop_halt_eq (c - 1) g0 x
  rw [← hc_eq] at hs₁ hs₂
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

private theorem stage_round_mismatch_to_chkC (x c' g y : ℕ) (hx : 3 ≤ x) (hy : 1 ≤ y)
    (hne : terras y ≠ x) :
    ∃ g0 : ℕ, reachPos (stageCfg x (c' + 1) g y)
      ⟨70, mkL (ones c' (zeros 2 (ones x B0))) (zeros (g0 + 4) (ones (terras y) B0))⟩ := by
  obtain ⟨g0, heval⟩ := terras_eval x (c' + 1) g y hy
  rw [← cmpLoopCfg_zero] at heval
  let z := terras y
  have hz_pos : 1 ≤ z := terras_pos_of_pos hy
  refine ⟨g0, reachPos_trans heval ?_⟩
  rcases Nat.lt_or_ge z x with hlt | hge
  · let q := z - 1
    let xRem := x - z - 1
    have hz_eq : z = q + 1 := by dsimp [q]; omega
    have hx_eq : x = (xRem + 1) + (q + 1) := by dsimp [xRem, q]; omega
    have hmany : reachPos (cmpLoopCfg x (c' + 1) (g0 + 3) z 0)
        (cmpLoopCfg (xRem + 1) (c' + 1) (g0 + 3) 0 (q + 1)) := by
      rw [hx_eq, hz_eq]
      rcases cmpLoop_many (xRem + 1) c' g0 0 0 (q + 1) with h0 | hp
      · exfalso; omega
      · rw [Nat.zero_add] at hp
        exact hp
    refine reachPos_trans hmany ?_
    have hgoal_eq :
        (⟨70, mkL (ones c' (zeros 2 (ones ((q + 1) + (xRem + 1)) B0)))
          (zeros (g0 + 4) (ones (q + 1) B0))⟩ : Cfg 75 2) =
        ⟨70, mkL (ones c' (zeros 2 (ones x B0)))
          (zeros (g0 + 4) (ones (terras y) B0))⟩ := by
      rw [show (q + 1) + (xRem + 1) = x by omega, show q + 1 = terras y from hz_eq.symm]
    rw [← hgoal_eq]
    exact cmp_mismatch_lt xRem c' g0 q
  · have hgt : x < z := by omega
    let q := x - 1
    let zRem := z - x - 1
    have hx_eq : x = q + 1 := by dsimp [q]; omega
    have hz_eq : z = (zRem + 1) + (q + 1) := by dsimp [zRem, q]; omega
    have hmany : reachPos (cmpLoopCfg x (c' + 1) (g0 + 3) z 0)
        (cmpLoopCfg 0 (c' + 1) (g0 + 3) (zRem + 1) (q + 1)) := by
      rw [hx_eq, hz_eq]
      rcases cmpLoop_many 0 c' g0 (zRem + 1) 0 (q + 1) with h0 | hp
      · exfalso; omega
      · rw [Nat.zero_add] at hp
        exact hp
    refine reachPos_trans hmany ?_
    have hgoal_eq :
        (⟨70, mkL (ones c' (zeros 2 (ones (q + 1) B0)))
          (zeros (g0 + 4) (ones (zRem + 1 + (q + 1)) B0))⟩ : Cfg 75 2) =
        ⟨70, mkL (ones c' (zeros 2 (ones x B0)))
          (zeros (g0 + 4) (ones (terras y) B0))⟩ := by
      rw [← hx_eq, show zRem + 1 + x = terras y by dsimp [zRem, z]; omega]
    rw [← hgoal_eq]
    exact cmp_mismatch_gt c' g0 zRem q

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
    ∃ g : ℕ, (m = 0 ∧ g = 0) ∨
      reachPos (stageCfg x x 0 x) (stageCfg x (x - m) g (terras^[m] x)) := by
  induction m with
  | zero => exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  | succ m ih =>
    rcases ih (by omega) (fun j hj1 hjm => hcl j hj1 (by omega)) with ⟨g, ⟨rfl, rfl⟩ | hprev⟩
    · have hne1 : terras x ≠ x := hcl 1 le_rfl le_rfl
      have hx_eq : x = (x - 1) + 1 := by omega
      have hxc1 : x - 1 = (x - 2) + 1 := by omega
      obtain ⟨g0, hchk⟩ := stage_round_mismatch_to_chkC x (x - 1) 0 x hx (by omega) hne1
      rw [← hx_eq] at hchk
      rw [hxc1] at hchk ⊢
      exact ⟨g0 + 2, Or.inr (reachPos_trans hchk (chkC_continue x (x - 2) g0 (terras x)))⟩
    · have hne : terras (terras^[m] x) ≠ x := by
        have hit : terras (terras^[m] x) = terras^[m + 1] x :=
          (Function.iterate_succ_apply' terras m x).symm
        rw [hit]
        exact hcl (m + 1) (by omega) le_rfl
      have hy_pos : 1 ≤ terras^[m] x := terras_iterate_pos (by omega) m
      have hxm_eq : x - m = (x - (m + 1)) + 1 := by omega
      have hxm1_eq : x - (m + 1) = (x - (m + 2)) + 1 := by omega
      rw [hxm_eq] at hprev
      obtain ⟨g0, hchk⟩ :=
        stage_round_mismatch_to_chkC x (x - (m + 1)) g (terras^[m] x) hx hy_pos hne
      rw [hxm1_eq] at hprev hchk ⊢
      have hcont := chkC_continue x (x - (m + 2)) g0 (terras (terras^[m] x))
      rw [Function.iterate_succ_apply']
      exact ⟨g0 + 2, Or.inr (reachPos_trans hprev (reachPos_trans hchk hcont))⟩

private theorem stage_full_advance (x : ℕ) (hx : 3 ≤ x) (hcl : StageClear x x) :
    reachPos (stageCfg x x 0 x) (stageCfg (x + 1) (x + 1) 0 (x + 1)) := by
  rcases stage_within_reach x hx (x - 1) (by omega)
      (fun j hj1 hjm => hcl j hj1 (by omega)) with ⟨g, ⟨h0, _⟩ | hprev⟩
  · exfalso; omega
  · have hsub1 : x - (x - 1) = 1 := by omega
    rw [hsub1] at hprev
    have hne : terras (terras^[x - 1] x) ≠ x := by
      have hit : terras (terras^[x - 1] x) = terras^[x] x := by
        rw [← Function.iterate_succ_apply' terras (x - 1) x, show (x - 1).succ = x by omega]
      rw [hit]
      exact hcl x (by omega) le_rfl
    have hy_pos : 1 ≤ terras^[x - 1] x := terras_iterate_pos (by omega) (x - 1)
    obtain ⟨g0, hchk⟩ := stage_round_mismatch_to_chkC x 0 g (terras^[x - 1] x) hx hy_pos hne
    have hnext := chkC_next_stage (x - 3) g0 (terras (terras^[x - 1] x))
      (terras_pos_of_pos hy_pos)
    rw [show x - 3 + 3 = x by omega, show x - 3 + 4 = x + 1 by omega] at hnext
    exact reachPos_trans hprev (reachPos_trans hchk hnext)

private theorem stage_first_hit_halt (x j : ℕ) (hx : 3 ≤ x) (hj1 : 1 ≤ j) (hjx : j ≤ x)
    (hcl : StageClear x (j - 1)) (hhit : terras^[j] x = x) :
    ∃ s cfg, nSteps weakCollatz75 s (stageCfg x x 0 x) = some cfg ∧
      step weakCollatz75 cfg = none := by
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj_gt1
  · exact stage_round_halt x x 0 x hx (by omega) (by omega) hhit
  · rcases stage_within_reach x hx (j - 1) (by omega) hcl with ⟨g, ⟨h0, _⟩ | hprev⟩
    · exfalso; omega
    · obtain ⟨s₁, _, hs₁⟩ := hprev
      have hhit' : terras (terras^[j - 1] x) = x := by
        rw [← Function.iterate_succ_apply' terras (j - 1) x, show (j - 1).succ = j by omega]
        exact hhit
      obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_round_halt x (x - (j - 1)) g (terras^[j - 1] x)
        hx (by omega) (terras_iterate_pos (by omega) (j - 1)) hhit'
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
    ∃ s : ℕ, X - 2 ≤ s ∧ nSteps weakCollatz75 s init = some (stageCfg X X 0 X) := by
  induction X, hX using Nat.le_induction with
  | base =>
    obtain ⟨s, hs1, hs⟩ := init_reaches_stage3
    exact ⟨s, by omega, hs⟩
  | succ X hX ih =>
    obtain ⟨s₁, hs₁_ge, hs₁⟩ := ih fun x hx3 hx_le => hAll x hx3 (by omega)
    have hclX : StageClear X X := hAll X hX (by omega)
    obtain ⟨s₂, hs₂_pos, hs₂⟩ := stage_full_advance X hX hclX
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- The 75-state machine `weakCollatz75` (`weak_collatz_75`) halts on the blank tape if and only if
there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(constructive, zero `Classical.choice`). -/
theorem halts_weakCollatz75_iff_bounded_cycle :
    ConjectureMachines.Halts weakCollatz75 ↔
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

end ConjectureMachines.WeakCollatz75
