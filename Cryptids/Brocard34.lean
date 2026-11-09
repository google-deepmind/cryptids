/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ErdosTernary14

/-!
# Brocard34

The 34-state Turing machine `brocard_34` halts on the blank tape if and only if Brocard's
problem `n! + 1 = m ^ 2` has a solution with `n > 7`, i.e. beyond the three known solutions
`n = 4, 5, 7`.

## Provenance and Attribution

The machine and the proofs are by Daniel Veljjanoski, with Claude (Anthropic) as assistant
(November 2026). Earlier machines for the same problem are Charlie Reams's 61-state machine
with a Lean proof (`calr3/tinycryptids`, November 2026) and a 43-state table without a
machine-checked proof by Tandi, Gonzalez-Hendrix and Brown (<https://arxiv.org/abs/2605.20215>).

## Machine Layout

The tape holds, left to right, a block `N` of `n` ones, a separator, and a block `B` of ones,
all in unary. Between rounds `B` holds `n! / 8` ones (`3` at `n = 4`). A round multiplies `B`
by `n + 1` and grows `N` by one cell, then tests whether `(n + 1)! / 8` is a triangular number
`1 + 2 + ⋯ + k`; this holds if and only if `(n + 1)! + 1` is a perfect square (`m = 2k + 1`).

* Multiply (states `1`–`10`): `LN0`/`LN1` walk left and write a `1` left of `N`; `EN` walks a
  hole through `N`, and for every cell `R0`/`R1`/`L0`/`L1`/`EC` copy the template `B` once,
  cell by cell, to the right end; `X` merges. `B` becomes `(n + 1) B + 1` ones.
* Test (states `0`, `11`–`18`): a hole walks right through `B` (`TLs`/`TLx` create it, `TE` moves
  it); a block `S` right of `B` holds the current chunk size with a hole walking left
  (`TR0`/`TR1`, `SB`); each wrap of `S` adds a cell to `S` for free (the blank beyond `S`
  acts as the hole), and `SC` then checks whether `B` is exhausted: if so, success.
* Fail (states `19`–`21`): `ER`/`ER2`/`ER3` erase `S`, and `ER3` erases the last cell of `B`
  on the way back, which cancels the extra cell left by the merge.
* Gate (states `22`–`32`): on success `Yp` walks left over `B` and `C1`–`C8` count the cells
  of `N`; fewer than `8` (`n = 5, 7`, the known solutions) returns via `Ns`/`Bs` and erases `S`
  (`ER`); the eighth cell halts (`C8` reading `1`).
* Start: the machine starts in `TLx` (state `0`) on the blank tape; its never-read `0`-cell and
  those of `C1`–`C5` and `C7` write `1111 0 111` leftward, `A` (state `33`) writes the last cell,
  and the gate's return path brings the head to the end of `B`.
-/

@[expose] public section

namespace ConjectureMachines.Brocard34

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_zero nSteps_succ nSteps_reaches nSteps_add
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- The 34-state Brocard machine (`brocard_34`), loaded from `artifacts/brocard_34/machine.txt`
in `Machines.lean`. -/
abbrev brocard34 : Machine 34 2 := Machines.brocard34

theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

theorem nSteps_cons {M : Machine 34 2} {n : ℕ} {c c₁ c₂ : Cfg 34 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps_succ, h₁, Option.bind_some, h₂]

theorem stepR {q q' : Fin 34} {a b : Fin 2}
    (h : brocard34.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step brocard34 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem stepL {q q' : Fin 34} {a b : Fin 2}
    (h : brocard34.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step brocard34 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table

States in file order:
`0` = TLx, `1` = LN0, `2` = LN1, `3` = EN, `4` = S1, `5` = R0, `6` = R1, `7` = L0, `8` = L1,
`9` = EC, `10` = X, `11` = TLs, `12` = TR0, `13` = TR1, `14` = SB, `15` = SC, `16` = TL0,
`17` = TL1, `18` = TE, `19` = ER, `20` = ER2, `21` = ER3, `22` = Yp, `23` = C1, `24` = C2,
`25` = C3, `26` = C4, `27` = C5, `28` = C6, `29` = C7, `30` = C8, `31` = Ns, `32` = Bs,
`33` = A.
-/

theorem sTLx_0 (L R) : step brocard34 ⟨0, ⟨0, L, R⟩⟩ = some ⟨23, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTLx_1 (L R) : step brocard34 ⟨0, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sLN0_0 (L R) : step brocard34 ⟨1, ⟨0, L, R⟩⟩ = some ⟨2, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sLN0_1 (L R) : step brocard34 ⟨1, ⟨1, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sLN1_0 (L R) : step brocard34 ⟨2, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sLN1_1 (L R) : step brocard34 ⟨2, ⟨1, L, R⟩⟩ = some ⟨2, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sEN_0 (L R) : step brocard34 ⟨3, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sEN_1 (L R) : step brocard34 ⟨3, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sS1_0 (L R) : step brocard34 ⟨4, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sS1_1 (L R) : step brocard34 ⟨4, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sR0_0 (L R) : step brocard34 ⟨5, ⟨0, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sR0_1 (L R) : step brocard34 ⟨5, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sR1_0 (L R) : step brocard34 ⟨6, ⟨0, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sR1_1 (L R) : step brocard34 ⟨6, ⟨1, L, R⟩⟩ = some ⟨6, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL0_0 (L R) : step brocard34 ⟨7, ⟨0, L, R⟩⟩ = some ⟨8, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sL0_1 (L R) : step brocard34 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sL1_0 (L R) : step brocard34 ⟨8, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL1_1 (L R) : step brocard34 ⟨8, ⟨1, L, R⟩⟩ = some ⟨8, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sEC_0 (L R) : step brocard34 ⟨9, ⟨0, L, R⟩⟩ = some ⟨1, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sEC_1 (L R) : step brocard34 ⟨9, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sX_0 (L R) : step brocard34 ⟨10, ⟨0, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sX_1 (L R) : step brocard34 ⟨10, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTLs_0 (L R) : step brocard34 ⟨11, ⟨0, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTLs_1 (L R) : step brocard34 ⟨11, ⟨1, L, R⟩⟩ = some ⟨11, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTR0_0 (L R) : step brocard34 ⟨12, ⟨0, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTR0_1 (L R) : step brocard34 ⟨12, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTR1_0 (L R) : step brocard34 ⟨13, ⟨0, L, R⟩⟩ = some ⟨14, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTR1_1 (L R) : step brocard34 ⟨13, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sSB_0 (L R) : step brocard34 ⟨14, ⟨0, L, R⟩⟩ = some ⟨15, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sSB_1 (L R) : step brocard34 ⟨14, ⟨1, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sSC_0 (L R) : step brocard34 ⟨15, ⟨0, L, R⟩⟩ = some ⟨22, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sSC_1 (L R) : step brocard34 ⟨15, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTL0_0 (L R) : step brocard34 ⟨16, ⟨0, L, R⟩⟩ = some ⟨17, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sTL0_1 (L R) : step brocard34 ⟨16, ⟨1, L, R⟩⟩ = some ⟨16, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTL1_0 (L R) : step brocard34 ⟨17, ⟨0, L, R⟩⟩ = some ⟨18, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTL1_1 (L R) : step brocard34 ⟨17, ⟨1, L, R⟩⟩ = some ⟨17, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTE_0 (L R) : step brocard34 ⟨18, ⟨0, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTE_1 (L R) : step brocard34 ⟨18, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER_0 (L R) : step brocard34 ⟨19, ⟨0, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER_1 (L R) : step brocard34 ⟨19, ⟨1, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER2_0 (L R) : step brocard34 ⟨20, ⟨0, L, R⟩⟩ = some ⟨21, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sER2_1 (L R) : step brocard34 ⟨20, ⟨1, L, R⟩⟩ = some ⟨20, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sER3_0 (L R) : step brocard34 ⟨21, ⟨0, L, R⟩⟩ = some ⟨21, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sER3_1 (L R) : step brocard34 ⟨21, ⟨1, L, R⟩⟩ = some ⟨1, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sYp_0 (L R) : step brocard34 ⟨22, ⟨0, L, R⟩⟩ = some ⟨23, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sYp_1 (L R) : step brocard34 ⟨22, ⟨1, L, R⟩⟩ = some ⟨22, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC1_0 (L R) : step brocard34 ⟨23, ⟨0, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC1_1 (L R) : step brocard34 ⟨23, ⟨1, L, R⟩⟩ = some ⟨24, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC2_0 (L R) : step brocard34 ⟨24, ⟨0, L, R⟩⟩ = some ⟨25, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC2_1 (L R) : step brocard34 ⟨24, ⟨1, L, R⟩⟩ = some ⟨25, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC3_0 (L R) : step brocard34 ⟨25, ⟨0, L, R⟩⟩ = some ⟨26, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sC3_1 (L R) : step brocard34 ⟨25, ⟨1, L, R⟩⟩ = some ⟨26, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC4_0 (L R) : step brocard34 ⟨26, ⟨0, L, R⟩⟩ = some ⟨27, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC4_1 (L R) : step brocard34 ⟨26, ⟨1, L, R⟩⟩ = some ⟨27, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC5_0 (L R) : step brocard34 ⟨27, ⟨0, L, R⟩⟩ = some ⟨29, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC5_1 (L R) : step brocard34 ⟨27, ⟨1, L, R⟩⟩ = some ⟨28, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC6_0 (L R) : step brocard34 ⟨28, ⟨0, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sC6_1 (L R) : step brocard34 ⟨28, ⟨1, L, R⟩⟩ = some ⟨29, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC7_0 (L R) : step brocard34 ⟨29, ⟨0, L, R⟩⟩ = some ⟨33, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC7_1 (L R) : step brocard34 ⟨29, ⟨1, L, R⟩⟩ = some ⟨30, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sC8_0 (L R) : step brocard34 ⟨30, ⟨0, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sC8_1 (L R : ListBlank (Fin 2)) : step brocard34 ⟨30, ⟨1, L, R⟩⟩ = none := rfl
theorem sNs_0 (L R) : step brocard34 ⟨31, ⟨0, L, R⟩⟩ = some ⟨32, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sNs_1 (L R) : step brocard34 ⟨31, ⟨1, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sBs_0 (L R) : step brocard34 ⟨32, ⟨0, L, R⟩⟩ = some ⟨19, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sBs_1 (L R) : step brocard34 ⟨32, ⟨1, L, R⟩⟩ = some ⟨32, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sA_0 (L R) : step brocard34 ⟨33, ⟨0, L, R⟩⟩ = some ⟨31, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sA_1 (L R : ListBlank (Fin 2)) : step brocard34 ⟨33, ⟨1, L, R⟩⟩ = none := rfl

/-- Runs the machine through a fixed sequence of steps on a concrete tape. -/
local macro "tm_run" : tactic => `(tactic| simp only [nSteps_succ, nSteps_zero, Option.bind_some,
  sTLx_0, sTLx_1, sLN0_0, sLN0_1, sLN1_0, sLN1_1, sEN_0, sEN_1, sS1_0, sS1_1, sR0_0, sR0_1,
  sR1_0, sR1_1, sL0_0, sL0_1, sL1_0, sL1_1, sEC_0, sEC_1, sX_0, sX_1, sTLs_0, sTLs_1, sTR0_0,
  sTR0_1, sTR1_0, sTR1_1, sSB_0, sSB_1, sSC_0, sSC_1, sTL0_0, sTL0_1, sTL1_0, sTL1_1, sTE_0,
  sTE_1, sER_0, sER_1, sER2_0, sER2_1, sER3_0, sER3_1, sYp_0, sYp_1, sC1_0, sC1_1, sC2_0,
  sC2_1, sC3_0, sC3_1, sC4_0, sC4_1, sC5_0, sC5_1, sC6_0, sC6_1, sC7_0, sC7_1, sC8_0, sNs_0,
  sNs_1, sBs_0, sBs_1, sA_0,
  ErdosTernary15.Tape.mk'_cons, ErdosTernary15.Tape.mkL_cons, ErdosTernary15.Tape.mk'_B0, mkL_B0,
  ListBlank.append, B0_cons_zero])

/-! ## Sweeps over Ones -/

theorem sweepR {q : Fin 34}
    (h : ∀ L R, step brocard34 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard34 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) R = (ones k R).cons 1 from rfl,
      ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

theorem sweepL {q : Fin 34}
    (h : ∀ L R, step brocard34 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard34 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) L = (ones k L).cons 1 from rfl,
      ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

/-! ## Tape Encoding and Configurations -/

/-- The cells left of `B`: the separator, then the `n` cells of `N`. -/
def NL (n : ℕ) : ListBlank (Fin 2) := (ones n B0).cons 0

/-- Start of a round: `LN0` on the last of the `v + 1` cells of `B`, `N` has `n` cells. -/
def roundCfg (n v : ℕ) : Cfg 34 2 := ⟨1, Tape.mk' (ones v (NL n)) (B0.cons 1)⟩

/-- Start of a test: `TLx` on the first of the `M` cells of `B`. -/
def testCfg (n M : ℕ) : Cfg 34 2 := ⟨0, Tape.mk' (NL n) (ones M B0)⟩

/-- Inside the copy loop: `R0` right of the cursor hole; `u` template cells are done and `v`
remain, `M` has `m` cells, and `N`'s hole has `a` cells to its left and `b` to its right. -/
def copyCfg (a b u v m : ℕ) : Cfg 34 2 :=
  ⟨5, Tape.mk' ((ones u ((ones b ((ones a B0).cons 0)).cons 0)).cons 0)
    (ones v ((ones m B0).cons 0))⟩

/-- `EN` on the first of the `b` remaining cells of `N`, `a` cells to its left; the template
has `V` cells and `M` has `m`. -/
def enCfg (a b V m : ℕ) : Cfg 34 2 :=
  ⟨3, Tape.mk' (ones a B0) (ones b ((ones V ((ones m B0).cons 0)).cons 0))⟩

/-- Inside the test: `TR0` on the separator right of `B`; the hole of `B` has `a` cells to its
left and `r` to its right; `S` has `p` cells, a hole, and `q` cells (`q = 0` and the blank
beyond `S` as the hole for a solid `S` of `p` cells). -/
def advCfg (n a r p q : ℕ) : Cfg 34 2 :=
  ⟨12, Tape.mk' (ones r ((ones a (NL n)).cons 0)) ((ones p ((ones q B0).cons 0)).cons 0)⟩

theorem ones_zero (L : ListBlank (Fin 2)) : ones 0 L = L := rfl

theorem ones_zero_B0 : ones 0 B0 = B0 := rfl

theorem advCfg_solid (n a r p : ℕ) :
    advCfg n a r p 0 = ⟨12, Tape.mk' (ones r ((ones a (NL n)).cons 0)) ((ones p B0).cons 0)⟩ := by
  simp only [advCfg, ones_zero_B0, B0_cons_zero]

/-! ## Multiply (States `8`–`17`) -/

/-- One copy step: the cursor moves one cell right and `M` gains a cell. -/
theorem copy_step (a b u v m : ℕ) :
    ∃ s, nSteps brocard34 s (copyCfg a b u (v + 1) m) = some (copyCfg a b (u + 1) v (m + 1)) := by
  set W := (ones b ((ones a B0).cons 0)).cons 0 with hW
  set Y := ones u W with hY
  have h₁ := sweepR sR0_1 (v + 1) (Y.cons 0) ((ones m B0).cons 0)
  have h₂ : step brocard34 ⟨5, Tape.mk' (ones (v + 1) (Y.cons 0)) ((ones m B0).cons 0)⟩ =
      some ⟨6, Tape.mk' ((ones (v + 1) (Y.cons 0)).cons 0) (ones m B0)⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons, sR0_0]
  have h₃ := sweepR sR1_1 m ((ones (v + 1) (Y.cons 0)).cons 0) B0
  have h₄ : step brocard34 ⟨6, Tape.mk' (ones m ((ones (v + 1) (Y.cons 0)).cons 0)) B0⟩ =
      some ⟨7, mkL (ones m ((ones (v + 1) (Y.cons 0)).cons 0)) (B0.cons 1)⟩ := by
    rw [ErdosTernary15.Tape.mk'_B0, sR1_0]
  have h₅ := sweepL sL0_1 m ((ones (v + 1) (Y.cons 0)).cons 0) (B0.cons 1)
  have h₆ : step brocard34 ⟨7, mkL ((ones (v + 1) (Y.cons 0)).cons 0) (ones m (B0.cons 1))⟩ =
      some ⟨8, mkL (ones (v + 1) (Y.cons 0)) ((ones (m + 1) B0).cons 0)⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons, sL0_0, ones_succ' m]
  have h₇ := sweepL sL1_1 (v + 1) (Y.cons 0) ((ones (m + 1) B0).cons 0)
  have h₈ : nSteps brocard34 2 ⟨8, mkL (Y.cons 0) (ones (v + 1) ((ones (m + 1) B0).cons 0))⟩ =
      some (copyCfg a b (u + 1) v (m + 1)) := by
    change nSteps brocard34 2 ⟨8, mkL (Y.cons 0) ((ones v ((ones (m + 1) B0).cons 0)).cons 1)⟩ =
      some ⟨5, Tape.mk' ((Y.cons 1).cons 0) (ones v ((ones (m + 1) B0).cons 0))⟩
    tm_run
  exact ⟨_, nSteps_bind_eq h₁ (nSteps_cons h₂ (nSteps_bind_eq h₃ (nSteps_cons h₄
    (nSteps_bind_eq h₅ (nSteps_cons h₆ (nSteps_bind_eq h₇ h₈))))))⟩

/-- The last copy step: the cursor leaves the template, `LN0`/`LN1` return to the hole of `N`
and fill it, and `EN` reads the next cell of `N`. -/
theorem copy_done (a b u m : ℕ) :
    ∃ s, nSteps brocard34 s (copyCfg a b u 0 m) = some (enCfg (a + 1) b (u + 1) (m + 1)) := by
  set W := (ones b ((ones a B0).cons 0)).cons 0 with hW
  set Y := ones u W with hY
  have h₂ : step brocard34 (copyCfg a b u 0 m) =
      some ⟨6, Tape.mk' ((Y.cons 0).cons 0) (ones m B0)⟩ := by
    change step brocard34 ⟨5, Tape.mk' (Y.cons 0) ((ones m B0).cons 0)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons, sR0_0]
  have h₃ := sweepR sR1_1 m ((Y.cons 0).cons 0) B0
  have h₄ : step brocard34 ⟨6, Tape.mk' (ones m ((Y.cons 0).cons 0)) B0⟩ =
      some ⟨7, mkL (ones m ((Y.cons 0).cons 0)) (B0.cons 1)⟩ := by
    rw [ErdosTernary15.Tape.mk'_B0, sR1_0]
  have h₅ := sweepL sL0_1 m ((Y.cons 0).cons 0) (B0.cons 1)
  have h₆ : nSteps brocard34 3 ⟨7, mkL ((Y.cons 0).cons 0) (ones m (B0.cons 1))⟩ =
      some ⟨1, mkL (Y.cons 1) ((ones (m + 1) B0).cons 0)⟩ := by
    rw [ones_succ' m]
    tm_run
  have h₇ := sweepL sLN0_1 (u + 1) W ((ones (m + 1) B0).cons 0)
  have h₈ : step brocard34 ⟨1, mkL W (ones (u + 1) ((ones (m + 1) B0).cons 0))⟩ =
      some ⟨2, mkL (ones b ((ones a B0).cons 0))
        ((ones (u + 1) ((ones (m + 1) B0).cons 0)).cons 0)⟩ := by
    rw [hW, ErdosTernary15.Tape.mkL_cons, sLN0_0]
  have h₉ := sweepL sLN1_1 b ((ones a B0).cons 0)
    ((ones (u + 1) ((ones (m + 1) B0).cons 0)).cons 0)
  have h₁₀ : step brocard34 ⟨2, mkL ((ones a B0).cons 0)
      (ones b ((ones (u + 1) ((ones (m + 1) B0).cons 0)).cons 0))⟩ =
      some (enCfg (a + 1) b (u + 1) (m + 1)) := by
    rw [ErdosTernary15.Tape.mkL_cons, sLN1_0]
    rfl
  have hY1 : Y.cons 1 = ones (u + 1) W := rfl
  rw [hY1] at h₆
  exact ⟨_, nSteps_cons h₂ (nSteps_bind_eq h₃ (nSteps_cons h₄ (nSteps_bind_eq h₅
    (nSteps_bind_eq h₆ (nSteps_bind_eq h₇ (nSteps_cons h₈ (nSteps_bind_eq h₉
    (step_one h₁₀))))))))⟩

/-- A whole copy of the template. -/
theorem copy_loop (a b u : ℕ) : ∀ v m, ∃ s, nSteps brocard34 s (copyCfg a b u v m) =
    some (enCfg (a + 1) b (u + v + 1) (m + v + 1)) := by
  intro v
  induction v generalizing u with
  | zero => intro m; simpa using copy_done a b u m
  | succ v ih =>
    intro m
    obtain ⟨s₁, hs₁⟩ := copy_step a b u v m
    obtain ⟨s₂, hs₂⟩ := ih (u + 1) (m + 1)
    refine ⟨s₁ + s₂, ?_⟩
    rw [show u + (v + 1) + 1 = u + 1 + v + 1 by omega,
      show m + (v + 1) + 1 = m + 1 + v + 1 by omega]
    exact nSteps_bind_eq hs₁ hs₂

/-- `EN` finds a cell of `N`: it becomes the hole, `S1` runs to `B`, and `EC` makes the cursor. -/
theorem en_step (a c w m : ℕ) :
    ∃ s, nSteps brocard34 s (enCfg a (c + 1) (w + 1) m) = some (copyCfg a c 0 w m) := by
  have h₁ : step brocard34 (enCfg a (c + 1) (w + 1) m) =
      some ⟨4, Tape.mk' ((ones a B0).cons 0)
        (ones c ((ones (w + 1) ((ones m B0).cons 0)).cons 0))⟩ := by
    change step brocard34 ⟨3, Tape.mk' (ones a B0)
      ((ones c ((ones (w + 1) ((ones m B0).cons 0)).cons 0)).cons 1)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons, sEN_1]
  have h₂ := sweepR sS1_1 c ((ones a B0).cons 0) ((ones (w + 1) ((ones m B0).cons 0)).cons 0)
  have h₃ : nSteps brocard34 2 ⟨4, Tape.mk' (ones c ((ones a B0).cons 0))
      ((ones (w + 1) ((ones m B0).cons 0)).cons 0)⟩ = some (copyCfg a c 0 w m) := by
    change nSteps brocard34 2 ⟨4, Tape.mk' (ones c ((ones a B0).cons 0))
      (((ones w ((ones m B0).cons 0)).cons 1).cons 0)⟩ =
      some ⟨5, Tape.mk' (((ones c ((ones a B0).cons 0)).cons 0).cons 0)
        (ones w ((ones m B0).cons 0))⟩
    tm_run
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ h₃)⟩

/-- The hole of `N` walks through the `b` remaining cells, one copy of the template each. -/
theorem en_loop (w : ℕ) : ∀ a b m, ∃ s, nSteps brocard34 s (enCfg a b (w + 1) m) =
    some (enCfg (a + b) 0 (w + 1) (m + b * (w + 1))) := by
  intro a b
  induction b generalizing a with
  | zero => intro m; exact ⟨0, by simp [enCfg]⟩
  | succ c ih =>
    intro m
    obtain ⟨s₁, hs₁⟩ := en_step a c w m
    obtain ⟨s₂, hs₂⟩ := copy_loop a c 0 w m
    obtain ⟨s₃, hs₃⟩ := ih (a + 1) (m + w + 1)
    refine ⟨s₁ + s₂ + s₃, ?_⟩
    rw [show a + (c + 1) = a + 1 + c by omega,
      show m + (c + 1) * (w + 1) = m + w + 1 + c * (w + 1) by ring]
    simp only [Nat.zero_add] at hs₂
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃

/-- `N` exhausted: `X` merges the template and `M`, `TLs` returns to the start of `B`. -/
theorem en_exit (a V m : ℕ) :
    ∃ s, nSteps brocard34 s (enCfg a 0 V (m + 1)) = some (testCfg a (V + m + 2)) := by
  have h₁ : step brocard34 (enCfg a 0 V (m + 1)) =
      some ⟨10, Tape.mk' ((ones a B0).cons 0) (ones V ((ones (m + 1) B0).cons 0))⟩ := by
    change step brocard34 ⟨3, Tape.mk' (ones a B0)
      ((ones V ((ones (m + 1) B0).cons 0)).cons 0)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons, sEN_0]
  have h₂ := sweepR sX_1 V ((ones a B0).cons 0) ((ones (m + 1) B0).cons 0)
  have h₃ : step brocard34 ⟨10, Tape.mk' (ones V ((ones a B0).cons 0))
      ((ones (m + 1) B0).cons 0)⟩ = some ⟨11, mkL (ones (V + 2) (NL a)) (ones m B0)⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons, sX_0]
    change some (⟨11, Tape.mk' ((ones V (NL a)).cons 1) ((ones m B0).cons 1)⟩ : Cfg 34 2) =
      some (⟨11, mkL (((ones V (NL a)).cons 1).cons 1) (ones m B0)⟩ : Cfg 34 2)
    rw [ErdosTernary15.Tape.mk'_cons, ErdosTernary15.Tape.mkL_cons]
  have h₄ := sweepL sTLs_1 (V + 2) (NL a) (ones m B0)
  have h₅ : step brocard34 ⟨11, mkL (NL a) (ones (V + 2) (ones m B0))⟩ =
      some (testCfg a (V + m + 2)) := by
    rw [NL, ErdosTernary15.Tape.mkL_cons, sTLs_0, ← ones_add]
    rw [show V + 2 + m = V + m + 2 by omega]
    rfl
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄
    (step_one h₅))))⟩

/-- The start of a round: `LN0`/`LN1` write a cell left of `N` and `EN` reads its first cell. -/
theorem round_start (n v : ℕ) :
    ∃ s, nSteps brocard34 s (roundCfg n v) = some (enCfg 1 n (v + 1) 0) := by
  have h₁ : roundCfg n v = ⟨1, mkL (ones (v + 1) (NL n)) B0⟩ := by
    change (⟨1, Tape.mk' (ones v (NL n)) (B0.cons 1)⟩ : Cfg 34 2) =
      ⟨1, mkL ((ones v (NL n)).cons 1) B0⟩
    rw [ErdosTernary15.Tape.mk'_cons, ErdosTernary15.Tape.mkL_cons]
  have h₂ := sweepL sLN0_1 (v + 1) (NL n) B0
  have h₃ : step brocard34 ⟨1, mkL (NL n) (ones (v + 1) B0)⟩ =
      some ⟨2, mkL (ones n B0) ((ones (v + 1) B0).cons 0)⟩ := by
    rw [NL, ErdosTernary15.Tape.mkL_cons, sLN0_0]
  have h₄ := sweepL sLN1_1 n B0 ((ones (v + 1) B0).cons 0)
  have h₅ : step brocard34 ⟨2, mkL B0 (ones n ((ones (v + 1) B0).cons 0))⟩ =
      some (enCfg 1 n (v + 1) 0) := by
    rw [mkL_B0, sLN1_0]
    change _ = some (⟨3, Tape.mk' (B0.cons 1)
      (ones n ((ones (v + 1) ((ones 0 B0).cons 0)).cons 0))⟩ : Cfg 34 2)
    rw [ones_zero_B0, B0_cons_zero]
  rw [h₁]
  exact ⟨_, nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄ (step_one h₅)))⟩

/-- A whole round: `B` with `v + 1` cells becomes `(n + 1) (v + 1) + 1` cells and `N` grows. -/
theorem multiply (n v : ℕ) (hn : 1 ≤ n) :
    ∃ s, 1 ≤ s ∧ nSteps brocard34 s (roundCfg n v) =
      some (testCfg (n + 1) ((n + 1) * (v + 1) + 1)) := by
  obtain ⟨s₁, hs₁⟩ := round_start n v
  obtain ⟨s₂, hs₂⟩ := en_loop v 1 n 0
  obtain ⟨m, hm⟩ : ∃ m, 0 + n * (v + 1) = m + 1 := ⟨n * (v + 1) - 1, by
    have : 1 ≤ n * (v + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega⟩
  rw [hm] at hs₂
  obtain ⟨s₃, hs₃⟩ := en_exit (1 + n) (v + 1) m
  refine ⟨s₁ + s₂ + s₃, ?_, ?_⟩
  · have : 1 ≤ s₁ := by
      rcases Nat.eq_zero_or_pos s₁ with rfl | h
      · simp [roundCfg, enCfg] at hs₁
      · exact h
    omega
  · have e : (n + 1) * (v + 1) + 1 = v + 1 + m + 2 := by
      have : (n + 1) * (v + 1) = v + 1 + n * (v + 1) := by ring
      omega
    rw [show n + 1 = 1 + n by omega] at e ⊢
    rw [e]
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃

/-! ## Test (States `18`–`26`) -/

/-- `k` zeros followed by `L`. -/
def zeros (k : ℕ) (L : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (List.replicate k 0) L

theorem zeros_succ' (k : ℕ) (L : ListBlank (Fin 2)) : zeros (k + 1) L = zeros k (L.cons 0) := by
  rw [zeros, List.replicate_succ', ListBlank.append_assoc]
  rfl

theorem zeros_B0 (k : ℕ) : zeros k B0 = B0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zeros_succ', B0_cons_zero, ih]

/-- A state that erases ones while moving right. -/
theorem sweepR_erase {q : Fin 34}
    (h : ∀ L R, step brocard34 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 0) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard34 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (zeros k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) R = (ones k R).cons 1 from rfl,
      ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, zeros_succ']

/-- A state that moves left over zeros. -/
theorem sweepL_zeros {q : Fin 34}
    (h : ∀ L R, step brocard34 ⟨q, ⟨0, L, R⟩⟩ = some ⟨q, mkL L (R.cons 0)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps brocard34 k ⟨q, mkL (zeros k L) R⟩ = some ⟨q, mkL L (zeros k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show zeros (k + 1) L = (zeros k L).cons 0 from rfl,
      ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, zeros_succ']

/-- `TR0` right after the hole of `B`, with `r` cells of `B` still to pass. -/
def tCfg (n a r p q : ℕ) : Cfg 34 2 :=
  ⟨12, Tape.mk' ((ones a (NL n)).cons 0) (ones r ((ones p ((ones q B0).cons 0)).cons 0))⟩

theorem t_to_adv (n a r p q : ℕ) :
    nSteps brocard34 r (tCfg n a r p q) = some (advCfg n a r p q) :=
  sweepR sTR0_1 r _ _

/-- The test starts: `TLx` erases the first cell of `B`. -/
theorem test_start (n r : ℕ) :
    ∃ s, nSteps brocard34 s (testCfg n (r + 1)) = some (advCfg n 0 r 0 0) := by
  have h₁ : step brocard34 (testCfg n (r + 1)) = some (tCfg n 0 r 0 0) := by
    change step brocard34 ⟨0, Tape.mk' (NL n) ((ones r B0).cons 1)⟩ =
      some ⟨12, Tape.mk' ((NL n).cons 0) (ones r ((ones 0 ((ones 0 B0).cons 0)).cons 0))⟩
    rw [ErdosTernary15.Tape.mk'_cons, sTLx_1, ones_zero_B0, B0_cons_zero, ones_zero_B0,
      B0_cons_zero]
  exact ⟨_, nSteps_cons h₁ (t_to_adv n 0 r 0 0)⟩

/-- One unit: the hole of `S` moves one cell left and the hole of `B` one cell right. -/
theorem adv_step (n a r p q : ℕ) :
    ∃ s, nSteps brocard34 s (advCfg n a (r + 1) (p + 1) q) = some (tCfg n (a + 1) r p (q + 1)) := by
  set H := (ones a (NL n)).cons 0 with hH
  set Lr := ones (r + 1) H with hLr
  have h₁ : step brocard34 (advCfg n a (r + 1) (p + 1) q) =
      some ⟨13, Tape.mk' (Lr.cons 0) (ones (p + 1) ((ones q B0).cons 0))⟩ := by
    change step brocard34 ⟨12, Tape.mk' Lr ((ones (p + 1) ((ones q B0).cons 0)).cons 0)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons, sTR0_0]
  have h₂ := sweepR sTR1_1 (p + 1) (Lr.cons 0) ((ones q B0).cons 0)
  have h₃ : nSteps brocard34 2 ⟨13, Tape.mk' (ones (p + 1) (Lr.cons 0)) ((ones q B0).cons 0)⟩ =
      some ⟨16, mkL (ones p (Lr.cons 0)) ((ones (q + 1) B0).cons 0)⟩ := by
    change nSteps brocard34 2 ⟨13, Tape.mk' ((ones p (Lr.cons 0)).cons 1) ((ones q B0).cons 0)⟩ =
      some ⟨16, mkL (ones p (Lr.cons 0)) (((ones q B0).cons 1).cons 0)⟩
    tm_run
  have h₄ := sweepL sTL0_1 p (Lr.cons 0) ((ones (q + 1) B0).cons 0)
  have h₅ : step brocard34 ⟨16, mkL (Lr.cons 0) (ones p ((ones (q + 1) B0).cons 0))⟩ =
      some ⟨17, mkL Lr ((ones p ((ones (q + 1) B0).cons 0)).cons 0)⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons, sTL0_0]
  have h₆ := sweepL sTL1_1 (r + 1) H ((ones p ((ones (q + 1) B0).cons 0)).cons 0)
  have h₇ : nSteps brocard34 2
      ⟨17, mkL H (ones (r + 1) ((ones p ((ones (q + 1) B0).cons 0)).cons 0))⟩ =
      some (tCfg n (a + 1) r p (q + 1)) := by
    change nSteps brocard34 2 ⟨17, mkL ((ones a (NL n)).cons 0)
      ((ones r ((ones p ((ones (q + 1) B0).cons 0)).cons 0)).cons 1)⟩ =
      some ⟨12, Tape.mk' (((ones a (NL n)).cons 1).cons 0)
        (ones r ((ones p ((ones (q + 1) B0).cons 0)).cons 0))⟩
    tm_run
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (nSteps_cons h₅ (nSteps_bind_eq h₆ h₇)))))⟩

/-- `p` units in a row, while `B` has enough cells. -/
theorem adv_many (n : ℕ) : ∀ p a r p' q, ∃ s, nSteps brocard34 s (advCfg n a (r + p) (p + p') q) =
    some (advCfg n (a + p) r p' (q + p)) := by
  intro p
  induction p with
  | zero => intro a r p' q; exact ⟨0, by simp⟩
  | succ p ih =>
    intro a r p' q
    obtain ⟨s₁, hs₁⟩ := adv_step n a (r + p) (p + p') q
    have h₂ := t_to_adv n (a + 1) (r + p) (p + p') (q + 1)
    obtain ⟨s₃, hs₃⟩ := ih (a + 1) r p' (q + 1)
    refine ⟨s₁ + (r + p) + s₃, ?_⟩
    rw [show r + (p + 1) = r + p + 1 by omega, show p + 1 + p' = p + p' + 1 by omega,
      show a + (p + 1) = a + 1 + p by omega, show q + (p + 1) = q + 1 + p by omega]
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ h₂) hs₃

/-- The wrap: the hole of `S` is at its first cell, `B` has cells left; `S` becomes solid with
one more cell and the next chunk starts. -/
theorem adv_wrap (n a r q : ℕ) :
    nSteps brocard34 4 (advCfg n a (r + 1) 0 q) = some (advCfg n a (r + 1) (q + 1) 0) := by
  rw [advCfg_solid]
  change nSteps brocard34 4 ⟨12, Tape.mk' ((ones r ((ones a (NL n)).cons 0)).cons 1)
      (((ones q B0).cons 0).cons 0)⟩ =
    some ⟨12, Tape.mk' ((ones r ((ones a (NL n)).cons 0)).cons 1)
      ((((ones q B0).cons 1).cons 0))⟩
  tm_run

/-- The wrap with `B` exhausted: success, `Yp` starts the gate on the last cell of `B`. -/
theorem adv_success (n a q : ℕ) :
    nSteps brocard34 4 (advCfg n a 0 0 q) =
      some ⟨22, mkL (ones a (NL n)) (((ones (q + 1) B0).cons 0).cons 0)⟩ := by
  change nSteps brocard34 4 ⟨12, Tape.mk' ((ones a (NL n)).cons 0) (((ones q B0).cons 0).cons 0)⟩ =
    some ⟨22, mkL (ones a (NL n)) ((((ones q B0).cons 1).cons 0).cons 0)⟩
  tm_run

/-- A unit with `B` exhausted: `TE` finds the separator, `ER`/`ER2` erase `S`, `ER3` returns,
erasing the last cell of `B`, and the next round starts. -/
theorem adv_fail (n a p q : ℕ) :
    ∃ s, nSteps brocard34 s (advCfg n (a + 1) 0 (p + 1) q) = some (roundCfg n a) := by
  set H := (ones (a + 1) (NL n)).cons 0 with hH
  have h₁ : step brocard34 (advCfg n (a + 1) 0 (p + 1) q) =
      some ⟨13, Tape.mk' (H.cons 0) (ones (p + 1) ((ones q B0).cons 0))⟩ := by
    change step brocard34 ⟨12, Tape.mk' H ((ones (p + 1) ((ones q B0).cons 0)).cons 0)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons, sTR0_0]
  have h₂ := sweepR sTR1_1 (p + 1) (H.cons 0) ((ones q B0).cons 0)
  have h₃ : nSteps brocard34 2 ⟨13, Tape.mk' (ones (p + 1) (H.cons 0)) ((ones q B0).cons 0)⟩ =
      some ⟨16, mkL (ones p (H.cons 0)) ((ones (q + 1) B0).cons 0)⟩ := by
    change nSteps brocard34 2 ⟨13, Tape.mk' ((ones p (H.cons 0)).cons 1) ((ones q B0).cons 0)⟩ =
      some ⟨16, mkL (ones p (H.cons 0)) (((ones q B0).cons 1).cons 0)⟩
    tm_run
  have h₄ := sweepL sTL0_1 p (H.cons 0) ((ones (q + 1) B0).cons 0)
  have h₅ : nSteps brocard34 3 ⟨16, mkL (H.cons 0) (ones p ((ones (q + 1) B0).cons 0))⟩ =
      some ⟨19, Tape.mk' (((ones (a + 1) (NL n)).cons 1).cons 0)
        (ones p ((ones (q + 1) B0).cons 0))⟩ := by
    rw [hH]
    tm_run
  have h₆ := sweepR_erase sER_1 p (((ones (a + 1) (NL n)).cons 1).cons 0) ((ones (q + 1) B0).cons 0)
  set W := ((ones (a + 1) (NL n)).cons 1).cons 0 with hW
  have h₇ : step brocard34 ⟨19, Tape.mk' (zeros p W) ((ones (q + 1) B0).cons 0)⟩ =
      some ⟨20, Tape.mk' ((zeros p W).cons 0) (ones (q + 1) B0)⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons, sER_0]
  have h₈ := sweepR_erase sER2_1 (q + 1) ((zeros p W).cons 0) B0
  have h₉ : step brocard34 ⟨20, Tape.mk' (zeros (q + 1) ((zeros p W).cons 0)) B0⟩ =
      some ⟨21, mkL (zeros (q + 1) ((zeros p W).cons 0)) B0⟩ := by
    rw [ErdosTernary15.Tape.mk'_B0, sER2_0, B0_cons_zero]
  have h₁₀ := sweepL_zeros sER3_0 (q + 1) ((zeros p W).cons 0) B0
  rw [zeros_B0] at h₁₀
  have h₁₁ : step brocard34 ⟨21, mkL ((zeros p W).cons 0) B0⟩ = some ⟨21, mkL (zeros p W) B0⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons, sER3_0, B0_cons_zero]
  have h₁₂ := sweepL_zeros sER3_0 p W B0
  rw [zeros_B0] at h₁₂
  have h₁₃ : nSteps brocard34 2 ⟨21, mkL W B0⟩ = some (roundCfg n a) := by
    rw [hW]
    change nSteps brocard34 2 ⟨21, mkL ((((ones a (NL n)).cons 1).cons 1).cons 0) B0⟩ =
      some ⟨1, Tape.mk' (ones a (NL n)) (B0.cons 1)⟩
    tm_run
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (nSteps_bind_eq h₅ (nSteps_bind_eq h₆ (nSteps_cons h₇ (nSteps_bind_eq h₈ (nSteps_cons h₉
    (nSteps_bind_eq h₁₀ (nSteps_cons h₁₁ (nSteps_bind_eq h₁₂ h₁₃)))))))))))⟩

/-! ## Triangular Numbers and the Chunk Loop -/

/-- `pre s = 0 + 1 + ⋯ + (s - 1)`: the cells of `B` consumed before the chunk of size `s`. -/
def pre : ℕ → ℕ
  | 0 => 0
  | s + 1 => pre s + s

/-- `tri k = 1 + 2 + ⋯ + k`. -/
def tri (k : ℕ) : ℕ := pre (k + 1)

theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := rfl

theorem tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ fun k => by rw [tri_succ]; omega

theorem tri_eq_iff (j k : ℕ) : tri j = tri k ↔ j = k := tri_strictMono.injective.eq_iff

/-- Nothing strictly between two consecutive triangular numbers is triangular. -/
theorem not_tri_between {k x : ℕ} (h₁ : tri k < x) (h₂ : x < tri (k + 1)) : ¬ ∃ j, x = tri j := by
  rintro ⟨j, rfl⟩
  have := tri_strictMono.lt_iff_lt.mp h₁
  have := tri_strictMono.lt_iff_lt.mp h₂
  omega

/-- The success configuration: `Yp` on the last cell of `B` (`a` cells, the hole after them),
`S` solid with `S` cells. -/
def succCfg (n a S : ℕ) : Cfg 34 2 :=
  ⟨22, mkL (ones a (NL n)) (((ones S B0).cons 0).cons 0)⟩

/-- From the start of the chunk of size `s ≥ 1` with `r + 1` cells of `B` left: success if the
cells of `B` form a triangular number, otherwise the next round. -/
theorem chunk_loop (n : ℕ) : ∀ r s a, 1 ≤ s → a = pre s →
    (∃ j, a + r + 1 = tri j ∧ ∃ t, nSteps brocard34 t (advCfg n a (r + 1) s 0) =
      some (succCfg n (a + r + 1) (j + 1))) ∨
    ((¬ ∃ j, a + r + 1 = tri j) ∧ ∃ t, nSteps brocard34 t (advCfg n a (r + 1) s 0) =
      some (roundCfg n (a + r))) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s a hs ha
  rcases Nat.lt_or_ge (r + 1) s with hlt | hge
  · -- not enough cells: fail inside this chunk
    obtain ⟨p', hp'⟩ : ∃ p', s = r + 1 + (p' + 1) := ⟨s - r - 2, by omega⟩
    obtain ⟨t₁, ht₁⟩ := adv_many n (r + 1) a 0 (p' + 1) 0
    rw [Nat.zero_add, ← hp', show a + (r + 1) = a + r + 1 by omega] at ht₁
    obtain ⟨t₂, ht₂⟩ := adv_fail n (a + r) p' (r + 1)
    refine Or.inr ⟨?_, t₁ + t₂, nSteps_bind_eq ht₁ ht₂⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have e1 : tri s' = pre s' + s' := rfl
    have e2 : tri (s' + 1) = pre s' + s' + (s' + 1) := rfl
    have e3 : pre (s' + 1) = pre s' + s' := rfl
    have h1 : tri s' < a + r + 1 := by omega
    have h2 : a + r + 1 < tri (s' + 1) := by omega
    exact not_tri_between h1 h2
  · -- the whole chunk fits
    obtain ⟨r', hr'⟩ : ∃ r', r + 1 = r' + s := ⟨r + 1 - s, by omega⟩
    obtain ⟨t₁, ht₁⟩ := adv_many n s a r' 0 0
    rw [Nat.zero_add, Nat.add_zero, ← hr'] at ht₁
    rcases Nat.eq_zero_or_pos r' with rfl | hr'pos
    · -- exhausted exactly at the wrap: success
      have ht₂ := adv_success n (a + s) s
      refine Or.inl ⟨s, ?_, t₁ + 4, ?_⟩
      · rw [tri, pre, ha]; omega
      · rw [show a + r + 1 = a + s by omega]
        exact nSteps_bind_eq ht₁ ht₂
    · obtain ⟨r'', rfl⟩ : ∃ r'', r' = r'' + 1 := ⟨r' - 1, by omega⟩
      have ht₂ := adv_wrap n (a + s) r'' s
      obtain ⟨j, hj, t₃, ht₃⟩ | ⟨hj, t₃, ht₃⟩ :=
        ih r'' (by omega) (s + 1) (a + s) (by omega) (by rw [ha]; rfl)
      · refine Or.inl ⟨j, ?_, t₁ + 4 + t₃, ?_⟩
        · rw [← hj]; omega
        · rw [show a + r + 1 = a + s + r'' + 1 by omega]
          exact nSteps_bind_eq (nSteps_bind_eq ht₁ ht₂) ht₃
      · refine Or.inr ⟨?_, t₁ + 4 + t₃, ?_⟩
        · rw [show a + r + 1 = a + s + r'' + 1 by omega]; exact hj
        · rw [show a + r = a + s + r'' by omega]
          exact nSteps_bind_eq (nSteps_bind_eq ht₁ ht₂) ht₃

/-- The test of `B` with `M + 1` cells: the first cell is consumed; if `M` is triangular the
machine reaches the success configuration, otherwise the next round with `M` cells. -/
theorem test_run (n M : ℕ) :
    (∃ j, M = tri j ∧ ∃ t, nSteps brocard34 t (testCfg n (M + 1)) =
      some (succCfg n M (j + 1))) ∨
    ((¬ ∃ j, M = tri j) ∧ ∃ t, nSteps brocard34 t (testCfg n (M + 1)) =
      some (roundCfg n (M - 1))) := by
  obtain ⟨t₀, ht₀⟩ := test_start n M
  cases M with
  | zero =>
    exact Or.inl ⟨0, rfl, t₀ + 4, nSteps_bind_eq ht₀ (adv_success n 0 0)⟩
  | succ r =>
    have ht₁ := adv_wrap n 0 r 0
    obtain ⟨j, hj, t, ht⟩ | ⟨hj, t, ht⟩ := chunk_loop n r 1 0 le_rfl rfl
    · simp only [Nat.zero_add] at hj ht
      exact Or.inl ⟨j, hj, t₀ + 4 + t, nSteps_bind_eq (nSteps_bind_eq ht₀ ht₁) ht⟩
    · simp only [Nat.zero_add] at hj ht
      rw [Nat.add_sub_cancel]
      exact Or.inr ⟨hj, t₀ + 4 + t, nSteps_bind_eq (nSteps_bind_eq ht₀ ht₁) ht⟩

/-! ## Gate (States `30`–`40`) and Start (States `0`–`7`) -/

/-- `Yp` walks left over `B` to the last cell of `N`, where `C1` starts counting. -/
theorem gate_scan (n a S : ℕ) :
    ∃ s, nSteps brocard34 s (succCfg n (a + 1) S) =
      some ⟨23, mkL (ones n B0) ((ones (a + 1) (((ones S B0).cons 0).cons 0)).cons 0)⟩ := by
  set R := ((ones S B0).cons 0).cons 0 with hR
  have h₁ : step brocard34 (succCfg n (a + 1) S) = some ⟨22, mkL (ones a (NL n)) (R.cons 1)⟩ := by
    change step brocard34 ⟨22, mkL ((ones a (NL n)).cons 1) R⟩ = _
    rw [ErdosTernary15.Tape.mkL_cons, sYp_1]
  have h₂ := sweepL sYp_1 a (NL n) (R.cons 1)
  have h₃ : step brocard34 ⟨22, mkL (NL n) (ones a (R.cons 1))⟩ =
      some ⟨23, mkL (ones n B0) ((ones (a + 1) R).cons 0)⟩ := by
    rw [NL, ErdosTernary15.Tape.mkL_cons, sYp_0, ones_succ']
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (step_one h₃))⟩

/-- With at least eight cells in `N`, `C8` halts. -/
theorem gate_halt (n : ℕ) (Y : ListBlank (Fin 2)) :
    ∃ cfg, nSteps brocard34 7 ⟨23, mkL (ones (n + 8) B0) Y⟩ = some cfg ∧
      step brocard34 cfg = none := by
  refine ⟨⟨30, mkL (ones (n + 1) B0) (ones 7 Y)⟩, ?_, ?_⟩
  · change nSteps brocard34 7 ⟨23, mkL (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
        (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
        (ListBlank.cons 1 (ones (n + 1) B0)))))))) Y⟩ =
      some ⟨30, mkL (ones (n + 1) B0)
        (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
          (ListBlank.cons 1 Y)))))))⟩
    tm_run
  · change step brocard34 ⟨30, mkL ((ones n B0).cons 1) (ones 7 Y)⟩ = none
    rw [ErdosTernary15.Tape.mkL_cons, sC8_1]

/-- After the count stops short, `Ns`/`Bs` return to `B`, fill its hole, `ER`/`ER2` erase the
solid `S`, and `ER3` erases the last cell of `B`: the next round. -/
theorem gate_back (n a S : ℕ) :
    ∃ s, nSteps brocard34 s
      ⟨31, Tape.mk' B0 (ones n ((ones (a + 1) (((ones S B0).cons 0).cons 0)).cons 0))⟩ =
      some (roundCfg n a) := by
  set R := ((ones S B0).cons 0).cons 0 with hR
  have h₁ := sweepR sNs_1 n B0 ((ones (a + 1) R).cons 0)
  have h₂ : step brocard34 ⟨31, Tape.mk' (ones n B0) ((ones (a + 1) R).cons 0)⟩ =
      some ⟨32, Tape.mk' (NL n) (ones (a + 1) R)⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons, sNs_0]
    rfl
  have h₃ := sweepR sBs_1 (a + 1) (NL n) R
  have h₄ : nSteps brocard34 2 ⟨32, Tape.mk' (ones (a + 1) (NL n)) R⟩ =
      some ⟨20, Tape.mk' (((ones (a + 1) (NL n)).cons 1).cons 0) (ones S B0)⟩ := by
    rw [hR]
    tm_run
  set W := ((ones (a + 1) (NL n)).cons 1).cons 0 with hW
  have h₅ := sweepR_erase sER2_1 S W B0
  have h₆ : step brocard34 ⟨20, Tape.mk' (zeros S W) B0⟩ = some ⟨21, mkL (zeros S W) B0⟩ := by
    rw [ErdosTernary15.Tape.mk'_B0, sER2_0, B0_cons_zero]
  have h₇ := sweepL_zeros sER3_0 S W B0
  rw [zeros_B0] at h₇
  have h₈ : nSteps brocard34 2 ⟨21, mkL W B0⟩ = some (roundCfg n a) := by
    rw [hW]
    change nSteps brocard34 2 ⟨21, mkL ((((ones a (NL n)).cons 1).cons 1).cons 0) B0⟩ =
      some ⟨1, Tape.mk' (ones a (NL n)) (B0.cons 1)⟩
    tm_run
  exact ⟨_, nSteps_bind_eq h₁ (nSteps_cons h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (nSteps_bind_eq h₅ (nSteps_cons h₆ (nSteps_bind_eq h₇ h₈))))))⟩

/-- With five cells in `N` the count stops at `C6`. -/
theorem gate_five (Y : ListBlank (Fin 2)) :
    nSteps brocard34 6 ⟨23, mkL (ones 5 B0) Y⟩ = some ⟨31, Tape.mk' B0 (ones 5 Y)⟩ := by
  change nSteps brocard34 6 ⟨23, mkL (((((B0.cons 1).cons 1).cons 1).cons 1).cons 1) Y⟩ =
    some ⟨31, Tape.mk' B0 (((((Y.cons 1).cons 1).cons 1).cons 1).cons 1)⟩
  tm_run

/-- With seven cells in `N` the count stops at `C8`. -/
theorem gate_seven (Y : ListBlank (Fin 2)) :
    nSteps brocard34 8 ⟨23, mkL (ones 7 B0) Y⟩ = some ⟨31, Tape.mk' B0 (ones 7 Y)⟩ := by
  change nSteps brocard34 8 ⟨23, mkL (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
      (ListBlank.cons 1 B0))))))) Y⟩ =
    some ⟨31, Tape.mk' B0
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
        (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 
        (ListBlank.cons 1 Y)))))))⟩
  tm_run

/-- A success with `n = 5` or `n = 7` is suppressed: the next round starts. -/
theorem gate_suppressed (n a S : ℕ) (hn : n = 5 ∨ n = 7) :
    ∃ s, nSteps brocard34 s (succCfg n (a + 1) S) = some (roundCfg n a) := by
  obtain ⟨s₁, hs₁⟩ := gate_scan n a S
  obtain ⟨s₃, hs₃⟩ := gate_back n a S
  rcases hn with rfl | rfl
  · exact ⟨_, nSteps_bind_eq hs₁ (nSteps_bind_eq (gate_five _) hs₃)⟩
  · exact ⟨_, nSteps_bind_eq hs₁ (nSteps_bind_eq (gate_seven _) hs₃)⟩

/-- A success with at least eight cells in `N` halts. -/
theorem gate_live (n a S : ℕ) :
    ∃ s cfg, nSteps brocard34 s (succCfg (n + 8) (a + 1) S) = some cfg ∧
      step brocard34 cfg = none := by
  obtain ⟨s₁, hs₁⟩ := gate_scan (n + 8) a S
  obtain ⟨cfg, h₂, hnone⟩ := gate_halt n _
  exact ⟨_, cfg, nSteps_bind_eq hs₁ h₂, hnone⟩

theorem init_eq : (init : Cfg 34 2) = ⟨0, Tape.mk' B0 B0⟩ := rfl

/-- From the blank tape, `TLx`, `C1`–`C5`, `C7` and `A` write `111 0 1111` in write order
(`1111 0 111` on the tape), moving left; `A` steps right into `Ns`. -/
theorem seed_write : nSteps brocard34 8 ⟨0, Tape.mk' B0 B0⟩ =
    some ⟨31, Tape.mk' (B0.cons 1)
      (((((((B0.cons 1).cons 1).cons 1).cons 0).cons 1).cons 1).cons 1)⟩ := by
  tm_run

/-- `Ns`, `Bs`, `ER`, `ER2`, `ER3` bring the head to the last cell of `B` (`Bs` adds a cell,
`ER3` removes it). -/
theorem seed_return : nSteps brocard34 12
    ⟨31, Tape.mk' (B0.cons 1) (((((((B0.cons 1).cons 1).cons 1).cons 0).cons 1).cons 1).cons 1)⟩ =
    some ⟨1, Tape.mk' (((((((B0.cons 1).cons 1).cons 1).cons 1).cons 0).cons 1).cons 1)
      (B0.cons 1)⟩ := by
  tm_run

/-- The start writes `1111 0 111` and enters the first round with `n = 4` and `B = 3`. -/
theorem seed : nSteps brocard34 20 init = some (roundCfg 4 2) := by
  rw [init_eq]
  exact nSteps_bind_eq seed_write seed_return

/-! ## Stages -/

/-- `V n = n! / 8`, the number of cells of `B` between rounds. -/
def V (n : ℕ) : ℕ := n.factorial / 8

theorem eight_dvd_factorial {n : ℕ} (hn : 4 ≤ n) : 8 ∣ n.factorial :=
  Nat.dvd_trans (by decide : 8 ∣ Nat.factorial 4) (Nat.factorial_dvd_factorial hn)

theorem V_succ {n : ℕ} (hn : 4 ≤ n) : V (n + 1) = (n + 1) * V n := by
  rw [V, V, Nat.factorial_succ, Nat.mul_div_assoc _ (eight_dvd_factorial hn)]

theorem V_four : V 4 = 3 := by decide

theorem V_pos {n : ℕ} (hn : 4 ≤ n) : 1 ≤ V n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [V_succ hn]; exact le_trans ih (Nat.le_mul_of_pos_left _ (by omega))

/-- `x` is a triangular number `1 + 2 + ⋯ + j`. -/
def IsTri (x : ℕ) : Prop := ∃ j, x = tri j

theorem le_tri (j : ℕ) : j ≤ tri j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => rw [tri_succ]; omega

theorem isTri_iff (x : ℕ) : IsTri x ↔ ∃ j < x + 1, x = tri j :=
  ⟨fun ⟨j, h⟩ => ⟨j, by have := le_tri j; omega, h⟩, fun ⟨j, _, h⟩ => ⟨j, h⟩⟩

instance : DecidablePred IsTri := fun x => decidable_of_iff _ (isTri_iff x).symm

/-- The configuration at the start of the round that multiplies by `n + 1`. -/
def stage (n : ℕ) : Cfg 34 2 := roundCfg n (V n - 1)

theorem stage_to_test {n : ℕ} (hn : 4 ≤ n) :
    ∃ s, 1 ≤ s ∧ nSteps brocard34 s (stage n) = some (testCfg (n + 1) (V (n + 1) + 1)) := by
  obtain ⟨s, hs1, hs⟩ := multiply n (V n - 1) (by omega)
  have := V_pos hn
  rw [show V n - 1 + 1 = V n by omega, ← V_succ hn] at hs
  exact ⟨s, hs1, hs⟩

/-- A round whose test fails. -/
theorem stage_fail {n : ℕ} (hn : 4 ≤ n) (h : ¬ IsTri (V (n + 1))) :
    ∃ s, 1 ≤ s ∧ nSteps brocard34 s (stage n) = some (stage (n + 1)) := by
  obtain ⟨s₁, hs₁1, hs₁⟩ := stage_to_test hn
  rcases test_run (n + 1) (V (n + 1)) with ⟨j, hj, -⟩ | ⟨-, s₂, hs₂⟩
  · exact absurd ⟨j, hj⟩ h
  · exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- A round whose test succeeds with `n + 1 = 5` or `n + 1 = 7`: suppressed. -/
theorem stage_suppressed {n : ℕ} (hn : 4 ≤ n) (h : IsTri (V (n + 1)))
    (h57 : n + 1 = 5 ∨ n + 1 = 7) :
    ∃ s, 1 ≤ s ∧ nSteps brocard34 s (stage n) = some (stage (n + 1)) := by
  obtain ⟨s₁, hs₁1, hs₁⟩ := stage_to_test hn
  rcases test_run (n + 1) (V (n + 1)) with ⟨j, -, s₂, hs₂⟩ | ⟨h', -⟩
  · have hV := V_pos (show 4 ≤ n + 1 by omega)
    obtain ⟨a, ha⟩ : ∃ a, V (n + 1) = a + 1 := ⟨V (n + 1) - 1, by omega⟩
    rw [ha] at hs₁ hs₂
    obtain ⟨s₃, hs₃⟩ := gate_suppressed (n + 1) a (j + 1) h57
    refine ⟨s₁ + s₂ + s₃, by omega, ?_⟩
    change nSteps brocard34 (s₁ + s₂ + s₃) (stage n) = some (roundCfg (n + 1) (V (n + 1) - 1))
    rw [ha, Nat.add_sub_cancel]
    exact nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃
  · exact absurd h h'

/-- A round whose test succeeds with `n + 1 ≥ 8` halts. -/
theorem stage_halt {n : ℕ} (hn : 7 ≤ n) (h : IsTri (V (n + 1))) :
    ∃ s cfg, nSteps brocard34 s (stage n) = some cfg ∧ step brocard34 cfg = none := by
  obtain ⟨s₁, -, hs₁⟩ := stage_to_test (show 4 ≤ n by omega)
  rcases test_run (n + 1) (V (n + 1)) with ⟨j, -, s₂, hs₂⟩ | ⟨h', -⟩
  · have hV := V_pos (show 4 ≤ n + 1 by omega)
    obtain ⟨a, ha⟩ : ∃ a, V (n + 1) = a + 1 := ⟨V (n + 1) - 1, by omega⟩
    obtain ⟨n', hn'⟩ : ∃ n', n + 1 = n' + 8 := ⟨n - 7, by omega⟩
    rw [ha, hn'] at hs₁ hs₂
    obtain ⟨s₃, cfg, hs₃, hnone⟩ := gate_live n' a (j + 1)
    exact ⟨s₁ + s₂ + s₃, cfg, nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃, hnone⟩
  · exact absurd h h'

theorem isTri_V5 : IsTri (V 5) := ⟨5, by decide⟩

theorem not_isTri_V6 : ¬ IsTri (V 6) :=
  not_tri_between (k := 12) (by decide) (by decide)

theorem isTri_V7 : IsTri (V 7) := ⟨35, by decide⟩

/-- No counterexample with `8 ≤ m ≤ K`. -/
def Clear (K : ℕ) : Prop := ∀ m, 8 ≤ m → m ≤ K → ¬ IsTri (V m)

theorem clear_or_witness (K : ℕ) : Clear K ∨ ∃ m, 8 ≤ m ∧ m ≤ K ∧ IsTri (V m) := by
  induction K with
  | zero => exact Or.inl fun m h8 h0 => absurd (le_trans h8 h0) (by decide)
  | succ K ih =>
    rcases ih with hc | ⟨m, hm8, hmK, hm⟩
    · by_cases hK : 8 ≤ K + 1
      · by_cases ht : IsTri (V (K + 1))
        · exact Or.inr ⟨K + 1, hK, le_rfl, ht⟩
        · refine Or.inl fun m h8 hK1 => ?_
          rcases Nat.lt_or_ge m (K + 1) with h | h
          · exact hc m h8 (by omega)
          · rw [show m = K + 1 by omega]; exact ht
      · exact Or.inl fun m h8 hK1 => absurd (le_trans h8 hK1) hK
    · exact Or.inr ⟨m, hm8, by omega, hm⟩

/-- Without a counterexample up to `n`, the machine reaches the start of round `n` in at least
`n` steps. -/
theorem reach (n : ℕ) (hn : 4 ≤ n) (hc : Clear n) :
    ∃ s, n ≤ s ∧ nSteps brocard34 s init = some (stage n) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨20, by omega, by rw [stage, V_four]; exact seed⟩
  | succ n hn ih =>
    obtain ⟨s₁, hs₁n, hs₁⟩ := ih fun m h8 hm => hc m h8 (by omega)
    have step : ∃ s, 1 ≤ s ∧ nSteps brocard34 s (stage n) = some (stage (n + 1)) := by
      rcases Nat.lt_or_ge (n + 1) 8 with h | h
      · obtain rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 := by omega
        · exact stage_suppressed hn isTri_V5 (Or.inl rfl)
        · exact stage_fail hn not_isTri_V6
        · exact stage_suppressed hn isTri_V7 (Or.inr rfl)
      · exact stage_fail hn (hc (n + 1) h le_rfl)
    obtain ⟨s₂, hs₂1, hs₂⟩ := step
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- The first counterexample halts the machine. -/
theorem halt_of (m : ℕ) (hm : 8 ≤ m) (h : IsTri (V m)) (hc : Clear (m - 1)) :
    ∃ s cfg, nSteps brocard34 s init = some cfg ∧ step brocard34 cfg = none := by
  obtain ⟨s₁, -, hs₁⟩ := reach (m - 1) (by omega) hc
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt (n := m - 1) (by omega)
    (by rw [show m - 1 + 1 = m by omega]; exact h)
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-- The least counterexample has none below it. -/
theorem first_witness (n : ℕ) : 8 ≤ n → IsTri (V n) →
    ∃ m, 8 ≤ m ∧ IsTri (V m) ∧ Clear (m - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h8 hn
  rcases clear_or_witness (n - 1) with hc | ⟨m, hm8, hmn, hm⟩
  · exact ⟨n, h8, hn, hc⟩
  · exact ih m (by omega) hm8 hm

/-! ## Halting Equivalence -/

/-- The 34-state machine `brocard34` (`brocard_34`) halts on the blank tape if and only if
`n! / 8` is a triangular number for some `n ≥ 8`. -/
theorem halts_brocard34_iff_exists_tri :
    ConjectureMachines.Halts brocard34 ↔ ∃ n, 8 ≤ n ∧ IsTri (V n) := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases clear_or_witness (k + 8) with hc | ⟨m, hm8, -, hm⟩
    · obtain ⟨s, hks, hs⟩ := reach (k + 8) (by omega) hc
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
    · exact ⟨m, hm8, hm⟩
  · rintro ⟨n, h8, hn⟩
    obtain ⟨m, hm8, hm, hc⟩ := first_witness n h8 hn
    obtain ⟨s, cfg, hs, hnone⟩ := halt_of m hm8 hm hc
    rw [Part.dom_iff_mem]
    exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches hs, hnone⟩⟩

end ConjectureMachines.Brocard34
