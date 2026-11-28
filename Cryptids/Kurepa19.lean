/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ErdosTernary14

/-!
# Kurepa19

The 19-state Turing machine `kurepa_19` halts on the blank tape if and only if Kurepa's left
factorial conjecture fails: some `n > 2` divides `!n = 0! + 1! + ⋯ + (n - 1)!`, equivalently
some odd prime `p` divides `!p`.

## Provenance and Attribution

The machine and the proofs are by Daniel Veljjanoski, with Claude (Anthropic) as assistant
(November 2026). An earlier machine for the same conjecture is Charlie Reams's 38-state machine
with a Lean proof (`calr3/tinycryptids`, October 2026). It tests `n ∣ !n` for every `n ≥ 3`: the
tape holds `n`, the sum `!n + n + 1`, `n!` and copies of `n!` in unary; a hole walks the sum
while a second hole steps cyclically through the cells of `n`; and filling a marker merges `n!`
into the sum. This machine keeps that scheme (a unary modulus, a running sum, a factorial, the
two holes, the merge by a filled marker) and, like Reams's machine, uses the standard reduction
of the conjecture to a test without primality (`!n ≡ !m (mod m)` for `m ≤ n`).
What is different: it tests `2 S ∣ !S` for every `S ≥ 2`, so that `S = 2` is no exception and
the tape holds half factorials, with `11 0 11 0 1` as the first tape; the hole of the sum
starts on the marker itself, so that the test and the merge are one walk; the multiplication is
the copy loop of `brocard_27`; and the table was shrunk by a computer search (delete a state,
redirect its transitions, change at most two cells) from a 21-state loop to an 18-state loop
that needs one start state.

## Machine Layout

States `0`–`18` of the table are `G0, S1, S2, EC, R1, L0, L1, LNa, LN0, W, W2, EN, TRa, TRb,
BE, TLa, TLb, K, LNf`. At the start of round `S ≥ 2` the tape holds, left to right, a block `N`
of `S` ones, a separator `0`, a block `A` of `!S / 2 + S - 1` ones, a marker `0`, and a block `T`
of `S! / 2` ones; `S1` is in `N` or on the separator. A round has two phases.

* Multiply (`S1`–`LN0`): `S + 1` passes. In each pass `EC` walks a cursor hole through `T`, and
  for every cell `S1`, `S2`, `EC`, `R1`, `L0`, `L1` append a `1` to a block `C` right of `T`. At the
  end of the first pass `L1` writes a new cell left of `N`; after each pass `EC` opens a hole in
  `N` one cell further right, and the passes end when that hole has passed the last cell of `N`.
  Then `C` has `(S + 1) · S! / 2` ones and `N` has `S + 1`.
* Test (`W`–`LNf`): `EN` opens a hole on the second cell of `N`. `TRa`, `TRb` run right to the
  first `0` of `A` and fill it; the first time this is the marker, which merges `T` into `A`.
  `BE` opens the next hole one cell to the left, `TLa`, `TLb` run back and fill the hole of `N`,
  and `EN` opens it one cell further right, or, through `W` and `W2`, on the second cell again
  when it has passed the last cell: the first cell of `N` is never used, so the hole steps
  cyclically through `S` cells. When `A` is used up `BE` reads the separator, and `K` reads the
  last cell of `N`. It is the hole exactly if `S ∣ |A| + 1`, i.e. `2 S ∣ !S`: `K` reading `0`
  is the one undefined cell. Otherwise `LNf` fills the hole and `S1` starts round `S + 1`:
  `A` now has `!S / 2 + S - 1 + 1 + S! / 2 = !(S + 1) / 2 + S` ones and `C` is the new `T`.
* Start: `G0` (state `0`) on the blank tape. `G0`, `EN`, `W`, `W2` write `11 0 11`, and the
  test states write the rest: after `15` steps the tape is `11 0 11 0 1` with `S1` on the
  separator, the start of round `2`. Both cells of `G0`, and `W2` reading `0`, are used for the
  start only.

## Proof Outline

`round_test` follows a round from its start to the last unit of the test (`multiply`, then
`test_loop`, which tracks the hole of `N` modulo `S`); `round_halt` and `round_next` finish the
two cases. `reach` iterates the rounds from the start, with `A` and `T` given by the recursions
`av` and `tv`; `dvd_av_iff` turns the test into `2 S ∣ !S`. The halting equivalence
`halts_kurepa19_iff` (`Halts kurepa19 ↔ ∃ S, 2 ≤ S ∧ 2 * S ∣ leftFact S`) uses only `propext`
and `Quot.sound`. `Cryptids/Semantics/Kurepa19.lean` turns it into the statements about Kurepa's
conjecture.
-/

@[expose] public section

namespace ConjectureMachines.Kurepa19

open Turing (Dir)
open StateTransition
open ErdosTernary15 (B0 B0_cons_zero nSteps nSteps_zero nSteps_succ nSteps_reaches nSteps_add
  nSteps_bind_eq step_one reaches_imp_nSteps nSteps_eq_none_of_step_none)
open ErdosTernary14 (ones ones_succ' ones_add)

local notation "mkL" => ErdosTernary15.Tape.mkL

/-- The 19-state Kurepa machine (`kurepa_19`), loaded from `artifacts/kurepa_19/machine.txt`
in `Machines.lean`. -/
abbrev kurepa19 : Machine 19 2 := Machines.kurepa19

theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

theorem nSteps_cons {M : Machine 19 2} {n : ℕ} {c c₁ c₂ : Cfg 19 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps_succ, h₁, Option.bind_some, h₂]

theorem stepR {q q' : Fin 19} {a b : Fin 2}
    (h : kurepa19.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step kurepa19 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem stepL {q q' : Fin 19} {a b : Fin 2}
    (h : kurepa19.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step kurepa19 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

/-! ## Transition Table

States in file order:
`0` = G0, `1` = S1, `2` = S2, `3` = EC, `4` = R1, `5` = L0, `6` = L1, `7` = LNa, `8` = LN0,
`9` = W, `10` = W2, `11` = EN, `12` = TRa, `13` = TRb, `14` = BE, `15` = TLa, `16` = TLb, `17` = K,
`18` = LNf.
-/

theorem sG0_0 (L R) : step kurepa19 ⟨0, ⟨0, L, R⟩⟩ = some ⟨11, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sG0_1 (L R) : step kurepa19 ⟨0, ⟨1, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sS1_0 (L R) : step kurepa19 ⟨1, ⟨0, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sS1_1 (L R) : step kurepa19 ⟨1, ⟨1, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sS2_0 (L R) : step kurepa19 ⟨2, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sS2_1 (L R) : step kurepa19 ⟨2, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sEC_0 (L R) : step kurepa19 ⟨3, ⟨0, L, R⟩⟩ = some ⟨4, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sEC_1 (L R) : step kurepa19 ⟨3, ⟨1, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sR1_0 (L R) : step kurepa19 ⟨4, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sR1_1 (L R) : step kurepa19 ⟨4, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sL0_0 (L R) : step kurepa19 ⟨5, ⟨0, L, R⟩⟩ = some ⟨6, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sL0_1 (L R) : step kurepa19 ⟨5, ⟨1, L, R⟩⟩ = some ⟨5, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sL1_0 (L R) : step kurepa19 ⟨6, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL1_1 (L R) : step kurepa19 ⟨6, ⟨1, L, R⟩⟩ = some ⟨6, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sLNa_0 (L R) : step kurepa19 ⟨7, ⟨0, L, R⟩⟩ = some ⟨8, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sLNa_1 (L R) : step kurepa19 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sLN0_0 (L R) : step kurepa19 ⟨8, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sLN0_1 (L R) : step kurepa19 ⟨8, ⟨1, L, R⟩⟩ = some ⟨5, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sW_0 (L R) : step kurepa19 ⟨9, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sW_1 (L R) : step kurepa19 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sW2_0 (L R) : step kurepa19 ⟨10, ⟨0, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sW2_1 (L R) : step kurepa19 ⟨10, ⟨1, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sEN_0 (L R) : step kurepa19 ⟨11, ⟨0, L, R⟩⟩ = some ⟨9, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sEN_1 (L R) : step kurepa19 ⟨11, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTRa_0 (L R) : step kurepa19 ⟨12, ⟨0, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sTRa_1 (L R) : step kurepa19 ⟨12, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTRb_0 (L R) : step kurepa19 ⟨13, ⟨0, L, R⟩⟩ = some ⟨14, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTRb_1 (L R) : step kurepa19 ⟨13, ⟨1, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sBE_0 (L R) : step kurepa19 ⟨14, ⟨0, L, R⟩⟩ = some ⟨17, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sBE_1 (L R) : step kurepa19 ⟨14, ⟨1, L, R⟩⟩ = some ⟨15, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sTLa_0 (L R) : step kurepa19 ⟨15, ⟨0, L, R⟩⟩ = some ⟨16, mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem sTLa_1 (L R) : step kurepa19 ⟨15, ⟨1, L, R⟩⟩ = some ⟨15, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sTLb_0 (L R) : step kurepa19 ⟨16, ⟨0, L, R⟩⟩ = some ⟨11, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sTLb_1 (L R) : step kurepa19 ⟨16, ⟨1, L, R⟩⟩ = some ⟨16, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sK_0 (L R : ListBlank (Fin 2)) : step kurepa19 ⟨17, ⟨0, L, R⟩⟩ = none := rfl
theorem sK_1 (L R) : step kurepa19 ⟨17, ⟨1, L, R⟩⟩ = some ⟨18, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sLNf_0 (L R) : step kurepa19 ⟨18, ⟨0, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem sLNf_1 (L R) : step kurepa19 ⟨18, ⟨1, L, R⟩⟩ = some ⟨18, mkL L (R.cons 1)⟩ :=
  stepL rfl L R

/-- Runs the machine through a fixed sequence of steps on a concrete tape. -/
local macro "tm_run" : tactic => `(tactic| simp only [nSteps_succ, nSteps_zero, Option.bind_some,
  sG0_0, sG0_1, sS1_0, sS1_1, sS2_0, sS2_1, sEC_0, sEC_1, sR1_0, sR1_1, sL0_0, sL0_1, sL1_0,
  sL1_1, sLNa_0, sLNa_1, sLN0_0, sLN0_1, sW_0, sW_1, sW2_0, sW2_1, sEN_0, sEN_1, sTRa_0, sTRa_1,
  sTRb_0, sTRb_1, sBE_0, sBE_1, sTLa_0, sTLa_1, sTLb_0, sTLb_1, sK_1, sLNf_0, sLNf_1,
  ErdosTernary15.Tape.mk'_cons, ErdosTernary15.Tape.mkL_cons, ErdosTernary15.Tape.mk'_B0, mkL_B0,
  ListBlank.append, B0_cons_zero])

/-! ## Sweeps over Ones -/

theorem sweepR {q : Fin 19}
    (h : ∀ L R, step kurepa19 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps kurepa19 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) R = (ones k R).cons 1 from rfl,
      ErdosTernary15.Tape.mk'_cons, h, Option.bind_some, ih, ones_succ']

theorem sweepL {q : Fin 19}
    (h : ∀ L R, step kurepa19 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps kurepa19 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) L = (ones k L).cons 1 from rfl,
      ErdosTernary15.Tape.mkL_cons, h, Option.bind_some, ih, ones_succ']

/-! ## Tape Encoding and Configurations -/

theorem ones_zero_B0 : ones 0 B0 = B0 := rfl

/-- The cells right of the separator of `N`: `A` (`a` ones), a `0`, `T` (`t` ones), a `0` and
`C` (`c` ones). In the test: `g` ones of `A`, its hole, `r` ones, a `0` and `C`. -/
def tl (a t c : ℕ) : ListBlank (Fin 2) := ones a ((ones t ((ones c B0).cons 0)).cons 0)

/-- Start of a round: `S1` in `N`, with `p` cells of `N` to its left and `q` from the head on
(`q = 0`: `S1` is on the separator); `A` has `a` ones and `T` has `t`; `C` is empty. -/
def rs (p q a t : ℕ) : Cfg 19 2 :=
  ⟨1, Tape.mk' (ones p B0) (ones q ((ones a ((ones t B0).cons 0)).cons 0))⟩

/-- Inside a pass: `EC` on the cursor cell of `T`; `u` cells of `T` are done and `v` remain, `C`
has `c` cells, and `Λ` is the tape left of `T`. -/
def copyCfg (Λ : ListBlank (Fin 2)) (u v c : ℕ) : Cfg 19 2 :=
  ⟨3, Tape.mk' (ones u Λ) (ones v ((ones c B0).cons 0))⟩

/-- Between passes: `EC` in `N` with `p` cells to its left (all ones) and `q` from the head on
(`q = 0`: `EC` is on the separator). -/
def enN (p q a t c : ℕ) : Cfg 19 2 := ⟨3, Tape.mk' (ones p B0) (ones q ((tl a t c).cons 0))⟩

/-- Inside the test: `EN` in `N` with `p` cells to its left (all ones) and `q` from the head on
(`q = 0`: `EN` is on the separator); the hole of `A` has `g` ones to its left and `r` to its
right. -/
def tEN (p q g r c : ℕ) : Cfg 19 2 := ⟨11, Tape.mk' (ones p B0) (ones q ((tl g r c).cons 0))⟩

/-! ## Multiply (States `1`–`8`) -/

/-- One copy step: the cursor moves one cell right and `C` gains a cell. -/
theorem copy_step (Λ : ListBlank (Fin 2)) (u v c : ℕ) :
    ∃ s, nSteps kurepa19 s (copyCfg Λ u (v + 1) c) = some (copyCfg Λ (u + 1) v (c + 1)) := by
  set Y := (ones u Λ).cons 0 with hY
  have h₁ : step kurepa19 (copyCfg Λ u (v + 1) c) =
      some ⟨1, Tape.mk' Y (ones v ((ones c B0).cons 0))⟩ := by
    change step kurepa19 ⟨3, Tape.mk' (ones u Λ) ((ones v ((ones c B0).cons 0)).cons 1)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sEC_1 _ _
  have h₂ := sweepR sS1_1 v Y ((ones c B0).cons 0)
  have h₃ : step kurepa19 ⟨1, Tape.mk' (ones v Y) ((ones c B0).cons 0)⟩ =
      some ⟨2, Tape.mk' ((ones v Y).cons 0) (ones c B0)⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sS1_0 _ _
  have h₄ := sweepR sS2_1 c ((ones v Y).cons 0) B0
  have h₅ : nSteps kurepa19 3 ⟨2, Tape.mk' (ones c ((ones v Y).cons 0)) B0⟩ =
      some ⟨5, mkL (ones c ((ones v Y).cons 0)) (B0.cons 1)⟩ := by
    tm_run
  have h₆ := sweepL sL0_1 c ((ones v Y).cons 0) (B0.cons 1)
  have h₇ : step kurepa19 ⟨5, mkL ((ones v Y).cons 0) (ones c (B0.cons 1))⟩ =
      some ⟨6, mkL (ones v Y) ((ones (c + 1) B0).cons 0)⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons, ones_succ' c]
    exact sL0_0 _ _
  have h₈ := sweepL sL1_1 v Y ((ones (c + 1) B0).cons 0)
  have h₉ : step kurepa19 ⟨6, mkL Y (ones v ((ones (c + 1) B0).cons 0))⟩ =
      some (copyCfg Λ (u + 1) v (c + 1)) := by
    rw [hY, ErdosTernary15.Tape.mkL_cons]
    exact sL1_0 _ _
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄
    (nSteps_bind_eq h₅ (nSteps_bind_eq h₆ (nSteps_cons h₇ (nSteps_bind_eq h₈
    (step_one h₉))))))))⟩

/-- A whole copy of `T`. -/
theorem copy_loop (Λ : ListBlank (Fin 2)) : ∀ v u c, ∃ s,
    nSteps kurepa19 s (copyCfg Λ u v c) = some (copyCfg Λ (u + v) 0 (c + v)) := by
  intro v
  induction v with
  | zero => intro u c; exact ⟨0, rfl⟩
  | succ v ih =>
    intro u c
    obtain ⟨s₁, hs₁⟩ := copy_step Λ u v c
    obtain ⟨s₂, hs₂⟩ := ih (u + 1) (c + 1)
    refine ⟨s₁ + s₂, ?_⟩
    rw [show u + (v + 1) = u + 1 + v by omega, show c + (v + 1) = c + 1 + v by omega]
    exact nSteps_bind_eq hs₁ hs₂

/-- The cursor has left `T`: `R1`, `LNa`, `LN0` and `L0` walk back over `T` and `A`, and `L1`
enters `N` on its last cell. `Y` is the tape left of the separator of `N`. -/
theorem copy_exit (Y : ListBlank (Fin 2)) (a t c : ℕ) :
    ∃ s, nSteps kurepa19 s (copyCfg ((ones (a + 1) (Y.cons 0)).cons 0) (t + 1) 0 c) =
      some ⟨6, mkL Y ((tl (a + 1) (t + 1) c).cons 0)⟩ := by
  have h₁ : nSteps kurepa19 2 (copyCfg ((ones (a + 1) (Y.cons 0)).cons 0) (t + 1) 0 c) =
      some ⟨7, mkL (ones t ((ones (a + 1) (Y.cons 0)).cons 0))
        (((ones c B0).cons 0).cons 1)⟩ := by
    change nSteps kurepa19 2 ⟨3, Tape.mk' ((ones t ((ones (a + 1) (Y.cons 0)).cons 0)).cons 1)
      ((ones c B0).cons 0)⟩ = _
    tm_run
  have h₂ := sweepL sLNa_1 t ((ones (a + 1) (Y.cons 0)).cons 0) (((ones c B0).cons 0).cons 1)
  have h₃ : nSteps kurepa19 2 ⟨7, mkL ((ones (a + 1) (Y.cons 0)).cons 0)
        (ones t (((ones c B0).cons 0).cons 1))⟩ =
      some ⟨5, mkL (ones a (Y.cons 0))
        (((ones (t + 1) ((ones c B0).cons 0)).cons 0).cons 1)⟩ := by
    rw [ones_succ' t]
    change nSteps kurepa19 2 ⟨7, mkL (((ones a (Y.cons 0)).cons 1).cons 0)
      (ones t (((ones c B0).cons 0).cons 1))⟩ = _
    tm_run
  have h₄ := sweepL sL0_1 a (Y.cons 0) (((ones (t + 1) ((ones c B0).cons 0)).cons 0).cons 1)
  have h₅ : step kurepa19 ⟨5, mkL (Y.cons 0)
        (ones a (((ones (t + 1) ((ones c B0).cons 0)).cons 0).cons 1))⟩ =
      some ⟨6, mkL Y ((tl (a + 1) (t + 1) c).cons 0)⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons, tl, ones_succ' a]
    exact sL0_0 _ _
  exact ⟨_, nSteps_bind_eq h₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (step_one h₅))))⟩

/-- One pass: the hole of `N` moves one cell to the right and `C` gains a copy of `T`. -/
theorem en_step (p q a t c : ℕ) :
    ∃ s, nSteps kurepa19 s (enN p (q + 1) (a + 1) (t + 1) c) =
      some (enN (p + 1) q (a + 1) (t + 1) (c + (t + 1))) := by
  set Y := ones q ((ones p B0).cons 0) with hY
  have h₁ : step kurepa19 (enN p (q + 1) (a + 1) (t + 1) c) =
      some ⟨1, Tape.mk' ((ones p B0).cons 0) (ones q ((tl (a + 1) (t + 1) c).cons 0))⟩ := by
    change step kurepa19 ⟨3, Tape.mk' (ones p B0)
      ((ones q ((tl (a + 1) (t + 1) c).cons 0)).cons 1)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sEC_1 _ _
  have h₂ := sweepR sS1_1 q ((ones p B0).cons 0) ((tl (a + 1) (t + 1) c).cons 0)
  have h₃ : step kurepa19 ⟨1, Tape.mk' Y ((tl (a + 1) (t + 1) c).cons 0)⟩ =
      some ⟨2, Tape.mk' (Y.cons 0)
        (ones (a + 1) ((ones (t + 1) ((ones c B0).cons 0)).cons 0))⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sS1_0 _ _
  have h₄ := sweepR sS2_1 (a + 1) (Y.cons 0) ((ones (t + 1) ((ones c B0).cons 0)).cons 0)
  have h₅ : step kurepa19 ⟨2, Tape.mk' (ones (a + 1) (Y.cons 0))
        ((ones (t + 1) ((ones c B0).cons 0)).cons 0)⟩ =
      some (copyCfg ((ones (a + 1) (Y.cons 0)).cons 0) 0 (t + 1) c) := by
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sS2_0 _ _
  obtain ⟨s₆, h₆⟩ := copy_loop ((ones (a + 1) (Y.cons 0)).cons 0) (t + 1) 0 c
  rw [Nat.zero_add] at h₆
  obtain ⟨s₇, h₇⟩ := copy_exit Y a t (c + (t + 1))
  have h₈ := sweepL sL1_1 q ((ones p B0).cons 0) ((tl (a + 1) (t + 1) (c + (t + 1))).cons 0)
  have h₉ : step kurepa19 ⟨6, mkL ((ones p B0).cons 0)
        (ones q ((tl (a + 1) (t + 1) (c + (t + 1))).cons 0))⟩ =
      some (enN (p + 1) q (a + 1) (t + 1) (c + (t + 1))) := by
    rw [ErdosTernary15.Tape.mkL_cons]
    exact sL1_0 _ _
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄ (nSteps_cons h₅
    (nSteps_bind_eq h₆ (nSteps_bind_eq h₇ (nSteps_bind_eq h₈ (step_one h₉))))))))⟩

/-- The hole of `N` walks through the `q` remaining cells, one copy of `T` each. -/
theorem en_loop (a t : ℕ) : ∀ q p c, ∃ s, nSteps kurepa19 s (enN p q (a + 1) (t + 1) c) =
    some (enN (p + q) 0 (a + 1) (t + 1) (c + q * (t + 1))) := by
  intro q
  induction q with
  | zero => intro p c; exact ⟨0, by simp [nSteps_zero]⟩
  | succ q ih =>
    intro p c
    obtain ⟨s₁, hs₁⟩ := en_step p q a t c
    obtain ⟨s₂, hs₂⟩ := ih (p + 1) (c + (t + 1))
    refine ⟨s₁ + s₂, ?_⟩
    rw [show p + (q + 1) = p + 1 + q by omega,
      show c + (q + 1) * (t + 1) = c + (t + 1) + q * (t + 1) by ring]
    exact nSteps_bind_eq hs₁ hs₂

/-- The first pass of a round: `N` is solid, and at the end of the pass `L1` writes a new cell
left of `N`. -/
theorem first_pass (p q a t : ℕ) :
    ∃ s, nSteps kurepa19 s (rs p q (a + 1) (t + 1)) =
      some (enN 1 (p + q) (a + 1) (t + 1) (t + 1)) := by
  set Y := ones q (ones p B0) with hY
  have h₂ := sweepR sS1_1 q (ones p B0) ((ones (a + 1) ((ones (t + 1) B0).cons 0)).cons 0)
  have h₃ : step kurepa19 ⟨1, Tape.mk' Y ((ones (a + 1) ((ones (t + 1) B0).cons 0)).cons 0)⟩ =
      some ⟨2, Tape.mk' (Y.cons 0) (ones (a + 1) ((ones (t + 1) B0).cons 0))⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sS1_0 _ _
  have h₄ := sweepR sS2_1 (a + 1) (Y.cons 0) ((ones (t + 1) B0).cons 0)
  have h₅ : step kurepa19 ⟨2, Tape.mk' (ones (a + 1) (Y.cons 0)) ((ones (t + 1) B0).cons 0)⟩ =
      some (copyCfg ((ones (a + 1) (Y.cons 0)).cons 0) 0 (t + 1) 0) := by
    rw [copyCfg, ones_zero_B0, B0_cons_zero, ErdosTernary15.Tape.mk'_cons]
    exact sS2_0 _ _
  obtain ⟨s₆, h₆⟩ := copy_loop ((ones (a + 1) (Y.cons 0)).cons 0) (t + 1) 0 0
  rw [Nat.zero_add] at h₆
  obtain ⟨s₇, h₇⟩ := copy_exit Y a t (t + 1)
  have h₈ : nSteps kurepa19 (p + q) ⟨6, mkL Y ((tl (a + 1) (t + 1) (t + 1)).cons 0)⟩ =
      some ⟨6, mkL B0 (ones (p + q) ((tl (a + 1) (t + 1) (t + 1)).cons 0))⟩ := by
    rw [hY, ← ones_add, Nat.add_comm q p]
    exact sweepL sL1_1 (p + q) B0 _
  have h₉ : step kurepa19 ⟨6, mkL B0 (ones (p + q) ((tl (a + 1) (t + 1) (t + 1)).cons 0))⟩ =
      some (enN 1 (p + q) (a + 1) (t + 1) (t + 1)) := by
    rw [mkL_B0]
    exact sL1_0 _ _
  exact ⟨_, nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄ (nSteps_cons h₅
    (nSteps_bind_eq h₆ (nSteps_bind_eq h₇ (nSteps_bind_eq h₈ (step_one h₉)))))))⟩

/-- All passes are done: `R1` and `LNa` walk to the blank left of `N`, `LN0`, `W` and `W2` turn
and skip the first cell of `N`, and `EN` is on its second cell: the test starts. -/
theorem en_exit (p a t c : ℕ) :
    ∃ s, nSteps kurepa19 s (enN (p + 2) 0 a t c) = some (tEN 1 (p + 1) a t c) := by
  have h₁ : nSteps kurepa19 2 (enN (p + 2) 0 a t c) =
      some ⟨7, mkL (ones (p + 1) B0) (((tl a t c).cons 0).cons 1)⟩ := by
    change nSteps kurepa19 2 ⟨3, Tape.mk' ((ones (p + 1) B0).cons 1) ((tl a t c).cons 0)⟩ = _
    tm_run
  have h₂ := sweepL sLNa_1 (p + 1) B0 (((tl a t c).cons 0).cons 1)
  have h₃ : nSteps kurepa19 4 ⟨7, mkL B0 (ones (p + 1) (((tl a t c).cons 0).cons 1))⟩ =
      some (tEN 1 (p + 1) a t c) := by
    rw [← ones_succ' (p + 1)]
    change nSteps kurepa19 4 ⟨7, mkL B0 ((ones (p + 1) ((tl a t c).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (B0.cons 1) (ones (p + 1) ((tl a t c).cons 0))⟩
    tm_run
  exact ⟨_, nSteps_bind_eq h₁ (nSteps_bind_eq h₂ h₃)⟩

/-- The multiply phase: from the start of a round to the start of the test. `N` has grown by
one cell, `A` and `T` are unchanged, and `C` has `(S + 1) t` cells (`S = p + q`). -/
theorem multiply (p q a t : ℕ) (hS : 1 ≤ p + q) :
    ∃ s, nSteps kurepa19 s (rs p q (a + 1) (t + 1)) =
      some (tEN 1 (p + q) (a + 1) (t + 1) ((p + q + 1) * (t + 1))) := by
  obtain ⟨s₁, h₁⟩ := first_pass p q a t
  obtain ⟨s₂, h₂⟩ := en_loop a t (p + q) 1 (t + 1)
  obtain ⟨n, hn⟩ : ∃ n, p + q = n + 1 := ⟨p + q - 1, by omega⟩
  obtain ⟨s₃, h₃⟩ := en_exit n (a + 1) (t + 1) (t + 1 + (p + q) * (t + 1))
  rw [show 1 + (p + q) = n + 2 by omega] at h₂
  rw [← hn] at h₃
  rw [show (p + q + 1) * (t + 1) = t + 1 + (p + q) * (t + 1) by ring]
  exact ⟨_, nSteps_bind_eq (nSteps_bind_eq h₁ h₂) h₃⟩

/-! ## Test (States `9`–`18`) -/

/-- One unit of the test: the hole of `N` moves one cell right and the hole of `A` one cell
left. -/
theorem test_step (p q g r c : ℕ) :
    ∃ s, nSteps kurepa19 s (tEN p (q + 1) (g + 1) r c) = some (tEN (p + 1) q g (r + 1) c) := by
  set H := (ones p B0).cons 0 with hH
  set E := (ones c B0).cons 0 with hE
  have h₁ : step kurepa19 (tEN p (q + 1) (g + 1) r c) =
      some ⟨12, Tape.mk' H (ones q ((tl (g + 1) r c).cons 0))⟩ := by
    change step kurepa19 ⟨11, Tape.mk' (ones p B0)
      ((ones q ((tl (g + 1) r c).cons 0)).cons 1)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sEN_1 _ _
  have h₂ := sweepR sTRa_1 q H ((tl (g + 1) r c).cons 0)
  have h₃ : step kurepa19 ⟨12, Tape.mk' (ones q H) ((tl (g + 1) r c).cons 0)⟩ =
      some ⟨13, Tape.mk' ((ones q H).cons 0) (ones (g + 1) ((ones r E).cons 0))⟩ := by
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sTRa_0 _ _
  have h₄ := sweepR sTRb_1 (g + 1) ((ones q H).cons 0) ((ones r E).cons 0)
  have h₅ : nSteps kurepa19 2
        ⟨13, Tape.mk' (ones (g + 1) ((ones q H).cons 0)) ((ones r E).cons 0)⟩ =
      some ⟨15, mkL (ones g ((ones q H).cons 0)) ((ones (r + 1) E).cons 0)⟩ := by
    change nSteps kurepa19 2
        ⟨13, Tape.mk' ((ones g ((ones q H).cons 0)).cons 1) ((ones r E).cons 0)⟩ =
      some ⟨15, mkL (ones g ((ones q H).cons 0)) (((ones r E).cons 1).cons 0)⟩
    tm_run
  have h₆ := sweepL sTLa_1 g ((ones q H).cons 0) ((ones (r + 1) E).cons 0)
  have h₇ : step kurepa19 ⟨15, mkL ((ones q H).cons 0) (ones g ((ones (r + 1) E).cons 0))⟩ =
      some ⟨16, mkL (ones q H) ((tl g (r + 1) c).cons 0)⟩ := by
    rw [ErdosTernary15.Tape.mkL_cons]
    exact sTLa_0 _ _
  have h₈ := sweepL sTLb_1 q H ((tl g (r + 1) c).cons 0)
  have h₉ : step kurepa19 ⟨16, mkL H (ones q ((tl g (r + 1) c).cons 0))⟩ =
      some (tEN (p + 1) q g (r + 1) c) := by
    rw [hH, ErdosTernary15.Tape.mkL_cons]
    exact sTLb_0 _ _
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄
    (nSteps_bind_eq h₅ (nSteps_bind_eq h₆ (nSteps_cons h₇ (nSteps_bind_eq h₈
    (step_one h₉))))))))⟩

/-- The hole of `N` has passed its last cell: `W` walks back to the blank, `W2` skips the first
cell of `N`, and the hole restarts on the second cell. -/
theorem test_wrap (p g r c : ℕ) :
    ∃ s, nSteps kurepa19 s (tEN (p + 1) 0 g r c) = some (tEN 1 p g r c) := by
  have h₁ : step kurepa19 (tEN (p + 1) 0 g r c) =
      some ⟨9, mkL (ones (p + 1) B0) ((tl g r c).cons 0)⟩ := by
    change step kurepa19 ⟨11, Tape.mk' (ones (p + 1) B0) ((tl g r c).cons 0)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sEN_0 _ _
  have h₂ := sweepL sW_1 (p + 1) B0 ((tl g r c).cons 0)
  have h₃ : nSteps kurepa19 2 ⟨9, mkL B0 (ones (p + 1) ((tl g r c).cons 0))⟩ =
      some (tEN 1 p g r c) := by
    change nSteps kurepa19 2 ⟨9, mkL B0 ((ones p ((tl g r c).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (B0.cons 1) (ones p ((tl g r c).cons 0))⟩
    tm_run
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ h₃)⟩

/-- `g` units of the test. `N` has `n + 1` cells; the cell on which `EN` opens the next hole
(index `p`, counted from `0` at the left end) moves cyclically through `1, …, n`, one step per
unit: `p' ≡ p + g (mod n)`. -/
theorem test_loop (n c : ℕ) : ∀ g p q r, 1 ≤ p → 1 ≤ q → p + q = n + 1 →
    ∃ s p' q' k, 1 ≤ p' ∧ 1 ≤ q' ∧ p' + q' = n + 1 ∧ p' + k * n = p + g ∧
      nSteps kurepa19 s (tEN p q g r c) = some (tEN p' q' 0 (r + g) c) := by
  intro g
  induction g with
  | zero =>
    intro p q r hp hq hpq
    exact ⟨0, p, q, 0, hp, hq, hpq, by simp, rfl⟩
  | succ g ih =>
    intro p q r hp hq hpq
    obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + 1 := ⟨q - 1, by omega⟩
    obtain ⟨s₁, hs₁⟩ := test_step p q₀ g r c
    rcases Nat.eq_zero_or_pos q₀ with rfl | hq₀
    · obtain ⟨s₂, hs₂⟩ := test_wrap p g (r + 1) c
      obtain ⟨s₃, p', q', k, hp', hq', hpq', hk, hs₃⟩ := ih 1 p (r + 1) le_rfl hp (by omega)
      refine ⟨s₁ + s₂ + s₃, p', q', k + 1, hp', hq', hpq', ?_, ?_⟩
      · rw [Nat.add_one_mul]
        omega
      · rw [show r + (g + 1) = r + 1 + g by omega]
        exact nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃
    · obtain ⟨s₃, p', q', k, hp', hq', hpq', hk, hs₃⟩ :=
        ih (p + 1) q₀ (r + 1) (by omega) hq₀ (by omega)
      refine ⟨s₁ + s₃, p', q', k, hp', hq', hpq', by omega, ?_⟩
      rw [show r + (g + 1) = r + 1 + g by omega]
      exact nSteps_bind_eq hs₁ hs₃

/-- The hole of `A` has reached the separator and the hole of `N` is its last cell: `K` reads
`0`, the undefined cell. -/
theorem test_halt (p r c : ℕ) :
    ∃ s cfg, nSteps kurepa19 s (tEN p 1 0 r c) = some cfg ∧ step kurepa19 cfg = none := by
  refine ⟨4, ⟨17, ⟨0, ones p B0, ((ones r ((ones c B0).cons 0)).cons 1).cons 0⟩⟩, ?_,
    sK_0 _ _⟩
  change nSteps kurepa19 4 ⟨11, Tape.mk' (ones p B0)
    ((((ones r ((ones c B0).cons 0)).cons 0).cons 0).cons 1)⟩ = _
  tm_run

/-- The hole of `A` has reached the separator and the hole of `N` is not its last cell: `K`
reads `1`, `LNf` fills the hole of `N`, and `S1` starts the next round on the cell to its
left. -/
theorem test_next (p q r c : ℕ) :
    ∃ s, 1 ≤ s ∧ nSteps kurepa19 s (tEN (p + 1) (q + 2) 0 r c) =
      some (rs p (q + 3) (r + 1) c) := by
  set H := (ones (p + 1) B0).cons 0 with hH
  have h₁ : step kurepa19 (tEN (p + 1) (q + 2) 0 r c) =
      some ⟨12, Tape.mk' H (ones (q + 1) (((ones r ((ones c B0).cons 0)).cons 0).cons 0))⟩ := by
    change step kurepa19 ⟨11, Tape.mk' (ones (p + 1) B0)
      ((ones (q + 1) (((ones r ((ones c B0).cons 0)).cons 0).cons 0)).cons 1)⟩ = _
    rw [ErdosTernary15.Tape.mk'_cons]
    exact sEN_1 _ _
  have h₂ := sweepR sTRa_1 (q + 1) H (((ones r ((ones c B0).cons 0)).cons 0).cons 0)
  have h₃ : nSteps kurepa19 4
        ⟨12, Tape.mk' (ones (q + 1) H) (((ones r ((ones c B0).cons 0)).cons 0).cons 0)⟩ =
      some ⟨18, mkL (ones q H) ((((ones r ((ones c B0).cons 0)).cons 1).cons 0).cons 1)⟩ := by
    change nSteps kurepa19 4
      ⟨12, Tape.mk' ((ones q H).cons 1) (((ones r ((ones c B0).cons 0)).cons 0).cons 0)⟩ = _
    tm_run
  have h₄ := sweepL sLNf_1 q H ((((ones r ((ones c B0).cons 0)).cons 1).cons 0).cons 1)
  have e : rs p (q + 3) (r + 1) c = ⟨1, mkL (ones (p + 1) B0)
      ((ones q ((((ones r ((ones c B0).cons 0)).cons 1).cons 0).cons 1)).cons 1)⟩ := by
    change (⟨1, Tape.mk' (ones p B0)
      (ones (q + 2 + 1) (((ones r ((ones c B0).cons 0)).cons 1).cons 0))⟩ : Cfg 19 2) =
      ⟨1, mkL ((ones p B0).cons 1)
        ((ones q ((((ones r ((ones c B0).cons 0)).cons 1).cons 0).cons 1)).cons 1)⟩
    rw [ones_succ' (q + 2)]
    change (⟨1, Tape.mk' (ones p B0)
      (((ones q ((((ones r ((ones c B0).cons 0)).cons 1).cons 0).cons 1)).cons 1).cons 1)⟩ :
        Cfg 19 2) = _
    rw [ErdosTernary15.Tape.mk'_cons, ErdosTernary15.Tape.mkL_cons]
  have h₅ : step kurepa19
        ⟨18, mkL H (ones q ((((ones r ((ones c B0).cons 0)).cons 1).cons 0).cons 1))⟩ =
      some (rs p (q + 3) (r + 1) c) := by
    rw [e, hH, ErdosTernary15.Tape.mkL_cons]
    exact sLNf_0 _ _
  have h := nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (nSteps_bind_eq h₄
    (step_one h₅))))
  refine ⟨_, ?_, h⟩
  omega

/-! ## Rounds -/

/-- The test, from its start to its last unit: `EN` is about to open the hole of `N` on the
cell of index `p'`, with `p' ≡ a + 2 (mod S)` and `1 ≤ p' ≤ S` (`S = p + q`); `A` has no
ones left of its hole. -/
theorem round_test (p q a t : ℕ) (hS : 1 ≤ p + q) :
    ∃ s p' q' k, 1 ≤ p' ∧ 1 ≤ q' ∧ p' + q' = p + q + 1 ∧ p' + k * (p + q) = a + 2 ∧
      nSteps kurepa19 s (rs p q (a + 1) (t + 1)) =
        some (tEN p' q' 0 (t + 1 + (a + 1)) ((p + q + 1) * (t + 1))) := by
  obtain ⟨s₁, h₁⟩ := multiply p q a t hS
  obtain ⟨s₂, p', q', k, hp', hq', hpq', hk, h₂⟩ :=
    test_loop (p + q) ((p + q + 1) * (t + 1)) (a + 1) 1 (p + q) (t + 1) le_rfl hS (by omega)
  exact ⟨s₁ + s₂, p', q', k, hp', hq', hpq', by omega, nSteps_bind_eq h₁ h₂⟩

/-- A round halts if `S` divides the number of cells of `A` plus one. -/
theorem round_halt (p q a t : ℕ) (hS : 1 ≤ p + q) (hd : p + q ∣ a + 2) :
    ∃ s cfg, nSteps kurepa19 s (rs p q (a + 1) (t + 1)) = some cfg ∧
      step kurepa19 cfg = none := by
  obtain ⟨s₁, p', q', k, hp', hq', hpq', hk, h₁⟩ := round_test p q a t hS
  have hdvd : p + q ∣ p' := by
    have h := Nat.dvd_sub hd (Nat.dvd_mul_left (p + q) k)
    rwa [show a + 2 - k * (p + q) = p' by omega] at h
  have hle := Nat.le_of_dvd (by omega) hdvd
  obtain rfl : q' = 1 := by omega
  obtain ⟨s₂, cfg, h₂, hnone⟩ := test_halt p' (t + 1 + (a + 1)) ((p + q + 1) * (t + 1))
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq h₁ h₂, hnone⟩

/-- Otherwise the next round starts: `N` has one more cell, `A` has gained one cell and the
cells of `T`, and the new `T` is the old one times `S + 1`. -/
theorem round_next (p q a t : ℕ) (hS : 1 ≤ p + q) (hd : ¬ p + q ∣ a + 2) :
    ∃ s p' q', 1 ≤ s ∧ p' + q' = p + q + 1 ∧
      nSteps kurepa19 s (rs p q (a + 1) (t + 1)) =
        some (rs p' q' (a + 1 + 1 + (t + 1)) ((p + q + 1) * (t + 1))) := by
  obtain ⟨s₁, p', q', k, hp', hq', hpq', hk, h₁⟩ := round_test p q a t hS
  have hne : p' ≠ p + q := by
    intro h
    apply hd
    rw [← hk, h]
    exact Nat.dvd_add (Nat.dvd_refl _) (Nat.dvd_mul_left _ _)
  obtain ⟨p₀, rfl⟩ : ∃ p₀, p' = p₀ + 1 := ⟨p' - 1, by omega⟩
  obtain ⟨q₀, rfl⟩ : ∃ q₀, q' = q₀ + 2 := ⟨q' - 2, by omega⟩
  obtain ⟨s₂, hs₂, h₂⟩ := test_next p₀ q₀ (t + 1 + (a + 1)) ((p + q + 1) * (t + 1))
  refine ⟨s₁ + s₂, p₀, q₀ + 3, by omega, by omega, ?_⟩
  rw [show a + 1 + 1 + (t + 1) = t + 1 + (a + 1) + 1 by omega]
  exact nSteps_bind_eq h₁ h₂

/-! ## Start (State `0`) -/

theorem init_eq : (init : Cfg 19 2) = ⟨0, Tape.mk' B0 B0⟩ := rfl

/-- Start, steps `1`–`8`: `G0`, `EN`, `W`, `W2` write `11 0 11`. -/
theorem start₁ : nSteps kurepa19 8 ⟨0, Tape.mk' B0 B0⟩ =
    some ⟨11, Tape.mk' (((B0.cons 1).cons 1).cons 0) ((B0.cons 1).cons 1)⟩ := by
  tm_run

/-- Start, steps `9`–`15`: `EN`, `TRa`, `TRb`, `BE` and `K` turn the tape into `11 0 0 1 0 1`,
and `LNf` fills the gap. `S1` is on the separator of `11 0 11 0 1`. -/
theorem start₂ : nSteps kurepa19 7
    ⟨11, Tape.mk' (((B0.cons 1).cons 1).cons 0) ((B0.cons 1).cons 1)⟩ = some (rs 2 0 2 1) := by
  change _ = some (⟨1, Tape.mk' ((B0.cons 1).cons 1)
    (((((B0.cons 1).cons 0).cons 1).cons 1).cons 0)⟩ : Cfg 19 2)
  tm_run

/-- From the blank tape the machine reaches the start of round `2` in `15` steps: the tape is
`11 0 11 0 1`. -/
theorem start : nSteps kurepa19 15 init = some (rs 2 0 2 1) := by
  rw [init_eq]
  exact nSteps_bind_eq start₁ start₂

/-! ## Stages -/

/-- The left factorial `!n = 0! + 1! + ⋯ + (n - 1)!`. -/
def leftFact : ℕ → ℕ
  | 0 => 0
  | n + 1 => leftFact n + n.factorial

/-- The cells of `T` at the start of round `S = k + 2`: `S! / 2`. -/
def tv : ℕ → ℕ
  | 0 => 1
  | k + 1 => (k + 3) * tv k

/-- The cells of `A` at the start of round `S = k + 2`: `!S / 2 + S - 1`. -/
def av : ℕ → ℕ
  | 0 => 2
  | k + 1 => av k + 1 + tv k

theorem two_mul_tv (k : ℕ) : 2 * tv k = (k + 2).factorial := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tv, Nat.factorial_succ (k + 2), ← ih]
    ring

theorem two_mul_av (k : ℕ) : 2 * av k + 2 = leftFact (k + 2) + 2 * (k + 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := two_mul_tv k
    rw [av, show k + 1 + 2 = k + 2 + 1 by omega, leftFact]
    omega

theorem tv_pos (k : ℕ) : 1 ≤ tv k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [tv]; exact le_trans ih (Nat.le_mul_of_pos_left _ (by omega))

theorem av_pos (k : ℕ) : 1 ≤ av k := by
  cases k with
  | zero => decide
  | succ k => rw [av]; omega

/-- The test of round `S = k + 2` is the test `2 S ∣ !S`. -/
theorem dvd_av_iff (k : ℕ) : k + 2 ∣ av k + 1 ↔ 2 * (k + 2) ∣ leftFact (k + 2) := by
  rw [← Nat.mul_dvd_mul_iff_left (show 0 < 2 by omega),
    show 2 * (av k + 1) = leftFact (k + 2) + 2 * (k + 2) by have := two_mul_av k; omega]
  exact Nat.dvd_add_self_right

/-- A round that does not halt. -/
theorem stage_next (k p q : ℕ) (hpq : p + q = k + 2)
    (h : ¬ 2 * (k + 2) ∣ leftFact (k + 2)) :
    ∃ s p' q', 1 ≤ s ∧ p' + q' = k + 3 ∧
      nSteps kurepa19 s (rs p q (av k) (tv k)) = some (rs p' q' (av (k + 1)) (tv (k + 1))) := by
  obtain ⟨a, ha⟩ : ∃ a, av k = a + 1 := ⟨av k - 1, by have := av_pos k; omega⟩
  obtain ⟨t, ht⟩ : ∃ t, tv k = t + 1 := ⟨tv k - 1, by have := tv_pos k; omega⟩
  have hd : ¬ p + q ∣ a + 2 := by
    rw [hpq, show a + 2 = av k + 1 by omega, dvd_av_iff]
    exact h
  obtain ⟨s, p', q', hs, hpq', hrun⟩ := round_next p q a t (by omega) hd
  refine ⟨s, p', q', hs, by omega, ?_⟩
  rw [av, tv, ha, ht, show k + 3 = p + q + 1 by omega]
  exact hrun

/-- A round that halts. -/
theorem stage_halt (k p q : ℕ) (hpq : p + q = k + 2)
    (h : 2 * (k + 2) ∣ leftFact (k + 2)) :
    ∃ s cfg, nSteps kurepa19 s (rs p q (av k) (tv k)) = some cfg ∧ step kurepa19 cfg = none := by
  obtain ⟨a, ha⟩ : ∃ a, av k = a + 1 := ⟨av k - 1, by have := av_pos k; omega⟩
  obtain ⟨t, ht⟩ : ∃ t, tv k = t + 1 := ⟨tv k - 1, by have := tv_pos k; omega⟩
  have hd : p + q ∣ a + 2 := by
    rw [hpq, show a + 2 = av k + 1 by omega, dvd_av_iff]
    exact h
  rw [ha, ht]
  exact round_halt p q a t (by omega) hd

/-- No `S` with `2 ≤ S ≤ K` and `2 S ∣ !S`. -/
def Clear (K : ℕ) : Prop := ∀ S, 2 ≤ S → S ≤ K → ¬ 2 * S ∣ leftFact S

theorem clear_or_witness (K : ℕ) : Clear K ∨ ∃ S, 2 ≤ S ∧ S ≤ K ∧ 2 * S ∣ leftFact S := by
  induction K with
  | zero => exact Or.inl fun S h2 h0 => absurd (le_trans h2 h0) (by decide)
  | succ K ih =>
    rcases ih with hc | ⟨S, hS2, hSK, hS⟩
    · by_cases hK : 2 ≤ K + 1
      · by_cases hd : 2 * (K + 1) ∣ leftFact (K + 1)
        · exact Or.inr ⟨K + 1, hK, le_rfl, hd⟩
        · refine Or.inl fun S h2 hK1 => ?_
          rcases Nat.lt_or_ge S (K + 1) with h | h
          · exact hc S h2 (by omega)
          · rw [show S = K + 1 by omega]; exact hd
      · exact Or.inl fun S h2 hK1 => absurd (le_trans h2 hK1) hK
    · exact Or.inr ⟨S, hS2, by omega, hS⟩

/-- Without a witness up to `k + 1`, the machine reaches the start of round `k + 2` in at least
`k` steps. -/
theorem reach (k : ℕ) (hc : Clear (k + 1)) :
    ∃ s p q, k ≤ s ∧ p + q = k + 2 ∧ nSteps kurepa19 s init = some (rs p q (av k) (tv k)) := by
  induction k with
  | zero => exact ⟨15, 2, 0, by omega, rfl, start⟩
  | succ k ih =>
    obtain ⟨s₁, p, q, hs₁, hpq, h₁⟩ := ih fun S h2 hS => hc S h2 (by omega)
    obtain ⟨s₂, p', q', hs₂, hpq', h₂⟩ :=
      stage_next k p q hpq (hc (k + 2) (by omega) le_rfl)
    exact ⟨s₁ + s₂, p', q', by omega, hpq', nSteps_bind_eq h₁ h₂⟩

/-- The first witness halts the machine. -/
theorem halt_of (S : ℕ) (hS : 2 ≤ S) (h : 2 * S ∣ leftFact S) (hc : Clear (S - 1)) :
    ∃ s cfg, nSteps kurepa19 s init = some cfg ∧ step kurepa19 cfg = none := by
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 2 := ⟨S - 2, by omega⟩
  obtain ⟨s₁, p, q, -, hpq, h₁⟩ := reach k hc
  obtain ⟨s₂, cfg, h₂, hnone⟩ := stage_halt k p q hpq h
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq h₁ h₂, hnone⟩

/-- The least witness has none below it. -/
theorem first_witness (n : ℕ) : 2 ≤ n → 2 * n ∣ leftFact n →
    ∃ S, 2 ≤ S ∧ 2 * S ∣ leftFact S ∧ Clear (S - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h2 hn
  rcases clear_or_witness (n - 1) with hc | ⟨S, hS2, hSn, hS⟩
  · exact ⟨n, h2, hn, hc⟩
  · exact ih S (by omega) hS2 hS

/-! ## Halting Equivalence -/

/-- The 19-state machine `kurepa_19` halts on the blank tape if and only if `2 S` divides the
left factorial `!S` for some `S ≥ 2`. -/
theorem halts_kurepa19_iff :
    ConjectureMachines.Halts kurepa19 ↔ ∃ S, 2 ≤ S ∧ 2 * S ∣ leftFact S := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases clear_or_witness (k + 2) with hc | ⟨S, hS2, -, hS⟩
    · obtain ⟨s, p, q, hks, -, hs⟩ := reach (k + 1) hc
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
    · exact ⟨S, hS2, hS⟩
  · rintro ⟨n, h2, hn⟩
    obtain ⟨S, hS2, hS, hc⟩ := first_witness n h2 hn
    obtain ⟨s, cfg, hs, hnone⟩ := halt_of S hS2 hS hc
    rw [Part.dom_iff_mem]
    exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches hs, hnone⟩⟩

end ConjectureMachines.Kurepa19
