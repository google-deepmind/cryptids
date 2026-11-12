/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Goldbach21

/-!
# Oppermann22

The 22-state Turing machine `oppermann_22` halts on the blank tape if and only if Oppermann's
conjecture fails: some `n ≥ 2` has no prime strictly between `n ^ 2 - n` and `n ^ 2`, or none
strictly between `n ^ 2` and `n ^ 2 + n`.

## Provenance and Attribution

The machine and the proofs are by Daniel Veljjanoski, with Claude (Anthropic) as assistant
(November 2026). The design follows `legendre_21`, a 21-state machine for Legendre's conjecture
by the same author (proposed separately): the same test and walker, with one new state (`C2`),
both cells of `C`, `(q7, 0)` and `(X, 1)` changed, and the start in `q12`. The primality test
is the one of
the Goldbach machines: the anonymous 2016 machine, Andrew Yao and Yijun Leng's `goldbach_25`
(2024), and `goldbach_21` of Maxence Faldor and Moritz Firsching (2026), whose lemmas in
`Cryptids/Goldbach21.lean` this file uses. Earlier machines for the same conjecture, both with
Lean proofs and both walking the blocks between consecutive quarter-squares as this one does:
the 28-state machine of Joseph Jabbour and Ralph Razzouk (`ralphrazzouk/busybeaver`, September
2026) and Charlie Reams's 45-state machine (`calr3/tinycryptids`, November 2026). Reams's
machine also tracks the block with a register of cells whose hole moves two cells per tested
number, and with a flag set by a prime.

## Machine Layout

States `0`–`21` of the table are `q12, q16, q0, q3, q4, q6, q7, q9, q11, q13, q14,
q15, q20, q22, q23, q24, A1, B, C, C2, Z1, X`; `q0`–`q24` are the numbers of the same states in
`Goldbach21.edited`. The tape holds, left to right, a block of ones for the number under test,
a separator `0`, a flag cell, and a walker area of ones with one hole. The tape left of the
block stays blank; the block grows to the left.

* Test (the sixteen `q` states): `q16` reading the blank left of a block of `t` ones writes a
  `1` (the block now has `t + 1` cells) and enters the trial division of `t`. A prime leaves
  `q6` on the separator; a composite leaves `q6` on the flag cell, through `A1`. The block is
  restored in both cases.
* Walker (`B`, `C`, `C2`, `Z1`): after each test `B` runs right to the hole and fills it, `C`
  steps one cell left, `C2` opens a hole on the next cell left, `Z1` runs back, and `q3`, `q4`,
  `q16` return to the left end of the block, where the next number is tested. So the hole moves
  two cells per tested number. The first prime of a block sets the flag.
* Block `j` is `⌊j² / 4⌋, …, ⌊(j + 1)² / 4⌋ - 1`: block `2 n` is `n ^ 2, …, n ^ 2 + n - 1` and
  block `2 n + 1` is `n ^ 2 + n, …, (n + 1) ^ 2 - 1`. Its first number is not prime (from block
  `4` on), so it has a prime exactly if the open half-interval of the conjecture has one. It
  starts with the flag clear and `j - 1` ones in the walker area (the blank beyond them is the
  hole). At its last number the hole would land on the flag cell (`j` even) or pass it (`j`
  odd). With the flag set, the flag is cleared and the walker area has `j` ones: block `j + 1`.
  With the flag clear and `j` odd, `C` reads the flag, `X` reads the separator, and the machine
  halts: `X` reading `0` is the one undefined cell. With the flag clear and `j` even, the hole
  moves one cell only, and the machine halts one number later, at the first number of the next
  block, which is not prime.
* Start: `q12` (state `0`) on the blank tape. After `9` steps the machine is at the test of `0`
  with the walker area `0 1 1`, one cell out of step with the blocks. The tests of `0, …, 11`
  bring it into step: it is at the start of block `7` (the number `12`) with `6` ones in the
  walker area. No state is used for the start only.

## Proof Outline

`opp25` is the machine in the 25-state numbering of `Goldbach21.edited` (`A1, B, C, Z1, X, C2`
take the numbers `1, 2, 5, 8, 10, 17`, which are free in our table), so the step and scan
lemmas and the machine-generic pass lemmas of `Cryptids/Goldbach21.lean` apply unchanged; the
lemmas stated there for `edited` only are proved again for `opp25`.
-/

@[expose] public section

namespace ConjectureMachines.Oppermann22

open Turing (Dir)
open StateTransition
open Goldbach21

/-- 22-state Oppermann machine (`oppermann_22`). -/
abbrev oppermann22 : Machine 22 2 := Machines.oppermann22

/-- `oppermann22` in the 25-state numbering of `Goldbach21.edited`: row `i` is state
`0` = `q0`, `1` = `A1`, `2` = `B`, `3` = `q3`, `4` = `q4`, `5` = `C`, `6` = `q6`, `7` = `q7`,
`8` = `Z1`, `9` = `q9`, `10` = `X`, `11` = `q11`, `12` = `q12`, `13` = `q13`, `14` = `q14`, `15`
= `q15`, `16` = `q16`, `17` = `C2`, `20` = `q20`, `22` = `q22`, `23` = `q23`, `24` = `q24`;
rows `18, 19, 21` are unused. -/
def opp25 : Machine 25 2 := Machine.ofRows [
  [some (0, .right, 11), some (1, .left, 22)],
  [some (0, .right, 6), some (1, .right, 1)],
  [some (1, .left, 5), some (1, .right, 2)],
  [some (0, .left, 16), some (1, .right, 4)],
  [some (0, .left, 16), some (1, .right, 6)],
  [some (0, .left, 10), some (1, .left, 17)],
  [some (0, .right, 2), some (0, .left, 7)],
  [some (0, .left, 4), some (1, .left, 22)],
  [some (0, .left, 3), some (1, .left, 8)],
  [some (1, .right, 0), some (0, .left, 9)],
  [none, some (1, .right, 6)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (1, .left, 15), some (1, .left, 14)],
  [some (1, .left, 1), some (0, .left, 23)],
  [some (1, .right, 3), some (1, .left, 16)],
  [some (0, .right, 17), some (0, .left, 8)],
  [none, none],
  [none, none],
  [some (1, .left, 9), some (1, .left, 20)],
  [none, none],
  [some (0, .right, 0), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 3), some (1, .right, 24)]
]

/-- State `i` of `oppermann22` is state `embed25 i` of `opp25`. -/
def embed25 (q : Fin 22) : Fin 25 :=
  ([12, 16, 0, 3, 4, 6, 7, 9, 11, 13, 14, 15, 20, 22, 23, 24, 1, 2, 5, 17, 8, 10] :
    List (Fin 25)).getD q.val 0

theorem transition_embed25 (q : Fin 22) (a : Fin 2) :
    opp25.transition (embed25 q) a =
      (oppermann22.transition q a).map fun t => (t.1, t.2.1, embed25 t.2.2) := by
  revert q a; decide

theorem step_embed25 (q : Fin 22) (T : Tape (Fin 2)) :
    step opp25 ⟨embed25 q, T⟩ =
      (step oppermann22 ⟨q, T⟩).map fun c => ⟨embed25 c.state, c.tape⟩ := by
  simp only [step, transition_embed25, Option.map_map]
  rcases oppermann22.transition q T.head with _ | ⟨a, d, q'⟩ <;> rfl

theorem respects_embed25 :
    Respects (step oppermann22) (step opp25)
      fun c₁ c₂ => c₂ = ⟨embed25 c₁.state, c₁.tape⟩ := by
  intro c₁ c₂ h
  subst h
  obtain ⟨q, T⟩ := c₁
  rcases e : step oppermann22 ⟨q, T⟩ with _ | c
  · simpa [step_embed25] using e
  · exact ⟨⟨embed25 c.state, c.tape⟩, rfl,
      Relation.TransGen.single (by simp [step_embed25, e])⟩

/-- Halting of `oppermann22` is halting of `opp25` from state `12` (`q12`, the start state). -/
theorem halts_iff_opp25 :
    ConjectureMachines.Halts oppermann22 ↔ (eval (step opp25) ⟨12, default⟩).Dom :=
  (tr_eval_dom' respects_embed25 rfl).symm

/-!
## The primality test in `opp25`

The test is the one of `Goldbach21.edited` with three changes:
* `q21` is merged into `q9`: `(q20, 0) = 1 L q9`, and `q9` reading `0` reaches `q22` through
  `(q0, 1) = 1 L q22` (three steps instead of one, same tape);
* the entry is `(q16, 0) = 1 R q3` instead of `(q0, 1) = 1 R q3`;
* the composite exit is `(q15, 0) = 1 L A1`: `A1` runs right over the restored block and
  `(A1, 0) = 0 R q6` leaves `q6` on the cell right of the separator.

Three more cells of the test states differ from `edited`, `(q3, 0)`, `(q6, 0)` and `(q7, 0)`;
they are read only at the exits of the test and by the block logic.

Used unchanged from `Goldbach21`: the step and scan lemmas and the machine-generic pass lemmas
`nSteps_pass_11_to_13` and `nSteps_pass_13_zero_to_15`.  The other lemmas of this section
follow the `_edit`, `cfg6E` and `cfg11E` lemmas of `Goldbach21` line by line, stated for `opp25`
and for arbitrary tape on both sides of the block.
-/

theorem pass_13_one_to_9 (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps opp25 (1 + ((m + 1) + 1))
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) (R.cons 1)⟩ =
      some ⟨9, Tape.mkL L ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_left (b := 0) (q' := 20) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 20) (a := 1) (b := 1) rfl (m + 1) _ _) ?_
  exact step_one (step_mkL_left (b := 1) (q' := 9) rfl _ _)

theorem pass_9_b0_to_11 (A : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps opp25 (3 + (A + (2 + A)))
      ⟨9, Tape.mkL (counterTape A 0 L_base) (R.cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base) (R.cons 1)⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 1) (q' := 0) rfl _ _)
      (step_nSteps (step_mk'_left (b := 1) (q' := 22) rfl _ _)
        (step_one (step_mkL_left (b := 0) (q' := 22) rfl _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl A _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  exact nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl A _ _

theorem pass_9_bsucc_to_11 (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps opp25 (1 + (b + (2 + b)))
      ⟨9, Tape.mkL (counterTape A (b + 1) L_base) R⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left (b := 0) (q' := 9) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 9) (a := 1) (b := 0) rfl b _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 1) (q' := 0) rfl _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  exact nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl b _ _

theorem pass_11_b0 (A m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps opp25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (3 + (A + (2 + A)))))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (pass_13_one_to_9 m _ _)
      (pass_9_b0_to_11 A _ _))

theorem pass_11_bsucc (A b m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps opp25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (2 + b)))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (pass_13_one_to_9 m _ _)
      (pass_9_bsucc_to_11 A b _ _))

theorem pass_15_bsucc_to_6 (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps opp25 (1 + (b + (1 + (b + 3))))
      ⟨15, Tape.mkL (counterTape A (b + 1) L_base) ((R.cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left (b := 0) (q' := 23) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl b _ _) ?_
  refine nSteps_bind_eq (step_one (step_mkL_right (b := 1) (q' := 24) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl b _ _) ?_
  have h_cnt : ListBlank.append (List.replicate b 1)
      ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1) =
      ListBlank.append (List.replicate (A + b + 1) 1) (L_base.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : b + 1 + A = A + b + 1 := by omega
    rw [this]
  rw [h_cnt]
  refine step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _) ?_
  refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
  exact step_one (step_mk'_right (b := 1) (q' := 6) rfl _ _)

theorem pass_11_to_6 (A b m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps opp25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (1 + (b + 3))))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk' ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1)
        (ListBlank.append (List.replicate m 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 rfl rfl rfl m _ _)
      (pass_15_bsucc_to_6 A b _ _))

/-- Composite exit.  `q15` reads the `0` of the counter with `A + 1 ≥ 1` ones of the block on
its left, so `A1` starts on a `1`; it leaves `q6` on the first cell right of the separator. -/
theorem pass_15_b0_to_exit (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps opp25 (2 + ((m + 3) + 1))
      ⟨15, Tape.mkL (counterTape (A + 1) 0 L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R_end.cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (A + m + 4) 1) (L_base.cons 0)).cons 0) R_end⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  have h1 : ListBlank.append (List.replicate (A + 1) 1) (L_base.cons 0) =
      (ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1 := rfl
  rw [h1]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left (b := 1) (q' := 1) rfl _ _)
      (step_one (step_mkL_right (b := 1) (q' := 1) rfl _ _))) ?_
  have h2 : ((ListBlank.append (List.replicate (m + 1) 1) (R_end.cons 0)).cons 1).cons 1 =
      ListBlank.append (List.replicate (m + 3) 1) (R_end.cons 0) := rfl
  rw [h2]
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 1) (a := 1) (b := 1) rfl (m + 3) _ _) ?_
  have h3 : ListBlank.append (List.replicate (m + 3) 1)
      ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1) =
      ListBlank.append (List.replicate (A + m + 4) 1) (L_base.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : m + 3 + 1 + A = A + m + 4 := by omega
    rw [this]
  rw [h3]
  exact step_one (step_mk'_right (b := 0) (q' := 6) rfl _ _)

theorem pass_11_to_exit (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps opp25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (2 + ((m + 3) + 1))))
      ⟨11, Tape.mk' (counterTape (A + 1) 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (A + m + 4) 1) (L_base.cons 0)).cons 0) R_end⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 rfl rfl rfl m _ _)
      (pass_15_b0_to_exit A m _ _))

theorem sim6_d (k : ℕ) (L_base R_rest : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    let R_mid := R_rest.cons 0
    nSteps opp25 (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + 1))))))
      ⟨6, Tape.mk' (L_cnt.cons 1) ((R_rest.cons 1).cons 1)⟩ =
      some ⟨0, Tape.mk' ((L_base.cons 0).cons 1)
        (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) (R_mid.cons 1))⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 22) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
      (step_one (step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl (k + 1) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_right (b := 0) (q' := 12) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 13) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 20) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 20) rfl _ _)
            (step_nSteps (step_mkL_left (b := 1) (q' := 9) rfl _ _)
              (step_one (step_mkL_left (b := 0) (q' := 9) rfl _ _))))))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 9) (a := 1) (b := 0) rfl k _ _) ?_
  rw [append_replicate_cons, List.replicate_succ, ListBlank.append]
  apply step_one
  simpa [ListBlank.append_assoc] using
    step_mkL_right (M := opp25) (q := 9) (q' := 0) (a := 0) (b := 1) rfl
      (L_base.cons 0) (ListBlank.append (0 :: List.replicate k 0) (((R_rest.cons 0).cons 1).cons 1))

theorem sim6_accept (k : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    nSteps opp25 (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (1 + (k + 3))))))))
      ⟨6, Tape.mk' (L_cnt.cons 1) ((R_end.cons 0).cons 1)⟩ =
      some ⟨6, Tape.mk' ((L_cnt.cons 1).cons 1) (R_end.cons 0)⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 22) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
      (step_one (step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl (k + 1) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_right (b := 0) (q' := 12) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 13) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 14) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 14) rfl _ _)
            (step_nSteps (step_mkL_left (b := 1) (q' := 15) rfl _ _)
              (step_one (step_mkL_left (b := 0) (q' := 23) rfl _ _))))))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl k _ _) ?_
  refine nSteps_bind_eq (step_one (step_mkL_right (b := 1) (q' := 24) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl k _ _) ?_
  rw [append_replicate_cons]
  refine step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _) ?_
  refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
  exact step_one (step_mk'_right (b := 1) (q' := 6) rfl _ _)

/-- Inside the test of `k + 3 + r`: `q6` on the block, `k + 2` is the next divisor to try,
`r + 1` cells of the block are right of the head.  `L.cons 0` is the tape left of the block,
`R.cons 0` the tape right of it. -/
def tcfg6 (L R : ListBlank (Fin 2)) (k r : ℕ) : Cfg 25 2 :=
  ⟨6, Tape.mk' ((ListBlank.append (List.replicate (k + 2) 1) (L.cons 0)).cons 1)
    (ListBlank.append (List.replicate (r + 1) 1) (R.cons 0))⟩

def tcfg11 (L R : ListBlank (Fin 2)) (A B m r : ℕ) : Cfg 25 2 :=
  ⟨11, Tape.mk' (counterTape A B L)
    ((ListBlank.append (List.replicate (m + 1) 1)
      ((ListBlank.append (List.replicate r 1) (R.cons 0)).cons 0)).cons 1)⟩

/-- Exit of the test of `p` (a block of `p + 1` ones, restored).  Prime: `q6` on the separator.
Composite: `q6` on the first cell right of the separator. -/
def testExit (L R : ListBlank (Fin 2)) (is_prime : Bool) (p : ℕ) : Cfg 25 2 :=
  if is_prime then
    ⟨6, Tape.mk' (ListBlank.append (List.replicate (p + 1) 1) (L.cons 0)) (R.cons 0)⟩
  else
    ⟨6, Tape.mk' ((ListBlank.append (List.replicate (p + 1) 1) (L.cons 0)).cons 0) R⟩

theorem tcfg11_step_b0 (L R : ListBlank (Fin 2)) (A m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (tcfg11 L R A 0 m (r' + 1)) = some (tcfg11 L R 0 A (m + 1) r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1) 1) (R.cons 0) =
      (ListBlank.append (List.replicate r' 1) (R.cons 0)).cons 1 := rfl
  unfold tcfg11
  rw [h_rep]
  have h := pass_11_b0 A (m + 1) L (ListBlank.append (List.replicate r' 1) (R.cons 0))
  exact ⟨_, by omega, h⟩

theorem tcfg11_step_bsucc (L R : ListBlank (Fin 2)) (A b m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (tcfg11 L R A (b + 1) m (r' + 1)) =
        some (tcfg11 L R (A + 1) b (m + 1) r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1) 1) (R.cons 0) =
      (ListBlank.append (List.replicate r' 1) (R.cons 0)).cons 1 := rfl
  unfold tcfg11
  rw [h_rep]
  have h := pass_11_bsucc A b (m + 1) L (ListBlank.append (List.replicate r' 1) (R.cons 0))
  exact ⟨_, by omega, h⟩

theorem tcfg11_drain (L R : ListBlank (Fin 2)) (k r A B m : ℕ)
    (hAB : A + B = k + 1) (hdvd : (k + 2) ∣ B + m + 2) :
    ∃ A' B', A' + B' = k + 1 ∧ (k + 2) ∣ B' + (m + r) + 2 ∧
      ∃ s, nSteps opp25 s (tcfg11 L R A B m r) = some (tcfg11 L R A' B' (m + r) 0) := by
  induction r generalizing A B m with
  | zero =>
    exact ⟨A, B, hAB, by simpa using hdvd, 0, rfl⟩
  | succ r' ih =>
    cases B with
    | zero =>
      obtain ⟨s₁, _, hs₁⟩ := tcfg11_step_b0 L R A m r'
      have hdvd' : (k + 2) ∣ A + (m + 1) + 2 := by
        have h_eq : A + (m + 1) + 2 = (0 + m + 2) + (k + 2) := by omega
        rw [h_eq]
        exact Nat.dvd_add_self_right.mpr hdvd
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih 0 A (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
    | succ b =>
      obtain ⟨s₁, _, hs₁⟩ := tcfg11_step_bsucc L R A b m r'
      have hdvd' : (k + 2) ∣ b + (m + 1) + 2 := by
        have h_eq : b + (m + 1) + 2 = b + 1 + m + 2 := by omega
        rwa [h_eq]
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih (A + 1) b (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩

theorem tcfg6_step_enter (L R : ListBlank (Fin 2)) (k r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (tcfg6 L R k (r' + 1)) = some (tcfg11 L R 1 k 0 r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1 + 1) 1) (R.cons 0) =
      ((ListBlank.append (List.replicate r' 1) (R.cons 0)).cons 1).cons 1 := rfl
  unfold tcfg6 tcfg11
  rw [h_rep]
  have h1 := sim6_d k L (ListBlank.append (List.replicate r' 1) (R.cons 0))
  have h0_to_11 (L_b R_m : ListBlank (Fin 2)) :
      nSteps opp25 (1 + k)
        ⟨0, Tape.mk' ((L_b.cons 0).cons 1)
          (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_m)⟩ =
        some ⟨11, Tape.mk' (counterTape 1 k L_b) (R_m.cons 1)⟩ := by
    rw [ListBlank.append, ListBlank.append_assoc, ListBlank.append, ListBlank.append]
    refine nSteps_bind_eq (step_one
      (step_mk'_right (M := opp25) (q := 0) (q' := 11) (a := 0) (b := 0) rfl _ _)) ?_
    exact nSteps_mk'_right_scan (M := opp25) (q := 11) (a := 0) (b := 1) rfl k _ _
  have h := nSteps_bind_eq h1 (h0_to_11 L _)
  exact ⟨_, by omega, h⟩

theorem tcfg6_pass_succ_dvd (L R : ListBlank (Fin 2)) (k r' : ℕ)
    (hdvd : (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (tcfg6 L R k (r' + 1)) = some (testExit L R false (k + 4 + r')) := by
  obtain ⟨s₀, _, hs₀⟩ := tcfg6_step_enter L R k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    tcfg11_drain L R k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  have hB0 : B' = 0 := by
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    have h_eq2 : B' + r' + 2 = B' + (r' + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right] at hdvd
    rw [h_eq2] at hdvd'
    exact Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_iff_left hdvd).mpr hdvd') (by omega)
  subst hB0
  have hA : A' = k + 1 := by omega
  subst hA
  have h_fin := pass_11_to_exit k (r' + 1) L R
  have h_p : k + (r' + 1) + 4 = (k + 4 + r') + 1 := by omega
  have h_fin' :
      nSteps opp25 ((1 + (r' + 1 + 1)) + ((1 + ((r' + 1 + 1) + 1)) + (2 + ((r' + 1 + 3) + 1))))
        (tcfg11 L R (k + 1) 0 r' 0) = some (testExit L R false (k + 4 + r')) := by
    unfold tcfg11 testExit
    simpa [List.replicate_zero, ListBlank.append, h_p] using h_fin
  exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem tcfg6_pass_succ_not_dvd (L R : ListBlank (Fin 2)) (k r' : ℕ)
    (hdvd : ¬ (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (tcfg6 L R k (r' + 1)) = some (tcfg6 L R (k + 1) r') := by
  obtain ⟨s₀, _, hs₀⟩ := tcfg6_step_enter L R k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    tcfg11_drain L R k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  cases B' with
  | zero =>
    exfalso
    apply hdvd
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right]
    simpa using hdvd'
  | succ b =>
    have h_fin := pass_11_to_6 A' b (r' + 1) L R
    have h_k : A' + b + 3 = (k + 1) + 2 := by omega
    have h_fin' :
        nSteps opp25 ((1 + (r' + 1 + 1)) + ((1 + ((r' + 1 + 1) + 1)) + (1 + (b + (1 + (b + 3))))))
          (tcfg11 L R A' (b + 1) r' 0) = some (tcfg6 L R (k + 1) r') := by
      unfold tcfg11 tcfg6
      simpa [List.replicate_zero, ListBlank.append, h_k] using h_fin
    exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem tcfg6_eval (L R : ListBlank (Fin 2)) (k r : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (tcfg6 L R k r) =
        some (testExit L R (decide (NoFactorFrom k (k + 3 + r))) (k + 3 + r)) := by
  induction r generalizing k with
  | zero =>
    have h_nf : NoFactorFrom k (k + 3 + 0) := by
      intro d hd1 hd2 hdvd
      have hd_eq : d = k + 2 := by omega
      subst hd_eq
      have h1 : (k + 2) ∣ 1 := by
        have h_add : (k + 2) ∣ (k + 2) + 1 := hdvd
        exact (Nat.dvd_add_right (Nat.dvd_refl (k + 2))).mp h_add
      have := Nat.le_of_dvd (by omega) h1
      omega
    rw [decide_eq_true h_nf]
    have h1 := sim6_accept k L R
    have h_cnt :
        ((ListBlank.append (List.replicate (k + 2) 1) (L.cons 0)).cons 1).cons 1 =
        ListBlank.append (List.replicate (k + 3 + 1) 1) (L.cons 0) := rfl
    refine ⟨2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (1 + (k + 3))))))), by omega, ?_⟩
    unfold tcfg6 testExit
    simpa [Nat.add_zero, List.replicate_zero, ListBlank.append, h_cnt] using h1
  | succ r' ih =>
    have h_arith : k + 3 + (r' + 1) = k + 4 + r' := by omega
    rw [h_arith]
    by_cases hdvd : (k + 2) ∣ (k + 4 + r')
    · have h_nf : ¬ NoFactorFrom k (k + 4 + r') := fun h => h (k + 2) (by omega) (by omega) hdvd
      rw [decide_eq_false h_nf]
      exact tcfg6_pass_succ_dvd L R k r' hdvd
    · obtain ⟨s₁, _, hs₁⟩ := tcfg6_pass_succ_not_dvd L R k r' hdvd
      obtain ⟨s₂, _, hs₂⟩ := ih (k + 1)
      have h_arith2 : k + 1 + 3 + r' = k + 4 + r' := by omega
      rw [h_arith2] at hs₂
      have h_iff : NoFactorFrom k (k + 4 + r') ↔ NoFactorFrom (k + 1) (k + 4 + r') := by
        constructor
        · intro h d hd1 hd2
          exact h d (by omega) hd2
        · intro h d hd1 hd2
          rcases Nat.eq_or_lt_of_le hd1 with rfl | hd_gt
          · exact hdvd
          · exact h d (by omega) hd2
      have h_dec : decide (NoFactorFrom k (k + 4 + r')) =
          decide (NoFactorFrom (k + 1) (k + 4 + r')) := by
        simp [h_iff]
      rw [h_dec]
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- The test event: `q16` reading the `0` left of a block of `t` ones.  `(q16, 0) = 1 R q3`
makes the block `t + 1` long and enters the test of `t`. -/
def testCfg (L R : ListBlank (Fin 2)) (t : ℕ) : Cfg 25 2 :=
  ⟨16, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (List.replicate t 1) (R.cons 0))⟩

theorem enter_two (L R : ListBlank (Fin 2)) :
    nSteps opp25 3 ⟨16, Tape.mkL (L.cons 0) (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L.cons 1).cons 1).cons 1) (R.cons 0)⟩ :=
  step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl L (((R.cons 0).cons 1).cons 1))
    (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L.cons 1) ((R.cons 0).cons 1))
      (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L.cons 1).cons 1) (R.cons 0))))

theorem enter_ge3 (L R : ListBlank (Fin 2)) :
    nSteps opp25 3 ⟨16, Tape.mkL (L.cons 0) (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L.cons 1).cons 1).cons 1) (R.cons 1)⟩ :=
  step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl L (((R.cons 1).cons 1).cons 1))
    (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L.cons 1) ((R.cons 1).cons 1))
      (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L.cons 1).cons 1) (R.cons 1))))

/-- **The test.**  From the test event of `t ≥ 2` the machine reaches the exit that says
whether `t` is prime, with the block (now `t + 1` ones) restored and `L`, `R` untouched. -/
theorem test_eval (L R : ListBlank (Fin 2)) (t : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (testCfg L R t) = some (testExit L R (decide (IsPrime t)) t) := by
  rcases Nat.eq_or_lt_of_le ht with rfl | ht3
  · rw [decide_eq_true isPrime_two]
    have h2 := enter_two (L.cons 0) R
    refine ⟨3, by omega, ?_⟩
    unfold testCfg testExit
    exact h2
  · obtain ⟨r0, rfl⟩ : ∃ r0, t = r0 + 3 := ⟨t - 3, by omega⟩
    have h_enter : nSteps opp25 3 (testCfg L R (r0 + 3)) = some (tcfg6 L R 0 r0) :=
      enter_ge3 (L.cons 0) (ListBlank.append (List.replicate r0 1) (R.cons 0))
    obtain ⟨s₂, _, hs₂⟩ := tcfg6_eval L R 0 r0
    have h_prime_iff : IsPrime (r0 + 3) ↔ NoFactorFrom 0 (0 + 3 + r0) := by
      unfold IsPrime
      have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
      rw [h_eq]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    have h_dec : decide (IsPrime (r0 + 3)) = decide (NoFactorFrom 0 (0 + 3 + r0)) := by
      simp [h_prime_iff]
    have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
    rw [h_dec]
    rw [h_eq] at hs₂ ⊢
    exact ⟨3 + s₂, by omega, nSteps_bind_eq h_enter hs₂⟩

/-!
## Walker

Right of the block: the separator `0`, the flag cell `f`, and the walker area `walkerTape h r`
(`h` ones, a hole, `r` ones; the blank beyond `walkerTape h 0` is the hole).  After a test `B` runs
right to the hole and fills it, `C` steps one cell left, `C2` opens a hole on the next cell
left, `Z1` runs back.  So the hole moves two cells per tested number.

* composite, flag clear, hole at cell `≥ 2`: next number;
* composite, flag clear, hole at cell `1`: `C2` reads the clear flag, steps right and opens the
  hole at cell `0` (the hole moves one cell only);
* composite, flag clear, hole at cell `0`: `C` reads the clear flag, `X` reads the separator:
  **halt**;
* prime, flag clear: `B` sets the flag, `C` and `X` turn round, then as with the flag set;
* flag set (a composite first makes the detour `q6 q7 q4 q6 B C X q6`, which clears the flag
  and sets it again): next number; with the hole at cell `1` the new hole is the flag cell, with
  the hole at cell `0` `C2` reads the separator, steps right and clears the flag: in both cases
  the flag is clear, the walker area is full, and the next block starts.
-/

local notation:max "ones(" n ", " L ")" => ListBlank.append (List.replicate n (1 : Fin 2)) L

theorem step_mkL_none {M : Machine 25 2} {q : Fin 25} {a : Fin 2}
    (h : M.transition q a = none) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = none := by
  simp [step, h, Tape.mkL]

/-- `B` runs right over `h + 2` ones and fills the hole, `C` steps left, `C2` opens a hole two
cells left of the old one, `Z1` runs back over the ones and stops on the cell left of them. -/
theorem walkB (h : ℕ) (Lf Rr : ListBlank (Fin 2)) :
    nSteps opp25 ((h + 2) + (3 + h)) ⟨2, Tape.mk' Lf ones(h + 2, Rr.cons 0)⟩ =
      some ⟨8, Tape.mkL Lf ones(h, ((Rr.cons 1).cons 1).cons 0)⟩ := by
  have h1 : nSteps opp25 (h + 2) ⟨2, Tape.mk' Lf ones(h + 2, Rr.cons 0)⟩ =
      some ⟨2, Tape.mk' ones(h + 2, Lf) (Rr.cons 0)⟩ :=
    nSteps_mk'_right_scan (q := 2) (a := 1) (b := 1) rfl (h + 2) Lf (Rr.cons 0)
  have h2 : nSteps opp25 3 ⟨2, Tape.mk' ((ones(h, Lf).cons 1).cons 1) (Rr.cons 0)⟩ =
      some ⟨8, Tape.mkL ones(h, Lf) (((Rr.cons 1).cons 1).cons 0)⟩ :=
    step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
      (step_nSteps (step_mkL_left (b := 1) (q' := 17) rfl _ _)
        (step_one (step_mkL_left (b := 0) (q' := 8) rfl _ _)))
  have h3 : nSteps opp25 h ⟨8, Tape.mkL ones(h, Lf) (((Rr.cons 1).cons 1).cons 0)⟩ =
      some ⟨8, Tape.mkL Lf ones(h, ((Rr.cons 1).cons 1).cons 0)⟩ :=
    nSteps_mkL_left_scan (q := 8) (a := 1) (b := 1) rfl h Lf (((Rr.cons 1).cons 1).cons 0)
  exact nSteps_bind_eq h1 (nSteps_bind_eq h2 h3)

/-- Way back when `Z1` stops on the separator: `q3` reads the last cell of the block, `q4` the
separator, `q16` runs left over the block of `n + 1` ones. -/
theorem ret_q4 (n : ℕ) (L X : ListBlank (Fin 2)) :
    nSteps opp25 (3 + (n + 1)) ⟨8, Tape.mkL (ones(n + 1, L.cons 0).cons 0) X⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ones(n + 1, X.cons 0)⟩ := by
  have h1 : nSteps opp25 3 ⟨8, Tape.mkL ((ones(n, L.cons 0).cons 1).cons 0) X⟩ =
      some ⟨16, Tape.mkL (ones(n, L.cons 0).cons 1) (X.cons 0)⟩ :=
    step_nSteps (step_mkL_left (b := 0) (q' := 3) rfl _ _)
      (step_nSteps (step_mkL_right (b := 1) (q' := 4) rfl _ _)
        (step_one (step_mk'_left (b := 0) (q' := 16) rfl _ _)))
  have h2 : nSteps opp25 (n + 1) ⟨16, Tape.mkL ones(n + 1, L.cons 0) (X.cons 0)⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ones(n + 1, X.cons 0)⟩ :=
    nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl (n + 1) (L.cons 0) (X.cons 0)
  exact nSteps_bind_eq h1 h2

/-- Way back when `Z1` stops on the clear flag: `q3` reads the separator, `q16` runs left over
the block of `m` ones. -/
theorem ret_q3 (m : ℕ) (Lz X : ListBlank (Fin 2)) :
    nSteps opp25 (2 + m) ⟨8, Tape.mkL ((ones(m, Lz).cons 0).cons 0) X⟩ =
      some ⟨16, Tape.mkL Lz ones(m, (X.cons 0).cons 0)⟩ := by
  have h1 : nSteps opp25 2 ⟨8, Tape.mkL ((ones(m, Lz).cons 0).cons 0) X⟩ =
      some ⟨16, Tape.mkL ones(m, Lz) ((X.cons 0).cons 0)⟩ :=
    step_nSteps (step_mkL_left (b := 0) (q' := 3) rfl _ _)
      (step_one (step_mkL_left (b := 0) (q' := 16) rfl _ _))
  exact nSteps_bind_eq h1
    (nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl m Lz ((X.cons 0).cons 0))

/-- `q6` on the separator, the flag clear: `B` sets the flag, `C` reads the separator, `X` the
last cell of the block, and `q6` sends `B` onto the set flag. -/
theorem setflag (Lm Y : ListBlank (Fin 2)) :
    nSteps opp25 5 ⟨6, Tape.mk' (Lm.cons 1) ((Y.cons 0).cons 0)⟩ =
      some ⟨2, Tape.mk' ((Lm.cons 1).cons 0) (Y.cons 1)⟩ :=
  step_nSteps (step_mk'_right (b := 0) (q' := 2) rfl _ _)
    (step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
      (step_nSteps (step_mkL_left (b := 0) (q' := 10) rfl _ _)
        (step_nSteps (step_mkL_right (b := 1) (q' := 6) rfl _ _)
          (step_one (step_mk'_right (b := 0) (q' := 2) rfl _ _)))))

/-- The detour of a composite exit with the flag set: `q6` clears the flag, `q7` on the
separator steps left, `q4` on the last cell of the block steps right, and `setflag` sets the
flag again; `B` is then on the set flag. -/
theorem detour (Lm Y : ListBlank (Fin 2)) :
    nSteps opp25 8 ⟨6, Tape.mk' ((Lm.cons 1).cons 0) (Y.cons 1)⟩ =
      some ⟨2, Tape.mk' ((Lm.cons 1).cons 0) (Y.cons 1)⟩ :=
  step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
    (step_nSteps (step_mkL_left (b := 0) (q' := 4) rfl _ _)
      (step_nSteps (step_mkL_right (b := 1) (q' := 6) rfl _ _)
        (setflag Lm Y)))

/-- The walker area: `h` ones, a hole, `r` ones, then blank. -/
def walkerTape (h r : ℕ) : ListBlank (Fin 2) := ones(h, ones(r, B0).cons 0)

theorem walkerTape_zero (h : ℕ) : walkerTape h 0 = ones(h, B0) :=
  congrArg (fun l : ListBlank (Fin 2) => ones(h, l)) B0_cons_zero

/-! ### Composite, flag clear -/

theorem comp_f0_ge2 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps opp25 (1 + (((h + 2) + (3 + h)) + (2 + (t + 1))))
      (testExit L ((walkerTape (h + 2) r).cons 0) false t) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ((walkerTape h (r + 2)).cons 0).cons 0)⟩ := by
  have h1 : nSteps opp25 1
      ⟨6, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((walkerTape (h + 2) r).cons 0)⟩ =
      some ⟨2, Tape.mk' ((ones(t + 1, L.cons 0).cons 0).cons 0) (walkerTape (h + 2) r)⟩ :=
    step_one (step_mk'_right (b := 0) (q' := 2) rfl _ _)
  have h2 := walkB h ((ones(t + 1, L.cons 0).cons 0).cons 0) ones(r, B0)
  have h3 := ret_q3 (t + 1) (L.cons 0) ones(h, ((ones(r, B0).cons 1).cons 1).cons 0)
  unfold testExit
  exact nSteps_bind_eq h1 (nSteps_bind_eq h2 h3)

/-- The hole at cell `1` and the flag clear: `C2` reads the clear flag, steps right and opens
the hole at cell `0`. -/
theorem comp_f0_one (L : ListBlank (Fin 2)) (t r : ℕ) :
    nSteps opp25 (6 + (2 + (t + 1)))
      (testExit L ((walkerTape 1 r).cons 0) false t) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ((walkerTape 0 (r + 1)).cons 0).cons 0)⟩ := by
  have h1 : nSteps opp25 6
      ⟨6, Tape.mk' (ones(t + 1, L.cons 0).cons 0) (((ones(r, B0).cons 0).cons 1).cons 0)⟩ =
      some ⟨8, Tape.mkL ((ones(t + 1, L.cons 0).cons 0).cons 0)
        ((ones(r, B0).cons 1).cons 0)⟩ :=
    step_nSteps (step_mk'_right (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 2) rfl _ _)
        (step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 17) rfl _ _)
            (step_nSteps (step_mkL_right (b := 0) (q' := 17) rfl _ _)
              (step_one (step_mk'_left (b := 0) (q' := 8) rfl _ _))))))
  have h3 := ret_q3 (t + 1) (L.cons 0) ((ones(r, B0).cons 1).cons 0)
  unfold testExit
  exact nSteps_bind_eq h1 h3

/-- The hole at cell `0` and the flag clear: **halt**. -/
theorem comp_f0_zero (L : ListBlank (Fin 2)) (t r : ℕ) :
    ∃ c, nSteps opp25 3 (testExit L ((walkerTape 0 r).cons 0) false t) = some c ∧
      step opp25 c = none := by
  have h1 : nSteps opp25 3
      ⟨6, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((ones(r, B0).cons 0).cons 0)⟩ =
      some ⟨10, Tape.mkL (ones(t + 1, L.cons 0).cons 0) ((ones(r, B0).cons 1).cons 0)⟩ :=
    step_nSteps (step_mk'_right (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
        (step_one (step_mkL_left (b := 0) (q' := 10) rfl _ _)))
  unfold testExit
  exact ⟨_, h1, step_mkL_none rfl _ _⟩

/-! ### `B` on the set flag -/

/-- `B` on the set flag, the separator on its left, the block of `t + 1` ones left of that. -/
def onFlagCfg (L : ListBlank (Fin 2)) (t h r : ℕ) : Cfg 25 2 :=
  ⟨2, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((walkerTape h r).cons 1)⟩

theorem onFlag_ge2 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps opp25 (((h + 1 + 2) + (3 + (h + 1))) + (3 + (t + 1))) (onFlagCfg L t (h + 2) r) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ((walkerTape h (r + 2)).cons 1).cons 0)⟩ := by
  have h2 := walkB (h + 1) (ones(t + 1, L.cons 0).cons 0) ones(r, B0)
  have h3 := ret_q4 t L ones(h + 1, ((ones(r, B0).cons 1).cons 1).cons 0)
  unfold onFlagCfg
  exact nSteps_bind_eq h2 h3

/-- The hole at cell `1`: the new hole is the flag cell.  The flag is clear, the area full. -/
theorem onFlag_one (L : ListBlank (Fin 2)) (t r : ℕ) :
    nSteps opp25 (((0 + 2) + (3 + 0)) + (3 + (t + 1))) (onFlagCfg L t 1 r) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, (ones(r + 2, B0).cons 0).cons 0)⟩ := by
  have h2 := walkB 0 (ones(t + 1, L.cons 0).cons 0) ones(r, B0)
  have h3 := ret_q4 t L (((ones(r, B0).cons 1).cons 1).cons 0)
  unfold onFlagCfg
  exact nSteps_bind_eq h2 h3

/-- The hole at cell `0`: `C` reads the set flag, `C2` the separator; `C2` steps right and
clears the flag.  The flag is clear, the area full. -/
theorem onFlag_zero (L : ListBlank (Fin 2)) (t r : ℕ) :
    nSteps opp25 (5 + (3 + (t + 1))) (onFlagCfg L t 0 r) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, (ones(r + 1, B0).cons 0).cons 0)⟩ := by
  have h1 : nSteps opp25 5
      ⟨2, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((ones(r, B0).cons 0).cons 1)⟩ =
      some ⟨8, Tape.mkL (ones(t + 1, L.cons 0).cons 0) ((ones(r, B0).cons 1).cons 0)⟩ :=
    step_nSteps (step_mk'_right (b := 1) (q' := 2) rfl _ _)
      (step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
        (step_nSteps (step_mkL_left (b := 1) (q' := 17) rfl _ _)
          (step_nSteps (step_mkL_right (b := 0) (q' := 17) rfl _ _)
            (step_one (step_mk'_left (b := 0) (q' := 8) rfl _ _)))))
  have h3 := ret_q4 t L ((ones(r, B0).cons 1).cons 0)
  unfold onFlagCfg
  exact nSteps_bind_eq h1 h3

/-! ### From the exits of the test to `B` on the set flag -/

theorem comp_f1 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps opp25 8 (testExit L ((walkerTape h r).cons 1) false t) = some (onFlagCfg L t h r) := by
  have h1 := detour ones(t, L.cons 0) (walkerTape h r)
  unfold testExit onFlagCfg
  exact h1

theorem prime_f1 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps opp25 1 (testExit L ((walkerTape h r).cons 1) true t) = some (onFlagCfg L t h r) := by
  have h1 : nSteps opp25 1
      ⟨6, Tape.mk' ones(t + 1, L.cons 0) (((walkerTape h r).cons 1).cons 0)⟩ =
      some ⟨2, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((walkerTape h r).cons 1)⟩ :=
    step_one (step_mk'_right (b := 0) (q' := 2) rfl _ _)
  unfold testExit onFlagCfg
  exact h1

theorem prime_f0 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps opp25 5 (testExit L ((walkerTape h r).cons 0) true t) = some (onFlagCfg L t h r) := by
  have h1 := setflag ones(t, L.cons 0) (walkerTape h r)
  unfold testExit onFlagCfg
  exact h1

/-- The number `0`: `q3` reads the separator and sends `q16` straight back. -/
theorem testCfg_zero (L R : ListBlank (Fin 2)) :
    nSteps opp25 3 (testCfg L R 0) = some ⟨16, Tape.mkL (L.cons 0) ones(1, R.cons 0)⟩ := by
  have h1 : nSteps opp25 3 ⟨16, Tape.mkL ((L.cons 0).cons 0) (R.cons 0)⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ((R.cons 0).cons 1)⟩ :=
    step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl _ _)
      (step_nSteps (step_mk'_left (b := 0) (q' := 16) rfl _ _)
        (step_one (step_mkL_left (b := 1) (q' := 16) rfl _ _)))
  unfold testCfg
  exact h1

/-- The number `1`: `q3` and `q4` send `q16` straight back; nothing right of the block moves. -/
theorem testCfg_one (L R : ListBlank (Fin 2)) :
    nSteps opp25 5 (testCfg L R 1) = some ⟨16, Tape.mkL (L.cons 0) ones(2, R.cons 0)⟩ := by
  have h1 : nSteps opp25 3 ⟨16, Tape.mkL ((L.cons 0).cons 0) ((R.cons 0).cons 1)⟩ =
      some ⟨16, Tape.mkL (((L.cons 0).cons 1).cons 1) (R.cons 0)⟩ :=
    step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _)
        (step_one (step_mk'_left (b := 0) (q' := 16) rfl _ _)))
  have h2 : nSteps opp25 2 ⟨16, Tape.mkL ones(2, L.cons 0) (R.cons 0)⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ones(2, R.cons 0)⟩ :=
    nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl 2 (L.cons 0) (R.cons 0)
  unfold testCfg
  exact nSteps_bind_eq h1 h2

/-!
## Events

`evCfg t f h r`: `q16` on the blank left of a block of `t` ones, nothing but blanks further left;
right of the block the separator, the flag `f`, and the walker area `walkerTape h r`.
-/

def evCfg (t : ℕ) (f : Fin 2) (h r : ℕ) : Cfg 25 2 :=
  ⟨16, Tape.mkL (B0.cons 0) ones(t, ((walkerTape h r).cons f).cons 0)⟩

theorem ev_congr {t t' : ℕ} (f : Fin 2) {h h' r r' : ℕ}
    (ht : t = t') (hh : h = h') (hr : r = r') : evCfg t f h r = evCfg t' f h' r' := by
  subst ht hh hr; rfl

theorem testCfg_B0 (R : ListBlank (Fin 2)) (t : ℕ) :
    testCfg B0 R t = ⟨16, Tape.mkL (B0.cons 0) ones(t, R.cons 0)⟩ :=
  congrArg (fun l : ListBlank (Fin 2) =>
    (⟨16, Tape.mkL (l.cons 0) ones(t, R.cons 0)⟩ : Cfg 25 2)) B0_cons_zero

theorem ev_test (t : ℕ) (f : Fin 2) (h r : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (evCfg t f h r) =
        some (testExit B0 ((walkerTape h r).cons f) (decide (IsPrime t)) t) := by
  have h0 := test_eval B0 ((walkerTape h r).cons f) t ht
  rw [testCfg_B0] at h0
  exact h0

theorem ev_zero (f : Fin 2) (h r : ℕ) : nSteps opp25 3 (evCfg 0 f h r) = some (evCfg 1 f h r) := by
  have h0 := testCfg_zero B0 ((walkerTape h r).cons f)
  rw [testCfg_B0] at h0
  exact h0

theorem ev_one (f : Fin 2) (h r : ℕ) : nSteps opp25 5 (evCfg 1 f h r) = some (evCfg 2 f h r) := by
  have h0 := testCfg_one B0 ((walkerTape h r).cons f)
  rw [testCfg_B0] at h0
  exact h0

theorem ev_comp_f0_ge2 (t h r : ℕ) (ht : 2 ≤ t) (hp : ¬ IsPrime t) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (evCfg t 0 (h + 2) r) = some (evCfg (t + 1) 0 h (r + 2)) := by
  obtain ⟨s, _, hs⟩ := ev_test t 0 (h + 2) r ht
  rw [decide_eq_false hp] at hs
  exact ⟨_, by omega, nSteps_bind_eq hs (comp_f0_ge2 B0 t h r)⟩

theorem ev_comp_f0_one (t r : ℕ) (ht : 2 ≤ t) (hp : ¬ IsPrime t) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (evCfg t 0 1 r) = some (evCfg (t + 1) 0 0 (r + 1)) := by
  obtain ⟨s, _, hs⟩ := ev_test t 0 1 r ht
  rw [decide_eq_false hp] at hs
  exact ⟨_, by omega, nSteps_bind_eq hs (comp_f0_one B0 t r)⟩

theorem ev_comp_f0_zero (t r : ℕ) (ht : 2 ≤ t) (hp : ¬ IsPrime t) :
    ∃ s c, nSteps opp25 s (evCfg t 0 0 r) = some c ∧ step opp25 c = none := by
  obtain ⟨s, _, hs⟩ := ev_test t 0 0 r ht
  rw [decide_eq_false hp] at hs
  obtain ⟨c, hc, hn⟩ := comp_f0_zero B0 t r
  exact ⟨_, c, nSteps_bind_eq hs hc, hn⟩

/-- Flag set: `B` reaches the set flag. -/
theorem ev_f1_onFlag (t h r : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (evCfg t 1 h r) = some (onFlagCfg B0 t h r) := by
  obtain ⟨s, _, hs⟩ := ev_test t 1 h r ht
  by_cases hp : IsPrime t
  · rw [decide_eq_true hp] at hs
    exact ⟨_, by omega, nSteps_bind_eq hs (prime_f1 B0 t h r)⟩
  · rw [decide_eq_false hp] at hs
    exact ⟨_, by omega, nSteps_bind_eq hs (comp_f1 B0 t h r)⟩

/-- A prime with the flag clear: the flag is set and `B` is on it. -/
theorem ev_p0_onFlag (t h r : ℕ) (ht : 2 ≤ t) (hp : IsPrime t) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (evCfg t 0 h r) = some (onFlagCfg B0 t h r) := by
  obtain ⟨s, _, hs⟩ := ev_test t 0 h r ht
  rw [decide_eq_true hp] at hs
  exact ⟨_, by omega, nSteps_bind_eq hs (prime_f0 B0 t h r)⟩

theorem onFlag_ev_ge2 (t h r : ℕ) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (onFlagCfg B0 t (h + 2) r) = some (evCfg (t + 1) 1 h (r + 2)) :=
  ⟨_, by omega, onFlag_ge2 B0 t h r⟩

theorem onFlag_ev_one (t r : ℕ) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (onFlagCfg B0 t 1 r) = some (evCfg (t + 1) 0 (r + 2) 0) := by
  refine ⟨((0 + 2) + (3 + 0)) + (3 + (t + 1)), by omega, ?_⟩
  have e : evCfg (t + 1) 0 (r + 2) 0 =
      ⟨16, Tape.mkL (B0.cons 0) ones(t + 1, (ones(r + 2, B0).cons 0).cons 0)⟩ := by
    unfold evCfg
    rw [walkerTape_zero]
  rw [e]
  exact onFlag_one B0 t r

theorem onFlag_ev_zero (t r : ℕ) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (onFlagCfg B0 t 0 r) = some (evCfg (t + 1) 0 (r + 1) 0) := by
  refine ⟨5 + (3 + (t + 1)), by omega, ?_⟩
  have e : evCfg (t + 1) 0 (r + 1) 0 =
      ⟨16, Tape.mkL (B0.cons 0) ones(t + 1, (ones(r + 1, B0).cons 0).cons 0)⟩ := by
    unfold evCfg
    rw [walkerTape_zero]
  rw [e]
  exact onFlag_zero B0 t r

/-!
## Blocks

`qs j = ⌊j² / 4⌋`.  Block `j` is `qs j, …, qs (j + 1) - 1`; it has `(j + 1) / 2` numbers.
Block `2 n` is `n², …, n² + n - 1` and block `2 n + 1` is `n² + n, …, (n + 1)² - 1`.

A block starts at the event `evCfg T 0 L 0` with `T = qs j` and `L = j - 1`: flag clear, walker
area `L` ones.  Every test moves the hole two cells left.  The hole would land on the flag cell
or pass it at test number `L / 2 + 1`.  With a prime in the block the flag is set by then; it
is cleared, the area has `L + 1` ones, and the next block starts.  Without a prime:
* `L` even: the hole is at cell `0` at the last number of the block, a composite: halt;
* `L` odd: the hole is at cell `1` at the last number; it moves to cell `0`, and the next
  number, `qs (j + 1)`, is not prime: halt one test later.
-/

/-- `j` composites in a row with the flag clear: the hole moves `2 j` cells left. -/
theorem walk0 (h j : ℕ) : ∀ (t r : ℕ), 2 ≤ t → (∀ i, i < j → ¬ IsPrime (t + i)) →
    ∃ s, j ≤ s ∧
      nSteps opp25 s (evCfg t 0 (h + 2 * j) r) = some (evCfg (t + j) 0 h (r + 2 * j)) := by
  induction j with
  | zero => intro t r _ _; exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    intro t r ht hnp
    obtain ⟨s₁, h1, hs₁⟩ := ev_comp_f0_ge2 t (h + 2 * j) r ht (hnp 0 (Nat.succ_pos j))
    obtain ⟨s₂, h2, hs₂⟩ := ih (t + 1) (r + 2) (by omega) (fun i hi => by
      have h' := hnp (i + 1) (by omega)
      have e : t + 1 + i = t + (i + 1) := by omega
      rw [e]; exact h')
    refine ⟨s₁ + s₂, by omega, ?_⟩
    have e1 : evCfg t 0 (h + 2 * (j + 1)) r = evCfg t 0 (h + 2 * j + 2) r :=
      ev_congr 0 rfl (by omega) rfl
    rw [e1]
    refine nSteps_bind_eq hs₁ ?_
    rw [hs₂]
    exact congrArg some (ev_congr 0 (by omega) rfl (by omega))

/-- From `B` on the set flag to the start of the next block: `h / 2 + 1` numbers, counting the
one under test. -/
theorem finish_onFlag : ∀ (h t r : ℕ), 2 ≤ t →
    ∃ s, 1 ≤ s ∧
      nSteps opp25 s (onFlagCfg B0 t h r) = some (evCfg (t + h / 2 + 1) 0 (h + r + 1) 0)
  | 0, t, r, _ => by
    obtain ⟨s, hs1, hs⟩ := onFlag_ev_zero t r
    refine ⟨s, hs1, ?_⟩
    rw [hs]
    exact congrArg some (ev_congr 0 (by omega) (by omega) rfl)
  | 1, t, r, _ => by
    obtain ⟨s, hs1, hs⟩ := onFlag_ev_one t r
    refine ⟨s, hs1, ?_⟩
    rw [hs]
    exact congrArg some (ev_congr 0 (by omega) (by omega) rfl)
  | h + 2, t, r, ht => by
    obtain ⟨s₁, _, hs₁⟩ := onFlag_ev_ge2 t h r
    obtain ⟨s₂, _, hs₂⟩ := ev_f1_onFlag (t + 1) h (r + 2) (by omega)
    obtain ⟨s₃, _, hs₃⟩ := finish_onFlag h (t + 1) (r + 2) (by omega)
    refine ⟨s₁ + (s₂ + s₃), by omega, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ ?_)⟩
    rw [hs₃]
    exact congrArg some (ev_congr 0 (by omega) (by omega) rfl)

/-- A prime with the flag clear: the block ends `h / 2 + 1` numbers later. -/
theorem finish_p0 (t h r : ℕ) (ht : 2 ≤ t) (hp : IsPrime t) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (evCfg t 0 h r) = some (evCfg (t + h / 2 + 1) 0 (h + r + 1) 0) := by
  obtain ⟨s₁, _, hs₁⟩ := ev_p0_onFlag t h r ht hp
  obtain ⟨s₂, _, hs₂⟩ := finish_onFlag h t r ht
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- The first prime of a block with a prime, as an offset from the block's first number. -/
theorem first_prime (T L : ℕ) (hp : ∃ x, x < T + L / 2 + 1 ∧ T ≤ x ∧ IsPrime x) :
    ∃ j0, IsPrime (T + j0) ∧ ∀ i, i < j0 → ¬ IsPrime (T + i) := by
  have hex : ∃ j, IsPrime (T + j) := by
    obtain ⟨x, _, hx2, hx3⟩ := hp
    have e : T + (x - T) = x := by omega
    exact ⟨x - T, by rw [e]; exact hx3⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩

theorem first_prime_le (T L j0 : ℕ) (hp : ∃ x, x < T + L / 2 + 1 ∧ T ≤ x ∧ IsPrime x)
    (hmin : ∀ i, i < j0 → ¬ IsPrime (T + i)) : j0 ≤ L / 2 := by
  obtain ⟨x, hx1, hx2, hx3⟩ := hp
  have hle : j0 ≤ x - T := Nat.le_of_not_lt (fun hlt => hmin (x - T) hlt (by
    have e : T + (x - T) = x := by omega
    rw [e]; exact hx3))
  omega

/-- A block with a prime: from its start to the start of the next block. -/
theorem block_adv (T L : ℕ) (hT : 2 ≤ T)
    (hp : ∃ x, x < T + L / 2 + 1 ∧ T ≤ x ∧ IsPrime x) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (evCfg T 0 L 0) = some (evCfg (T + L / 2 + 1) 0 (L + 1) 0) := by
  obtain ⟨j0, hj0, hmin⟩ := first_prime T L hp
  have hj0_le : j0 ≤ L / 2 := first_prime_le T L j0 hp hmin
  clear hp
  obtain ⟨h0, hh0⟩ : ∃ h0, L = h0 + 2 * j0 := ⟨L - 2 * j0, by omega⟩
  obtain ⟨s₁, _, hs₁⟩ := walk0 h0 j0 T 0 hT hmin
  obtain ⟨s₂, hs2, hs₂⟩ := finish_p0 (T + j0) h0 (0 + 2 * j0) (by omega) hj0
  refine ⟨s₁ + s₂, by omega, ?_⟩
  have e1 : evCfg T 0 L 0 = evCfg T 0 (h0 + 2 * j0) 0 := ev_congr 0 rfl hh0 rfl
  have e2 : evCfg (T + j0 + h0 / 2 + 1) 0 (h0 + (0 + 2 * j0) + 1) 0 =
      evCfg (T + L / 2 + 1) 0 (L + 1) 0 := ev_congr 0 (by omega) (by omega) rfl
  rw [e1]
  rw [e2] at hs₂
  exact nSteps_bind_eq hs₁ hs₂

/-- A block without a prime, followed by a number that is not prime: the machine halts. -/
theorem block_halt (T L : ℕ) (hT : 2 ≤ T)
    (hnp : ∀ i, i < L / 2 + 1 → ¬ IsPrime (T + i)) (hq : ¬ IsPrime (T + L / 2 + 1)) :
    ∃ s c, nSteps opp25 s (evCfg T 0 L 0) = some c ∧ step opp25 c = none := by
  rcases Nat.mod_two_eq_zero_or_one L with hpar | hpar
  · -- `L` even: the hole reaches cell `0` at the last number of the block
    obtain ⟨s₁, _, hs₁⟩ := walk0 0 (L / 2) T 0 hT (fun i hi => hnp i (by omega))
    obtain ⟨s₂, c, hs₂, hc⟩ :=
      ev_comp_f0_zero (T + L / 2) (0 + 2 * (L / 2)) (by omega) (hnp (L / 2) (by omega))
    have e1 : evCfg T 0 L 0 = evCfg T 0 (0 + 2 * (L / 2)) 0 := ev_congr 0 rfl (by omega) rfl
    rw [e1]
    exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hc⟩
  · -- `L` odd: cell `1` at the last number, cell `0` one number later
    obtain ⟨s₁, _, hs₁⟩ := walk0 1 (L / 2) T 0 hT (fun i hi => hnp i (by omega))
    obtain ⟨s₂, _, hs₂⟩ :=
      ev_comp_f0_one (T + L / 2) (0 + 2 * (L / 2)) (by omega) (hnp (L / 2) (by omega))
    obtain ⟨s₃, c, hs₃, hc⟩ :=
      ev_comp_f0_zero (T + L / 2 + 1) (0 + 2 * (L / 2) + 1) (by omega) hq
    have e1 : evCfg T 0 L 0 = evCfg T 0 (1 + 2 * (L / 2)) 0 := ev_congr 0 rfl (by omega) rfl
    rw [e1]
    exact ⟨s₁ + (s₂ + s₃), c, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ hs₃), hc⟩

/-!
## Quarter-squares
-/

/-- `qs j = ⌊j² / 4⌋`, by its recursion `qs (j + 1) = qs j + (j + 1) / 2`. -/
def qs : ℕ → ℕ
  | 0 => 0
  | j + 1 => qs j + (j + 1) / 2

theorem qs_succ (j : ℕ) : qs (j + 1) = qs j + (j + 1) / 2 := rfl

theorem sq_succ (n : ℕ) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  rw [Nat.add_mul, Nat.mul_add]; omega

theorem qs_even_odd (n : ℕ) : qs (2 * n) = n * n ∧ qs (2 * n + 1) = n * n + n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hsq := sq_succ n
    have e1 : qs (2 * (n + 1)) = (n + 1) * (n + 1) := by
      have e : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [e, qs_succ, ih.2]
      omega
    refine ⟨e1, ?_⟩
    have e : 2 * (n + 1) + 1 = (2 * (n + 1)) + 1 := rfl
    rw [e, qs_succ, e1]
    omega

theorem qs_even (n : ℕ) : qs (2 * n) = n * n := (qs_even_odd n).1

theorem qs_odd (n : ℕ) : qs (2 * n + 1) = n * n + n := (qs_even_odd n).2

/-- Quarter-squares from the fourth on are `n * n` or `n * (n + 1)` with `n ≥ 2`: not prime. -/
theorem not_isPrime_qs (j : ℕ) (hj : 4 ≤ j) : ¬ IsPrime (qs j) := by
  obtain ⟨n, hn⟩ : ∃ n, j = 2 * n ∨ j = 2 * n + 1 := ⟨j / 2, by omega⟩
  have hn2 : 2 ≤ n := by omega
  have h2 : n * 2 ≤ n * n := Nat.mul_le_mul_left n hn2
  rintro ⟨_, hnf⟩
  rcases hn with rfl | rfl
  · rw [qs_even] at hnf
    exact hnf n (by omega) (by omega) (Dvd.intro n rfl)
  · rw [qs_odd] at hnf
    exact hnf n (by omega) (by omega) (Dvd.intro (n + 1) (Nat.mul_succ n n))

theorem qs_ge (w : ℕ) : 12 ≤ qs (w + 7) := by
  induction w with
  | zero => exact le_rfl
  | succ w ih =>
    have e : qs (w + 1 + 7) = qs (w + 7) + (w + 7 + 1) / 2 := rfl
    rw [e]; omega

/-- Block `j` has a prime. -/
def HasPrime (j : ℕ) : Prop := ∃ x, x < qs (j + 1) ∧ qs j ≤ x ∧ IsPrime x

instance instDecidableHasPrime (j : ℕ) : Decidable (HasPrime j) :=
  inferInstanceAs (Decidable (∃ x, x < qs (j + 1) ∧ qs j ≤ x ∧ IsPrime x))

/-!
## Start and main theorem
-/

/-- Start of block `w + 7`. -/
def blockCfg (w : ℕ) : Cfg 25 2 := evCfg (qs (w + 7)) 0 (w + 6) 0

theorem qs_block (w : ℕ) : qs (w + 8) = qs (w + 7) + (w + 6) / 2 + 1 := by
  have e : qs (w + 8) = qs (w + 7) + (w + 7 + 1) / 2 := rfl
  rw [e]; omega

theorem blockCfg_advance (w : ℕ) (h : HasPrime (w + 7)) :
    ∃ s, 1 ≤ s ∧ nSteps opp25 s (blockCfg w) = some (blockCfg (w + 1)) := by
  have hq := qs_block w
  have hge := qs_ge w
  obtain ⟨x, hx1, hx2, hx3⟩ := h
  have hx1' : x < qs (w + 8) := hx1
  obtain ⟨s, hs1, hs⟩ := block_adv (qs (w + 7)) (w + 6) (by omega) ⟨x, by omega, hx2, hx3⟩
  refine ⟨s, hs1, ?_⟩
  have e : blockCfg (w + 1) = evCfg (qs (w + 7) + (w + 6) / 2 + 1) 0 (w + 6 + 1) 0 := by
    unfold blockCfg
    exact ev_congr 0 hq rfl rfl
  rw [e]
  exact hs

theorem blockCfg_halt (w : ℕ) (h : ¬ HasPrime (w + 7)) :
    ∃ s c, nSteps opp25 s (blockCfg w) = some c ∧ step opp25 c = none := by
  have hq := qs_block w
  have hge := qs_ge w
  refine block_halt (qs (w + 7)) (w + 6) (by omega) (fun i hi hpi => ?_) ?_
  · exact h ⟨qs (w + 7) + i, by
      have e : qs (w + 7 + 1) = qs (w + 8) := rfl
      rw [e]; omega, by omega, hpi⟩
  · rw [← hq]
    exact not_isPrime_qs (w + 8) (by omega)

theorem boot_9 :
    nSteps opp25 9 ⟨12, default⟩ =
      some ⟨16, ⟨0, ListBlank.mk [], ListBlank.mk [0, 0, 0, 1, 1]⟩⟩ := by
  have h : nSteps opp25 9 ⟨12, default⟩ =
      some ⟨16, ⟨0, ListBlank.mk [], ListBlank.mk ([0, 0, 0, 1, 1] ++ List.replicate 1 0)⟩⟩ := rfl
  rw [h, mk_append_replicate_zero]

/-- From the blank tape the machine reaches the test event of `0` in `9` steps, with the
walker area `0 1 1`: three cells, the hole at cell `0`.  That is one cell out of step with the
blocks. -/
theorem boot_ev : nSteps opp25 9 ⟨12, default⟩ = some (evCfg 0 0 0 2) := boot_9

/-- The numbers `0, …, 11` by the general lemmas, with their real verdicts: `0` and `1` move
nothing; `2`, `3`, `5` are prime and set the flag (`4`, `6`, `7` are tested with the flag set,
so their verdicts do not matter); `8`, `9`, `10` are not prime, and at `10` the hole stands at
cell `1` and moves to cell `0`; `11` is prime.  The machine is then at the start of block `7`
(`12, …, 15`), in step from here on. -/
theorem boot_block : ∃ s, nSteps opp25 s ⟨12, default⟩ = some (blockCfg 0) := by
  have h0 := ev_zero 0 0 2
  have h1 := ev_one 0 0 2
  obtain ⟨s₂, _, hs₂⟩ := finish_p0 2 0 2 (by omega) isPrime_two
  obtain ⟨s₃, _, hs₃⟩ := finish_p0 3 3 0 (by omega) (by decide)
  obtain ⟨s₅, _, hs₅⟩ := finish_p0 5 4 0 (by omega) (by decide)
  obtain ⟨s₈, _, hs₈⟩ := walk0 1 2 8 0 (by omega) (fun i hi => by
    rcases i with _ | _ | i
    · decide
    · decide
    · omega)
  obtain ⟨sa, _, hsa⟩ := ev_comp_f0_one 10 4 (by omega) (by decide)
  obtain ⟨sb, _, hsb⟩ := finish_p0 11 0 5 (by omega) (by decide)
  exact ⟨_, nSteps_bind_eq boot_ev
    (nSteps_bind_eq h0 (nSteps_bind_eq h1 (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃
      (nSteps_bind_eq hs₅ (nSteps_bind_eq hs₈ (nSteps_bind_eq hsa hsb)))))))⟩

theorem empty_or_all (N : ℕ) :
    (∃ w, ¬ HasPrime (w + 7)) ∨ ∀ w, w < N → HasPrime (w + 7) := by
  induction N with
  | zero => exact Or.inr (fun w hw => absurd hw (Nat.not_lt_zero w))
  | succ N ih =>
    rcases ih with hce | hall
    · exact Or.inl hce
    · by_cases hN : HasPrime (N + 7)
      · refine Or.inr (fun w hw => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | h
        · exact hall w h
        · subst h; exact hN
      · exact Or.inl ⟨N, hN⟩

theorem blockCfg_iter_bounded (N : ℕ) (hall : ∀ w, w < N → HasPrime (w + 7)) :
    ∃ s, N ≤ s ∧ nSteps opp25 s (blockCfg 0) = some (blockCfg N) := by
  induction N with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ N ih =>
    obtain ⟨s₁, _, hs₁⟩ := ih (fun w hw => hall w (Nat.lt_succ_of_lt hw))
    obtain ⟨s₂, _, hs₂⟩ := blockCfg_advance N (hall N (Nat.lt_succ_self N))
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem blockCfg_reach_or_halt (w : ℕ) :
    (∃ s, nSteps opp25 s (blockCfg 0) = some (blockCfg w)) ∨
    (∃ s c, nSteps opp25 s (blockCfg 0) = some c ∧ step opp25 c = none) := by
  induction w with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ w ih =>
    rcases ih with ⟨s₁, hs₁⟩ | hhalt
    · by_cases hw : HasPrime (w + 7)
      · obtain ⟨s₂, _, hs₂⟩ := blockCfg_advance w hw
        exact Or.inl ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
      · obtain ⟨s₂, c, hs₂, hnone⟩ := blockCfg_halt w hw
        exact Or.inr ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
    · exact Or.inr hhalt

theorem halts_opp25_iff :
    (eval (step opp25) ⟨12, default⟩).Dom ↔ ∃ w : ℕ, ¬ HasPrime (w + 7) := by
  obtain ⟨s0, hboot⟩ := boot_block
  rw [nSteps_eval_dom hboot]
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases empty_or_all (k + 1) with hce | hall
    · exact hce
    · obtain ⟨s, hks, hs⟩ := blockCfg_iter_bounded (k + 1) hall
      have h_eq_none := nSteps_eq_none_of_step_none s hk hnone (by omega)
      rw [h_eq_none] at hs
      cases hs
  · rintro ⟨w, hw⟩
    have h_halt : ∃ s c, nSteps opp25 s (blockCfg 0) = some c ∧ step opp25 c = none := by
      rcases blockCfg_reach_or_halt w with ⟨s₁, hs₁⟩ | hhalt
      · obtain ⟨s₂, c, hs₂, hnone⟩ := blockCfg_halt w hw
        exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
      · exact hhalt
    obtain ⟨s, c, hs, hnone⟩ := h_halt
    rw [Part.dom_iff_mem]
    exact ⟨c, mem_eval'.mpr ⟨nSteps_reaches hs, hnone⟩⟩

/-- No prime strictly between `n ^ 2 - n` and `n ^ 2`. -/
def EmptyLeft (n : ℕ) : Prop := ∀ x, n * n - n < x → x < n * n → ¬ IsPrime x

/-- No prime strictly between `n ^ 2` and `n ^ 2 + n`. -/
def EmptyRight (n : ℕ) : Prop := ∀ x, n * n < x → x < n * n + n → ¬ IsPrime x

/-- The two half-intervals of `n = 2` and `n = 3` have the primes `3`, `5`, `7`, `11`. -/
theorem small_cases (n : ℕ) (hn : 2 ≤ n) (h : EmptyLeft n ∨ EmptyRight n) : 4 ≤ n := by
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · exfalso
    obtain rfl | rfl : n = 2 ∨ n = 3 := by omega
    · rcases h with h | h
      · exact h 3 (by decide) (by decide) (by decide)
      · exact h 5 (by decide) (by decide) (by decide)
    · rcases h with h | h
      · exact h 7 (by decide) (by decide) (by decide)
      · exact h 11 (by decide) (by decide) (by decide)
  · exact hge

/-- **Main theorem.**  The 22-state machine halts on the blank tape if and only if some
`n ≥ 2` has no prime strictly between `n ^ 2 - n` and `n ^ 2`, or none strictly between
`n ^ 2` and `n ^ 2 + n`. -/
theorem halts_oppermann22_iff :
    ConjectureMachines.Halts oppermann22 ↔ ∃ n, 2 ≤ n ∧ (EmptyLeft n ∨ EmptyRight n) := by
  rw [halts_iff_opp25, halts_opp25_iff]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨m, hm⟩ : ∃ m, w + 7 = 2 * m ∨ w + 7 = 2 * m + 1 := ⟨(w + 7) / 2, by omega⟩
    have hsq := sq_succ m
    rcases hm with hm | hm
    · -- block `2 m` is `m², …, m² + m - 1`: the right half-interval of `m`
      refine ⟨m, by omega, Or.inr (fun x hx1 hx2 hx3 => hw ⟨x, ?_, ?_, hx3⟩)⟩
      · rw [hm, qs_odd]; exact hx2
      · rw [hm, qs_even]; omega
    · -- block `2 m + 1` is `m² + m, …, (m + 1)² - 1`: the left half-interval of `m + 1`
      refine ⟨m + 1, by omega, Or.inl (fun x hx1 hx2 hx3 => hw ⟨x, ?_, ?_, hx3⟩)⟩
      · have e : w + 7 + 1 = 2 * (m + 1) := by omega
        rw [e, qs_even]; exact hx2
      · rw [hm, qs_odd]; omega
  · rintro ⟨n, hn, hE⟩
    have hn4 := small_cases n hn hE
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsq := sq_succ m
    rcases hE with hE | hE
    · -- left half-interval of `m + 1` = block `2 m + 1`
      refine ⟨2 * m + 1 - 7, ?_⟩
      have e : 2 * m + 1 - 7 + 7 = 2 * m + 1 := by omega
      rw [e]
      rintro ⟨x, hx1, hx2, hx3⟩
      have e2 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      rw [e2, qs_even] at hx1
      rw [qs_odd] at hx2
      rcases Nat.eq_or_lt_of_le hx2 with heq | hlt
      · have hnp := not_isPrime_qs (2 * m + 1) (by omega)
        rw [qs_odd, heq] at hnp
        exact hnp hx3
      · exact hE x (by omega) hx1 hx3
    · -- right half-interval of `m + 1` = block `2 (m + 1)`
      refine ⟨2 * (m + 1) - 7, ?_⟩
      have e : 2 * (m + 1) - 7 + 7 = 2 * (m + 1) := by omega
      rw [e]
      rintro ⟨x, hx1, hx2, hx3⟩
      rw [qs_odd] at hx1
      rw [qs_even] at hx2
      rcases Nat.eq_or_lt_of_le hx2 with heq | hlt
      · have hnp := not_isPrime_qs (2 * (m + 1)) (by omega)
        rw [qs_even, heq] at hnp
        exact hnp hx3
      · exact hE x hlt hx1 hx3

end ConjectureMachines.Oppermann22
