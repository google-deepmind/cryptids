/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Goldbach21

/-!
# Legendre21

The 21-state Turing machine `legendre_21` halts on the blank tape if and only if Legendre's
conjecture fails: some `n ≥ 1` has no prime strictly between `n ^ 2` and `(n + 1) ^ 2`.

## Provenance and Attribution

The machine and the proofs are by Daniel Veljjanoski, with Claude (Anthropic) as assistant
(November 2026). The primality test is the one of the Goldbach machines: the anonymous 2016
machine, Andrew Yao and Yijun Leng's `goldbach_25` (2024), and `goldbach_21` of Maxence Faldor
and Moritz Firsching (2026), whose lemmas in `Cryptids/Goldbach21.lean` this file uses. An
earlier machine for the same conjecture is Charlie Reams's 44-state machine with a Lean proof
(`calr3/tinycryptids`, November 2026).

## Machine Layout

States `0`–`20` of the table are `q14, q0, q3, q4, q6, q7, q9, q11, q12, q13, q15, q16, q20, q22,
q23, q24, A1, B, C, Z1, X`; `q0`–`q24` are the numbers of the same states in
`Goldbach21.edited`. The tape holds, left to right, a block of ones for the number under test,
a separator `0`, a flag cell, and a walker area of ones with one hole. The tape left of the
block stays blank; the block grows to the left.

* Test (the sixteen `q` states): `q16` reading the blank left of a block of `t` ones writes a
  `1` (the block now has `t + 1` cells) and enters the trial division of `t`. A prime leaves
  `q6` on the separator; a composite leaves `q6` on the flag cell, through `A1`. The block is
  restored in both cases.
* Walker (`B`, `C`, `Z1`): after each test `B` runs right to the hole and fills it, `C` opens a
  hole one cell further left, `Z1` runs back, and `q3`, `q4`, `q16` return to the left end of
  the block, where the next number is tested.
* Interval `n` is `n ^ 2, …, n ^ 2 + 2 n`. It starts with the flag clear and `2 n` ones in the
  walker area (the blank beyond them is the hole). The first prime of the interval sets the
  flag, moves the separator one cell left, and is tested once more. When the hole reaches the
  left end with the flag set, it moves into the flag cell: the flag is clear again and the
  walker area has `2 n + 2` ones, the start of interval `n + 1`. When the hole reaches the left
  end with the flag clear after a composite, `C` reads the flag, `X` reads the separator, and
  the machine halts: `X` reading `0` is the one undefined cell.
* Start: `q14` (state `0`) on the blank tape. After `17` steps the machine is at the test of `1`
  with the walker area `1 0 1`. No state is used for the start only.

## Proof Outline

`leg25` is the machine in the 25-state numbering of `Goldbach21.edited` (`A1, B, C, Z1, X`
take the numbers `1, 2, 5, 8, 10`, which are free in our table), so the step and scan lemmas
and the machine-generic pass lemmas of `Cryptids/Goldbach21.lean` apply unchanged; the lemmas
stated there for `edited` only are proved again for `leg25`.
-/

@[expose] public section

namespace ConjectureMachines.Legendre21

open Turing (Dir)
open StateTransition
open Goldbach21

/-- 21-state Legendre machine (`legendre_21`). -/
abbrev legendre21 : Machine 21 2 := Machines.legendre21

/-- `legendre21` in the 25-state numbering of `Goldbach21.edited`: row `i` is state
`0` = `q0`, `1` = `A1`, `2` = `B`, `3` = `q3`, `4` = `q4`, `5` = `C`, `6` = `q6`, `7` = `q7`,
`8` = `Z1`, `9` = `q9`, `10` = `X`, `11` = `q11`, `12` = `q12`, `13` = `q13`, `14` = `q14`, `15`
= `q15`, `16` = `q16`, `20` = `q20`, `22` = `q22`, `23` = `q23`, `24` = `q24`;
rows `17, 18, 19, 21` are unused. -/
def leg25 : Machine 25 2 := Machine.ofRows [
  [some (0, .right, 11), some (1, .left, 22)],
  [some (0, .right, 6), some (1, .right, 1)],
  [some (1, .left, 5), some (1, .right, 2)],
  [some (0, .left, 16), some (1, .right, 4)],
  [some (0, .left, 16), some (1, .right, 6)],
  [some (1, .left, 10), some (0, .left, 8)],
  [some (0, .right, 2), some (0, .left, 7)],
  [some (1, .right, 5), some (1, .left, 22)],
  [some (0, .left, 3), some (1, .left, 8)],
  [some (1, .right, 0), some (0, .left, 9)],
  [none, some (0, .right, 2)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (1, .left, 15), some (1, .left, 14)],
  [some (1, .left, 1), some (0, .left, 23)],
  [some (1, .right, 3), some (1, .left, 16)],
  [none, none],
  [none, none],
  [none, none],
  [some (1, .left, 9), some (1, .left, 20)],
  [none, none],
  [some (0, .right, 0), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 3), some (1, .right, 24)]
]

/-- State `i` of `legendre21` is state `embed25 i` of `leg25`. -/
def embed25 (q : Fin 21) : Fin 25 :=
  ([14, 0, 3, 4, 6, 7, 9, 11, 12, 13, 15, 16, 20, 22, 23, 24, 1, 2, 5, 8, 10] :
    List (Fin 25)).getD q.val 0

theorem transition_embed25 (q : Fin 21) (a : Fin 2) :
    leg25.transition (embed25 q) a =
      (legendre21.transition q a).map fun t => (t.1, t.2.1, embed25 t.2.2) := by
  revert q a; decide

theorem step_embed25 (q : Fin 21) (T : Tape (Fin 2)) :
    step leg25 ⟨embed25 q, T⟩ =
      (step legendre21 ⟨q, T⟩).map fun c => ⟨embed25 c.state, c.tape⟩ := by
  simp only [step, transition_embed25, Option.map_map]
  rcases legendre21.transition q T.head with _ | ⟨a, d, q'⟩ <;> rfl

theorem respects_embed25 :
    Respects (step legendre21) (step leg25)
      fun c₁ c₂ => c₂ = ⟨embed25 c₁.state, c₁.tape⟩ := by
  intro c₁ c₂ h
  subst h
  obtain ⟨q, T⟩ := c₁
  rcases e : step legendre21 ⟨q, T⟩ with _ | c
  · simpa [step_embed25] using e
  · exact ⟨⟨embed25 c.state, c.tape⟩, rfl,
      Relation.TransGen.single (by simp [step_embed25, e])⟩

/-- Halting of `legendre21` is halting of `leg25` from state `14` (`q14`, the start state). -/
theorem halts_iff_leg25 :
    ConjectureMachines.Halts legendre21 ↔ (eval (step leg25) ⟨14, default⟩).Dom :=
  (tr_eval_dom' respects_embed25 rfl).symm

/-!
## The primality test in `leg25`

The test is the one of `Goldbach21.edited`.  Inside the test three things differ:
* `q21` is merged into `q9`: `(q20, 0) = 1 L q9`, and `q9` reading `0` reaches `q22` through
  `(q0, 1) = 1 L q22` (three steps instead of one, same tape);
* the entry is `(q16, 0) = 1 R q3` instead of `(q0, 1) = 1 R q3`;
* the composite exit is `(q15, 0) = 1 L A1`: `A1` runs right over the restored block and
  `(A1, 0) = 0 R q6` leaves `q6` on the cell right of the separator.

Three more cells of the test states differ from `edited`, `(q3, 0)`, `(q6, 0)` and `(q7, 0)`;
they are read only at the exits of the test and by the interval logic.

Used unchanged from `Goldbach21`: the step and scan lemmas and the machine-generic pass lemmas
`nSteps_pass_11_to_13` and `nSteps_pass_13_zero_to_15`.  The other lemmas of this section
follow the `_edit`, `cfg6E` and `cfg11E` lemmas of `Goldbach21` line by line (`pass_15_bsucc_to_6`
and `sim6_accept` word for word), stated for `leg25` and for arbitrary tape on both sides of the
block.
-/

theorem pass_13_one_to_9 (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps leg25 (1 + ((m + 1) + 1))
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) (R.cons 1)⟩ =
      some ⟨9, Tape.mkL L ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_left (b := 0) (q' := 20) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 20) (a := 1) (b := 1) rfl (m + 1) _ _) ?_
  exact step_one (step_mkL_left (b := 1) (q' := 9) rfl _ _)

theorem pass_9_b0_to_11 (A : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps leg25 (3 + (A + (2 + A)))
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
    nSteps leg25 (1 + (b + (2 + b)))
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
    nSteps leg25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (3 + (A + (2 + A)))))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (pass_13_one_to_9 m _ _)
      (pass_9_b0_to_11 A _ _))

theorem pass_11_bsucc (A b m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps leg25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (2 + b)))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (pass_13_one_to_9 m _ _)
      (pass_9_bsucc_to_11 A b _ _))

theorem pass_15_bsucc_to_6 (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps leg25 (1 + (b + (1 + (b + 3))))
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
    nSteps leg25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (1 + (b + 3))))))
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
    nSteps leg25 (2 + ((m + 3) + 1))
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
    nSteps leg25 ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (2 + ((m + 3) + 1))))
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
    nSteps leg25 (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + 1))))))
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
    step_mkL_right (M := leg25) (q := 9) (q' := 0) (a := 0) (b := 1) rfl
      (L_base.cons 0) (ListBlank.append (0 :: List.replicate k 0) (((R_rest.cons 0).cons 1).cons 1))

theorem sim6_accept (k : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    nSteps leg25 (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (1 + (k + 3))))))))
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
      nSteps leg25 s (tcfg11 L R A 0 m (r' + 1)) = some (tcfg11 L R 0 A (m + 1) r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1) 1) (R.cons 0) =
      (ListBlank.append (List.replicate r' 1) (R.cons 0)).cons 1 := rfl
  unfold tcfg11
  rw [h_rep]
  have h := pass_11_b0 A (m + 1) L (ListBlank.append (List.replicate r' 1) (R.cons 0))
  exact ⟨_, by omega, h⟩

theorem tcfg11_step_bsucc (L R : ListBlank (Fin 2)) (A b m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps leg25 s (tcfg11 L R A (b + 1) m (r' + 1)) =
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
      ∃ s, nSteps leg25 s (tcfg11 L R A B m r) = some (tcfg11 L R A' B' (m + r) 0) := by
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
      nSteps leg25 s (tcfg6 L R k (r' + 1)) = some (tcfg11 L R 1 k 0 r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1 + 1) 1) (R.cons 0) =
      ((ListBlank.append (List.replicate r' 1) (R.cons 0)).cons 1).cons 1 := rfl
  unfold tcfg6 tcfg11
  rw [h_rep]
  have h1 := sim6_d k L (ListBlank.append (List.replicate r' 1) (R.cons 0))
  have h0_to_11 (L_b R_m : ListBlank (Fin 2)) :
      nSteps leg25 (1 + k)
        ⟨0, Tape.mk' ((L_b.cons 0).cons 1)
          (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_m)⟩ =
        some ⟨11, Tape.mk' (counterTape 1 k L_b) (R_m.cons 1)⟩ := by
    rw [ListBlank.append, ListBlank.append_assoc, ListBlank.append, ListBlank.append]
    refine nSteps_bind_eq (step_one
      (step_mk'_right (M := leg25) (q := 0) (q' := 11) (a := 0) (b := 0) rfl _ _)) ?_
    exact nSteps_mk'_right_scan (M := leg25) (q := 11) (a := 0) (b := 1) rfl k _ _
  have h := nSteps_bind_eq h1 (h0_to_11 L _)
  exact ⟨_, by omega, h⟩

theorem tcfg6_pass_succ_dvd (L R : ListBlank (Fin 2)) (k r' : ℕ)
    (hdvd : (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps leg25 s (tcfg6 L R k (r' + 1)) = some (testExit L R false (k + 4 + r')) := by
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
      nSteps leg25 ((1 + (r' + 1 + 1)) + ((1 + ((r' + 1 + 1) + 1)) + (2 + ((r' + 1 + 3) + 1))))
        (tcfg11 L R (k + 1) 0 r' 0) = some (testExit L R false (k + 4 + r')) := by
    unfold tcfg11 testExit
    simpa [List.replicate_zero, ListBlank.append, h_p] using h_fin
  exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem tcfg6_pass_succ_not_dvd (L R : ListBlank (Fin 2)) (k r' : ℕ)
    (hdvd : ¬ (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps leg25 s (tcfg6 L R k (r' + 1)) = some (tcfg6 L R (k + 1) r') := by
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
        nSteps leg25 ((1 + (r' + 1 + 1)) + ((1 + ((r' + 1 + 1) + 1)) + (1 + (b + (1 + (b + 3))))))
          (tcfg11 L R A' (b + 1) r' 0) = some (tcfg6 L R (k + 1) r') := by
      unfold tcfg11 tcfg6
      simpa [List.replicate_zero, ListBlank.append, h_k] using h_fin
    exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem tcfg6_eval (L R : ListBlank (Fin 2)) (k r : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps leg25 s (tcfg6 L R k r) =
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
    nSteps leg25 3 ⟨16, Tape.mkL (L.cons 0) (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L.cons 1).cons 1).cons 1) (R.cons 0)⟩ :=
  step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl L (((R.cons 0).cons 1).cons 1))
    (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L.cons 1) ((R.cons 0).cons 1))
      (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L.cons 1).cons 1) (R.cons 0))))

theorem enter_ge3 (L R : ListBlank (Fin 2)) :
    nSteps leg25 3 ⟨16, Tape.mkL (L.cons 0) (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L.cons 1).cons 1).cons 1) (R.cons 1)⟩ :=
  step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl L (((R.cons 1).cons 1).cons 1))
    (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L.cons 1) ((R.cons 1).cons 1))
      (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L.cons 1).cons 1) (R.cons 1))))

/-- **The test.**  From the test event of `t ≥ 2` the machine reaches the exit that says
whether `t` is prime, with the block (now `t + 1` ones) restored and `L`, `R` untouched. -/
theorem test_eval (L R : ListBlank (Fin 2)) (t : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧
      nSteps leg25 s (testCfg L R t) = some (testExit L R (decide (IsPrime t)) t) := by
  rcases Nat.eq_or_lt_of_le ht with rfl | ht3
  · rw [decide_eq_true isPrime_two]
    have h2 := enter_two (L.cons 0) R
    refine ⟨3, by omega, ?_⟩
    unfold testCfg testExit
    exact h2
  · obtain ⟨r0, rfl⟩ : ∃ r0, t = r0 + 3 := ⟨t - 3, by omega⟩
    have h_enter : nSteps leg25 3 (testCfg L R (r0 + 3)) = some (tcfg6 L R 0 r0) :=
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
## Interval logic

Right of the block: the separator `0`, the flag cell `f`, and the walker area `walkerTape h r`
(`h` ones, a hole, `r` ones; the blank beyond `walkerTape h 0` is the hole).  After a test `B` runs
right to the hole and fills it, `C` opens a hole one cell further left, `Z1` runs back.

* composite, flag clear, hole not at the left end: next number;
* composite, flag clear, hole at the left end: `C` reads the clear flag, `X` reads the
  separator: **halt**;
* prime, flag clear: `B` sets the flag, `C` and `X` move the separator one cell left (the block
  loses a cell, the walker area gains one), and the same number is tested once more;
* flag set (prime or composite; a composite makes the four-step detour `q6 q7 C X` first):
  next number; when the hole is at the left end it moves into the flag cell, which clears the
  flag and leaves the walker area full: the next interval starts.
-/

local notation:max "ones(" n ", " L ")" => ListBlank.append (List.replicate n (1 : Fin 2)) L

theorem step_mkL_none {M : Machine 25 2} {q : Fin 25} {a : Fin 2}
    (h : M.transition q a = none) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = none := by
  simp [step, h, Tape.mkL]

/-- `B` runs right over `h + 1` ones and fills the hole, `C` opens a hole one cell to the left,
`Z1` runs back over the ones and stops on the cell left of them. -/
theorem walkB (h : ℕ) (Lf Rr : ListBlank (Fin 2)) :
    nSteps leg25 ((h + 1) + (2 + h)) ⟨2, Tape.mk' Lf ones(h + 1, Rr.cons 0)⟩ =
      some ⟨8, Tape.mkL Lf ones(h, (Rr.cons 1).cons 0)⟩ := by
  have h1 : nSteps leg25 (h + 1) ⟨2, Tape.mk' Lf ones(h + 1, Rr.cons 0)⟩ =
      some ⟨2, Tape.mk' ones(h + 1, Lf) (Rr.cons 0)⟩ :=
    nSteps_mk'_right_scan (q := 2) (a := 1) (b := 1) rfl (h + 1) Lf (Rr.cons 0)
  have h2 : nSteps leg25 2 ⟨2, Tape.mk' (ones(h, Lf).cons 1) (Rr.cons 0)⟩ =
      some ⟨8, Tape.mkL ones(h, Lf) ((Rr.cons 1).cons 0)⟩ :=
    step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
      (step_one (step_mkL_left (b := 0) (q' := 8) rfl _ _))
  have h3 : nSteps leg25 h ⟨8, Tape.mkL ones(h, Lf) ((Rr.cons 1).cons 0)⟩ =
      some ⟨8, Tape.mkL Lf ones(h, (Rr.cons 1).cons 0)⟩ :=
    nSteps_mkL_left_scan (q := 8) (a := 1) (b := 1) rfl h Lf ((Rr.cons 1).cons 0)
  exact nSteps_bind_eq h1 (nSteps_bind_eq h2 h3)

/-- Way back when `Z1` stops on the separator: `q3` reads the last cell of the block, `q4` the
separator, `q16` runs left over the block of `n + 1` ones. -/
theorem ret_q4 (n : ℕ) (L X : ListBlank (Fin 2)) :
    nSteps leg25 (3 + (n + 1)) ⟨8, Tape.mkL (ones(n + 1, L.cons 0).cons 0) X⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ones(n + 1, X.cons 0)⟩ := by
  have h1 : nSteps leg25 3 ⟨8, Tape.mkL ((ones(n, L.cons 0).cons 1).cons 0) X⟩ =
      some ⟨16, Tape.mkL (ones(n, L.cons 0).cons 1) (X.cons 0)⟩ :=
    step_nSteps (step_mkL_left (b := 0) (q' := 3) rfl _ _)
      (step_nSteps (step_mkL_right (b := 1) (q' := 4) rfl _ _)
        (step_one (step_mk'_left (b := 0) (q' := 16) rfl _ _)))
  have h2 : nSteps leg25 (n + 1) ⟨16, Tape.mkL ones(n + 1, L.cons 0) (X.cons 0)⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ones(n + 1, X.cons 0)⟩ :=
    nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl (n + 1) (L.cons 0) (X.cons 0)
  exact nSteps_bind_eq h1 h2

/-- Way back when `Z1` stops on the clear flag: `q3` reads the separator, `q16` runs left over
the block of `m` ones. -/
theorem ret_q3 (m : ℕ) (Lz X : ListBlank (Fin 2)) :
    nSteps leg25 (2 + m) ⟨8, Tape.mkL ((ones(m, Lz).cons 0).cons 0) X⟩ =
      some ⟨16, Tape.mkL Lz ones(m, (X.cons 0).cons 0)⟩ := by
  have h1 : nSteps leg25 2 ⟨8, Tape.mkL ((ones(m, Lz).cons 0).cons 0) X⟩ =
      some ⟨16, Tape.mkL ones(m, Lz) ((X.cons 0).cons 0)⟩ :=
    step_nSteps (step_mkL_left (b := 0) (q' := 3) rfl _ _)
      (step_one (step_mkL_left (b := 0) (q' := 16) rfl _ _))
  exact nSteps_bind_eq h1
    (nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl m Lz ((X.cons 0).cons 0))

/-- The detour of a composite exit with the flag set: `q6` clears the flag, `q7` marks the
separator, `C` and `X` put both back; `B` is then on the set flag. -/
theorem detour (Lm Y : ListBlank (Fin 2)) :
    nSteps leg25 4 ⟨6, Tape.mk' (Lm.cons 0) (Y.cons 1)⟩ =
      some ⟨2, Tape.mk' (Lm.cons 0) (Y.cons 1)⟩ :=
  step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
    (step_nSteps (step_mkL_right (b := 1) (q' := 5) rfl _ _)
      (step_nSteps (step_mk'_left (b := 1) (q' := 10) rfl _ _)
        (step_one (step_mkL_right (b := 0) (q' := 2) rfl _ _))))

/-- The walker area: `h` ones, a hole, `r` ones, then blank. -/
def walkerTape (h r : ℕ) : ListBlank (Fin 2) := ones(h, ones(r, B0).cons 0)

theorem walkerTape_zero (h : ℕ) : walkerTape h 0 = ones(h, B0) :=
  congrArg (fun l : ListBlank (Fin 2) => ones(h, l)) B0_cons_zero

theorem comp_f0_succ (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps leg25 (1 + (((h + 1) + (2 + h)) + (2 + (t + 1))))
      (testExit L ((walkerTape (h + 1) r).cons 0) false t) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ((walkerTape h (r + 1)).cons 0).cons 0)⟩ := by
  have h1 : nSteps leg25 1
      ⟨6, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((walkerTape (h + 1) r).cons 0)⟩ =
      some ⟨2, Tape.mk' ((ones(t + 1, L.cons 0).cons 0).cons 0) (walkerTape (h + 1) r)⟩ :=
    step_one (step_mk'_right (b := 0) (q' := 2) rfl _ _)
  have h2 := walkB h ((ones(t + 1, L.cons 0).cons 0).cons 0) ones(r, B0)
  have h3 := ret_q3 (t + 1) (L.cons 0) ones(h, (ones(r, B0).cons 1).cons 0)
  unfold testExit
  exact nSteps_bind_eq h1 (nSteps_bind_eq h2 h3)

theorem comp_f0_zero (L : ListBlank (Fin 2)) (t r : ℕ) :
    ∃ c, nSteps leg25 3 (testExit L ((walkerTape 0 r).cons 0) false t) = some c ∧
      step leg25 c = none := by
  have h1 : nSteps leg25 3
      ⟨6, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((ones(r, B0).cons 0).cons 0)⟩ =
      some ⟨10, Tape.mkL (ones(t + 1, L.cons 0).cons 0) ((ones(r, B0).cons 1).cons 1)⟩ :=
    step_nSteps (step_mk'_right (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
        (step_one (step_mkL_left (b := 1) (q' := 10) rfl _ _)))
  unfold testExit
  exact ⟨_, h1, step_mkL_none rfl _ _⟩

/-- `B` on the set flag, the separator on its left: one walker step and back to `q16`. -/
theorem flag1_pass (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps leg25 (((h + 1) + (2 + h)) + (3 + (t + 1)))
      ⟨2, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((walkerTape h r).cons 1)⟩ =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ones(h, ones(r + 1, B0).cons 0).cons 0)⟩ := by
  have h2 := walkB h (ones(t + 1, L.cons 0).cons 0) ones(r, B0)
  have h3 := ret_q4 t L ones(h, (ones(r, B0).cons 1).cons 0)
  exact nSteps_bind_eq h2 h3

theorem comp_f1 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps leg25 (4 + (((h + 1) + (2 + h)) + (3 + (t + 1))))
      (testExit L ((walkerTape h r).cons 1) false t) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ones(h, ones(r + 1, B0).cons 0).cons 0)⟩ := by
  have h1 := detour ones(t + 1, L.cons 0) (walkerTape h r)
  unfold testExit
  exact nSteps_bind_eq h1 (flag1_pass L t h r)

theorem prime_f1 (L : ListBlank (Fin 2)) (t h r : ℕ) :
    nSteps leg25 (1 + (((h + 1) + (2 + h)) + (3 + (t + 1))))
      (testExit L ((walkerTape h r).cons 1) true t) =
      some ⟨16, Tape.mkL (L.cons 0) ones(t + 1, ones(h, ones(r + 1, B0).cons 0).cons 0)⟩ := by
  have h1 : nSteps leg25 1
      ⟨6, Tape.mk' ones(t + 1, L.cons 0) (((walkerTape h r).cons 1).cons 0)⟩ =
      some ⟨2, Tape.mk' (ones(t + 1, L.cons 0).cons 0) ((walkerTape h r).cons 1)⟩ :=
    step_one (step_mk'_right (b := 0) (q' := 2) rfl _ _)
  unfold testExit
  exact nSteps_bind_eq h1 (flag1_pass L t h r)

/-- First prime of an interval (flag clear): the flag is set, the separator moves one cell
left, and the machine is back at the test event of the same number `n + 1`. -/
theorem prime_f0 (L : ListBlank (Fin 2)) (n h r : ℕ) :
    nSteps leg25 (4 + (((h + 1 + 1) + (2 + (h + 1))) + (3 + (n + 1))))
      (testExit L ((walkerTape h r).cons 0) true (n + 1)) =
      some ⟨16, Tape.mkL (L.cons 0) ones(n + 1, ((walkerTape h (r + 1)).cons 1).cons 0)⟩ := by
  have h1 : nSteps leg25 4
      ⟨6, Tape.mk' (ones(n + 1, L.cons 0).cons 1) (((walkerTape h r).cons 0).cons 0)⟩ =
      some ⟨2, Tape.mk' (ones(n + 1, L.cons 0).cons 0) (((walkerTape h r).cons 1).cons 1)⟩ :=
    step_nSteps (step_mk'_right (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mk'_left (b := 1) (q' := 5) rfl _ _)
        (step_nSteps (step_mkL_left (b := 1) (q' := 10) rfl _ _)
          (step_one (step_mkL_right (b := 0) (q' := 2) rfl _ _))))
  have h2 := walkB (h + 1) (ones(n + 1, L.cons 0).cons 0) ones(r, B0)
  have h3 := ret_q4 n L ones(h + 1, (ones(r, B0).cons 1).cons 0)
  unfold testExit
  exact nSteps_bind_eq h1 (nSteps_bind_eq h2 h3)

/-- The number `1`: `q3` and `q4` send `q16` straight back; nothing right of the block moves. -/
theorem testCfg_one (L R : ListBlank (Fin 2)) :
    nSteps leg25 5 (testCfg L R 1) = some ⟨16, Tape.mkL (L.cons 0) ones(2, R.cons 0)⟩ := by
  have h1 : nSteps leg25 3 ⟨16, Tape.mkL ((L.cons 0).cons 0) ((R.cons 0).cons 1)⟩ =
      some ⟨16, Tape.mkL (((L.cons 0).cons 1).cons 1) (R.cons 0)⟩ :=
    step_nSteps (step_mkL_right (b := 1) (q' := 3) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _)
        (step_one (step_mk'_left (b := 0) (q' := 16) rfl _ _)))
  have h2 : nSteps leg25 2 ⟨16, Tape.mkL ones(2, L.cons 0) (R.cons 0)⟩ =
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
      nSteps leg25 s (evCfg t f h r) =
        some (testExit B0 ((walkerTape h r).cons f) (decide (IsPrime t)) t) := by
  have h0 := test_eval B0 ((walkerTape h r).cons f) t ht
  rw [testCfg_B0] at h0
  exact h0

theorem ev_one (f : Fin 2) (h r : ℕ) : nSteps leg25 5 (evCfg 1 f h r) = some (evCfg 2 f h r) := by
  have h0 := testCfg_one B0 ((walkerTape h r).cons f)
  rw [testCfg_B0] at h0
  exact h0

theorem ev_comp_f0_succ (t h r : ℕ) (ht : 2 ≤ t) (hp : ¬ IsPrime t) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (evCfg t 0 (h + 1) r) = some (evCfg (t + 1) 0 h (r + 1)) := by
  obtain ⟨s, _, hs⟩ := ev_test t 0 (h + 1) r ht
  rw [decide_eq_false hp] at hs
  exact ⟨_, by omega, nSteps_bind_eq hs (comp_f0_succ B0 t h r)⟩

theorem ev_comp_f0_zero (t r : ℕ) (ht : 2 ≤ t) (hp : ¬ IsPrime t) :
    ∃ s c, nSteps leg25 s (evCfg t 0 0 r) = some c ∧ step leg25 c = none := by
  obtain ⟨s, _, hs⟩ := ev_test t 0 0 r ht
  rw [decide_eq_false hp] at hs
  obtain ⟨c, hc, hn⟩ := comp_f0_zero B0 t r
  exact ⟨_, c, nSteps_bind_eq hs hc, hn⟩

theorem ev_f1 (t h r : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (evCfg t 1 h r) =
      some ⟨16, Tape.mkL (B0.cons 0) ones(t + 1, ones(h, ones(r + 1, B0).cons 0).cons 0)⟩ := by
  obtain ⟨s, _, hs⟩ := ev_test t 1 h r ht
  by_cases hp : IsPrime t
  · rw [decide_eq_true hp] at hs
    exact ⟨_, by omega, nSteps_bind_eq hs (prime_f1 B0 t h r)⟩
  · rw [decide_eq_false hp] at hs
    exact ⟨_, by omega, nSteps_bind_eq hs (comp_f1 B0 t h r)⟩

theorem ev_f1_succ (t h r : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (evCfg t 1 (h + 1) r) = some (evCfg (t + 1) 1 h (r + 1)) :=
  ev_f1 t (h + 1) r ht

theorem ev_f1_zero (t r : ℕ) (ht : 2 ≤ t) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (evCfg t 1 0 r) = some (evCfg (t + 1) 0 (r + 1) 0) := by
  obtain ⟨s, hs1, hs⟩ := ev_f1 t 0 r ht
  refine ⟨s, hs1, ?_⟩
  have e : evCfg (t + 1) 0 (r + 1) 0 =
      ⟨16, Tape.mkL (B0.cons 0) ones(t + 1, (ones(r + 1, B0).cons 0).cons 0)⟩ := by
    unfold evCfg
    rw [walkerTape_zero]
  rw [e]
  exact hs

theorem ev_prime_f0 (t h r : ℕ) (ht : 2 ≤ t) (hp : IsPrime t) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (evCfg t 0 h r) = some (evCfg t 1 h (r + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  obtain ⟨s, _, hs⟩ := ev_test (n + 1) 0 h r ht
  rw [decide_eq_true hp] at hs
  exact ⟨_, by omega, nSteps_bind_eq hs (prime_f0 B0 n h r)⟩

/-!
## Intervals

Interval `n` is `n ^ 2, …, n ^ 2 + 2 n`.  It starts at the event `evCfg (n * n) 0 (2 * n) 0`:
flag clear, walker area `2 n` ones.  Every test moves the hole one cell left, except the first
test of the first prime: it sets the flag and adds a cell to the walker area instead, and the
same prime is then tested again.  With a prime, the hole reaches the left end with the flag
set at the last number and the next interval starts with `2 n + 2` ones.  Without a prime the
hole reaches the left end with the flag clear at the last number, a composite: the machine halts.
-/

theorem not_isPrime_sq (n : ℕ) (hn : 2 ≤ n) : ¬ IsPrime (n * n) := by
  intro ⟨_, hnf⟩
  have h2 : n * 2 ≤ n * n := Nat.mul_le_mul_left n hn
  exact hnf n (by omega) (by omega) (Dvd.intro n rfl)

theorem sq_succ (n : ℕ) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  rw [Nat.add_mul, Nat.mul_add]; omega

/-- `j` composites in a row with the flag clear: the hole moves `j` cells left. -/
theorem walk0 (h j : ℕ) : ∀ (t r : ℕ), 2 ≤ t → (∀ i, i < j → ¬ IsPrime (t + i)) →
    ∃ s, j ≤ s ∧ nSteps leg25 s (evCfg t 0 (h + j) r) = some (evCfg (t + j) 0 h (r + j)) := by
  induction j with
  | zero => intro t r _ _; exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    intro t r ht hnp
    obtain ⟨s₁, h1, hs₁⟩ := ev_comp_f0_succ t (h + j) r ht (hnp 0 (Nat.succ_pos j))
    obtain ⟨s₂, h2, hs₂⟩ := ih (t + 1) (r + 1) (by omega) (fun i hi => by
      have h' := hnp (i + 1) (by omega)
      have e : t + 1 + i = t + (i + 1) := by omega
      rw [e]; exact h')
    refine ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ ?_⟩
    rw [hs₂]
    exact congrArg some (ev_congr 0 (by omega) rfl (by omega))

/-- `j` numbers in a row with the flag set: the hole moves `j` cells left. -/
theorem walk1 (h j : ℕ) : ∀ (t r : ℕ), 2 ≤ t →
    ∃ s, j ≤ s ∧ nSteps leg25 s (evCfg t 1 (h + j) r) = some (evCfg (t + j) 1 h (r + j)) := by
  induction j with
  | zero => intro t r _; exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    intro t r ht
    obtain ⟨s₁, h1, hs₁⟩ := ev_f1_succ t (h + j) r ht
    obtain ⟨s₂, h2, hs₂⟩ := ih (t + 1) (r + 1) (by omega)
    refine ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ ?_⟩
    rw [hs₂]
    exact congrArg some (ev_congr 1 (by omega) rfl (by omega))

/-- Interval `n` has a prime. -/
def HasPrime (n : ℕ) : Prop := ∃ x, x < (n + 1) * (n + 1) ∧ n * n < x ∧ IsPrime x

instance instDecidableHasPrime (n : ℕ) : Decidable (HasPrime n) :=
  inferInstanceAs (Decidable (∃ x, x < (n + 1) * (n + 1) ∧ n * n < x ∧ IsPrime x))

/-- An interval with a prime: from the start of interval `n` to the start of interval `n + 1`. -/
theorem cycle_adv (n : ℕ) (hn : 2 ≤ n) (hp : HasPrime n) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (evCfg (n * n) 0 (2 * n) 0) =
      some (evCfg ((n + 1) * (n + 1)) 0 (2 * (n + 1)) 0) := by
  have hsq := sq_succ n
  have h4 : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
  have hex : ∃ j, IsPrime (n * n + j) := by
    obtain ⟨x, _, hx2, hx3⟩ := hp
    have e : n * n + (x - n * n) = x := by omega
    exact ⟨x - n * n, by rw [e]; exact hx3⟩
  obtain ⟨j0, hj0, hmin⟩ :
      ∃ j0, IsPrime (n * n + j0) ∧ ∀ i, i < j0 → ¬ IsPrime (n * n + i) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj0_pos : 1 ≤ j0 := by
    rcases Nat.eq_zero_or_pos j0 with hz | hpos
    · subst hz; exact absurd hj0 (not_isPrime_sq n hn)
    · exact hpos
  have hj0_le : j0 ≤ 2 * n := by
    obtain ⟨x, hx1, hx2, hx3⟩ := hp
    have hle : j0 ≤ x - n * n := Nat.le_of_not_lt (fun hlt => hmin (x - n * n) hlt (by
      have e : n * n + (x - n * n) = x := by omega
      rw [e]; exact hx3))
    omega
  obtain ⟨h0, hh0⟩ : ∃ h0, 2 * n = h0 + j0 := ⟨2 * n - j0, by omega⟩
  obtain ⟨s₁, _, hs₁⟩ := walk0 h0 j0 (n * n) 0 (by omega) hmin
  obtain ⟨s₂, hs2, hs₂⟩ := ev_prime_f0 (n * n + j0) h0 (0 + j0) (by omega) hj0
  obtain ⟨s₃, _, hs₃⟩ := walk1 0 h0 (n * n + j0) (0 + j0 + 1) (by omega)
  obtain ⟨s₄, _, hs₄⟩ := ev_f1_zero (n * n + j0 + h0) (0 + j0 + 1 + h0) (by omega)
  refine ⟨s₁ + (s₂ + (s₃ + s₄)), by omega, ?_⟩
  have e1 : evCfg (n * n) 0 (2 * n) 0 = evCfg (n * n) 0 (h0 + j0) 0 := ev_congr 0 rfl hh0 rfl
  have e3 : evCfg (n * n + j0) 1 h0 (0 + j0 + 1) = evCfg (n * n + j0) 1 (0 + h0) (0 + j0 + 1) :=
    ev_congr 1 rfl (by omega) rfl
  have e4 : evCfg (n * n + j0 + h0 + 1) 0 (0 + j0 + 1 + h0 + 1) 0 =
      evCfg ((n + 1) * (n + 1)) 0 (2 * (n + 1)) 0 := ev_congr 0 (by omega) (by omega) rfl
  rw [e1]
  rw [e3] at hs₂
  rw [e4] at hs₄
  exact nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄))

/-- An interval without a prime: the machine halts. -/
theorem cycle_halt (n : ℕ) (hn : 2 ≤ n) (hnp : ¬ HasPrime n) :
    ∃ s c, nSteps leg25 s (evCfg (n * n) 0 (2 * n) 0) = some c ∧ step leg25 c = none := by
  have hsq := sq_succ n
  have h4 : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
  have hno : ∀ i, i < 2 * n + 1 → ¬ IsPrime (n * n + i) := by
    intro i hi hpi
    rcases Nat.eq_zero_or_pos i with hz | hpos
    · subst hz; exact not_isPrime_sq n hn hpi
    · exact hnp ⟨n * n + i, by omega, by omega, hpi⟩
  obtain ⟨s₁, _, hs₁⟩ := walk0 0 (2 * n) (n * n) 0 (by omega) (fun i hi => hno i (by omega))
  obtain ⟨s₂, c, hs₂, hc⟩ :=
    ev_comp_f0_zero (n * n + 2 * n) (0 + 2 * n) (by omega) (hno (2 * n) (by omega))
  have e1 : evCfg (n * n) 0 (2 * n) 0 = evCfg (n * n) 0 (0 + 2 * n) 0 :=
    ev_congr 0 rfl (by omega) rfl
  rw [e1]
  exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hc⟩

/-!
## Start and main theorem
-/

/-- Start of interval `w + 2`. -/
def intervalCfg (w : ℕ) : Cfg 25 2 := evCfg ((w + 2) * (w + 2)) 0 (2 * (w + 2)) 0

theorem interval_advance (w : ℕ) (h : HasPrime (w + 2)) :
    ∃ s, 1 ≤ s ∧ nSteps leg25 s (intervalCfg w) = some (intervalCfg (w + 1)) := by
  obtain ⟨s, hs1, hs⟩ := cycle_adv (w + 2) (by omega) h
  exact ⟨s, hs1, hs⟩

theorem interval_halt (w : ℕ) (h : ¬ HasPrime (w + 2)) :
    ∃ s c, nSteps leg25 s (intervalCfg w) = some c ∧ step leg25 c = none :=
  cycle_halt (w + 2) (by omega) h

theorem boot_17 :
    nSteps leg25 17 ⟨14, default⟩ =
      some ⟨16, ⟨0, ListBlank.mk [], ListBlank.mk [1, 0, 0, 1, 0, 1]⟩⟩ := rfl

/-- From the blank tape the machine reaches the test event of `1` in `17` steps, with the
walker area `1 0 1`.  The number `1` does not move the hole (`ev_one`), so the hole starts one
cell further left than at the start of a later interval. -/
theorem boot_ev : nSteps leg25 17 ⟨14, default⟩ = some (evCfg 1 0 1 1) := boot_17

/-- Interval `1` (`1, 2, 2, 3`) by the general lemmas: the machine reaches the start of
interval `2`. -/
theorem boot_interval : ∃ s, nSteps leg25 s ⟨14, default⟩ = some (intervalCfg 0) := by
  have h1 := ev_one 0 1 1
  obtain ⟨s₂, _, hs₂⟩ := ev_prime_f0 2 1 1 (by omega) isPrime_two
  obtain ⟨s₃, _, hs₃⟩ := ev_f1_succ 2 0 2 (by omega)
  obtain ⟨s₄, _, hs₄⟩ := ev_f1_zero 3 3 (by omega)
  exact ⟨_, nSteps_bind_eq boot_ev
    (nSteps_bind_eq h1 (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄)))⟩

theorem empty_or_all (N : ℕ) :
    (∃ w, ¬ HasPrime (w + 2)) ∨ ∀ w, w < N → HasPrime (w + 2) := by
  induction N with
  | zero => exact Or.inr (fun w hw => absurd hw (Nat.not_lt_zero w))
  | succ N ih =>
    rcases ih with hce | hall
    · exact Or.inl hce
    · by_cases hN : HasPrime (N + 2)
      · refine Or.inr (fun w hw => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | h
        · exact hall w h
        · subst h; exact hN
      · exact Or.inl ⟨N, hN⟩

theorem interval_iter_bounded (N : ℕ) (hall : ∀ w, w < N → HasPrime (w + 2)) :
    ∃ s, N ≤ s ∧ nSteps leg25 s (intervalCfg 0) = some (intervalCfg N) := by
  induction N with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ N ih =>
    obtain ⟨s₁, _, hs₁⟩ := ih (fun w hw => hall w (Nat.lt_succ_of_lt hw))
    obtain ⟨s₂, _, hs₂⟩ := interval_advance N (hall N (Nat.lt_succ_self N))
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem interval_reach_or_halt (w : ℕ) :
    (∃ s, nSteps leg25 s (intervalCfg 0) = some (intervalCfg w)) ∨
    (∃ s c, nSteps leg25 s (intervalCfg 0) = some c ∧ step leg25 c = none) := by
  induction w with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ w ih =>
    rcases ih with ⟨s₁, hs₁⟩ | hhalt
    · by_cases hw : HasPrime (w + 2)
      · obtain ⟨s₂, _, hs₂⟩ := interval_advance w hw
        exact Or.inl ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
      · obtain ⟨s₂, c, hs₂, hnone⟩ := interval_halt w hw
        exact Or.inr ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
    · exact Or.inr hhalt

theorem halts_leg25_iff :
    (eval (step leg25) ⟨14, default⟩).Dom ↔ ∃ w : ℕ, ¬ HasPrime (w + 2) := by
  obtain ⟨s0, hboot⟩ := boot_interval
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
    · obtain ⟨s, hks, hs⟩ := interval_iter_bounded (k + 1) hall
      have h_eq_none := nSteps_eq_none_of_step_none s hk hnone (by omega)
      rw [h_eq_none] at hs
      cases hs
  · rintro ⟨w, hw⟩
    have h_halt : ∃ s c, nSteps leg25 s (intervalCfg 0) = some c ∧ step leg25 c = none := by
      rcases interval_reach_or_halt w with ⟨s₁, hs₁⟩ | hhalt
      · obtain ⟨s₂, c, hs₂, hnone⟩ := interval_halt w hw
        exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
      · exact hhalt
    obtain ⟨s, c, hs, hnone⟩ := h_halt
    rw [Part.dom_iff_mem]
    exact ⟨c, mem_eval'.mpr ⟨nSteps_reaches hs, hnone⟩⟩

/-- No prime strictly between `n ^ 2` and `(n + 1) ^ 2`. -/
def EmptyInterval (n : ℕ) : Prop := ∀ x, n * n < x → x < (n + 1) * (n + 1) → ¬ IsPrime x

/-- **Main theorem.**  The 21-state machine halts on the blank tape if and only if some
`n ≥ 1` has no prime strictly between `n ^ 2` and `(n + 1) ^ 2`. -/
theorem halts_legendre21_iff :
    ConjectureMachines.Halts legendre21 ↔ ∃ n, 1 ≤ n ∧ EmptyInterval n := by
  rw [halts_iff_leg25, halts_leg25_iff]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w + 2, by omega, fun x hx1 hx2 hx3 => hw ⟨x, hx2, hx1, hx3⟩⟩
  · rintro ⟨n, hn, hE⟩
    have hn2 : 2 ≤ n := by
      rcases Nat.eq_or_lt_of_le hn with h | h
      · subst h; exact absurd isPrime_two (hE 2 (by omega) (by omega))
      · exact h
    obtain ⟨w, rfl⟩ : ∃ w, n = w + 2 := ⟨n - 2, by omega⟩
    exact ⟨w, fun ⟨x, hx1, hx2, hx3⟩ => hE x hx2 hx1 hx3⟩

end ConjectureMachines.Legendre21
