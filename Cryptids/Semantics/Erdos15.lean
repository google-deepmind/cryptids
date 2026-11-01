/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Erdos15
public import Cryptids.Propositions

/-!
# Semantics of the Erdős Powers-of-Two Turing Machine (`erdos_15`)

This file proves that the 15-state Turing machine `erdos15` (`erdos_15`) halts on the blank tape
if and only if Erdős's conjecture on powers of two is false (i.e., there exists `n > 8` such that
the base-3 expansion of `2 ^ n` has no digit `2`).

`Cryptids.Erdos15` proves `Halts erdos15 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n` without `Classical.choice`,
where `pw n` is the digit list of `2 ^ n` computed by repeated doubling. This file identifies
`pw n` with Mathlib's `Nat.digits 3 (2 ^ n)`, whose definition and lemmas use `Classical.choice`.
The negated form `¬ ErdosPowersOfTwoConjecture` also uses Markov's Principle (`not_forall`), as
for `¬ GoldbachConjecture`.

## Provenance and Attribution

* Tristan Stérin and Damien Woods, *Hardness of busy beaver value BB(15)*
  (<https://arxiv.org/abs/2107.12475>, 2021; machine file in <https://github.com/tcosmo/bbsim>):
  the machine and its pen-and-paper correctness proof.
* Paul Erdős, *Some unconventional problems in number theory*, Math. Mag. 52 (1979): the
  conjecture.
-/

@[expose] public section

namespace ConjectureMachines.Erdos15

/-- Doubling with carry `c ≤ 1` on base-3 digit lists agrees with `Nat.digits`. -/
theorem dbl_digits (x c : ℕ) (hc : c ≤ 1) :
    dbl (Nat.digits 3 x) c = Nat.digits 3 (2 * x + c) := by
  induction x using Nat.strong_induction_on generalizing c with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
      · simp [dbl]
      · simp [dbl]
    · rw [Nat.digits_def' (by omega) hx, dbl, ih (x / 3) (by omega) _ (by omega),
        Nat.digits_def' (b := 3) (n := 2 * x + c) (by omega) (by omega)]
      have e₁ : (2 * (x % 3) + c) % 3 = (2 * x + c) % 3 := by omega
      have e₂ : 2 * (x / 3) + (2 * (x % 3) + c) / 3 = (2 * x + c) / 3 := by omega
      rw [e₁, e₂]

/-- `pw n` is the list of base-3 digits of `2 ^ n`, least significant first. -/
theorem pw_eq (n : ℕ) : pw n = Nat.digits 3 (2 ^ n) := by
  induction n with
  | zero => simp [pw]
  | succ n ih => rw [pw, ih, dbl_digits _ _ (by omega), pow_succ, Nat.mul_comm, Nat.add_zero]

/-- The 15-state machine `erdos15` (`erdos_15`) halts on the blank tape if and only if some
power `2 ^ n` with `n > 8` has no digit `2` in base `3`. -/
theorem halts_erdos15_iff_exists_counterexample :
    ConjectureMachines.Halts erdos15 ↔ ∃ n : ℕ, 8 < n ∧ 2 ∉ Nat.digits 3 (2 ^ n) := by
  simp only [← pw_eq]
  exact halts_erdos15_iff_exists_free

/-- The 15-state machine `erdos15` (`erdos_15`) halts on the blank tape if and only if Erdős's
conjecture on powers of two is false. -/
theorem halts_erdos15_iff_not_erdosPowersOfTwo :
    ConjectureMachines.Halts erdos15 ↔ ¬ ErdosPowersOfTwoConjecture := by
  rw [halts_erdos15_iff_exists_counterexample]
  simp only [ErdosPowersOfTwoConjecture, not_forall, exists_prop]

end ConjectureMachines.Erdos15
