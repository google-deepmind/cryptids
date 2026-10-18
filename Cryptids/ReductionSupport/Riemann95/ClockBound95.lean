/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104

@[expose] public section

namespace ConjectureMachines.Riemann95.Algorithm

open ConjectureMachines.Riemann120

/-- A linear upper bound for the finite quartering clock. -/
theorem five_mul_quarterClock_le (j : ℕ) : 5 * quarterClock j ≤ j + 5 := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [quarterClock]
    | succ n =>
      by_cases hn : n < 5
      · interval_cases n <;> norm_num [quarterClock]
      · have hdiv : n / 4 < n + 1 :=
          Nat.lt_succ_of_le (Nat.div_le_self n 4)
        have hclock := ih (n / 4) hdiv
        rw [quarterClock]
        omega

/-- The stage padding bound; positivity is necessary for the fixed floor 16. -/
theorem width_padding_le (j : ℕ) (hj : 1 ≤ j) :
    max 16 (10 + 5 * quarterClock j) + 5 ≤ j + 20 := by
  have hclock := five_mul_quarterClock_le j
  have hmax : max 16 (10 + 5 * quarterClock j) ≤ j + 15 :=
    max_le (by omega) (by omega)
  omega

/-- A uniform padding form that also covers the zero-clock input. -/
theorem width_padding_le_max (j : ℕ) :
    max 16 (10 + 5 * quarterClock j) + 5 ≤ max 21 (j + 20) := by
  by_cases hj : 1 ≤ j
  · exact le_trans (width_padding_le j hj) (le_max_right _ _)
  · have hz : j = 0 := by omega
    subst j
    norm_num [quarterClock]

end ConjectureMachines.Riemann95.Algorithm
