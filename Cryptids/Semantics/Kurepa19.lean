/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Kurepa19
public import Cryptids.Propositions

/-!
# Semantics of `kurepa_19`

`Halts kurepa19 ↔ ∃ n, 2 < n ∧ n ∣ leftFactorial n`: the machine's test `2 S ∣ !S` for `S ≥ 2`
(`Cryptids/Kurepa19.lean`) finds exactly the counterexamples to Kurepa's conjecture. An `S > 2`
with `2 S ∣ !S` is one, and `S = 2` never passes (`4 ∤ !2 = 2`). Conversely, an odd
counterexample `n` passes the test itself, because `!n` is even; an even one, `n = 2 j`, has
`j > 2` (`4 ∤ !4 = 10`), and `j` is a counterexample again, because `j ∣ n ∣ !n` and `j ∣ k!`
for `k ≥ j` give `j ∣ !j`; this is repeated until the counterexample is odd. Hence
`Halts kurepa19 ↔ ¬ KurepaConjecture`. The same reduction gives the
form with odd primes, `halts_kurepa19_iff_exists_prime`.
-/

@[expose] public section

namespace ConjectureMachines.Kurepa19

/-- `leftFact` of `Cryptids/Kurepa19.lean` is `leftFactorial` of `Cryptids/Propositions.lean`. -/
theorem leftFact_eq_leftFactorial (n : ℕ) : leftFact n = leftFactorial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [leftFact, leftFactorial, ih]

/-- `leftFactorial` is the sum `0! + 1! + ⋯ + (n - 1)!`. -/
theorem leftFactorial_eq_sum (n : ℕ) :
    leftFactorial n = ∑ i ∈ Finset.range n, i.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [leftFactorial, Finset.sum_range_succ, ih]

/-- `!S` is even for `S ≥ 2`. -/
theorem two_dvd_leftFact {S : ℕ} (hS : 2 ≤ S) : 2 ∣ leftFact S := by
  induction S, hS using Nat.le_induction with
  | base => decide
  | succ S hS ih =>
    rw [leftFact]
    exact Nat.dvd_add ih (Nat.dvd_factorial (by omega) hS)

/-- `!S ≡ 2 (mod 4)` for `S ≥ 4`. -/
theorem leftFact_mod_four {S : ℕ} (hS : 4 ≤ S) : leftFact S % 4 = 2 := by
  induction S, hS using Nat.le_induction with
  | base => decide
  | succ S hS ih =>
    obtain ⟨m, hm⟩ : 4 ∣ S.factorial := Nat.dvd_factorial (by omega) hS
    rw [leftFact, hm]
    omega

/-- Modulo `m`, the left factorial does not change from `m` on: `m ∣ k!` for `k ≥ m`. -/
theorem dvd_leftFact_iff {m S : ℕ} (hm : 0 < m) (hmS : m ≤ S) :
    m ∣ leftFact S ↔ m ∣ leftFact m := by
  induction S, hmS using Nat.le_induction with
  | base => exact Iff.rfl
  | succ S hS ih =>
    rw [leftFact, ← ih]
    exact (Nat.dvd_add_iff_left (Nat.dvd_factorial hm hS)).symm

/-- A counterexample `n > 2` to Kurepa's conjecture gives an `S ≥ 2` with `2 S ∣ !S`: an odd
`n` itself (`!n` is even); for an even `n` (then `n ≥ 6`, since `4 ∤ !4`) the one obtained
from `n / 2`, which is a counterexample again. -/
theorem exists_two_mul_dvd_of_dvd (n : ℕ) :
    2 < n → n ∣ leftFact n → ∃ S, 2 ≤ S ∧ 2 * S ∣ leftFact S := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn2 hn
  obtain ⟨j, hj | hj⟩ : ∃ j, n = 2 * j ∨ n = 2 * j + 1 := ⟨n / 2, by omega⟩
  · rcases Nat.lt_or_ge 2 j with h | h
    · have hjn : j ∣ leftFact n := Nat.dvd_trans ⟨2, by omega⟩ hn
      exact ih j (by omega) h ((dvd_leftFact_iff (by omega) (by omega)).mp hjn)
    · obtain rfl : n = 4 := by omega
      exact absurd hn (by decide)
  · refine ⟨n, by omega, ?_⟩
    obtain ⟨c, hc⟩ := hn
    obtain ⟨e, he⟩ := two_dvd_leftFact (show 2 ≤ n by omega)
    obtain ⟨c', hc' | hc'⟩ : ∃ c', c = 2 * c' ∨ c = 2 * c' + 1 := ⟨c / 2, by omega⟩
    · exact ⟨c', by rw [hc, hc']; ring⟩
    · exfalso
      have h : n * c = 2 * (2 * (j * c') + j + c') + 1 := by rw [hj, hc']; ring
      omega

/-- The test of the machine and Kurepa's conjecture: `2 S ∣ !S` for some `S ≥ 2` if and only
if `n ∣ !n` for some `n > 2`. -/
theorem exists_two_mul_dvd_iff :
    (∃ S, 2 ≤ S ∧ 2 * S ∣ leftFact S) ↔ ∃ n, 2 < n ∧ n ∣ leftFact n := by
  constructor
  · rintro ⟨S, hS2, hS⟩
    rcases Nat.lt_or_ge 2 S with h | h
    · exact ⟨S, h, Nat.dvd_trans (Nat.dvd_mul_left S 2) hS⟩
    · obtain rfl : S = 2 := by omega
      exact absurd hS (by decide)
  · rintro ⟨n, hn2, hn⟩
    exact exists_two_mul_dvd_of_dvd n hn2 hn

/-- `2 S ∣ !S` for some `S ≥ 2` if and only if some odd prime `p` divides `!p`. -/
theorem exists_two_mul_dvd_iff_exists_prime :
    (∃ S, 2 ≤ S ∧ 2 * S ∣ leftFact S) ↔ ∃ p, p.Prime ∧ 2 < p ∧ p ∣ leftFact p := by
  constructor
  · rintro ⟨S, hS2, hS⟩
    rcases Nat.even_or_odd S with ⟨m, hm⟩ | hodd
    · -- `S` even: `4 ∣ !S`, impossible (`!2 = 2`, `!S ≡ 2 (mod 4)` for `S ≥ 4`)
      exfalso
      have h4 : 4 ∣ leftFact S := Nat.dvd_trans ⟨m, by omega⟩ hS
      rcases Nat.lt_or_ge S 4 with h | h
      · obtain rfl : S = 2 := by omega
        revert h4
        decide
      · have := leftFact_mod_four h
        omega
    · -- `S` odd: its least prime factor is odd
      have hp : S.minFac.Prime := Nat.minFac_prime (by omega)
      have hpS : S.minFac ∣ S := Nat.minFac_dvd S
      have hne : S.minFac ≠ 2 := by
        intro h
        rw [h] at hpS
        obtain ⟨m, hm⟩ := hpS
        obtain ⟨j, hj⟩ := hodd
        omega
      refine ⟨S.minFac, hp, lt_of_le_of_ne hp.two_le (Ne.symm hne), ?_⟩
      rw [← dvd_leftFact_iff hp.pos (Nat.minFac_le (by omega))]
      exact Nat.dvd_trans hpS (Nat.dvd_trans (Nat.dvd_mul_left S 2) hS)
  · rintro ⟨p, hp, hp2, hdvd⟩
    exact exists_two_mul_dvd_of_dvd p hp2 hdvd

/-- The 19-state machine `kurepa_19` halts on the blank tape if and only if some `n > 2`
divides the left factorial `!n = 0! + 1! + ⋯ + (n - 1)!`. -/
theorem halts_kurepa19_iff_exists_dvd :
    ConjectureMachines.Halts kurepa19 ↔ ∃ n : ℕ, 2 < n ∧ n ∣ leftFactorial n := by
  rw [halts_kurepa19_iff, exists_two_mul_dvd_iff]
  simp only [leftFact_eq_leftFactorial]

/-- The 19-state machine `kurepa_19` halts on the blank tape if and only if some odd prime `p`
divides the left factorial `!p`. -/
theorem halts_kurepa19_iff_exists_prime :
    ConjectureMachines.Halts kurepa19 ↔ ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ leftFactorial p := by
  rw [halts_kurepa19_iff, exists_two_mul_dvd_iff_exists_prime]
  simp only [leftFact_eq_leftFactorial]

/-- The 19-state machine `kurepa_19` halts on the blank tape if and only if Kurepa's conjecture
is false. -/
theorem halts_kurepa19_iff_not_kurepa :
    ConjectureMachines.Halts kurepa19 ↔ ¬ KurepaConjecture := by
  rw [halts_kurepa19_iff_exists_dvd]
  exact ⟨fun ⟨n, h2, hn⟩ hK => hK n h2 hn,
    fun h => by_contra fun hne => h fun n h2 hn => hne ⟨n, h2, hn⟩⟩

end ConjectureMachines.Kurepa19
