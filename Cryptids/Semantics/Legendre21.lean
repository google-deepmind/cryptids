/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Legendre21
public import Cryptids.Propositions
public import Cryptids.Semantics.Goldbach

/-!
# Semantics of `legendre_21`

`Halts legendre21 ↔ ∃ n, 1 ≤ n ∧ ∀ p, p.Prime → ¬ (n ^ 2 < p ∧ p < (n + 1) ^ 2)`: the statement
of `Cryptids/Legendre21.lean` with Mathlib's `Nat.Prime` (through `isPrime_iff_prime` of
`Cryptids/Semantics/Goldbach.lean`) and `n ^ 2` for `n * n`. Hence
`Halts legendre21 ↔ ¬ LegendreConjecture`.
-/

@[expose] public section

namespace ConjectureMachines.Legendre21

/-- The 21-state machine halts on the blank tape if and only if some `n ≥ 1` has no prime
strictly between `n ^ 2` and `(n + 1) ^ 2`. -/
theorem halts_legendre21_iff_exists_gap :
    ConjectureMachines.Halts legendre21 ↔
      ∃ n : ℕ, 1 ≤ n ∧ ∀ p : ℕ, p.Prime → ¬ (n ^ 2 < p ∧ p < (n + 1) ^ 2) := by
  rw [halts_legendre21_iff]
  constructor
  · rintro ⟨n, hn, hE⟩
    refine ⟨n, hn, fun p hp ⟨h1, h2⟩ =>
      hE p ?_ ?_ ((Goldbach21.Semantics.isPrime_iff_prime p).mpr hp)⟩
    · rwa [Nat.pow_two] at h1
    · rwa [Nat.pow_two] at h2
  · rintro ⟨n, hn, hE⟩
    refine ⟨n, hn, fun x h1 h2 hx =>
      hE x ((Goldbach21.Semantics.isPrime_iff_prime x).mp hx) ⟨?_, ?_⟩⟩
    · rwa [Nat.pow_two]
    · rwa [Nat.pow_two]

/-- The 21-state machine halts on the blank tape if and only if Legendre's conjecture is
false. -/
theorem halts_legendre21_iff_not_legendre :
    ConjectureMachines.Halts legendre21 ↔ ¬ LegendreConjecture := by
  rw [halts_legendre21_iff_exists_gap]
  constructor
  · rintro ⟨n, hn, hE⟩ hL
    obtain ⟨p, hp, h⟩ := hL n hn
    exact hE p hp h
  · intro h
    by_contra hne
    exact h fun n hn => by
      by_contra hnp
      exact hne ⟨n, hn, fun p hp hlt => hnp ⟨p, hp, hlt⟩⟩

end ConjectureMachines.Legendre21
