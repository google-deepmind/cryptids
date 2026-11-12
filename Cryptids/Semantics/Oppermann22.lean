/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Oppermann22
public import Cryptids.Propositions
public import Cryptids.Semantics.Goldbach

/-!
# Semantics of `oppermann_22`

`Halts oppermann22 ↔ ∃ n, 2 ≤ n ∧ ((∀ p, p.Prime → ¬ (n ^ 2 - n < p ∧ p < n ^ 2)) ∨
(∀ p, p.Prime → ¬ (n ^ 2 < p ∧ p < n ^ 2 + n)))`: the statement of `Cryptids/Oppermann22.lean`
with Mathlib's `Nat.Prime` (through `isPrime_iff_prime` of `Cryptids/Semantics/Goldbach.lean`)
and `n ^ 2` for `n * n`. Hence `Halts oppermann22 ↔ ¬ OppermannConjecture`.
-/

@[expose] public section

namespace ConjectureMachines.Oppermann22

/-- The 22-state machine halts on the blank tape if and only if some `n ≥ 2` has no prime
strictly between `n ^ 2 - n` and `n ^ 2`, or none strictly between `n ^ 2` and `n ^ 2 + n`. -/
theorem halts_oppermann22_iff_exists_gap :
    ConjectureMachines.Halts oppermann22 ↔
      ∃ n : ℕ, 2 ≤ n ∧
        ((∀ p : ℕ, p.Prime → ¬ (n ^ 2 - n < p ∧ p < n ^ 2)) ∨
         (∀ p : ℕ, p.Prime → ¬ (n ^ 2 < p ∧ p < n ^ 2 + n))) := by
  rw [halts_oppermann22_iff]
  constructor
  · rintro ⟨n, hn, hE⟩
    refine ⟨n, hn, ?_⟩
    rcases hE with hE | hE
    · refine Or.inl (fun p hp ⟨h1, h2⟩ =>
        hE p ?_ ?_ ((Goldbach21.Semantics.isPrime_iff_prime p).mpr hp))
      · rwa [Nat.pow_two] at h1
      · rwa [Nat.pow_two] at h2
    · refine Or.inr (fun p hp ⟨h1, h2⟩ =>
        hE p ?_ ?_ ((Goldbach21.Semantics.isPrime_iff_prime p).mpr hp))
      · rwa [Nat.pow_two] at h1
      · rwa [Nat.pow_two] at h2
  · rintro ⟨n, hn, hE⟩
    refine ⟨n, hn, ?_⟩
    rcases hE with hE | hE
    · refine Or.inl (fun x h1 h2 hx =>
        hE x ((Goldbach21.Semantics.isPrime_iff_prime x).mp hx) ⟨?_, ?_⟩)
      · rwa [Nat.pow_two]
      · rwa [Nat.pow_two]
    · refine Or.inr (fun x h1 h2 hx =>
        hE x ((Goldbach21.Semantics.isPrime_iff_prime x).mp hx) ⟨?_, ?_⟩)
      · rwa [Nat.pow_two]
      · rwa [Nat.pow_two]

/-- The 22-state machine halts on the blank tape if and only if Oppermann's conjecture is
false. -/
theorem halts_oppermann22_iff_not_oppermann :
    ConjectureMachines.Halts oppermann22 ↔ ¬ OppermannConjecture := by
  rw [halts_oppermann22_iff_exists_gap]
  constructor
  · rintro ⟨n, hn, hE⟩ hO
    obtain ⟨⟨p, hp, h⟩, ⟨p', hp', h'⟩⟩ := hO n hn
    rcases hE with hE | hE
    · exact hE p hp h
    · exact hE p' hp' h'
  · intro h
    by_contra hne
    refine h fun n hn => ⟨?_, ?_⟩
    · by_contra hnp
      exact hne ⟨n, hn, Or.inl fun p hp hlt => hnp ⟨p, hp, hlt⟩⟩
    · by_contra hnp
      exact hne ⟨n, hn, Or.inr fun p hp hlt => hnp ⟨p, hp, hlt⟩⟩

end ConjectureMachines.Oppermann22
