/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz15
public import Cryptids.Semantics.WeakCollatz16

/-!
# Semantics of `weak_collatz_15` (`WeakCollatz15.Semantics`)

Composes the constructive state-reduction equivalence `WeakCollatz15.candidate_equivalent`
(`15 < 16` states; `75 → 41 → 27 → 17 → 16 → 15` overall) with the end-to-end mathematical
semantics of `weak_collatz_16`, yielding:
1. Constructive nontrivial `terras` cycle existence (`halts_candidate_iff_exists_cycle`, zero
   `Classical.choice`);
2. Constructive Böhm–Sontacchi (1978) Diophantine cycle equation
   (`halts_candidate_iff_bohmSontacchi`, zero `Classical.choice`);
3. Equivalence with the falsity of Tao's Weak Collatz Conjecture
   (`halts_candidate_iff_not_weakCollatz`).
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz15.Semantics

/-- Constructive equivalence between `weak_collatz_15` blank-tape halting and the existence of a
nontrivial positive cycle of `terras` (zero `Classical.choice`). -/
theorem halts_candidate_iff_exists_cycle :
    Halts ConjectureMachines.WeakCollatz15.candidate ↔
      ∃ x k : ℕ, 1 ≤ x ∧ 1 ≤ k ∧ terras^[k] x = x ∧ x ≠ 1 ∧ x ≠ 2 :=
  ConjectureMachines.WeakCollatz15.candidate_equivalent.trans
    ConjectureMachines.WeakCollatz16.Semantics.halts_candidate_iff_exists_cycle

/-- Constructive equivalence between `weak_collatz_15` blank-tape halting and the Böhm–Sontacchi
(1978) Diophantine cycle equation on `x ≥ 3` (zero `Classical.choice`). -/
theorem halts_candidate_iff_bohmSontacchi :
    Halts ConjectureMachines.WeakCollatz15.candidate ↔
      ∃ x n : ℕ, 3 ≤ x ∧ 1 ≤ n ∧
        3 ^ (terrasParityWord n x).sum < 2 ^ n ∧
        (2 ^ n - 3 ^ (terrasParityWord n x).sum) * x =
          collatzCycleNum (terrasParityWord n x) :=
  ConjectureMachines.WeakCollatz15.candidate_equivalent.trans
    ConjectureMachines.WeakCollatz16.Semantics.halts_candidate_iff_bohmSontacchi

/-- The 15-state machine (`weak_collatz_15`) halts on the blank tape if and only if Tao's Weak
Collatz Conjecture is false. -/
theorem halts_candidate_iff_not_weakCollatz :
    Halts ConjectureMachines.WeakCollatz15.candidate ↔ ¬ WeakCollatzConjecture :=
  ConjectureMachines.WeakCollatz15.candidate_equivalent.trans
    ConjectureMachines.WeakCollatz16.Semantics.halts_candidate_iff_not_weakCollatz

end ConjectureMachines.WeakCollatz15.Semantics
