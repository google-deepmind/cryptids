/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz17
public import Cryptids.Semantics.WeakCollatz27

/-!
# Semantics of `weak_collatz_17` (`WeakCollatz17.Semantics`)

Composes the constructive state-reduction equivalence `WeakCollatz17.candidate_equivalent`
(`17 < 27` states; `75 → 41 → 27 → 17` overall) with the end-to-end mathematical semantics of
`weak_collatz_27`, yielding:
1. Constructive nontrivial `terras` cycle existence (`halts_candidate_iff_exists_cycle`, zero
   `Classical.choice`);
2. Constructive Böhm–Sontacchi (1978) Diophantine cycle equation
   (`halts_candidate_iff_bohmSontacchi`, zero `Classical.choice`);
3. Equivalence with the falsity of Tao's Weak Collatz Conjecture
   (`halts_candidate_iff_not_weakCollatz`).
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz17.Semantics

/-- Constructive equivalence between `weak_collatz_17` blank-tape halting and the existence of a
nontrivial positive cycle of `terras` (zero `Classical.choice`). -/
theorem halts_candidate_iff_exists_cycle :
    Halts ConjectureMachines.WeakCollatz17.candidate ↔
      ∃ x k : ℕ, 1 ≤ x ∧ 1 ≤ k ∧ terras^[k] x = x ∧ x ≠ 1 ∧ x ≠ 2 :=
  ConjectureMachines.WeakCollatz17.candidate_equivalent.trans
    ConjectureMachines.WeakCollatz27.Semantics.halts_candidate_iff_exists_cycle

/-- Constructive equivalence between `weak_collatz_17` blank-tape halting and the Böhm–Sontacchi
(1978) Diophantine cycle equation on `x ≥ 3` (zero `Classical.choice`). -/
theorem halts_candidate_iff_bohmSontacchi :
    Halts ConjectureMachines.WeakCollatz17.candidate ↔
      ∃ x n : ℕ, 3 ≤ x ∧ 1 ≤ n ∧
        3 ^ (terrasParityWord n x).sum < 2 ^ n ∧
        (2 ^ n - 3 ^ (terrasParityWord n x).sum) * x =
          collatzCycleNum (terrasParityWord n x) :=
  ConjectureMachines.WeakCollatz17.candidate_equivalent.trans
    ConjectureMachines.WeakCollatz27.Semantics.halts_candidate_iff_bohmSontacchi

/-- The 17-state machine (`weak_collatz_17`) halts on the blank tape if and only if Tao's Weak
Collatz Conjecture is false. -/
theorem halts_candidate_iff_not_weakCollatz :
    Halts ConjectureMachines.WeakCollatz17.candidate ↔ ¬ WeakCollatzConjecture :=
  ConjectureMachines.WeakCollatz17.candidate_equivalent.trans
    ConjectureMachines.WeakCollatz27.Semantics.halts_candidate_iff_not_weakCollatz

end ConjectureMachines.WeakCollatz17.Semantics
