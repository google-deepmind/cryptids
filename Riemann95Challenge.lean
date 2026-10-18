/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Challenge

/-! Independent Riemann95 specification. This module imports no solution proofs. -/

@[expose] public section
namespace ConjectureMachines

open Turing

namespace Riemann95
/-- Literal 95-state machine, read independently from the exported transition table. -/
def rows : List (List (Option (Fin 2 × Dir × Fin 95))) :=
  load_machine_rows% "artifacts/riemann_95/machine.txt"

def machine : Machine 95 2 := Machine.ofRows rows

abbrev candidate : BundledMachine 2 := machine.bundle

theorem candidate_fewer_states : candidate.states < Riemann104.candidate.states := by sorry

theorem candidate_equivalent : Halts candidate ↔ Halts Riemann104.candidate := by sorry

namespace Semantics
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts candidate ↔ ¬ RiemannHypothesis := by sorry
end Semantics
end Riemann95

end ConjectureMachines
