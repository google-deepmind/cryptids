/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Witness95
public import Cryptids.ReductionSupport.Riemann95.ReferenceBridge95

/-!
# A 95-state Riemann Hypothesis machine

The blank initializer and physical stage simulation give an arithmetic counterexample
criterion. The reference bridge identifies that criterion with the existing 104-state
machine. `Semantics.Riemann95` then supplies the mathematical Riemann Hypothesis statement.
-/

@[expose] public section

namespace ConjectureMachines.Riemann95

/-- Complete execution from the blank tape detects precisely the original counterexamples. -/
theorem halts_candidate_iff_counterexample :
    Halts candidate ↔ ∃ M : Nat, Riemann120.ShuniaCounterexample (M + 2) := by
  rw [BootCertificate.halts_iff_initialRoot, Physical.initialRoot_eq_rootCfg]
  simpa only [initialRegs, initialExtra] using physical_stage0_halts_iff_witness

/-- The literal 95-state blank-tape machine preserves the reference's halting criterion. -/
theorem candidate_equivalent : Halts candidate ↔ Halts Riemann104.candidate :=
  halts_candidate_iff_counterexample.trans
    (counterexample_iff_positive_stage.trans reference_halts_iff_stage1_witness95.symm)

/-- The new machine has nine fewer states than the 104-state reference. -/
theorem candidate_fewer_states : candidate.states < Riemann104.candidate.states := by
  decide +kernel

end ConjectureMachines.Riemann95
