/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Witness95
public import Cryptids.ReductionSupport.Riemann95.ReferenceBridge95

@[expose] public section

namespace ConjectureMachines.Riemann95

/-- The literal95-state blank-tape machine preserves the original halting criterion. -/
theorem candidate_equivalent : Halts candidate ↔ Halts Riemann104.candidate := by
  have htwo : ¬ Riemann120.ShuniaCounterexample 2 :=
    Riemann104.FiniteStage.earlier_stages_safe (M := 1) (by decide)
      (j := 0) (by decide)
  have hw : (∃ M : Nat, Riemann120.ShuniaCounterexample (M+2)) ↔
      ∃ M : Nat, 1 ≤ M ∧ Riemann120.ShuniaCounterexample (M+2) := by
    constructor
    · rintro ⟨M,hM⟩
      refine ⟨M,?_,hM⟩
      by_contra h
      have hz : M = 0 := by omega
      subst M
      exact htwo hM
    · rintro ⟨M,_,hM⟩
      exact ⟨M,hM⟩
  rw [BootCertificate.halts_iff_initialRoot, Physical.initialRoot_eq_rootCfg]
  simp only [initialRegs, initialExtra]
  exact physical_stage0_halts_iff_witness.trans
    (hw.trans reference_halts_iff_stage1_witness95.symm)

theorem candidate_fewer_states : candidate.states < Riemann104.candidate.states := by
  decide +kernel

end ConjectureMachines.Riemann95
