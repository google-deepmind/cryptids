/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Stage95
public import Cryptids.ReductionSupport.Riemann95.Cofinality95

@[expose] public section

namespace ConjectureMachines.Riemann95

/-- The actual stage simulation discharges every premise of physical cofinality. -/
theorem stage_outcomes : StageOutcomes := physical_stage_outcomes

/-- The stage-zero seed advances to a positive stage because its n=2 test is safe. -/
theorem physical_stage0_safe :
    ∃ P ≥ 23, ∃ s ≥ 1, ∃ extra,
      nSteps s (Physical.rootCfg 22 [] ([0,0,0,0,0] ++ List.replicate 4 0)) =
        some (Physical.rootCfg P [] ([0,0,0,1,0] ++ extra)) := by
  have htwo : ¬ Riemann120.ShuniaCounterexample 2 :=
    Riemann104.FiniteStage.earlier_stages_safe (M := 1) (by decide)
      (j := 0) (by decide)
  exact (physical_stage_outcomes 0 22 (by decide) (List.replicate 4 0)).1 htwo

theorem physical_stage0_halts_iff_witness :
    (StateTransition.eval (ConjectureMachines.step machine)
      (Physical.rootCfg 22 [] ([0,0,0,0,0] ++ List.replicate 4 0))).Dom ↔
      ∃ M : Nat, Riemann120.ShuniaCounterexample (M+2) :=
  physical_stage0_halts_iff_witness_of_outcomes stage_outcomes

end ConjectureMachines.Riemann95
