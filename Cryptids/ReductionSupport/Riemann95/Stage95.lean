/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Terminal95
public import Cryptids.ReductionSupport.Riemann95.PhysicalTrace95
public import Cryptids.ReductionSupport.Riemann95.TypedPrewidth95
public import Cryptids.ReductionSupport.Riemann95.ClockBound95

@[expose] public section

namespace ConjectureMachines.Riemann95

open Turing ConjectureMachines

theorem residual_criterion (M : Nat) :
    Riemann120.ShuniaCounterexample (M + 2) ↔
      0 < Algorithm.residual (M + 1) (Riemann120.shuniaDeficit (M + 2)) := by
  rw [Algorithm.residual_eq]
  have hn : M + 2 - 1 = M + 1 := by omega
  simpa only [hn] using Riemann120.Layer2.shuniaCounterexample_iff_sub_pos (M + 2)

/-- Each full stage either advances with one more padding cell or halts on its exact criterion. -/
theorem physical_stage_outcomes (M P : Nat) (hP : M + 21 ≤ P) (extra : List Nat) :
    (¬ Riemann120.ShuniaCounterexample (M + 2) →
      ∃ P' ≥ P + 1, ∃ s ≥ 1, ∃ extra',
        nSteps s (Physical.rootCfg P [] ([0,0,0,M,0] ++ extra)) =
          some (Physical.rootCfg P' [] ([0,0,0,M+1,0] ++ extra'))) ∧
    (Riemann120.ShuniaCounterexample (M + 2) →
      ∃ s, ∃ c : Cfg 95 2,
        nSteps s (Physical.rootCfg P [] ([0,0,0,M,0] ++ extra)) = some c ∧
          step machine c = none) := by
  have hpre := Trace.bounded_trace_lift 19 P (by omega)
    (⟨.outside 0,[0,0,0,M,0]⟩ : Control.Cfg)
    (⟨.outside 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ : Control.Cfg)
    (by rfl) (TypedPrewidth.stage_prewidth M) extra
  obtain ⟨Ppre,hPpre,spre,hspre,epre,hpre⟩ := hpre
  change nSteps spre (Physical.rootCfg P [] ([0,0,0,M,0] ++ extra)) =
    some (Physical.rootCfg Ppre [1,1,1,1]
      ([0,0,Riemann120.shuniaDeficit (M+2),0,M+1] ++ epre)) at hpre
  have hbudget : Control.widthBudget (M+1) ≤ Ppre := by
    have hb := Algorithm.width_padding_le (M+1) (by omega)
    change max 16 (10 + 5 * Riemann120.quarterClock (M+1)) + 5 ≤ Ppre
    omega
  constructor
  · intro hsafe
    have hz : Algorithm.residual (M+1) (Riemann120.shuniaDeficit (M+2)) = 0 := by
      have hn := mt (residual_criterion M).mpr hsafe
      omega
    obtain ⟨Pout,hPout,sout,hsout,eout,hout⟩ :=
      Trace.physical_precredit_width_zero Ppre 0 (M+1)
        (Riemann120.shuniaDeficit (M+2)) epre hbudget hz
    simp only [Nat.zero_add] at hout
    refine ⟨Pout,by omega,spre+sout,by omega,eout,?_⟩
    rw [Dispatch.nSteps_composition,hpre]
    exact hout
  · intro hbad
    have hpos := (residual_criterion M).mp hbad
    obtain ⟨Pout,_,sout,_,eout,hout⟩ :=
      Trace.physical_precredit_width Ppre 0 (M+1)
        (Riemann120.shuniaDeficit (M+2)) epre hbudget
    have hn : Algorithm.residual (M+1) (Riemann120.shuniaDeficit (M+2)) ≠ 0 := by omega
    simp only [hn,ite_false,Nat.zero_add] at hout
    obtain ⟨shalt,c,hhalt,hstop⟩ := physical_halt_word Pout
      ([0,0,Algorithm.residual (M+1) (Riemann120.shuniaDeficit (M+2))-1,M+1,0] ++ eout)
    refine ⟨spre+sout+shalt,c,?_,hstop⟩
    rw [Dispatch.nSteps_composition,Dispatch.nSteps_composition,hpre]
    change (nSteps sout (Physical.rootCfg Ppre [1,1,1,1]
      ([0,0,Riemann120.shuniaDeficit (M+2),0,M+1] ++ epre))).bind (nSteps shalt) = some c
    rw [hout]
    exact hhalt

end ConjectureMachines.Riemann95
