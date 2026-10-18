/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.TraceLift95
public import Cryptids.ReductionSupport.Riemann95.StrictExit95
public import Cryptids.ReductionSupport.Riemann95.PrecreditTrace95

@[expose] public section

namespace ConjectureMachines.Riemann95.Trace

open Riemann120.Layer2 Schema Control

theorem physical_precredit_width (P x j f : Nat) (extra : List Nat)
    (hP : widthBudget j ≤ P) :
    ∃ P' ≥ P, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P [1,1,1,1] ([0,0,f,x,j] ++ extra)) =
        some (Physical.rootCfg P'
          (if Algorithm.residual j f = 0 then [] else word (.outside finalHaltId))
          ([0,0,Algorithm.residual j f-1,x+j,0] ++ extra')) := by
  have h := bounded_trace_lift (widthBudget j) P hP _ _ (by rfl)
    (bounded_precredit_width x j f) extra
  rw [widthCall_word] at h
  by_cases hz : Algorithm.residual j f = 0
  · simpa only [hz,ite_true,initial_word] using h
  · simpa only [hz,ite_false] using h

theorem physical_precredit_width_zero (P x j f : Nat) (extra : List Nat)
    (hP : widthBudget j ≤ P) (hr : Algorithm.residual j f = 0) :
    ∃ P' ≥ P+1, ∃ n ≥ 1, ∃ extra',
      nSteps n (Physical.rootCfg P [1,1,1,1] ([0,0,f,x,j] ++ extra)) =
        some (Physical.rootCfg P' [] ([0,0,0,x+j,0] ++ extra')) := by
  have h := strict_exit_lift (widthBudget j) P hP _ _ (by rfl) (by rfl)
    (strict_precredit_width_zero x j f hr) extra
  simpa only [widthCall_word,initial_word] using h

end ConjectureMachines.Riemann95.Trace
