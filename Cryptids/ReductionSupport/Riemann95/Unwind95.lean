/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Descent95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open StateTransition Schema
open ConjectureMachines.Riemann120 (quarterClock)

attribute [local irreducible] localEffects outsideEffects outsideInstrs rawInstr
  localInstr instruction

theorem unwind0_step (f x : Nat) :
    step ⟨unwind 0,[0,0,f,x,0]⟩ =
      some ⟨if f = 0 then .outside 0 else .outside finalTestId,[0,0,f-1,x,0]⟩ := by
  simp only [step,unwind_zero]
  by_cases hf : f = 0 <;> simp [hf]

theorem unwind1_zero_step (x : Nat) :
    step ⟨unwind 1,[0,0,0,x,0]⟩ = some ⟨.outside finalTestId,[0,0,0,x,0]⟩ := by
  simp [step,unwind_one]

theorem unwind_succ_positive_step (d f x : Nat) :
    step ⟨unwind (d+1),[0,0,f+1,x,0]⟩ = some ⟨unwind d,[0,0,f,x,0]⟩ := by
  cases d with
  | zero => simp [step,unwind_one]
  | succ d => simp [step,unwind_succ_succ]

theorem unwind_succ_succ_zero_step (d x : Nat) :
    step ⟨unwind (d+2),[0,0,0,x,0]⟩ = some ⟨unwind d,[0,0,0,x,0]⟩ := by
  simp [step,unwind_succ_succ]

theorem final_test_step (f x : Nat) :
    step ⟨.outside finalTestId,[0,0,f,x,0]⟩ =
      some ⟨if f = 0 then .outside 0 else .outside finalHaltId,[0,0,f-1,x,0]⟩ := by
  simp only [step,final_test]
  by_cases hf : f = 0 <;> simp [hf]

end ConjectureMachines.Riemann95.Control
