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

theorem unwind_eval (d x f : Nat) :
    Reaches₁ step ⟨unwind d,[0,0,f,x,0]⟩
      ⟨if f ≤ d ∧ (d-f)%2 = 0 then .outside 0 else .outside finalTestId,
        [0,0,f-(d+1),x,0]⟩ := by
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    cases d with
    | zero =>
      cases f with
      | zero => exact Relation.TransGen.single (by simpa using unwind0_step 0 x)
      | succ f => exact Relation.TransGen.single (by simpa using unwind0_step (f+1) x)
    | succ d =>
      cases f with
      | zero =>
        cases d with
        | zero => exact Relation.TransGen.single (by simpa using unwind1_zero_step x)
        | succ d =>
          have hs : Reaches₁ step ⟨unwind (d+2),[0,0,0,x,0]⟩
              ⟨unwind d,[0,0,0,x,0]⟩ :=
            Relation.TransGen.single (unwind_succ_succ_zero_step d x)
          have hpar : (d+1+1)%2 = d%2 := by omega
          have hi := ih d (by omega) 0
          simpa only [Reaches₁,Nat.zero_le,Nat.sub_zero,true_and,Nat.zero_sub,hpar]
            using hs.trans hi
      | succ f =>
        have hs : Reaches₁ step ⟨unwind (d+1),[0,0,f+1,x,0]⟩
            ⟨unwind d,[0,0,f,x,0]⟩ :=
          Relation.TransGen.single (unwind_succ_positive_step d f x)
        have hc : (f+1 ≤ d+1 ∧ (d+1-(f+1))%2 = 0) ↔
            (f ≤ d ∧ (d-f)%2 = 0) := by omega
        have hsub : f+1-(d+1+1) = f-(d+1) := by omega
        simpa only [Reaches₁,hc,hsub] using hs.trans (ih d (by omega) f)

theorem final_test_step (f x : Nat) :
    step ⟨.outside finalTestId,[0,0,f,x,0]⟩ =
      some ⟨if f = 0 then .outside 0 else .outside finalHaltId,[0,0,f-1,x,0]⟩ := by
  simp only [step,final_test]
  by_cases hf : f = 0 <;> simp [hf]

theorem final_halt_step (f x : Nat) :
    step ⟨.outside finalHaltId,[0,0,f,x,0]⟩ = none := by
  simp only [step,final_halt]

theorem finish (q f x : Nat) :
    Reaches₁ step ⟨.entry q,[0,0,f,x,0]⟩
      ⟨if f-q = 0 then .outside 0 else .outside finalHaltId,[0,0,(f-q)-1,x,0]⟩ := by
  have test (a : Nat) : Reaches₁ step ⟨.outside finalTestId,[0,0,a,x,0]⟩
      ⟨if a = 0 then .outside 0 else .outside finalHaltId,[0,0,a-1,x,0]⟩ :=
    Relation.TransGen.single (final_test_step a x)
  cases q with
  | zero =>
    have hs : Reaches₁ step ⟨.entry 0,[0,0,f,x,0]⟩
        ⟨.outside finalTestId,[0,0,f,x,0]⟩ :=
      Relation.TransGen.single (by simp [step,entry_zero])
    simpa only [Reaches₁,Nat.sub_zero] using hs.trans (test f)
  | succ d =>
    have hs : Reaches₁ step ⟨.entry (d+1),[0,0,f,x,0]⟩
        ⟨unwind d,[0,0,f,x,0]⟩ :=
      Relation.TransGen.single (by simp [step,entry_succ])
    have hu := hs.trans (unwind_eval d x f)
    by_cases hc : f ≤ d ∧ (d-f)%2 = 0
    · have hz : f-(d+1) = 0 := by omega
      simpa only [ite_eq_left hc,hz,Nat.zero_sub,ite_true,Reaches₁] using hu
    · simp only [ite_eq_right hc] at hu
      exact hu.trans (test (f-(d+1)))

theorem width_outcome (x j f : Nat) :
    Reaches₁ step ⟨.entry 0,[0,0,f,x,j]⟩
      ⟨if Algorithm.residual j f = 0 then .outside 0 else .outside finalHaltId,
        [0,0,Algorithm.residual j f-1,x,0]⟩ := by
  have hd := descent 0 x j f
  simp only [Nat.zero_add] at hd
  have hf := (finish (quarterClock j) (f/2^quarterClock j) x).trans_right hd
  simpa only [Reaches₁,Algorithm.residual_eq] using hf

end ConjectureMachines.Riemann95.Control
