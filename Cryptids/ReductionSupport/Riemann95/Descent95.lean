/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Half95
public import Cryptids.ReductionSupport.Riemann95.Algorithm95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open StateTransition Schema
open ConjectureMachines.Riemann120 (quarterClock)

attribute [local irreducible] localEffects outsideEffects outsideInstrs rawInstr localInstr

theorem entry_positive_step (d f x j : Nat) :
    step ⟨.entry d,[0,0,f,x,j+1]⟩ = some ⟨.local d 0,[0,0,f,x,j]⟩ := by
  cases d <;> simp [step,instruction]

theorem body (d f x j : Nat) :
    Reaches₁ step ⟨.entry d,[0,0,f,x,j+1]⟩
      ⟨.entry (d+1),[0,0,f/2,x,j/4]⟩ := by
  have he : Reaches₁ step ⟨.entry d,[0,0,f,x,j+1]⟩
      ⟨.local d 0,[0,0,f,x,j]⟩ := Relation.TransGen.single (entry_positive_step d f x j)
  have h1 := halfj_first d 0 0 f x j
  have h2 := halfj_second d 0 0 f x (j/2)
  have h3 := halff d 0 0 f x (j/2/2)
  simp only [Nat.add_zero] at h1 h2 h3
  have hquarter : j/2/2 = j/4 := by omega
  rw [hquarter] at h2 h3
  exact he.trans (h1.trans (h2.trans h3))

theorem descent (d x j f : Nat) :
    Reaches step ⟨.entry d,[0,0,f,x,j]⟩
      ⟨.entry (d+quarterClock j),[0,0,f/2^quarterClock j,x,0]⟩ := by
  induction j using Nat.strong_induction_on generalizing d f with
  | h j ih =>
    cases j with
    | zero =>
      simp only [quarterClock,pow_zero,Nat.div_one,Nat.add_zero]
      exact Relation.ReflTransGen.refl
    | succ j =>
      have hb := body d f x j
      have hi := ih (j/4) (by omega) (d+1) (f/2)
      have hclock : quarterClock (j+1) = quarterClock (j/4)+1 := by
        rw [quarterClock]
        omega
      have hd : d+1+quarterClock (j/4) = d+quarterClock (j+1) := by omega
      have hf : f/2/2^quarterClock (j/4) = f/2^quarterClock (j+1) := by
        rw [hclock,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 2]
      rw [hd,hf] at hi
      exact hb.to_reflTransGen.trans hi

end ConjectureMachines.Riemann95.Control
