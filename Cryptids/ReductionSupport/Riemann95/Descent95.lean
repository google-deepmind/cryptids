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

end ConjectureMachines.Riemann95.Control
