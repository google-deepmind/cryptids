/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Projection95
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Return

@[expose] public section

namespace ConjectureMachines.Riemann95.Return

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 (rootLeftOf stackLeftOf)
open ConjectureMachines.Semantics.Riemann.Layer1 (Tape.mkL)
open ConjectureMachines.Riemann104.OnePassGuard (NoThreeZeros)

/-- The intrinsic NoThree return scanner on the actual95-state machine. -/
theorem run_return (word : List (Fin 2))
    (hok : NoThreeZeros (1 :: word).reverse = true) (R : ListBlank (Fin 2)) :
    ∃ s ≥ 1, nSteps s ⟨5, Tape.mkL (stackLeftOf true word) R⟩ =
      some ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append word R)⟩ := by
  obtain ⟨s, hs, h⟩ := Riemann95Auxiliary.Return.run_return98 word hok R
  have ht := Projection.of_aux h
  exact ⟨s, hs, ht⟩

/-- The one-cell peeled interface retains the adjacent-ONE premise. -/
theorem run_return_after_one (word : List (Fin 2))
    (hok : NoThreeZeros (1 :: word).reverse = true)
    (hhead : (stackLeftOf true word).head = 1) (R : ListBlank (Fin 2)) :
    ∃ s ≥ 1, nSteps s
      ⟨5, Tape.mkL (stackLeftOf true word).tail (R.cons 1)⟩ =
      some ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append word R)⟩ := by
  obtain ⟨s, hs, h⟩ :=
    Riemann95Auxiliary.Return.run_return98_after_one word hok hhead R
  have ht := Projection.of_aux h
  exact ⟨s, hs, ht⟩

end ConjectureMachines.Riemann95.Return
