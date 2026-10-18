/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104

/-! The scanner guard used by the Riemann95 physical return proofs. -/

@[expose] public section

namespace ConjectureMachines.Riemann104.OnePassGuard

open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2

/-- Three consecutive zeros must occur only in the blank left root fence. -/
def NoThreeZeros : List (Fin 2) → Bool
  | 0 :: 0 :: 0 :: _ => false
  | _ :: rest => NoThreeZeros rest
  | [] => true

end ConjectureMachines.Riemann104.OnePassGuard
