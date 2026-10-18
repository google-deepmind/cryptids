/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary

open Turing ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1 (encodeRegs)

/-- The caller is the direct canonical physical word, without mapStack. -/
def rawRootCfg (pad : Nat) (word : List (Fin 2)) (regs extra : List Nat) : Cfg 98 2 :=
  ⟨15, Tape.mk' (ListBlank.cons 1 default)
    (ListBlank.mk (word ++ List.replicate (pad - word.length) 0 ++
      [1,0] ++ encodeRegs (regs ++ extra)))⟩

abbrev rootCfg := rawRootCfg

end ConjectureMachines.Riemann95Auxiliary
