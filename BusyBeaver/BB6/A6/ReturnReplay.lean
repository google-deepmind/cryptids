/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.BB6.A6.Cert
meta import BusyBeaver.WordRLE
meta import BusyBeaver.AffRLE
meta import BusyBeaver.ElabRLE
meta import BusyBeaver.BB6.A6.Defs
meta import BusyBeaver.BB6.A6.Cert

/-!
# Symbolic Affine Certificate Replay for BB6 `A6`

Verifies the 202-operation `BTree AffOp` symbolic trace (`9,844` affine sweeps and `67` inner
countdown cycles) from `initReturnCfg` to `a6FinalCfg` via depth-sliced `mkAuxTheorem` kernel
evaluation.
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.AffRLE

local elab "prove_a6_replay%" : term =>
  ElabRLE.proveAffReplay 6 a6Exits (Lean.mkConst ``a6Exits)
    returnTarget (Lean.mkConst ``returnTarget) a6Ops initReturnCfg a6FinalCfg 4

/-- Kernel-verified symbolic affine derivation of `a6Ops` from `initReturnCfg` to `a6FinalCfg`. -/
theorem a6_replay_ok :
    AffReplayReaches 6 a6Exits returnTarget a6Ops ⟨0, 0⟩ initReturnCfg returnTarget a6FinalCfg :=
  prove_a6_replay%

end BusyBeaver.BB6.A6

end
