/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ErdosTernary14
public import Cryptids.Semantics.ErdosTernary15

@[expose] public section

namespace ConjectureMachines.ErdosTernary14.Semantics

/-- The 14-state machine (`erdos_ternary_14`) halts on the blank tape if and only if Erdős's ternary
conjecture is false. -/
theorem halts_candidate_iff_not_erdosTernary :
    Halts ConjectureMachines.ErdosTernary14.candidate ↔ ¬ ErdosTernaryConjecture :=
  ConjectureMachines.ErdosTernary14.candidate_equivalent.trans
    ConjectureMachines.ErdosTernary15.halts_erdosTernary15_iff_not_erdosTernary

end ConjectureMachines.ErdosTernary14.Semantics
