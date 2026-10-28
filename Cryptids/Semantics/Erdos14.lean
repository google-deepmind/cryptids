/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Erdos14
public import Cryptids.Semantics.Erdos15

@[expose] public section

namespace ConjectureMachines.Erdos14.Semantics

/-- The 14-state machine (`erdos_14`) halts on the blank tape if and only if Erdős's conjecture on
powers of two is false. -/
theorem halts_candidate_iff_not_erdosPowersOfTwo :
    Halts ConjectureMachines.Erdos14.candidate ↔ ¬ ErdosPowersOfTwoConjecture :=
  ConjectureMachines.Erdos14.candidate_equivalent.trans
    ConjectureMachines.Erdos15.halts_erdos15_iff_not_erdosPowersOfTwo

end ConjectureMachines.Erdos14.Semantics
