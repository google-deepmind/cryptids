/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95
public import Cryptids.Semantics.Riemann120

@[expose] public section

namespace ConjectureMachines.Riemann95.Semantics

/-- Unconditional blank-tape correctness for Mathlib's Riemann Hypothesis. -/
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts ConjectureMachines.Riemann95.candidate ↔ ¬ RiemannHypothesis :=
  ConjectureMachines.Riemann95.candidate_equivalent.trans
    ConjectureMachines.Riemann104.Semantics.halts_candidate_iff_not_riemannHypothesis

end ConjectureMachines.Riemann95.Semantics
