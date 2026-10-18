/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann120.Analytic
public import Cryptids.Semantics.Riemann120.Program

/-! Abstract finite-stage initialization, using the existing unconditional
small-n analytic theorem. This source says nothing about any new tape table.
-/

@[expose] public section

namespace ConjectureMachines.Riemann104.FiniteStage

open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2

def stageCfg (M : Nat) : RhRegCfg := ⟨[], [M, 0, 0, 0, 0]⟩

theorem earlier_stages_safe {M : Nat} (hM : M ≤ 21844) {j : Nat} (hj : j < M) :
    ¬ ShuniaCounterexample (j + 2) :=
  Riemann120Analytic.not_shuniaCounterexample_of_le_21845 (by omega) (by omega)

end ConjectureMachines.Riemann104.FiniteStage
