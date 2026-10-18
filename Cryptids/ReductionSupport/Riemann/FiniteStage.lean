/-
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

theorem init_reaches_stage (M : Nat) (hM : M ≤ 21844) :
    ∃ N, rhRegNSteps N rhRegInit = some (stageCfg M) := by
  induction M with
  | zero => exact ⟨0, rfl⟩
  | succ M ih =>
    obtain ⟨N, hN⟩ := ih (by omega)
    have hsafe : ¬ ShuniaCounterexample (M + 2) :=
      Riemann120Analytic.not_shuniaCounterexample_of_le_21845 (by omega) (by omega)
    obtain ⟨s, _, hs⟩ := (main_stage_step M).1 hsafe
    exact ⟨N + s, rhRegNSteps_bind_eq hN hs⟩

theorem abstract_nSteps_reaches {N : Nat} {c c' : RhRegCfg}
    (h : rhRegNSteps N c = some c') : StateTransition.Reaches rhRegStep c c' := by
  induction N generalizing c with
  | zero => injection h with hc; subst hc; exact Relation.ReflTransGen.refl
  | succ N ih =>
    simp only [rhRegNSteps, Option.bind_eq_some_iff] at h
    obtain ⟨next, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem stage_halts_iff_original (M : Nat) (hM : M ≤ 21844) :
    (StateTransition.eval rhRegStep (stageCfg M)).Dom ↔ RhRegHalts := by
  obtain ⟨N, hN⟩ := init_reaches_stage M hM
  unfold RhRegHalts
  rw [StateTransition.reaches_eval (abstract_nSteps_reaches hN)]

end ConjectureMachines.Riemann104.FiniteStage
