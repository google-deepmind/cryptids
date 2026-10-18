/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104
public import Cryptids.ReductionSupport.Riemann.FiniteStage

@[expose] public section

namespace ConjectureMachines.RiemannReferenceStageRange

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2

theorem edited_stage_halts_iff_reference (M : ℕ) (hM : M ≤ 21844) :
    (StateTransition.eval (rhRegStepOf true)
  (Riemann104.FiniteStage.stageCfg M)).Dom ↔ Halts Riemann104.candidate := by
  have hrel : StateTransition.Respects (rhRegStepOf false) (rhRegStepOf true)
      (fun c₁ c₂ => Riemann104.RhRegInv c₁ ∧ c₁ = c₂) := by
    intro c₁ c₂ ⟨hinv, hc₂⟩
    cases hc₂
    by_cases h11 : (c₁.stack == [1, 1, 1, 1, 1, 0, 1, 1]) = true
    · have hstk : c₁.stack = [1, 1, 1, 1, 1, 0, 1, 1] := beq_iff_eq.mp h11
      have hcmp : Riemann104.inCompare c₁.stack = true := by rw [hstk]; decide
      have hj0 : c₁.regs.getD 1 0 = 0 := hinv.2 hcmp
      have hj0_beq : (c₁.regs.getD 1 0 == 0) = true := beq_iff_eq.mpr hj0
      have hs_false : rhRegStepOf false c₁ = some ⟨[1, 1, 1, 1, 1], c₁.regs⟩ := by
        obtain ⟨stk, rgs⟩ := c₁
        dsimp only at hstk ⊢
        subst hstk
        rfl
      have hs_true1 : rhRegStepOf true c₁ = some ⟨[1, 1, 1, 1], c₁.regs⟩ := by
        obtain ⟨stk, rgs⟩ := c₁
        dsimp only at hstk ⊢
        subst hstk
        rfl
      have hs_true2 : rhRegStepOf true ⟨[1, 1, 1, 1], c₁.regs⟩ =
          some ⟨[1, 1, 1, 1, 1], c₁.regs⟩ := by
        unfold rhRegStepOf
        have hev4 : evalStackOf true [1, 1, 1, 1] =
            .decnz 1 [1, 1, 1, 1, 0, 1] [1, 1, 1, 1, 1] := by decide
        dsimp only
        rw [hev4]
        dsimp only
        rw [hj0_beq, ite_eq_left rfl]
      rw [hs_false]
      dsimp only
      exact ⟨⟨[1, 1, 1, 1, 1], c₁.regs⟩, ⟨Riemann104.rhRegInv_step hinv hs_false, rfl⟩,
        Relation.TransGen.head' hs_true1 (Relation.ReflTransGen.single hs_true2)⟩
    · have h11_f : (c₁.stack == [1, 1, 1, 1, 1, 0, 1, 1]) = false :=
        Bool.eq_false_iff.mpr h11
      have heq_step : rhRegStepOf true c₁ = rhRegStepOf false c₁ := by
        unfold rhRegStepOf evalStackOf
        rw [h11_f]; rfl
      rcases hs : rhRegStepOf false c₁ with _ | c₁'
      · dsimp only
        rw [heq_step, hs]
      · dsimp only
        have hs_true : rhRegStepOf true c₁ = some c₁' := by rw [heq_step, hs]
        exact ⟨c₁', ⟨Riemann104.rhRegInv_step hinv hs, rfl⟩,
          Relation.TransGen.single hs_true⟩
  have hinv : Riemann104.RhRegInv (Riemann104.FiniteStage.stageCfg M) := by
    refine ⟨isValidStack_nil, ?_⟩
    intro h
    cases h
  have htf : (StateTransition.eval (rhRegStepOf true) (Riemann104.FiniteStage.stageCfg M)).Dom ↔
      (StateTransition.eval (rhRegStepOf false) (Riemann104.FiniteStage.stageCfg M)).Dom :=
    StateTransition.tr_eval_dom hrel ⟨hinv, rfl⟩
  have hrel' : StateTransition.Respects rhRegStep (rhRegStepOf false)
      (fun c₁ c₂ => isValidStack c₁.stack = true ∧ c₁ = c₂) := by
    intro c₁ c₂ ⟨hv, hc⟩
    cases hc
    have hmem : c₁.stack ∈ allValidStacks :=
      (List.contains_iff_mem (a := c₁.stack) (as := allValidStacks)).mp hv
    have hev := evalStackOf_false_eq_evalStack c₁.stack hmem
    have hstep_eq : rhRegStepOf false c₁ = rhRegStep c₁ := by
      unfold rhRegStepOf rhRegStep
      rw [hev]
    rcases hs : rhRegStep c₁ with _ | c₁'
    · dsimp only
      rw [hstep_eq, hs]
    · dsimp only
      have hs' : rhRegStepOf false c₁ = some c₁' := by rw [hstep_eq, hs]
      exact ⟨c₁', ⟨rhRegStep_preserves_isValidStack hv hs, rfl⟩,
        Relation.TransGen.single hs'⟩
  have hfo : (StateTransition.eval (rhRegStepOf false) (Riemann104.FiniteStage.stageCfg M)).Dom ↔
      (StateTransition.eval rhRegStep (Riemann104.FiniteStage.stageCfg M)).Dom :=
    (StateTransition.tr_eval_dom hrel' ⟨hinv.1, rfl⟩).symm
  have hc : Halts Riemann104.candidate ↔ RhRegHalts :=
    Riemann104.halts_candidate_iff_halts_edited121
      |>.trans (Riemann120.halts_tm_iff_rhRegHaltsOf true)
      |>.trans Riemann104.rhRegHalts_true_iff_false
      |>.trans Riemann120.rhRegHaltsOf_false_iff_rhRegHalts
  exact htf.trans (hfo.trans ((Riemann104.FiniteStage.stage_halts_iff_original M hM).trans hc.symm))


theorem edited_stage2_halts_iff_reference :
    (StateTransition.eval (rhRegStepOf true) (Riemann104.FiniteStage.stageCfg 2)).Dom ↔
      Halts Riemann104.candidate :=
  edited_stage_halts_iff_reference 2 (by decide)

end ConjectureMachines.RiemannReferenceStageRange
