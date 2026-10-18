/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ReferenceBridge95
public import Cryptids.ReductionSupport.Riemann95.PrecreditTrace95

@[expose] public section

namespace ConjectureMachines.Riemann95.TypedPrewidth

open ConjectureMachines.Riemann120.Layer2 (RhRegCfg)

attribute [local irreducible] ReferenceProgram.word ReferenceProgram.decoded
  ReferenceProgram.instruction ReferenceLogical.word ReferenceLogical.decoded
  ReferenceLogical.instruction ReferencePreStep95

theorem reference_word0 : ReferenceProgram.word 0 = [] := by decide +kernel

theorem reference_step_word (s : Fin 121) (regs : List Nat) :
    ReferencePreStep95 ⟨ReferenceProgram.word s,regs⟩ =
      if ReferenceProgram.word s = ReferenceProgram.word 88 then none
      else Control.applyInstr (ReferenceProgram.decoded s) regs := by
  unfold ReferencePreStep95
  split
  · rfl
  · unfold ReferenceProgram.step
    rw [ReferenceProgram.instruction_word]
    cases ReferenceProgram.decoded s <;> rfl

theorem reference_decoded0 : ReferenceProgram.decoded 0 =
    .decnz 3 (ReferenceProgram.word 1) (ReferenceProgram.word 3) := by decide +kernel
theorem reference_decoded1 : ReferenceProgram.decoded 1 =
    .inc 2 (ReferenceProgram.word 2) := by decide +kernel
theorem reference_decoded2 : ReferenceProgram.decoded 2 =
    .jump (ReferenceProgram.word 0) := by decide +kernel

theorem reference_word0_ne88 : ReferenceProgram.word 0 ≠ ReferenceProgram.word 88 := by
  decide +kernel
theorem reference_word1_ne88 : ReferenceProgram.word 1 ≠ ReferenceProgram.word 88 := by
  decide +kernel
theorem reference_word2_ne88 : ReferenceProgram.word 2 ≠ ReferenceProgram.word 88 := by
  decide +kernel

private theorem reference_one_step {a b : RhRegCfg} (h : ReferencePreStep95 a = some b) :
    StateTransition.Reaches₁ ReferencePreStep95 a b := Relation.TransGen.single h

theorem reference_step0 (f M : Nat) :
    ReferencePreStep95 ⟨ReferenceProgram.word 0,[0,0,f,M,0]⟩ =
      if M = 0 then some ⟨ReferenceProgram.word 3,[0,0,f,0,0]⟩
      else some ⟨ReferenceProgram.word 1,[0,0,f,M-1,0]⟩ := by
  rw [reference_step_word,ite_eq_right reference_word0_ne88,reference_decoded0]
  cases M <;> rfl

theorem reference_step1 (f M : Nat) :
    ReferencePreStep95 ⟨ReferenceProgram.word 1,[0,0,f,M,0]⟩ =
      some ⟨ReferenceProgram.word 2,[0,0,f+1,M,0]⟩ := by
  rw [reference_step_word,ite_eq_right reference_word1_ne88,reference_decoded1]
  rfl

theorem reference_step2 (f M : Nat) :
    ReferencePreStep95 ⟨ReferenceProgram.word 2,[0,0,f,M,0]⟩ =
      some ⟨ReferenceProgram.word 0,[0,0,f,M,0]⟩ := by
  rw [reference_step_word,ite_eq_right reference_word2_ne88,reference_decoded2]
  rfl

/-- The stopped reference initializer transfers M into the accumulator and reaches word 3. -/
theorem reference_init (M f : Nat) :
    StateTransition.Reaches₁ ReferencePreStep95 ⟨ReferenceProgram.word 0,[0,0,f,M,0]⟩
      ⟨ReferenceProgram.word 3,[0,0,f+M,0,0]⟩ := by
  induction M generalizing f with
  | zero =>
    exact Relation.TransGen.single (show ReferencePreStep95 ⟨ReferenceProgram.word 0,[0,0,f,0,0]⟩ =
      some ⟨ReferenceProgram.word 3,[0,0,f+0,0,0]⟩ from by
        simpa only [ite_true,Nat.add_zero] using reference_step0 f 0)
  | succ M ih =>
    have h0 : ReferencePreStep95 ⟨ReferenceProgram.word 0,[0,0,f,M+1,0]⟩ =
        some ⟨ReferenceProgram.word 1,[0,0,f,M,0]⟩ := by
      simpa only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel] using reference_step0 f (M+1)
    have h1 : ReferencePreStep95 ⟨ReferenceProgram.word 1,[0,0,f,M,0]⟩ =
        some ⟨ReferenceProgram.word 2,[0,0,f+1,M,0]⟩ := reference_step1 f M
    have h2 : ReferencePreStep95 ⟨ReferenceProgram.word 2,[0,0,f+1,M,0]⟩ =
        some ⟨ReferenceProgram.word 0,[0,0,f+1,M,0]⟩ := reference_step2 (f+1) M
    have ht := (reference_one_step h0).trans
      ((reference_one_step h1).trans ((reference_one_step h2).trans (ih (f+1))))
    simpa only [StateTransition.Reaches₁,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem reference_word3_ne88 : ReferenceProgram.word 3 ≠ ReferenceProgram.word 88 := by
  decide +kernel

theorem post_reference_trace (M : Nat) :
    StateTransition.Reaches₁ ReferencePreStep95
      ⟨ReferenceProgram.word 3,[0,0,M,0,0]⟩
      ⟨ReferenceProgram.word 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ := by
  have hi : StateTransition.Reaches ReferencePreStep95 (ReferenceProgram.stageCfg M)
      ⟨ReferenceProgram.word 3,[0,0,M,0,0]⟩ := by
    simpa only [StateTransition.Reaches,ReferenceProgram.stageCfg,reference_word0,Nat.zero_add]
      using (reference_init M 0).to_reflTransGen
  have hf := (reference_prewidth_execution95 M).to_reflTransGen
  have hne : (⟨ReferenceProgram.word 3,[0,0,M,0,0]⟩ : RhRegCfg) ≠
      ⟨ReferenceProgram.word 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ := by
    intro he
    exact reference_word3_ne88 (congrArg RhRegCfg.stack he)
  rcases StateTransition.reaches_total hi hf with hpost | hback
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpost with he | ht
    · exact False.elim (hne he.symm)
    · exact ht
  · have hsink : ReferencePreStep95
        ⟨ReferenceProgram.word 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ = none := by
      unfold ReferencePreStep95
      exact ite_eq_left rfl
    have he := (Relation.reflTransGen_iff_eq
      (Option.eq_none_iff_forall_not_mem.mp hsink)).mp hback
    exact False.elim (hne he)

theorem initializer (M f : Nat) :
    Relation.TransGen (Control.BoundedEdge 19)
      ⟨.outside 0,[0,0,f,M,0]⟩ ⟨.outside 3,[0,0,f+M,0,0]⟩ := by
  induction M generalizing f with
  | zero =>
    exact Relation.TransGen.single (Control.bounded_outside_edge 0 _ _ (by rfl))
  | succ M ih =>
    have h0 : Control.step ⟨.outside 0,[0,0,f,M+1,0]⟩ =
        some ⟨.outside 1,[0,0,f,M,0]⟩ := rfl
    have h1 : Control.step ⟨.outside 1,[0,0,f,M,0]⟩ =
        some ⟨.outside 2,[0,0,f+1,M,0]⟩ := rfl
    have h2 : Control.step ⟨.outside 2,[0,0,f+1,M,0]⟩ =
        some ⟨.outside 0,[0,0,f+1,M,0]⟩ := rfl
    have ht := (Relation.TransGen.single (Control.bounded_outside_edge 0 _ _ h0)).trans
      ((Relation.TransGen.single (Control.bounded_outside_edge 1 _ _ h1)).trans
        ((Relation.TransGen.single (Control.bounded_outside_edge 2 _ _ h2)).trans (ih (f+1))))
    simpa only [StateTransition.Reaches₁,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

end ConjectureMachines.Riemann95.TypedPrewidth
