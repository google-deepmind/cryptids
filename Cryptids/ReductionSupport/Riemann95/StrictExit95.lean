/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.PrecreditTrace95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open Schema
open ConjectureMachines.Riemann120 (quarterClock)

/-- A final zero DECf edge, separated from its possibly empty bounded prefix. -/
def StrictExitTrace (B : Nat) (a b : Cfg) : Prop :=
  ∃ mid, Relation.ReflTransGen (BoundedEdge B) a mid ∧ BoundedEdge B mid b ∧
    effect mid.control = .decnz 2 ∧ mid.regs.getD 2 0 = 0 ∧ mid.regs = b.regs

theorem strictExit_prepend (B : Nat) (a b c : Cfg)
    (hab : Relation.ReflTransGen (BoundedEdge B) a b)
    (hbc : StrictExitTrace B b c) : StrictExitTrace B a c := by
  obtain ⟨mid,hm,he,hf,hz,hr⟩ := hbc
  exact ⟨mid,hab.trans hm,he,hf,hz,hr⟩

theorem strict_test_zero (B x : Nat) (hB : 19 ≤ B) :
    StrictExitTrace B ⟨.outside finalTestId,[0,0,0,x,0]⟩ ⟨.outside 0,[0,0,0,x,0]⟩ := by
  refine ⟨⟨.outside finalTestId,[0,0,0,x,0]⟩,Relation.ReflTransGen.refl,?_,?_,?_,rfl⟩
  · exact ⟨by simpa using final_test_step 0 x,le_trans (outside_frontier_bound _) hB⟩
  · rfl
  · rfl

theorem strict_unwind0_zero (B x : Nat) (hB : 18 ≤ B) :
    StrictExitTrace B ⟨unwind 0,[0,0,0,x,0]⟩ ⟨.outside 0,[0,0,0,x,0]⟩ := by
  refine ⟨⟨unwind 0,[0,0,0,x,0]⟩,Relation.ReflTransGen.refl,?_,?_,?_,rfl⟩
  · exact bounded_unwind_edge B 0 0 x hB _ (by simpa using unwind0_step 0 x)
  · rfl
  · rfl

theorem strict_unwind_zero (B d x f : Nat) (hB : 5 * d + 18 ≤ B)
    (hO : 19 ≤ B) (hf : f ≤ d + 1) :
    StrictExitTrace B ⟨unwind d,[0,0,f,x,0]⟩ ⟨.outside 0,[0,0,0,x,0]⟩ := by
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    cases d with
    | zero =>
      cases f with
      | zero => exact strict_unwind0_zero B x hB
      | succ f =>
        have hz : f = 0 := by omega
        subst f
        apply strictExit_prepend B _ ⟨.outside finalTestId,[0,0,0,x,0]⟩ _
          (Relation.ReflTransGen.single ?_) (strict_test_zero B x hO)
        exact bounded_unwind_edge B 0 1 x hB _ (by simpa using unwind0_step 1 x)
    | succ d =>
      cases f with
      | zero =>
        cases d with
        | zero =>
          apply strictExit_prepend B _ ⟨.outside finalTestId,[0,0,0,x,0]⟩ _
            (Relation.ReflTransGen.single ?_) (strict_test_zero B x hO)
          exact bounded_unwind_edge B 1 0 x hB _ (unwind1_zero_step x)
        | succ d =>
          apply strictExit_prepend B _ ⟨unwind d,[0,0,0,x,0]⟩ _
            (Relation.ReflTransGen.single ?_) (ih d (by omega) 0 (by omega) (by omega))
          exact bounded_unwind_edge B (d+2) 0 x hB _ (unwind_succ_succ_zero_step d x)
      | succ f =>
        apply strictExit_prepend B _ ⟨unwind d,[0,0,f,x,0]⟩ _
          (Relation.ReflTransGen.single ?_) (ih d (by omega) f (by omega) (by omega))
        exact bounded_unwind_edge B (d+1) (f+1) x hB _ (unwind_succ_positive_step d f x)

theorem strict_finish_zero (J q f x : Nat) (hq : q ≤ quarterClock J) (hf : f ≤ q) :
    StrictExitTrace (widthBudget J) ⟨.entry q,[0,0,f,x,0]⟩ ⟨.outside 0,[0,0,0,x,0]⟩ := by
  have hO : 19 ≤ widthBudget J := by
    unfold widthBudget
    have h := le_max_left 16 (10 + 5 * quarterClock J)
    omega
  have hmax := le_max_right 16 (10 + 5 * quarterClock J)
  cases q with
  | zero =>
    have hz : f = 0 := by omega
    subst f
    apply strictExit_prepend (widthBudget J) _ ⟨.outside finalTestId,[0,0,0,x,0]⟩ _
      (Relation.ReflTransGen.single ?_) (strict_test_zero _ x hO)
    refine ⟨?_,?_⟩
    · simp [step,entry_zero]
    · rw [entry_frontier_length]
      omega
  | succ d =>
    have hB : 5 * d + 18 ≤ widthBudget J := by unfold widthBudget; omega
    apply strictExit_prepend (widthBudget J) _ ⟨unwind d,[0,0,f,x,0]⟩ _
      (Relation.ReflTransGen.single ?_) (strict_unwind_zero _ d x f hB hO hf)
    refine ⟨?_,?_⟩
    · simp [step,entry_succ]
    · rw [entry_frontier_length]
      unfold widthBudget
      omega

theorem strict_width_zero (x j f : Nat) (hr : Algorithm.residual j f = 0) :
    StrictExitTrace (widthBudget j) ⟨.entry 0,[0,0,f,x,j]⟩ ⟨.outside 0,[0,0,0,x,0]⟩ := by
  have hf : f/2^quarterClock j ≤ quarterClock j := by
    rw [Algorithm.residual_eq] at hr
    omega
  have hd := bounded_descent j 0 x j f (by omega)
  simp only [Nat.zero_add] at hd
  exact strictExit_prepend _ _ _ _ hd
    (strict_finish_zero j (quarterClock j) (f/2^quarterClock j) x (by omega) hf)

theorem strict_precredit_width_zero (x j f : Nat) (hr : Algorithm.residual j f = 0) :
    StrictExitTrace (widthBudget j) ⟨.outside widthCallId,[0,0,f,x,j]⟩
      ⟨.outside 0,[0,0,0,x+j,0]⟩ := by
  have hbudget : 19 ≤ widthBudget j := by
    unfold widthBudget
    have h := le_max_left 16 (10 + 5 * quarterClock j)
    omega
  have hp : Relation.TransGen (BoundedEdge (widthBudget j))
      ⟨.outside widthCallId,[0,0,f,x,j]⟩ ⟨.entry 0,[0,0,f,x+j,j]⟩ :=
    Relation.TransGen.mono (r := BoundedEdge 19) (p := BoundedEdge (widthBudget j))
      (fun _ _ h => ⟨h.1,le_trans h.2 hbudget⟩) _ _ (bounded_precredit x j f)
  exact strictExit_prepend _ _ _ _ hp.to_reflTransGen (strict_width_zero (x+j) j f hr)

end ConjectureMachines.Riemann95.Control
