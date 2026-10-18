/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Bounded95
public import Cryptids.ReductionSupport.Riemann95.Algorithm95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open StateTransition Schema
open ConjectureMachines.Riemann120 (quarterClock)

theorem unwind_frontier_bound (d f x : Nat) :
    (walked (⟨unwind d,[0,0,f,x,0]⟩ : Cfg).control).length + 3 ≤ 5 * d + 18 := by
  have h := localWalk_length d unwindId
  change (localWalk d unwindId).length + 3 ≤ 5 * d + 18
  omega

theorem bounded_unwind_edge (B d f x : Nat) (hB : 5 * d + 18 ≤ B) (next : Cfg)
    (he : step ⟨unwind d, [0, 0, f, x, 0]⟩ = some next) :
    BoundedEdge B ⟨unwind d,[0,0,f,x,0]⟩ next :=
  ⟨he,le_trans (unwind_frontier_bound d f x) hB⟩

theorem bounded_unwind_eval (B d x f : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) ⟨unwind d,[0,0,f,x,0]⟩
      ⟨if f ≤ d ∧ (d-f)%2 = 0 then .outside 0 else .outside finalTestId,
        [0,0,f-(d+1),x,0]⟩ := by
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    cases d with
    | zero =>
      cases f with
      | zero =>
        exact Relation.TransGen.single (by
          simpa using bounded_unwind_edge B 0 0 x hB _ (unwind0_step 0 x))
      | succ f =>
        exact Relation.TransGen.single (by
          simpa using bounded_unwind_edge B 0 (f+1) x hB _ (unwind0_step (f+1) x))
    | succ d =>
      cases f with
      | zero =>
        cases d with
        | zero =>
          exact Relation.TransGen.single (by
            simpa using bounded_unwind_edge B 1 0 x hB _ (unwind1_zero_step x))
        | succ d =>
          have hs : Relation.TransGen (BoundedEdge B) ⟨unwind (d+2),[0,0,0,x,0]⟩
              ⟨unwind d,[0,0,0,x,0]⟩ := Relation.TransGen.single
            (bounded_unwind_edge B (d+2) 0 x hB _ (unwind_succ_succ_zero_step d x))
          have hpar : (d+1+1)%2 = d%2 := by omega
          have hi := ih d (by omega) 0 (by omega)
          simpa only [Nat.zero_le,Nat.sub_zero,true_and,Nat.zero_sub,hpar]
            using hs.trans hi
      | succ f =>
        have hs : Relation.TransGen (BoundedEdge B) ⟨unwind (d+1),[0,0,f+1,x,0]⟩
            ⟨unwind d,[0,0,f,x,0]⟩ := Relation.TransGen.single
          (bounded_unwind_edge B (d+1) (f+1) x hB _ (unwind_succ_positive_step d f x))
        have hc : (f+1 ≤ d+1 ∧ (d+1-(f+1))%2 = 0) ↔
            (f ≤ d ∧ (d-f)%2 = 0) := by omega
        have hsub : f+1-(d+1+1) = f-(d+1) := by omega
        simpa only [hc,hsub] using hs.trans (ih d (by omega) f (by omega))

theorem outside_frontier_bound (s : Fin 97) :
    (walked (.outside s)).length + 3 ≤ 19 :=
  Nat.add_le_add_right (outsideWalk_length s) 3

theorem bounded_finish (J q f x : Nat) (hq : q ≤ quarterClock J) :
    Relation.TransGen (BoundedEdge (widthBudget J)) ⟨.entry q,[0,0,f,x,0]⟩
      ⟨if f-q = 0 then .outside 0 else .outside finalHaltId,[0,0,(f-q)-1,x,0]⟩ := by
  have hbudget : 19 ≤ widthBudget J := by
    unfold widthBudget
    have hm := le_max_left 16 (10 + 5 * quarterClock J)
    omega
  have hmax := le_max_right 16 (10 + 5 * quarterClock J)
  have test (a : Nat) : Relation.TransGen (BoundedEdge (widthBudget J))
      ⟨.outside finalTestId,[0,0,a,x,0]⟩
      ⟨if a = 0 then .outside 0 else .outside finalHaltId,[0,0,a-1,x,0]⟩ :=
    Relation.TransGen.single ⟨final_test_step a x,le_trans (outside_frontier_bound _) hbudget⟩
  cases q with
  | zero =>
    have hs : Relation.TransGen (BoundedEdge (widthBudget J)) ⟨.entry 0,[0,0,f,x,0]⟩
        ⟨.outside finalTestId,[0,0,f,x,0]⟩ := Relation.TransGen.single
      ⟨by simp [step,entry_zero],by rw [entry_frontier_length]; omega⟩
    simpa only [Nat.sub_zero] using hs.trans (test f)
  | succ d =>
    have hs : Relation.TransGen (BoundedEdge (widthBudget J))
        ⟨.entry (d+1),[0,0,f,x,0]⟩ ⟨unwind d,[0,0,f,x,0]⟩ :=
      Relation.TransGen.single ⟨by simp [step,entry_succ],by
        rw [entry_frontier_length]
        unfold widthBudget
        omega⟩
    have hlocal : 5 * d + 18 ≤ widthBudget J := by unfold widthBudget; omega
    have hu := hs.trans (bounded_unwind_eval (widthBudget J) d x f hlocal)
    by_cases hc : f ≤ d ∧ (d-f)%2 = 0
    · have hz : f-(d+1) = 0 := by omega
      simpa only [ite_eq_left hc,hz,Nat.zero_sub,ite_true] using hu
    · simp only [ite_eq_right hc] at hu
      exact hu.trans (test (f-(d+1)))

theorem bounded_width_outcome (x j f : Nat) :
    Relation.TransGen (BoundedEdge (widthBudget j)) ⟨.entry 0,[0,0,f,x,j]⟩
      ⟨if Algorithm.residual j f = 0 then .outside 0 else .outside finalHaltId,
        [0,0,Algorithm.residual j f-1,x,0]⟩ := by
  have hd := bounded_descent j 0 x j f (by omega)
  simp only [Nat.zero_add] at hd
  have hf := (bounded_finish j (quarterClock j) (f/2^quarterClock j) x (by omega)).trans_right hd
  simpa only [Algorithm.residual_eq] using hf

end ConjectureMachines.Riemann95.Control
