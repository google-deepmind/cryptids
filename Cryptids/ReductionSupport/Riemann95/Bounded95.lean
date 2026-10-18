/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Unwind95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open StateTransition Schema
open ConjectureMachines.Riemann120 (quarterClock)

/-- Every executed source frontier has the requested physical fill budget. -/
def BoundedEdge (B : Nat) (a b : Cfg) : Prop :=
  step a = some b ∧ (walked a.control).length + 3 ≤ B

def widthBudget (j : Nat) : Nat := max 16 (10 + 5 * quarterClock j) + 5

theorem half_frontier_bound (k : Fin 3) (d : Nat) (s : Fin 8)
    (hs : s.val < 7) (m v a x other : Nat) :
    (walked (halfCfg k d s m v a x other).control).length + 3 ≤ 5 * d + 18 := by
  have hn : s.val ≠ 7 := by omega
  simp only [halfCfg,halfWord,hn,ite_false,walked]
  have h := localWalk_length d ⟨7 * k.val + s.val,by omega⟩
  omega

theorem bounded_half_edge (B : Nat) (k : Fin 3) (d : Nat)
    (hB : 5 * d + 18 ≤ B) (s : Fin 8) (hs : s.val < 7)
    (m v a x other : Nat) (next : Cfg)
    (he : step (halfCfg k d s m v a x other) = some next) :
    BoundedEdge B (halfCfg k d s m v a x other) next :=
  ⟨he,le_trans (half_frontier_bound k d s hs m v a x other) hB⟩

theorem bounded_half_restore (B : Nat) (k : Fin 3) (d m v a x other : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) (halfCfg k d 4 m v a x other)
      (halfCfg k d 7 m 0 (a + v) x other) := by
  induction v generalizing a with
  | zero =>
    exact Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 4 (by decide) m 0 a x other _
          (half_step4 k d m 0 a x other)))
  | succ v ih =>
    have h1 : Relation.TransGen (BoundedEdge B) (halfCfg k d 4 m (v + 1) a x other)
        (halfCfg k d 5 m v a x other) :=
      Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 4 (by decide) m (v + 1) a x other _
          (half_step4 k d m (v + 1) a x other)))
    have h2 : Relation.TransGen (BoundedEdge B) (halfCfg k d 5 m v a x other)
        (halfCfg k d 6 m v (a + 1) x other) :=
      Relation.TransGen.single
        (bounded_half_edge B k d hB 5 (by decide) m v a x other _
          (half_step5 k d m v a x other))
    have h3 : Relation.TransGen (BoundedEdge B) (halfCfg k d 6 m v (a + 1) x other)
        (halfCfg k d 4 m v (a + 1) x other) :=
      Relation.TransGen.single
        (bounded_half_edge B k d hB 6 (by decide) m v (a + 1) x other _
          (half_step6 k d m v (a + 1) x other))
    have he : a + (v + 1) = (a + 1) + v := by omega
    rw [he]
    exact h1.trans (h2.trans (h3.trans (ih (a + 1))))

theorem bounded_half_eval (B : Nat) (k : Fin 3) (d m v a x other : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) (halfCfg k d 0 m v a x other)
      (halfCfg k d 7 m 0 (a/2 + v) x other) := by
  induction a using Nat.twoStepInduction generalizing v with
  | zero =>
    have h : Relation.TransGen (BoundedEdge B) (halfCfg k d 0 m v 0 x other)
        (halfCfg k d 4 m v 0 x other) :=
      Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 0 (by decide) m v 0 x other _
          (half_step0 k d m v 0 x other)))
    simpa only [Nat.zero_div, Nat.zero_add, Nat.add_zero] using
      h.trans (bounded_half_restore B k d m v 0 x other hB)
  | one =>
    have h1 : Relation.TransGen (BoundedEdge B) (halfCfg k d 0 m v 1 x other)
        (halfCfg k d 1 m v 0 x other) :=
      Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 0 (by decide) m v 1 x other _
          (half_step0 k d m v 1 x other)))
    have h2 : Relation.TransGen (BoundedEdge B) (halfCfg k d 1 m v 0 x other)
        (halfCfg k d 4 m v 0 x other) :=
      Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 1 (by decide) m v 0 x other _
          (half_step1 k d m v 0 x other)))
    simpa only [Nat.reduceDiv, Nat.zero_add, Nat.add_zero] using
      h1.trans (h2.trans (bounded_half_restore B k d m v 0 x other hB))
  | more a ih _ =>
    have h1 : Relation.TransGen (BoundedEdge B) (halfCfg k d 0 m v (a + 2) x other)
        (halfCfg k d 1 m v (a + 1) x other) :=
      Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 0 (by decide) m v (a + 2) x other _
          (half_step0 k d m v (a + 2) x other)))
    have h2 : Relation.TransGen (BoundedEdge B) (halfCfg k d 1 m v (a + 1) x other)
        (halfCfg k d 2 m v a x other) :=
      Relation.TransGen.single (by
        simpa using
          (bounded_half_edge B k d hB 1 (by decide) m v (a + 1) x other _
          (half_step1 k d m v (a + 1) x other)))
    have h3 : Relation.TransGen (BoundedEdge B) (halfCfg k d 2 m v a x other)
        (halfCfg k d 3 m (v + 1) a x other) :=
      Relation.TransGen.single
        (bounded_half_edge B k d hB 2 (by decide) m v a x other _
          (half_step2 k d m v a x other))
    have h4 : Relation.TransGen (BoundedEdge B) (halfCfg k d 3 m (v + 1) a x other)
        (halfCfg k d 0 m (v + 1) a x other) :=
      Relation.TransGen.single
        (bounded_half_edge B k d hB 3 (by decide) m (v + 1) a x other _
          (half_step3 k d m (v + 1) a x other))
    have he : (a + 2)/2 + v = a/2 + (v + 1) := by omega
    rw [he]
    exact h1.trans (h2.trans (h3.trans (h4.trans (ih (v + 1)))))

theorem bounded_halfj_first (B d m v f x j : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) ⟨.local d 0,[m,v,f,x,j]⟩ ⟨.local d 7,[m,0,f,x,j/2 + v]⟩ :=
  bounded_half_eval B 0 d m v j x f hB

theorem bounded_halfj_second (B d m v f x j : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) ⟨.local d 7,[m,v,f,x,j]⟩ ⟨.local d 14,[m,0,f,x,j/2 + v]⟩ :=
  bounded_half_eval B 1 d m v j x f hB

theorem bounded_halff (B d m v f x j : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) ⟨.local d 14,[m,v,f,x,j]⟩
      ⟨.entry (d + 1),[m,0,f/2 + v,x,j]⟩ :=
  bounded_half_eval B 2 d m v f x j hB


theorem entry_frontier_length (d : Nat) :
    (walked (.entry d)).length + 3 = 5 * d + 10 := by
  simp [walked,List.length_append,callerPrefix_length]

theorem bounded_body (B d f x j : Nat) (hB : 5 * d + 18 ≤ B) :
    Relation.TransGen (BoundedEdge B) ⟨.entry d,[0,0,f,x,j + 1]⟩
      ⟨.entry (d + 1),[0,0,f/2,x,j/4]⟩ := by
  have he : Relation.TransGen (BoundedEdge B) ⟨.entry d,[0,0,f,x,j + 1]⟩
      ⟨.local d 0,[0,0,f,x,j]⟩ := Relation.TransGen.single
    ⟨entry_positive_step d f x j,by rw [entry_frontier_length]; omega⟩
  have h1 := bounded_halfj_first B d 0 0 f x j hB
  have h2 := bounded_halfj_second B d 0 0 f x (j/2) hB
  have h3 := bounded_halff B d 0 0 f x (j/2/2) hB
  simp only [Nat.add_zero] at h1 h2 h3
  have hquarter : j/2/2 = j/4 := by omega
  rw [hquarter] at h2 h3
  exact he.trans (h1.trans (h2.trans h3))

theorem bounded_descent (J d x j f : Nat)
    (hclock : d + quarterClock j ≤ quarterClock J) :
    Relation.ReflTransGen (BoundedEdge (widthBudget J)) ⟨.entry d,[0,0,f,x,j]⟩
      ⟨.entry (d + quarterClock j),[0,0,f/2^quarterClock j,x,0]⟩ := by
  induction j using Nat.strong_induction_on generalizing d f with
  | h j ih =>
    cases j with
    | zero =>
      simp only [quarterClock,pow_zero,Nat.div_one,Nat.add_zero]
      exact Relation.ReflTransGen.refl
    | succ j =>
      have hclockj : quarterClock (j + 1) = quarterClock (j/4) + 1 := by
        rw [quarterClock]
        omega
      have hB : 5 * d + 18 ≤ widthBudget J := by
        unfold widthBudget
        have hm := le_max_right 16 (10 + 5 * quarterClock J)
        omega
      have hclock' : d + 1 + quarterClock (j/4) ≤ quarterClock J := by omega
      have hb := bounded_body (widthBudget J) d f x j hB
      have hi := ih (j/4) (by omega) (d + 1) (f/2) hclock'
      have hd : d + 1 + quarterClock (j/4) = d + quarterClock (j + 1) := by omega
      have hf : f/2/2^quarterClock (j/4) = f/2^quarterClock (j + 1) := by
        rw [hclockj,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 2]
      rw [hd,hf] at hi
      exact hb.to_reflTransGen.trans hi

end ConjectureMachines.Riemann95.Control
