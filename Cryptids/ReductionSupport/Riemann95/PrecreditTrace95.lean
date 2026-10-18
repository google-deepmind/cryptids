/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.BoundedUnwind95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open Schema

def widthCallId : Fin 97 := 88

theorem widthCall_word : word (.outside widthCallId) = [1,1,1,1] := by decide +kernel

theorem bounded_outside_edge (s : Fin 97) (regs : List Nat) (next : Cfg)
    (he : step ⟨.outside s, regs⟩ = some next) :
    BoundedEdge 19 ⟨.outside s,regs⟩ next := ⟨he,outside_frontier_bound s⟩

private theorem pc88 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 88,[m,v,f,x,j]⟩
      ⟨.outside (if j = 0 then 92 else 89),[m,v,f,x,j-1]⟩ := by
  apply bounded_outside_edge
  by_cases hj : j = 0 <;> simp [step,instruction,outsideInstrs,hj]

private theorem pc89 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 89,[m,v,f,x,j]⟩ ⟨.outside 90,[m,v,f,x+1,j]⟩ := by
  apply bounded_outside_edge
  simp [step,instruction,outsideInstrs]

private theorem pc90 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 90,[m,v,f,x,j]⟩ ⟨.outside 91,[m,v+1,f,x,j]⟩ := by
  apply bounded_outside_edge
  simp [step,instruction,outsideInstrs]

private theorem pc91 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 91,[m,v,f,x,j]⟩ ⟨.outside 88,[m,v,f,x,j]⟩ := by
  apply bounded_outside_edge
  simp [step,instruction,outsideInstrs]

private theorem pc92 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 92,[m,v,f,x,j]⟩
      ⟨if v = 0 then .entry 0 else .outside 93,[m,v-1,f,x,j]⟩ := by
  apply bounded_outside_edge
  by_cases hv : v = 0 <;> simp [step,instruction,outsideInstrs,hv]

private theorem pc93 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 93,[m,v,f,x,j]⟩ ⟨.outside 94,[m,v,f,x,j+1]⟩ := by
  apply bounded_outside_edge
  simp [step,instruction,outsideInstrs]

private theorem pc94 (x v f m j : Nat) :
    BoundedEdge 19 ⟨.outside 94,[m,v,f,x,j]⟩ ⟨.outside 92,[m,v,f,x,j]⟩ := by
  apply bounded_outside_edge
  simp [step,instruction,outsideInstrs]

theorem precredit_consume (x v f m j : Nat) :
    Relation.TransGen (BoundedEdge 19) ⟨.outside 88,[m,v,f,x,j]⟩
      ⟨.outside 92,[m,v+j,f,x+j,0]⟩ := by
  induction j generalizing x v with
  | zero => exact Relation.TransGen.single (by simpa using pc88 x v f m 0)
  | succ j ih =>
    have h1 : Relation.TransGen (BoundedEdge 19) ⟨.outside 88,[m,v,f,x,j+1]⟩
        ⟨.outside 89,[m,v,f,x,j]⟩ := Relation.TransGen.single (by simpa using pc88 x v f m (j+1))
    have h2 := Relation.TransGen.single (pc89 x v f m j)
    have h3 := Relation.TransGen.single (pc90 (x+1) v f m j)
    have h4 := Relation.TransGen.single (pc91 (x+1) (v+1) f m j)
    have hx : x+(j+1) = (x+1)+j := by omega
    have hv : v+(j+1) = (v+1)+j := by omega
    rw [hx,hv]
    exact h1.trans (h2.trans (h3.trans (h4.trans (ih (x+1) (v+1)))))

theorem precredit_restore (x v f m j : Nat) :
    Relation.TransGen (BoundedEdge 19) ⟨.outside 92,[m,v,f,x,j]⟩
      ⟨.entry 0,[m,0,f,x,j+v]⟩ := by
  induction v generalizing j with
  | zero => exact Relation.TransGen.single (by simpa using pc92 x 0 f m j)
  | succ v ih =>
    have h1 : Relation.TransGen (BoundedEdge 19) ⟨.outside 92,[m,v+1,f,x,j]⟩
        ⟨.outside 93,[m,v,f,x,j]⟩ := Relation.TransGen.single (by simpa using pc92 x (v+1) f m j)
    have h2 := Relation.TransGen.single (pc93 x v f m j)
    have h3 := Relation.TransGen.single (pc94 x v f m (j+1))
    have hj : j+(v+1) = (j+1)+v := by omega
    rw [hj]
    exact h1.trans (h2.trans (h3.trans (ih (j+1))))

theorem bounded_precredit_all (x v f m j : Nat) :
    Relation.TransGen (BoundedEdge 19) ⟨.outside widthCallId,[m,v,f,x,j]⟩
      ⟨.entry 0,[m,0,f,x+j,j+v]⟩ := by
  have h1 := precredit_consume x v f m j
  have h2 := precredit_restore (x+j) (v+j) f m 0
  have hj : v+j = j+v := by omega
  simpa only [widthCallId,Nat.zero_add,hj] using h1.trans h2

theorem bounded_precredit (x j f : Nat) :
    Relation.TransGen (BoundedEdge 19) ⟨.outside widthCallId,[0,0,f,x,j]⟩
      ⟨.entry 0,[0,0,f,x+j,j]⟩ := by
  simpa only [Nat.add_zero] using bounded_precredit_all x 0 f 0 j

theorem bounded_precredit_width (x j f : Nat) :
    Relation.TransGen (BoundedEdge (widthBudget j)) ⟨.outside widthCallId,[0,0,f,x,j]⟩
      ⟨if Algorithm.residual j f = 0 then .outside 0 else .outside finalHaltId,
        [0,0,Algorithm.residual j f-1,x+j,0]⟩ := by
  have hbudget : 19 ≤ widthBudget j := by
    unfold widthBudget
    have h := le_max_left 16 (10 + 5 * ConjectureMachines.Riemann120.quarterClock j)
    omega
  have hp : Relation.TransGen (BoundedEdge (widthBudget j))
      ⟨.outside widthCallId,[0,0,f,x,j]⟩ ⟨.entry 0,[0,0,f,x+j,j]⟩ :=
    Relation.TransGen.mono (r := BoundedEdge 19) (p := BoundedEdge (widthBudget j))
      (fun _ _ h => ⟨h.1,le_trans h.2 hbudget⟩) _ _ (bounded_precredit x j f)
  exact hp.trans (bounded_width_outcome (x+j) j f)

end ConjectureMachines.Riemann95.Control
