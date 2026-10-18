/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95

@[expose] public section
namespace ConjectureMachines.Riemann95.Projection

open Turing ConjectureMachines

/-- Three duplicate proof-only labels map to entry0; all95 actual labels are counted. -/
def stateMap (q : Fin 98) : Fin 95 :=
  if h : q.val = 61 ∨ q.val = 72 ∨ q.val = 95 then 0
  else if h1 : q.val < 61 then ⟨q.val, by omega⟩
  else if h2 : q.val < 72 then ⟨q.val - 1, by omega⟩
  else if h3 : q.val < 95 then ⟨q.val - 2, by omega⟩
  else ⟨q.val - 3, by omega⟩

def cfgMap (c : Cfg 98 2) : Cfg 95 2 := ⟨stateMap c.state, c.tape⟩

theorem transition_map : ∀ (q : Fin 98) (a : Fin 2),
    machine.transition (stateMap q) a =
      (Riemann95Auxiliary.machine.transition q a).map
        (fun e => (e.1, e.2.1, stateMap e.2.2)) := by
  decide +kernel

theorem step_map (c : Cfg 98 2) :
    step machine (cfgMap c) = (step Riemann95Auxiliary.machine c).map cfgMap := by
  rcases c with ⟨q, tape⟩
  unfold step cfgMap
  dsimp only
  rw [transition_map]
  cases h : Riemann95Auxiliary.machine.transition q tape.head with
  | none => rfl
  | some e => rcases e with ⟨b, d, q'⟩; rfl

theorem nSteps_map (n : Nat) (c : Cfg 98 2) :
    nSteps n (cfgMap c) = (Riemann95Auxiliary.nSteps n c).map cfgMap := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [nSteps, Riemann95Auxiliary.nSteps, step_map]
    cases h : step Riemann95Auxiliary.machine c with
    | none => rfl
    | some c' => exact ih c'

theorem of_aux {n : Nat} {c c' : Cfg 98 2}
    (h : Riemann95Auxiliary.nSteps n c = some c') :
    nSteps n (cfgMap c) = some (cfgMap c') := by
  rw [nSteps_map, h]
  rfl

end ConjectureMachines.Riemann95.Projection
