/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition

/-! Derive the auxiliary presentation from the literal 95-state machine.
Labels 61, 72, and 95 duplicate label 0; all other labels embed the actual states. -/

@[expose] public section

namespace ConjectureMachines.Riemann95.Projection

/-- Three duplicate auxiliary labels map to entry 0; all 95 actual labels are counted. -/
def stateMap (q : Fin 98) : Fin 95 :=
  if h : q.val = 61 ∨ q.val = 72 ∨ q.val = 95 then 0
  else if h1 : q.val < 61 then ⟨q.val, by omega⟩
  else if h2 : q.val < 72 then ⟨q.val - 1, by omega⟩
  else if h3 : q.val < 95 then ⟨q.val - 2, by omega⟩
  else ⟨q.val - 3, by omega⟩

/-- Choose the canonical auxiliary label for each actual state. -/
def liftState (q : Fin 95) : Fin 98 :=
  if h : q.val < 61 then ⟨q.val, by omega⟩
  else if h1 : q.val < 71 then ⟨q.val + 1, by omega⟩
  else if h2 : q.val < 93 then ⟨q.val + 2, by omega⟩
  else ⟨q.val + 3, by omega⟩

theorem stateMap_liftState : ∀ q : Fin 95, stateMap (liftState q) = q := by decide +kernel

end ConjectureMachines.Riemann95.Projection

namespace ConjectureMachines.Riemann95Auxiliary

open Turing ConjectureMachines

/-- Expand labels without maintaining a second transition table. -/
def machine : Machine 98 2 :=
  ⟨fun q a => (Riemann95.machine.transition (Riemann95.Projection.stateMap q) a).map
    (fun e => (e.1, e.2.1, Riemann95.Projection.liftState e.2.2))⟩

def nSteps : Nat → Cfg 98 2 → Option (Cfg 98 2)
  | 0, c => some c
  | n + 1, c => (step machine c).bind (nSteps n)

end ConjectureMachines.Riemann95Auxiliary
