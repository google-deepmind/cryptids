/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Raw

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary.Renaming

open Turing ConjectureMachines

/-- Only control states zero and 36 are exchanged; tape symbols are unchanged. -/
def swap (q : Fin 98) : Fin 98 := if q = 0 then 36 else if q = 36 then 0 else q

def renameCfg (c : Cfg 98 2) : Cfg 98 2 := ⟨swap c.state, c.tape⟩

theorem transition_rename : ∀ (q : Fin 98) (a : Fin 2),
    machine.transition (swap q) a = (Raw.machine.transition q a).map
      (fun e => (e.1, e.2.1, swap e.2.2)) := by decide

theorem step_rename (c : Cfg 98 2) :
    step machine (renameCfg c) = (step Raw.machine c).map renameCfg := by
  rcases c with ⟨q, tape⟩
  unfold step renameCfg
  dsimp only
  rw [transition_rename]
  cases h : Raw.machine.transition q tape.head with
  | none => rfl
  | some e => rcases e with ⟨b, d, q'⟩; rfl

theorem nSteps_rename (n : Nat) (c : Cfg 98 2) :
    nSteps n (renameCfg c) = (Raw.nSteps n c).map renameCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [nSteps, Raw.nSteps, step_rename]
    cases h : step Raw.machine c with
    | none => rfl
    | some c' => exact ih c'

theorem of_raw {n : Nat} {c c' : Cfg 98 2} (h : Raw.nSteps n c = some c') :
    nSteps n (renameCfg c) = some (renameCfg c') := by
  rw [nSteps_rename, h]
  rfl

end ConjectureMachines.Riemann95Auxiliary.Renaming
