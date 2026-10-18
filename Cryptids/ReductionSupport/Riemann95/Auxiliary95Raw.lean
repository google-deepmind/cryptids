/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95

/-! Derive the raw auxiliary table by exchanging labels 0 and 36. -/

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary

open Turing ConjectureMachines

namespace Renaming

/-- Only control states zero and 36 are exchanged; tape symbols are unchanged. -/
def swap (q : Fin 98) : Fin 98 := if q = 0 then 36 else if q = 36 then 0 else q

theorem swap_involutive (q : Fin 98) : swap (swap q) = q := by
  by_cases h0 : q = 0
  · subst q; rfl
  by_cases h36 : q = 36
  · subst q; rfl
  simp only [swap, h0, h36, ↓reduceIte]

end Renaming

namespace Raw

/-- The same auxiliary machine before renaming its control labels. -/
def machine : Machine 98 2 :=
  ⟨fun q a => (Riemann95Auxiliary.machine.transition (Renaming.swap q) a).map
    (fun e => (e.1, e.2.1, Renaming.swap e.2.2))⟩

def nSteps : Nat → Cfg 98 2 → Option (Cfg 98 2)
  | 0, c => some c
  | n + 1, c => (step machine c).bind (nSteps n)

end Raw

namespace Renaming

def renameCfg (c : Cfg 98 2) : Cfg 98 2 := ⟨swap c.state, c.tape⟩

theorem transition_rename : ∀ (q : Fin 98) (a : Fin 2),
    machine.transition (swap q) a = (Raw.machine.transition q a).map
      (fun e => (e.1, e.2.1, swap e.2.2)) := by
  intro q a
  change _ = ((machine.transition (swap q) a).map _).map _
  cases machine.transition (swap q) a with
  | none => rfl
  | some e =>
    rcases e with ⟨b, d, q'⟩
    simp only [Option.map_some, swap_involutive]

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

end Renaming

end ConjectureMachines.Riemann95Auxiliary
