/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ParserSchema95
public import Cryptids.ReductionSupport.Riemann95.Physical95
public import Cryptids.ReductionSupport.Riemann95.ControlStep95

@[expose] public section

namespace ConjectureMachines.Riemann95.Dispatch

open Turing ConjectureMachines
open CryptidsResearch.Recursive95Parser

def terminal : Schema.ControlWord → Fin 95
  | .outside s => outsideTerminal s
  | .entry _ => 58
  | .local _ s => localTerminal s

/-- The unbounded typed caller frontier follows this exact literal machine. -/
theorem actual_parse (c : Schema.ControlWord) :
    walkInternal 15 (Control.walked c) = some (terminal c) := by
  cases c with
  | outside s => exact outsideTerminal_walk s
  | entry d => exact entryWalk_parse d
  | «local» d s => exact localWalk_parse d s

def nativeCorrect (c : Schema.ControlWord) : Prop :=
  match Control.effect c with
  | .halt => machine.transition (terminal c) 1 = none
  | .inc r => terminal c = Physical.incLeaf r
  | .decnz r => terminal c = Physical.decLeaf r
  | .jump _ _ => ∃ next : Fin 95,
      machine.transition (terminal c) 1 = some (0, .left, next)

instance (c : Schema.ControlWord) : Decidable (nativeCorrect c) := by
  unfold nativeCorrect
  cases Control.effect c <;> infer_instance

theorem outside_nativeCorrect : ∀ s : Fin 97, nativeCorrect (.outside s) := by
  decide +kernel

theorem local_nativeCorrect : ∀ s : Fin 22, nativeCorrect (.local 0 s) := by
  decide +kernel

/-- Native arithmetic indices are literal Fin5 leaves; halt and jump use the actual ONE cell. -/
theorem nativeCorrect_all (c : Schema.ControlWord) : nativeCorrect c := by
  cases c with
  | outside s => exact outside_nativeCorrect s
  | entry d => rfl
  | «local» d s => exact local_nativeCorrect s

end ConjectureMachines.Riemann95.Dispatch
