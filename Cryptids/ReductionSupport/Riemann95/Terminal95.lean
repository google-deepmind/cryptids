/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Parser95
public import Cryptids.ReductionSupport.Riemann95.Physical95
public import Cryptids.ReductionSupport.Riemann95.ControlStep95

/-! # Terminal execution and arithmetic frames -/

@[expose] public section

/-! ## Terminal configurations -/

section

namespace ConjectureMachines.Riemann95.Dispatch

open Turing ConjectureMachines
open ConjectureMachines.Riemann95.Parser

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

end

/-! ## Arithmetic frames -/

section

namespace ConjectureMachines.Riemann95.Dispatch

open Turing ConjectureMachines

theorem entry_append_zero (d : Nat) : Schema.entry d ++ [0] = Schema.callerPrefix d := by
  have hp : ∃ p : List (Fin 2), Schema.callerPrefix d = p ++ [0] := by
    cases d with
    | zero => exact ⟨[1,1,1,1,1], rfl⟩
    | succ d =>
      refine ⟨Schema.callerPrefix d ++ [1,1,1,1], ?_⟩
      simp only [Schema.callerPrefix, List.append_assoc]
      rfl
  obtain ⟨p, hp⟩ := hp
  simp only [Schema.entry, hp, List.dropLast_concat]

def arithmeticPrefix (c : Schema.ControlWord) : Prop :=
  match Control.effect c with
  | .inc _ | .decnz _ => Control.walked c =
      Schema.word c ++ List.replicate ((Control.walked c).length - (Schema.word c).length) 0
  | _ => True

instance (c : Schema.ControlWord) : Decidable (arithmeticPrefix c) := by
  unfold arithmeticPrefix
  cases Control.effect c <;> infer_instance

theorem outside_arithmeticPrefix : ∀ s : Fin 97, arithmeticPrefix (.outside s) := by
  decide +kernel

theorem entry_arithmeticPrefix (d : Nat) : arithmeticPrefix (.entry d) := by
  have hlen : (Control.walked (.entry d)).length - (Schema.word (.entry d)).length = 2 := by
    simp only [Control.walked, Schema.word, List.length_append, Schema.callerPrefix_length,
      Schema.entry_length, List.length_cons, List.length_nil]
    omega
  change Schema.callerPrefix d ++ [0] = Schema.entry d ++
    List.replicate ((Control.walked (.entry d)).length - (Schema.word (.entry d)).length) 0
  rw [hlen, ← entry_append_zero]
  simp only [List.append_assoc]
  rfl

theorem local_arithmeticPrefix (d : Nat) (s : Fin 22) : arithmeticPrefix (.local d s) := by
  fin_cases s <;>
    simp [arithmeticPrefix, Control.effect, Control.localEffects, Control.walked,
      Schema.word, Schema.localWalk, Schema.localWalkSuffix, Schema.localWalkSuffixes,
      Schema.suffix, Schema.suffixes, List.length_append, Nat.add_sub_add_left,
      List.append_assoc]

/-- The arithmetic dispatcher consumes exactly the word followed by blank cells. -/
theorem arithmeticPrefix_all (c : Schema.ControlWord) : arithmeticPrefix c := by
  cases c with
  | outside s => exact outside_arithmeticPrefix s
  | entry d => exact entry_arithmeticPrefix d
  | «local» d s => exact local_arithmeticPrefix d s

end ConjectureMachines.Riemann95.Dispatch

end

/-! ## Halting transition -/

section

namespace ConjectureMachines.Riemann95

open Turing ConjectureMachines

/-- The final typed HALT word reaches the actual unique NONE cell before touching the bank. -/
theorem physical_halt_word (P : Nat) (bank : List Nat) :
    ∃ s, ∃ c : Cfg 95 2,
      nSteps s (Physical.rootCfg P (Schema.word (.outside Control.finalHaltId)) bank) =
        some c ∧ step machine c = none := by
  let bits : List (Fin 2) := [1,1,1,1,1,1]
  let L := Riemann120.rootLeftOf true
  let R := ListBlank.mk ([1] ++ List.replicate (P - 7) 0 ++ [1,0] ++
    Semantics.Riemann.Layer1.encodeRegs bank)
  have hword : Schema.word (.outside Control.finalHaltId) = bits ++ [1] := rfl
  have hwalk : ConjectureMachines.Riemann95.Parser.walkInternal 15 bits = some 61 := by
    rfl
  have hroot : Physical.rootCfg P (Schema.word (.outside Control.finalHaltId)) bank =
      ⟨15, Tape.mk' L (ListBlank.append bits R)⟩ := by
    simp only [Physical.rootCfg, hword, List.length_cons,
      List.length_nil, bits, L, R, ListBlank.append_mk, List.cons_append, List.nil_append]
    rfl
  refine ⟨6, ⟨61, Tape.mk' (ListBlank.append bits.reverse L) R⟩, ?_, ?_⟩
  · rw [hroot]
    exact ConjectureMachines.Riemann95.Parser.walkInternal_nSteps bits 15 61 L R hwalk
  · rfl

end ConjectureMachines.Riemann95

end
