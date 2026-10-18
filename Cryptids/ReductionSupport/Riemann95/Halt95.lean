/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ParserTape95
public import Cryptids.ReductionSupport.Riemann95.Physical95
public import Cryptids.ReductionSupport.Riemann95.ControlRoles95

@[expose] public section

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
  have hwalk : CryptidsResearch.Recursive95Parser.walkInternal 15 bits = some 61 := by
    rfl
  have hroot : Physical.rootCfg P (Schema.word (.outside Control.finalHaltId)) bank =
      ⟨15, Tape.mk' L (ListBlank.append bits R)⟩ := by
    simp only [Physical.rootCfg, hword, List.length_cons,
      List.length_nil, bits, L, R, ListBlank.append_mk, List.cons_append, List.nil_append]
    rfl
  refine ⟨6, ⟨61, Tape.mk' (ListBlank.append bits.reverse L) R⟩, ?_, ?_⟩
  · rw [hroot]
    exact CryptidsResearch.Recursive95Parser.walkInternal_nSteps bits 15 61 L R hwalk
  · rfl

end ConjectureMachines.Riemann95
