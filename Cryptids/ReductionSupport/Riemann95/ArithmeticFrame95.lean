/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Terminal95

@[expose] public section

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
