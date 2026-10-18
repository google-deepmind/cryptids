/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ArithmeticFrame95
public import Cryptids.ReductionSupport.Riemann95.TypedClosure95

@[expose] public section

namespace ConjectureMachines.Riemann95.Dispatch

open Turing ConjectureMachines
open Riemann120.Layer2

theorem inc_return_guard (c : Schema.ControlWord) (r : Fin 5)
    (he : Control.effect c = .inc r) :
    Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 (Control.walked c).reverse).reverse).reverse = true := by
  have hc := Control.instruction_words c
  simp only [Control.rawInstr, he, Control.returned, Bool.false_eq_true, ite_false] at hc
  cases hi : Control.instruction c with
  | halt => rw [hi, Control.toRhInstr] at hc; cases hc
  | jump n => rw [hi, Control.toRhInstr] at hc; cases hc
  | inc r' n =>
    rw [hi, Control.toRhInstr] at hc
    obtain ⟨_, hw⟩ := RhInstr.inc.inj hc
    rw [hw]
    exact (Schema.word_noThree n).2
  | decnz r' p z => rw [hi, Control.toRhInstr] at hc; cases hc

theorem dec_return_guards (c : Schema.ControlWord) (r : Fin 5)
    (he : Control.effect c = .decnz r) :
    Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 0 (Control.walked c).reverse).reverse).reverse = true ∧
    Riemann104.OnePassGuard.NoThreeZeros
      (1 :: (popBreakRev 1 (Control.walked c).reverse).reverse).reverse = true := by
  have hc := Control.instruction_words c
  simp only [Control.rawInstr, he, Control.returned, Bool.false_eq_true, ite_false] at hc
  cases hi : Control.instruction c with
  | halt => rw [hi, Control.toRhInstr] at hc; cases hc
  | jump n => rw [hi, Control.toRhInstr] at hc; cases hc
  | inc r' n => rw [hi, Control.toRhInstr] at hc; cases hc
  | decnz r' p z =>
    rw [hi, Control.toRhInstr] at hc
    obtain ⟨_, hp, hz⟩ := RhInstr.decnz.inj hc
    rw [hp, hz]
    exact ⟨(Schema.word_noThree p).2, (Schema.word_noThree z).2⟩

theorem callerPrefix_count_zero (d : Nat) : 1 ≤ (Schema.callerPrefix d).count 0 := by
  induction d with
  | zero => decide
  | succ d ih =>
    simp only [Schema.callerPrefix, List.count_append]
    omega

theorem outside_dec_count : ∀ (s : Fin 97) (r : Fin 5),
    Control.effect (.outside s) = .decnz r → 1 ≤ (Control.walked (.outside s)).count 0 := by
  decide +kernel

theorem dec_walk_count (c : Schema.ControlWord) (r : Fin 5)
    (he : Control.effect c = .decnz r) : 1 ≤ (Control.walked c).count 0 := by
  cases c with
  | outside s => exact outside_dec_count s r he
  | entry d =>
    have hp := callerPrefix_count_zero d
    simp only [Control.walked, List.count_append]
    omega
  | «local» d s =>
    have hp := callerPrefix_count_zero d
    simp only [Control.walked, Schema.localWalk, List.count_append]
    omega

end ConjectureMachines.Riemann95.Dispatch
