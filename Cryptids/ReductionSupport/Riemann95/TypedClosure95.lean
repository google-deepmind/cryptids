/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ControlStep95

@[expose] public section

namespace ConjectureMachines.Riemann95.Control

open Turing StateTransition
open ConjectureMachines.Riemann120.Layer2
open Schema

attribute [local irreducible] localEffects outsideEffects outsideInstrs localInstr
  instruction effect walked rawInstr

structure Cfg where
  control : ControlWord
  regs : List Nat
  deriving DecidableEq, Repr

def encodeCfg (c : Cfg) : RhRegCfg := ⟨word c.control,c.regs⟩

def applyInstr (i : RhInstr) (regs : List Nat) : Option RhRegCfg :=
  match i with
  | .halt => none
  | .jump n => some ⟨n,regs⟩
  | .inc r n => some ⟨n,regs.set r (regs.getD r 0 + 1)⟩
  | .decnz r p z =>
    if regs.getD r 0 == 0 then some ⟨z,regs⟩
    else some ⟨p,regs.set r (regs.getD r 0 - 1)⟩

def step (c : Cfg) : Option Cfg :=
  match instruction c.control with
  | .halt => none
  | .jump n => some ⟨n,c.regs⟩
  | .inc r n => some ⟨n,c.regs.set r.val (c.regs.getD r.val 0 + 1)⟩
  | .decnz r p z =>
    if c.regs.getD r.val 0 == 0 then some ⟨z,c.regs⟩
    else some ⟨p,c.regs.set r.val (c.regs.getD r.val 0 - 1)⟩

theorem step_encode (c : Cfg) :
    (step c).map encodeCfg = applyInstr (rawInstr c.control) c.regs := by
  rw [instruction_words]
  unfold step
  cases instruction c.control with
  | halt => rfl
  | jump n => rfl
  | inc r n => rfl
  | decnz r p z =>
    simp only [toRhInstr,applyInstr]
    split <;> rfl

theorem decoded_next_word_schema (c : ControlWord) (regs : List Nat) (next : RhRegCfg)
    (hs : applyInstr (rawInstr c) regs = some next) :
    ∃ nextControl : ControlWord, word nextControl = next.stack := by
  have hm : (step ⟨c,regs⟩).map encodeCfg = some next := (step_encode _).trans hs
  cases ht : step ⟨c,regs⟩ with
  | none => simp only [ht,Option.map_none] at hm; contradiction
  | some nc =>
    simp only [ht,Option.map_some,Option.some.injEq] at hm
    exact ⟨nc.control,congrArg RhRegCfg.stack hm⟩

theorem decoded_next_noThree (c : ControlWord) (regs : List Nat) (next : RhRegCfg)
    (hs : applyInstr (rawInstr c) regs = some next) :
    ConjectureMachines.Riemann104.OnePassGuard.NoThreeZeros (1 :: next.stack) = true ∧
    ConjectureMachines.Riemann104.OnePassGuard.NoThreeZeros (1 :: next.stack).reverse = true := by
  obtain ⟨nc,hc⟩ := decoded_next_word_schema c regs next hs
  rw [←hc]
  exact word_noThree nc

theorem step_regs_length (c next : Cfg) (hs : step c = some next) :
    next.regs.length = c.regs.length := by
  unfold step at hs
  cases hi : instruction c.control with
  | halt => simp only [hi] at hs; contradiction
  | jump n => simp only [hi,Option.some.injEq] at hs; subst next; rfl
  | inc r n => simp only [hi,Option.some.injEq] at hs; subst next; simp
  | decnz r p z =>
    simp only [hi] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst next <;> simp

theorem initial_word : word (.outside 0) = [] := by decide +kernel

end ConjectureMachines.Riemann95.Control
