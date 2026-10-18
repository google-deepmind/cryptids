/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ControllerSchema95
public import Cryptids.ReductionSupport.Riemann95.NoThree95

/-! # Control semantics and closure -/

@[expose] public section

/-! ## Instruction semantics -/

section

namespace ConjectureMachines.Riemann95.Control

open ConjectureMachines.Riemann120.Layer2
open Schema

inductive Effect where
  | halt
  | inc (r : Fin 5)
  | decnz (r : Fin 5)
  | jump (isContinue : Bool) (k : Nat)
  deriving Inhabited, DecidableEq, Repr

inductive Instr where
  | halt
  | jump (next : ControlWord)
  | inc (r : Fin 5) (next : ControlWord)
  | decnz (r : Fin 5) (positive zero : ControlWord)
  deriving Inhabited, DecidableEq, Repr

def localEffects : Array Effect := #[
  .decnz 4,
  .decnz 4,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 4,
  .decnz 4,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 2,
  .decnz 2,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 2,
  .jump true 1,
  .decnz 2]

def outsideEffects : Array Effect := #[
  .decnz 3,
  .inc 2,
  .jump true 1,
  .inc 4,
  .decnz 4,
  .inc 1,
  .jump true 1,
  .decnz 3,
  .inc 0,
  .jump true 1,
  .decnz 0,
  .decnz 1,
  .inc 4,
  .jump false 1,
  .decnz 4,
  .inc 1,
  .jump true 1,
  .inc 3,
  .jump true 1,
  .decnz 1,
  .inc 1,
  .decnz 3,
  .inc 0,
  .jump true 1,
  .decnz 4,
  .inc 3,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 0,
  .inc 3,
  .jump true 2,
  .decnz 3,
  .inc 0,
  .jump true 1,
  .decnz 4,
  .inc 3,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 0,
  .inc 3,
  .jump true 2,
  .decnz 3,
  .inc 0,
  .jump true 1,
  .decnz 4,
  .inc 3,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 0,
  .inc 3,
  .jump true 2,
  .decnz 2,
  .jump true 1,
  .decnz 4,
  .inc 2,
  .inc 1,
  .jump true 2,
  .decnz 3,
  .decnz 4,
  .inc 1,
  .jump true 1,
  .decnz 3,
  .inc 0,
  .jump true 1,
  .decnz 0,
  .decnz 1,
  .inc 4,
  .jump false 1,
  .decnz 4,
  .inc 1,
  .jump true 1,
  .inc 3,
  .jump true 1,
  .decnz 2,
  .jump false 0,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 4,
  .inc 3,
  .inc 1,
  .jump true 2,
  .decnz 1,
  .inc 4,
  .jump true 1,
  .decnz 2,
  .halt]

def outsideInstrs : Array Instr := #[
  .decnz 3 (.outside 1) (.outside 3),
  .inc 2 (.outside 2),
  .jump (.outside 0),
  .inc 4 (.outside 4),
  .decnz 4 (.outside 5) (.outside 7),
  .inc 1 (.outside 6),
  .jump (.outside 4),
  .decnz 3 (.outside 8) (.outside 10),
  .inc 0 (.outside 9),
  .jump (.outside 7),
  .decnz 0 (.outside 11) (.outside 19),
  .decnz 1 (.outside 12) (.outside 14),
  .inc 4 (.outside 13),
  .jump (.outside 18),
  .decnz 4 (.outside 15) (.outside 17),
  .inc 1 (.outside 16),
  .jump (.outside 14),
  .inc 3 (.outside 18),
  .jump (.outside 10),
  .decnz 1 (.outside 20) (.outside 34),
  .inc 1 (.outside 21),
  .decnz 3 (.outside 22) (.outside 24),
  .inc 0 (.outside 23),
  .jump (.outside 21),
  .decnz 4 (.outside 25) (.outside 28),
  .inc 3 (.outside 26),
  .inc 1 (.outside 27),
  .jump (.outside 24),
  .decnz 1 (.outside 29) (.outside 31),
  .inc 4 (.outside 30),
  .jump (.outside 28),
  .decnz 0 (.outside 32) (.outside 34),
  .inc 3 (.outside 33),
  .jump (.outside 24),
  .decnz 3 (.outside 35) (.outside 37),
  .inc 0 (.outside 36),
  .jump (.outside 34),
  .decnz 4 (.outside 38) (.outside 41),
  .inc 3 (.outside 39),
  .inc 1 (.outside 40),
  .jump (.outside 37),
  .decnz 1 (.outside 42) (.outside 44),
  .inc 4 (.outside 43),
  .jump (.outside 41),
  .decnz 0 (.outside 45) (.outside 47),
  .inc 3 (.outside 46),
  .jump (.outside 37),
  .decnz 3 (.outside 48) (.outside 50),
  .inc 0 (.outside 49),
  .jump (.outside 47),
  .decnz 4 (.outside 51) (.outside 54),
  .inc 3 (.outside 52),
  .inc 1 (.outside 53),
  .jump (.outside 50),
  .decnz 1 (.outside 55) (.outside 57),
  .inc 4 (.outside 56),
  .jump (.outside 54),
  .decnz 0 (.outside 58) (.outside 60),
  .inc 3 (.outside 59),
  .jump (.outside 50),
  .decnz 2 (.outside 61) (.outside 62),
  .jump (.outside 3),
  .decnz 4 (.outside 63) (.outside 66),
  .inc 2 (.outside 64),
  .inc 1 (.outside 65),
  .jump (.outside 62),
  .decnz 3 (.outside 67) (.outside 85),
  .decnz 4 (.outside 68) (.outside 70),
  .inc 1 (.outside 69),
  .jump (.outside 67),
  .decnz 3 (.outside 71) (.outside 73),
  .inc 0 (.outside 72),
  .jump (.outside 70),
  .decnz 0 (.outside 74) (.outside 82),
  .decnz 1 (.outside 75) (.outside 77),
  .inc 4 (.outside 76),
  .jump (.outside 81),
  .decnz 4 (.outside 78) (.outside 80),
  .inc 1 (.outside 79),
  .jump (.outside 77),
  .inc 3 (.outside 81),
  .jump (.outside 73),
  .decnz 2 (.outside 83) (.outside 84),
  .jump (.outside 84),
  .jump (.outside 66),
  .decnz 1 (.outside 86) (.outside 88),
  .inc 4 (.outside 87),
  .jump (.outside 85),
  .decnz 4 (.outside 89) (.outside 92),
  .inc 3 (.outside 90),
  .inc 1 (.outside 91),
  .jump (.outside 88),
  .decnz 1 (.outside 93) (.entry 0),
  .inc 4 (.outside 94),
  .jump (.outside 92),
  .decnz 2 (.outside 96) (.outside 0),
  .halt]

def localInstr (d : Nat) (s : Fin 22) : Instr :=
  match s.val with
  | 0 => .decnz 4 (.local d 1) (.local d 4)
  | 1 => .decnz 4 (.local d 2) (.local d 4)
  | 2 => .inc 1 (.local d 3)
  | 3 => .jump (.local d 0)
  | 4 => .decnz 1 (.local d 5) (.local d 7)
  | 5 => .inc 4 (.local d 6)
  | 6 => .jump (.local d 4)
  | 7 => .decnz 4 (.local d 8) (.local d 11)
  | 8 => .decnz 4 (.local d 9) (.local d 11)
  | 9 => .inc 1 (.local d 10)
  | 10 => .jump (.local d 7)
  | 11 => .decnz 1 (.local d 12) (.local d 14)
  | 12 => .inc 4 (.local d 13)
  | 13 => .jump (.local d 11)
  | 14 => .decnz 2 (.local d 15) (.local d 18)
  | 15 => .decnz 2 (.local d 16) (.local d 18)
  | 16 => .inc 1 (.local d 17)
  | 17 => .jump (.local d 14)
  | 18 => .decnz 1 (.local d 19) (.entry (d+1))
  | 19 => .inc 2 (.local d 20)
  | 20 => .jump (.local d 18)
  | 21 =>
    match d with
    | 0 => .decnz 2 (.outside 95) (.outside 0)
    | 1 => .decnz 2 (.local 0 21) (.outside 95)
    | d+2 => .decnz 2 (.local (d+1) 21) (.local d 21)
  | _ => .halt

def instruction : ControlWord → Instr
  | .outside s => outsideInstrs.getD s.val .halt
  | .entry 0 => .decnz 4 (.local 0 0) (.outside 95)
  | .entry (d+1) => .decnz 4 (.local (d+1) 0) (.local d 21)
  | .local d s => localInstr d s

def effect : ControlWord → Effect
  | .outside s => outsideEffects.getD s.val .halt
  | .entry _ => .decnz 4
  | .local _ s => localEffects.getD s.val .halt

def walked : ControlWord → Word
  | .outside s => outsideWalk s
  | .entry d => callerPrefix d ++ [0]
  | .local d s => localWalk d s

def returned (isContinue : Bool) (k : Nat) (w : Word) : Word :=
  if isContinue then (popContinueRev k w.reverse).reverse
  else (popBreakRev k w.reverse).reverse

def rawInstr (c : ControlWord) : RhInstr :=
  let w := walked c
  match effect c with
  | .halt => .halt
  | .inc r => .inc r.val (returned false 0 w)
  | .decnz r => .decnz r.val (returned false 0 w) (returned false 1 w)
  | .jump cont k => .jump (returned cont k w)

def toRhInstr : Instr → RhInstr
  | .halt => .halt
  | .jump n => .jump (word n)
  | .inc r n => .inc r.val (word n)
  | .decnz r p z => .decnz r.val (word p) (word z)

end ConjectureMachines.Riemann95.Control

namespace ConjectureMachines.Riemann95.Control

open ConjectureMachines.Riemann120.Layer2
open Schema

theorem outside_instruction_words : ∀ s : Fin 97,
    rawInstr (.outside s) = toRhInstr (instruction (.outside s)) := by decide +kernel

theorem entry_instruction_words (d : Nat) :
    rawInstr (.entry d) = toRhInstr (instruction (.entry d)) := by
  cases d with
  | zero => rfl
  | succ d =>
    simp [rawInstr,effect,walked,instruction,toRhInstr,returned,
      word,suffix,suffixes,callerPrefix,popBreakRev,
      List.reverse_append,List.reverse_cons,List.append_assoc]

theorem local_instruction_words (d : Nat) (s : Fin 22) :
    rawInstr (.local d s) = toRhInstr (instruction (.local d s)) := by
  cases d with
  | zero => fin_cases s <;> rfl
  | succ d =>
    cases d with
    | zero => fin_cases s <;> rfl
    | succ d =>
      fin_cases s <;>
        simp [rawInstr,effect,walked,instruction,localInstr,toRhInstr,returned,
          word,localWalk,localWalkSuffix,localWalkSuffixes,suffix,suffixes,localEffects,
          callerPrefix,popBreakRev,popContinueRev,
          List.reverse_append,List.reverse_cons,List.append_assoc]
      all_goals simp [entry,callerPrefix,List.append_assoc]

theorem instruction_words (c : ControlWord) :
    rawInstr c = toRhInstr (instruction c) := by
  cases c with
  | outside s => exact outside_instruction_words s
  | entry d => exact entry_instruction_words d
  | «local» d s => exact local_instruction_words d s

end ConjectureMachines.Riemann95.Control

end

/-! ## Control flow labels -/

section

namespace ConjectureMachines.Riemann95.Control

open Schema

def unwindId : Fin 22 := 21
def finalTestId : Fin 97 := 95
def finalHaltId : Fin 97 := 96
def enterBodyId : Fin 22 := 0

def unwind (d : Nat) : ControlWord := .local d unwindId

theorem entry_zero : instruction (.entry 0) =
    .decnz 4 (.local 0 enterBodyId) (.outside finalTestId) := rfl

theorem entry_succ (d : Nat) : instruction (.entry (d+1)) =
    .decnz 4 (.local (d+1) enterBodyId) (unwind d) := rfl

theorem unwind_zero : instruction (unwind 0) =
    .decnz 2 (.outside finalTestId) (.outside 0) := rfl

theorem unwind_one : instruction (unwind 1) =
    .decnz 2 (unwind 0) (.outside finalTestId) := rfl

theorem unwind_succ_succ (d : Nat) : instruction (unwind (d+2)) =
    .decnz 2 (unwind (d+1)) (unwind d) := rfl

theorem final_test : instruction (.outside finalTestId) =
    .decnz 2 (.outside finalHaltId) (.outside 0) := rfl

end ConjectureMachines.Riemann95.Control

end

/-! ## Configuration closure -/

section

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

end
