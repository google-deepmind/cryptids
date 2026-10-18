/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ReferenceLogical95

@[expose] public section

namespace ConjectureMachines.Riemann95.ReferenceProgram

open Turing StateTransition ConjectureMachines.Riemann120
open ConjectureMachines.Riemann120.Layer2

abbrev Word := ReferenceLogical.Word
abbrev ControlInstr := ReferenceLogical.ControlInstr
def perm : Nat → Nat
  | 0 => 3
  | 1 => 4
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | n + 5 => n + 5

def mapControl : ControlInstr → ControlInstr
  | .halt => .halt
  | .jump n => .jump n
  | .inc r n => .inc (perm r) n
  | .decnz r p z => .decnz (perm r) p z

def mapInstr : RhInstr → RhInstr
  | .halt => .halt
  | .jump n => .jump n
  | .inc r n => .inc (perm r) n
  | .decnz r p z => .decnz (perm r) p z

def word (s : Fin 121) : Word := ReferenceLogical.word s
def oldWord (s : Fin 121) : Word := ReferenceLogical.oldWord s
def rowInstr (s : Fin 121) : ControlInstr := mapControl (ReferenceLogical.rowInstr s)
abbrev toInstr := ReferenceLogical.toInstr

def decoded (s : Fin 121) : RhInstr := toInstr word (rowInstr s)
def instruction (bits : Word) : RhInstr := mapInstr (ReferenceLogical.instruction bits)

def step (c : RhRegCfg) : Option RhRegCfg :=
  match instruction c.stack with
  | .halt => none
  | .jump target => some ⟨target,c.regs⟩
  | .inc r target => some ⟨target,c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r positive zero =>
    if c.regs.getD r 0 == 0 then some ⟨zero,c.regs⟩
    else some ⟨positive,c.regs.set r (c.regs.getD r 0 - 1)⟩

theorem map_toInstr (target : Fin 121 → Word) (i : ControlInstr) :
    mapInstr (toInstr target i) = toInstr target (mapControl i) := by
  cases i <;> rfl

theorem instruction_word (s : Fin 121) : instruction (word s) = decoded s := by
  change mapInstr (ReferenceLogical.instruction (ReferenceLogical.word s)) = _
  rw [ReferenceLogical.instruction_word]
  exact map_toInstr _ _

def stageCfg (M : Nat) : RhRegCfg := ⟨[],[0,0,0,M,0]⟩

end ConjectureMachines.Riemann95.ReferenceProgram
