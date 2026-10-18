/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ReferenceBridge95
public import Cryptids.ReductionSupport.Riemann95.PrecreditTrace95

@[expose] public section

namespace ConjectureMachines.Riemann95.TypedPrewidth

open ConjectureMachines.Riemann120.Layer2 (RhRegCfg RhInstr)

def swapReg : Nat → Nat
  | 0 => 3
  | 3 => 0
  | r => r

def swapBank (regs : List Nat) : List Nat :=
  [regs.getD 3 0, regs.getD 1 0, regs.getD 2 0, regs.getD 0 0, regs.getD 4 0]

def swapCfg (c : RhRegCfg) : RhRegCfg := ⟨c.stack, swapBank c.regs⟩

def swapInstr : RhInstr → RhInstr
  | .halt => .halt
  | .jump n => .jump n
  | .inc r n => .inc (swapReg r) n
  | .decnz r p z => .decnz (swapReg r) p z

theorem swapBank_twice (regs : List Nat) (hlen : regs.length = 5) :
    swapBank (swapBank regs) = regs := by
  obtain ⟨a,b,c,d,e,rfl⟩ := ReferenceProgram.bank_five regs hlen
  rfl

theorem swapBank_getD (regs : List Nat) (hlen : regs.length = 5) (r : Nat) :
    (swapBank regs).getD r 0 = regs.getD (swapReg r) 0 := by
  obtain ⟨a,b,c,d,e,rfl⟩ := ReferenceProgram.bank_five regs hlen
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl

theorem swapBank_set (regs : List Nat) (hlen : regs.length = 5) (r value : Nat) :
    swapBank (regs.set (swapReg r) value) = (swapBank regs).set r value := by
  obtain ⟨a,b,c,d,e,rfl⟩ := ReferenceProgram.bank_five regs hlen
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> try rfl
  rcases r with _ | r <;> rfl

theorem apply_swapInstr (i : RhInstr) (regs : List Nat) (hlen : regs.length = 5) :
    (Control.applyInstr (swapInstr i) regs).map swapCfg =
      Control.applyInstr i (swapBank regs) := by
  cases i with
  | halt => rfl
  | jump n => rfl
  | inc r n =>
    simp only [Control.applyInstr, swapInstr, swapBank_getD _ hlen, Option.map_some, swapCfg]
    rw [swapBank_set _ hlen]
  | decnz r p z =>
    simp only [Control.applyInstr, swapInstr, swapBank_getD _ hlen]
    split <;> simp only [Option.map_some, swapCfg]
    rw [swapBank_set _ hlen]

end ConjectureMachines.Riemann95.TypedPrewidth
