/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104

@[expose] public section

namespace ConjectureMachines.Riemann95.ReferenceLogical

open Turing StateTransition ConjectureMachines.Riemann120
open ConjectureMachines.Riemann120.Layer2

abbrev Word := List (Fin 2)

inductive ControlInstr where
  | halt
  | jump (next : Fin 121)
  | inc (reg : Nat) (next : Fin 121)
  | decnz (reg : Nat) (positive zero : Fin 121)
  deriving Inhabited, DecidableEq, Repr

inductive Role where
  | plain
  | firstSwap (reg : Nat)
  | secondSwap (reg : Nat)
  | halfDec
  deriving Inhabited, DecidableEq, Repr

structure Row where
  word : Word
  oldWord : Word
  instr : ControlInstr
  role : Role
  deriving Inhabited, DecidableEq, Repr

def rows : Array Row := #[
  ⟨[], [], .decnz 0 1 3, .plain⟩,
  ⟨[0,1], [0,1], .inc 3 2, .plain⟩,
  ⟨[0,1,1], [0,1,1], .jump 0, .plain⟩,
  ⟨[1], [1], .inc 1 4, .plain⟩,
  ⟨[1,0,0,1], [1,0,0,1], .decnz 1 5 7, .plain⟩,
  ⟨[1,0,0,1,0,0,1], [1,0,0,1,0,0,1], .inc 4 6, .plain⟩,
  ⟨[1,0,0,1,0,0,1,1], [1,0,0,1,0,0,1,1], .jump 4, .plain⟩,
  ⟨[1,0,0,1,0,1], [1,0,0,1,0,1], .decnz 2 8 10, .plain⟩,
  ⟨[1,0,0,1,0,1,0,1], [1,0,0,1,0,1,0,1], .inc 0 9, .plain⟩,
  ⟨[1,0,0,1,0,1,0,1,1], [1,0,0,1,0,1,0,1,1], .jump 7, .plain⟩,
  ⟨[1,0,0,1,0,1,1], [1,0,0,1,0,1,1], .decnz 0 11 19, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1], [1,0,0,1,0,1,1,1], .decnz 4 12 14, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,0,0,1], [1,0,0,1,0,1,1,1,0,0,1], .inc 1 13, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,0,0,1,1], [1,0,0,1,0,1,1,1,0,0,1,1], .jump 18, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,0,1], [1,0,0,1,0,1,1,1,0,1], .decnz 1 15 17, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,0,1,0,1], [1,0,0,1,0,1,1,1,0,1,0,1], .inc 4 16, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,0,1,0,1,1], [1,0,0,1,0,1,1,1,0,1,0,1,1], .jump 14, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,0,1,1], [1,0,0,1,0,1,1,1,0,1,1], .inc 2 18, .plain⟩,
  ⟨[1,0,0,1,0,1,1,1,1], [1,0,0,1,0,1,1,1,1], .jump 10, .plain⟩,
  ⟨[1,0,0,1,1], [1,0,0,1,1], .decnz 4 20 34, .plain⟩,
  ⟨[1,0,0,1,1,0,1], [1,0,0,1,1,0,1], .inc 4 21, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1], [1,0,0,1,1,0,1,1], .decnz 2 22 24, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,0,1], [1,0,0,1,1,0,1,1,0,1], .inc 0 23, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,0,1,1], [1,0,0,1,1,0,1,1,0,1,1], .jump 21, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1], [1,0,0,1,1,0,1,1,1], .decnz 1 25 28, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,0,0,1], [1,0,0,1,1,0,1,1,1,0,0,1], .inc 2 26, .firstSwap 2⟩,
  ⟨[1,0,0,1,1,0,1,1,1,0,0,1,1], [1,0,0,1,1,0,1,1,1,0,0,1,1], .inc 4 27, .secondSwap 2⟩,
  ⟨[1,0,0,1,1,0,1,1,1,0,0,1,1,1], [1,0,0,1,1,0,1,1,1,0,0,1,1,1], .jump 24, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,0,1], [1,0,0,1,1,0,1,1,1,0,1], .decnz 4 29 31, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,0,1,1], [1,0,0,1,1,0,1,1,1,0,1,1], .inc 1 30, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,0,1,1,1], [1,0,0,1,1,0,1,1,1,0,1,1,1], .jump 28, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,1], [1,0,0,1,1,0,1,1,1,1], .decnz 0 32 34, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,1,1], [1,0,0,1,1,0,1,1,1,1,1], .inc 2 33, .plain⟩,
  ⟨[1,0,0,1,1,0,1,1,1,1,1,1], [1,0,0,1,1,0,1,1,1,1,1,1], .jump 24, .plain⟩,
  ⟨[1,0,0,1,1,1], [1,0,0,1,1,1], .decnz 2 35 37, .plain⟩,
  ⟨[1,0,0,1,1,1,0,0,1], [1,0,0,1,1,1,0,0,1], .inc 0 36, .plain⟩,
  ⟨[1,0,0,1,1,1,0,0,1,1], [1,0,0,1,1,1,0,0,1,1], .jump 34, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1], [1,0,0,1,1,1,0,1], .decnz 1 38 41, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,0,0,1], [1,0,0,1,1,1,0,1,0,0,1], .inc 2 39, .firstSwap 2⟩,
  ⟨[1,0,0,1,1,1,0,1,0,0,1,1], [1,0,0,1,1,1,0,1,0,0,1,1], .inc 4 40, .secondSwap 2⟩,
  ⟨[1,0,0,1,1,1,0,1,0,0,1,1,1], [1,0,0,1,1,1,0,1,0,0,1,1,1], .jump 37, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,0,1], [1,0,0,1,1,1,0,1,0,1], .decnz 4 42 44, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,0,1,1], [1,0,0,1,1,1,0,1,0,1,1], .inc 1 43, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,0,1,1,1], [1,0,0,1,1,1,0,1,0,1,1,1], .jump 41, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,1], [1,0,0,1,1,1,0,1,1], .decnz 0 45 47, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,1,1], [1,0,0,1,1,1,0,1,1,1], .inc 2 46, .plain⟩,
  ⟨[1,0,0,1,1,1,0,1,1,1,1], [1,0,0,1,1,1,0,1,1,1,1], .jump 37, .plain⟩,
  ⟨[1,0,0,1,1,1,1], [1,0,0,1,1,1,1], .decnz 2 48 50, .plain⟩,
  ⟨[1,0,0,1,1,1,1,0,1], [1,0,0,1,1,1,1,0,1], .inc 0 49, .plain⟩,
  ⟨[1,0,0,1,1,1,1,0,1,1], [1,0,0,1,1,1,1,0,1,1], .jump 47, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1], [1,0,0,1,1,1,1,1], .decnz 1 51 54, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,0,0,1], [1,0,0,1,1,1,1,1,0,0,1], .inc 2 52, .firstSwap 2⟩,
  ⟨[1,0,0,1,1,1,1,1,0,0,1,1], [1,0,0,1,1,1,1,1,0,0,1,1], .inc 4 53, .secondSwap 2⟩,
  ⟨[1,0,0,1,1,1,1,1,0,0,1,1,1], [1,0,0,1,1,1,1,1,0,0,1,1,1], .jump 50, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,0,1], [1,0,0,1,1,1,1,1,0,1], .decnz 4 55 57, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,0,1,1], [1,0,0,1,1,1,1,1,0,1,1], .inc 1 56, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,0,1,1,1], [1,0,0,1,1,1,1,1,0,1,1,1], .jump 54, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,1], [1,0,0,1,1,1,1,1,1], .decnz 0 58 60, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,1,1], [1,0,0,1,1,1,1,1,1,1], .inc 2 59, .plain⟩,
  ⟨[1,0,0,1,1,1,1,1,1,1,1], [1,0,0,1,1,1,1,1,1,1,1], .jump 50, .plain⟩,
  ⟨[1,0,1], [1,0,1], .decnz 3 61 62, .plain⟩,
  ⟨[1,0,1,1], [1,0,1,1], .jump 3, .plain⟩,
  ⟨[1,1], [1,1], .decnz 1 63 66, .plain⟩,
  ⟨[1,1,0,1], [1,1,0,1], .inc 3 64, .firstSwap 3⟩,
  ⟨[1,1,0,1,1], [1,1,0,1,0,1], .inc 4 65, .secondSwap 3⟩,
  ⟨[1,1,0,1,1,1], [1,1,0,1,1], .jump 62, .plain⟩,
  ⟨[1,1,1], [1,1,1], .decnz 2 67 85, .plain⟩,
  ⟨[1,1,1,0,0,1], [1,1,1,0,0,1], .decnz 1 68 70, .plain⟩,
  ⟨[1,1,1,0,0,1,0,0,1], [1,1,1,0,0,1,0,0,1], .inc 4 69, .plain⟩,
  ⟨[1,1,1,0,0,1,0,0,1,1], [1,1,1,0,0,1,0,0,1,1], .jump 67, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1], [1,1,1,0,0,1,0,1], .decnz 2 71 73, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,0,1], [1,1,1,0,0,1,0,1,0,1], .inc 0 72, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,0,1,1], [1,1,1,0,0,1,0,1,0,1,1], .jump 70, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1], [1,1,1,0,0,1,0,1,1], .decnz 0 74 82, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1], [1,1,1,0,0,1,0,1,1,1], .decnz 4 75 77, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,0,0,1], [1,1,1,0,0,1,0,1,1,1,0,0,1], .inc 1 76, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,0,0,1,1], [1,1,1,0,0,1,0,1,1,1,0,0,1,1], .jump 81, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,0,1], [1,1,1,0,0,1,0,1,1,1,0,1], .decnz 1 78 80, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,0,1,0,1], [1,1,1,0,0,1,0,1,1,1,0,1,0,1], .inc 4 79, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,0,1,0,1,1], [1,1,1,0,0,1,0,1,1,1,0,1,0,1,1], .jump 77, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,0,1,1], [1,1,1,0,0,1,0,1,1,1,0,1,1], .inc 2 81, .plain⟩,
  ⟨[1,1,1,0,0,1,0,1,1,1,1], [1,1,1,0,0,1,0,1,1,1,1], .jump 73, .plain⟩,
  ⟨[1,1,1,0,0,1,1], [1,1,1,0,0,1,1], .decnz 3 83 84, .plain⟩,
  ⟨[1,1,1,0,0,1,1,0,1], [1,1,1,0,0,1,1,0,1], .jump 84, .plain⟩,
  ⟨[1,1,1,0,0,1,1,1], [1,1,1,0,0,1,1,1], .jump 66, .plain⟩,
  ⟨[1,1,1,0,1], [1,1,1,0,1], .decnz 4 86 88, .plain⟩,
  ⟨[1,1,1,0,1,1], [1,1,1,0,1,1], .inc 1 87, .plain⟩,
  ⟨[1,1,1,0,1,1,1], [1,1,1,0,1,1,1], .jump 85, .plain⟩,
  ⟨[1,1,1,1], [1,1,1,1], .decnz 1 89 115, .plain⟩,
  ⟨[1,1,1,1,0,0,1], [1,1,1,1,0,1], .inc 0 90, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1], [1,1,1,1,0,1,0,1], .decnz 1 91 95, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,0,1], [1,1,1,1,0,1,0,1,0,0,1], .inc 0 92, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,0,1,0,1], [1,1,1,1,0,1,0,1,0,0,1,0,1], .decnz 1 93 94, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,0,1,0,1,1], [1,1,1,1,0,1,0,1,0,0,1,0,1,1], .inc 4 94, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,0,1,1], [1,1,1,1,0,1,0,1,0,0,1,1], .jump 90, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,1], [1,1,1,1,0,1,0,1,0,1], .decnz 4 96 98, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,1,1], [1,1,1,1,0,1,0,1,0,1,1], .inc 1 97, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,0,1,1,1], [1,1,1,1,0,1,0,1,0,1,1,1], .jump 95, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1], [1,1,1,1,0,1,0,1,1], .decnz 1 99 103, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,0,1], [1,1,1,1,0,1,0,1,1,0,0,1], .inc 0 100, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,0,1,0,1], [1,1,1,1,0,1,0,1,1,0,0,1,0,1], .decnz 1 101 102, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,0,1,0,1,1], [1,1,1,1,0,1,0,1,1,0,0,1,0,1,1], .inc 4 102, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,0,1,1], [1,1,1,1,0,1,0,1,1,0,0,1,1], .jump 98, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,1], [1,1,1,1,0,1,0,1,1,0,1], .decnz 4 104 106, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,1,1], [1,1,1,1,0,1,0,1,1,0,1,1], .inc 1 105, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,0,1,1,1], [1,1,1,1,0,1,0,1,1,0,1,1,1], .jump 103, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1], [1,1,1,1,0,1,0,1,1,1], .decnz 3 107 110, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1,0,1], [1,1,1,1,0,1,0,1,1,1,0,1], .decnz 3 108 110, .halfDec⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1,0,1,1], [1,1,1,1,0,1,0,1,1,1,0,1,0,1], .inc 4 109, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1,0,1,1,1], [1,1,1,1,0,1,0,1,1,1,0,1,1], .jump 106, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1,1], [1,1,1,1,0,1,0,1,1,1,1], .decnz 4 111 113, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1,1,1], [1,1,1,1,0,1,0,1,1,1,1,1], .inc 3 112, .plain⟩,
  ⟨[1,1,1,1,0,0,1,0,1,1,1,1,1,1], [1,1,1,1,0,1,0,1,1,1,1,1,1], .jump 110, .plain⟩,
  ⟨[1,1,1,1,0,0,1,1], [1,1,1,1,0,1,1], .inc 2 114, .plain⟩,
  ⟨[1,1,1,1,0,0,1,1,1], [1,1,1,1,0,1,1,1], .jump 88, .plain⟩,
  ⟨[1,1,1,1,0,1], [1,1,1,1,1], .decnz 2 116 119, .plain⟩,
  ⟨[1,1,1,1,0,1,1], [1,1,1,1,1,0,1], .decnz 3 117 118, .plain⟩,
  ⟨[1,1,1,1,0,1,1,0,1], [1,1,1,1,1,0,1,0,1], .jump 118, .plain⟩,
  ⟨[1,1,1,1,0,1,1,1], [1,1,1,1,1,0,1,1], .jump 88, .plain⟩,
  ⟨[1,1,1,1,1], [1,1,1,1,1,1], .decnz 3 120 0, .plain⟩,
  ⟨[1,1,1,1,1,1], [1,1,1,1,1,1,1], .halt, .plain⟩
]

def row (s : Fin 121) : Row := rows.getD s.val default
def word (s : Fin 121) : Word := (row s).word
def oldWord (s : Fin 121) : Word := (row s).oldWord
def rowInstr (s : Fin 121) : ControlInstr := (row s).instr
def role (s : Fin 121) : Role := (row s).role

def toInstr (target : Fin 121 → Word) : ControlInstr → RhInstr
  | .halt => .halt
  | .jump n => .jump (target n)
  | .inc r n => .inc r (target n)
  | .decnz r p z => .decnz r (target p) (target z)

def decoded (s : Fin 121) : RhInstr := toInstr word (rowInstr s)

def instruction (bits : Word) : RhInstr :=
  match (List.finRange 121).find? (fun s => word s == bits) with
  | some s => decoded s
  | none => .halt

def step (c : RhRegCfg) : Option RhRegCfg :=
  match instruction c.stack with
  | .halt => none
  | .jump target => some ⟨target,c.regs⟩
  | .inc r target => some ⟨target,c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r positive zero =>
    if c.regs.getD r 0 == 0 then some ⟨zero,c.regs⟩
    else some ⟨positive,c.regs.set r (c.regs.getD r 0 - 1)⟩

def ordinary (s : Fin 121) : Prop :=
  match role s with
  | .secondSwap _ => False
  | _ => True

instance (s : Fin 121) : Decidable (ordinary s) := by
  unfold ordinary
  split <;> infer_instance

def ordinaryTargets : ControlInstr → Prop
  | .halt => True
  | .jump n | .inc _ n => ordinary n
  | .decnz _ p z => ordinary p ∧ ordinary z

instance (i : ControlInstr) : Decidable (ordinaryTargets i) := by
  cases i <;> dsimp [ordinaryTargets] <;> infer_instance

def halfJump : Word := [1,1,1,1,0,1,0,1,1,1,0,1,1]
def halfLoop : Word := [1,1,1,1,0,1,0,1,1,1]

def Spec (s : Fin 121) : Prop :=
  match role s with
  | .plain =>
    evalStackOf true (oldWord s) = toInstr oldWord (rowInstr s) ∧
      ordinaryTargets (rowInstr s)
  | .firstSwap r =>
    match rowInstr s with
    | .inc r' n => r' = r ∧ role n = .secondSwap r ∧
        evalStackOf true (oldWord s) = .inc 4 (oldWord n) ∧ (r = 2 ∨ r = 3)
    | _ => False
  | .secondSwap r =>
    match rowInstr s with
    | .inc r' n => r' = 4 ∧ ordinary n ∧
        evalStackOf true (oldWord s) = .inc r (oldWord n) ∧ (r = 2 ∨ r = 3)
    | _ => False
  | .halfDec =>
    match rowInstr s with
    | .decnz r p z => r = 3 ∧ ordinary p ∧ ordinary z ∧
        evalStackOf true (oldWord s) = .decnz 3 (oldWord p) halfJump ∧
        evalStackOf true halfJump = .jump halfLoop ∧
        evalStackOf true halfLoop = .decnz 3 (oldWord s) (oldWord z)
    | _ => False

instance (s : Fin 121) : Decidable (Spec s) := by
  unfold Spec
  split
  · infer_instance
  · split <;> infer_instance
  · split <;> infer_instance
  · split <;> infer_instance

theorem instruction_word : ∀ s : Fin 121, instruction (word s) = decoded s := by decide +kernel

theorem specs : ∀ s : Fin 121, Spec s := by decide +kernel

end ConjectureMachines.Riemann95.ReferenceLogical
