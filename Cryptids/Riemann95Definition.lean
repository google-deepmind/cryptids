/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104

/-! Literal95-state table and initial-root geometry. No halting equivalence is asserted. -/

@[expose] public section

namespace ConjectureMachines.Riemann95

open Turing ConjectureMachines

def rows : List (List (Option (Fin 2 × Dir × Fin 95))) := [
  [some (1, .left, 48), some (0, .right, 49)],
  [some (1, .right, 1), some (0, .right, 4)],
  [some (0, .left, 11), some (0, .left, 2)],
  [some (0, .right, 4), some (1, .right, 3)],
  [some (0, .right, 36), some (1, .right, 4)],
  [some (0, .left, 7), some (1, .left, 5)],
  [some (0, .left, 8), some (0, .right, 36)],
  [some (0, .left, 10), some (1, .left, 5)],
  [some (0, .left, 9), some (1, .left, 8)],
  [some (1, .left, 11), some (1, .left, 8)],
  [some (0, .right, 12), some (1, .left, 5)],
  [some (1, .left, 5), some (0, .left, 11)],
  [some (0, .right, 12), some (1, .right, 15)],
  [some (0, .left, 14), some (0, .right, 13)],
  [some (1, .left, 5), some (0, .left, 5)],
  [some (0, .right, 16), some (1, .right, 17)],
  [some (0, .right, 31), some (1, .right, 19)],
  [some (0, .right, 20), some (1, .right, 21)],
  [some (1, .right, 18), some (0, .right, 28)],
  [some (0, .right, 77), some (0, .left, 14)],
  [some (0, .right, 24), some (1, .right, 25)],
  [some (0, .right, 26), some (1, .right, 27)],
  [some (0, .right, 28), some (1, .right, 22)],
  [some (1, .right, 23), some (0, .right, 37)],
  [some (0, .right, 55), some (1, .right, 30)],
  [some (0, .right, 56), some (0, .left, 14)],
  [some (0, .right, 58), some (1, .right, 33)],
  [some (0, .right, 34), some (1, .right, 35)],
  [some (0, .right, 0), some (1, .right, 28)],
  [some (1, .right, 29), some (0, .right, 3)],
  [some (0, .right, 39), some (1, .right, 40)],
  [some (1, .right, 31), some (0, .right, 54)],
  [some (1, .right, 32), some (0, .right, 22)],
  [some (0, .right, 77), some (1, .right, 43)],
  [some (0, .right, 44), some (1, .right, 45)],
  [some (0, .right, 80), some (1, .right, 90)],
  [some (1, .right, 6), some (1, .right, 36)],
  [some (0, .right, 38), some (1, .right, 37)],
  [some (0, .right, 3), some (1, .right, 38)],
  [some (0, .right, 50), some (1, .right, 51)],
  [some (0, .right, 52), some (1, .right, 53)],
  [some (0, .right, 54), some (1, .right, 80)],
  [some (0, .right, 22), some (1, .right, 42)],
  [some (0, .right, 29), some (0, .left, 19)],
  [some (0, .right, 31), some (1, .right, 57)],
  [some (0, .right, 32), some (1, .right, 59)],
  [some (0, .right, 58), some (1, .right, 60)],
  [some (0, .right, 46), some (1, .right, 56)],
  [some (0, .left, 62), some (1, .left, 48)],
  [some (0, .left, 0), some (1, .right, 63)],
  [some (0, .right, 58), some (1, .right, 64)],
  [some (0, .right, 65), some (1, .right, 66)],
  [some (0, .right, 32), some (1, .right, 67)],
  [some (0, .right, 68), some (1, .right, 68)],
  [some (0, .right, 42), some (1, .right, 54)],
  [some (1, .right, 55), some (0, .right, 70)],
  [some (1, .right, 56), some (0, .right, 42)],
  [some (0, .right, 39), some (1, .right, 69)],
  [some (1, .right, 58), some (0, .right, 41)],
  [some (0, .right, 55), some (0, .left, 70)],
  [some (0, .right, 82), some (1, .right, 76)],
  [some (0, .right, 56), none],
  [some (1, .left, 2), some (1, .left, 48)],
  [some (0, .right, 72), some (1, .right, 63)],
  [some (0, .right, 29), some (0, .left, 14)],
  [some (0, .right, 31), some (1, .right, 73)],
  [some (0, .right, 18), some (1, .right, 74)],
  [some (0, .right, 29), some (1, .right, 68)],
  [some (0, .right, 65), some (1, .right, 75)],
  [some (0, .right, 25), some (0, .left, 19)],
  [some (0, .right, 37), some (0, .left, 13)],
  [some (0, .right, 23), some (0, .left, 19)],
  [some (0, .left, 78), some (1, .right, 63)],
  [some (0, .right, 1), some (0, .left, 14)],
  [some (0, .right, 79), some (0, .left, 14)],
  [some (0, .right, 80), some (1, .right, 81)],
  [some (0, .right, 82), some (1, .right, 83)],
  [some (1, .right, 77), some (0, .right, 38)],
  [some (1, .left, 84), some (1, .left, 78)],
  [some (0, .right, 45), some (1, .right, 85)],
  [some (0, .right, 86), some (1, .right, 45)],
  [some (0, .right, 18), some (1, .right, 71)],
  [some (0, .right, 87), some (1, .right, 45)],
  [some (0, .right, 88), some (1, .right, 47)],
  [some (0, .left, 9), some (0, .left, 78)],
  [some (0, .right, 50), some (1, .right, 23)],
  [some (0, .right, 58), some (1, .right, 89)],
  [some (0, .right, 58), some (1, .right, 94)],
  [some (0, .right, 91), some (1, .right, 92)],
  [some (0, .right, 23), some (1, .right, 43)],
  [some (0, .right, 46), some (1, .right, 61)],
  [some (0, .right, 56), some (1, .right, 93)],
  [some (0, .right, 32), some (1, .right, 19)],
  [some (0, .right, 56), some (1, .right, 43)],
  [some (0, .right, 58), some (1, .right, 43)]
]

def machine : Machine 95 2 := Machine.ofRows rows

abbrev candidate : BundledMachine 2 := machine.bundle

def nSteps : Nat → Cfg 95 2 → Option (Cfg 95 2)
  | 0, c => some c
  | n + 1, c => (step machine c).bind (nSteps n)

def initialRegs : List Nat := [0,0,0,0,0]

def initialExtra : List Nat := List.replicate 4 0

def initialRoot : Cfg 95 2 :=
  ⟨15, Tape.mk' (ListBlank.cons 1 default)
    (ListBlank.mk
      (Riemann120.mapStack [] ++ List.replicate (22 - (Riemann120.mapStack []).length) 0 ++
        [1,0] ++ Semantics.Riemann.Layer1.encodeRegs (initialRegs ++ initialExtra)))⟩

end ConjectureMachines.Riemann95
