/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann.ControlSoundness

/-!
# Finite control-word guards for the one-pass scanner

These theorems certify canonical abstract control words and a local write/read
fact. They do not assert unary macro correctness or blank-tape equivalence.
-/

@[expose] public section

namespace ConjectureMachines.Riemann104.OnePassGuard

open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2

/-- Three consecutive zeros must occur only in the blank left root fence. -/
def NoThreeZeros : List (Fin 2) → Bool
  | 0 :: 0 :: 0 :: _ => false
  | _ :: rest => NoThreeZeros rest
  | [] => true

/-- The edited physical root header is the single one at coordinate minus one. -/
theorem valid_words_noThree (s : Fin 121) :
    NoThreeZeros (1 :: mapStack (PhaseB1.stack s)) = true ∧
    NoThreeZeros (1 :: mapStack (PhaseB1.stack s)).reverse = true := by
  fin_cases s <;> decide

/-- Every edited root control word leaves room before a padding marker at19. -/
theorem valid_words_width (s : Fin 121) :
    (mapStack (PhaseB1.stack s)).length ≤ 16 := by
  fin_cases s <;> decide

/-- Includes both arithmetic outcomes and the edited exceptional jump. -/
theorem updated_words_noThree (s : Fin 121) :
    ∀ next ∈ instrNextStacks (evalStackOf true (PhaseB1.stack s)),
      NoThreeZeros (1 :: mapStack next) = true ∧
      NoThreeZeros (1 :: mapStack next).reverse = true := by
  fin_cases s <;> decide

/-- Actual edited register execution has this scanner-word guard. -/
theorem executed_word_noThree (k : Nat) {c : RhRegCfg}
    (hsteps : rhRegNStepsOf true k rhRegInit = some c) :
    NoThreeZeros (1 :: mapStack c.stack) = true ∧
    NoThreeZeros (1 :: mapStack c.stack).reverse = true := by
  obtain ⟨s, m, hs, _, _⟩ := PhaseB1.executed_cap_allowed k hsteps
  rw [hs]
  exact valid_words_noThree s

/-- Frozen one-pass102 microcode in its original104 state labels.
The two removed labels are retained only to keep predecessor facts readable. -/
def sourceTable (q : Fin 104) (a : Fin 2) : Option (Fin 2 × Bool × Fin 104) :=
  match q.val, a.val with
  | 0, 0 => some (1, true, 8)
  | 0, 1 => some (1, true, 0)
  | 1, 0 => some (1, true, 1)
  | 1, 1 => some (0, true, 5)
  | 2, 0 => some (0, false, 14)
  | 2, 1 => some (0, false, 2)
  | 3, 0 => some (0, true, 5)
  | 3, 1 => some (1, true, 3)
  | 4, 0 => some (1, true, 4)
  | 4, 1 => some (1, false, 6)
  | 5, 0 => some (0, true, 0)
  | 5, 1 => some (1, true, 5)
  | 6, 0 => some (0, false, 6)
  | 6, 1 => some (1, false, 7)
  | 7, 0 => some (0, false, 9)
  | 7, 1 => some (1, false, 7)
  | 8, 0 => some (0, false, 10)
  | 8, 1 => some (0, true, 0)
  | 9, 0 => some (0, false, 13)
  | 9, 1 => some (1, false, 7)
  | 10, 0 => some (0, false, 12)
  | 10, 1 => some (1, false, 10)
  | 11, 0 => some (0, false, 13)
  | 11, 1 => some (1, false, 7)
  | 12, 0 => some (1, false, 14)
  | 12, 1 => some (1, false, 10)
  | 13, 0 => some (0, true, 15)
  | 13, 1 => some (1, false, 7)
  | 14, 0 => some (1, true, 16)
  | 14, 1 => some (0, false, 14)
  | 15, 0 => some (0, true, 15)
  | 15, 1 => some (1, true, 19)
  | 16, 0 => some (0, true, 16)
  | 16, 1 => some (1, false, 6)
  | 17, 0 => some (0, false, 18)
  | 17, 1 => some (0, true, 17)
  | 18, 0 => some (1, false, 6)
  | 18, 1 => some (0, false, 6)
  | 19, 0 => some (0, true, 20)
  | 19, 1 => some (1, true, 21)
  | 20, 0 => some (0, true, 22)
  | 20, 1 => some (1, true, 23)
  | 21, 0 => some (0, true, 24)
  | 21, 1 => some (1, true, 25)
  | 22, 0 => some (1, true, 22)
  | 22, 1 => some (0, true, 32)
  | 23, 0 => some (0, true, 27)
  | 23, 1 => some (0, false, 18)
  | 24, 0 => some (0, true, 28)
  | 24, 1 => some (1, true, 29)
  | 25, 0 => some (0, true, 30)
  | 25, 1 => some (1, true, 31)
  | 26, 0 => some (0, true, 32)
  | 26, 1 => some (1, true, 26)
  | 27, 0 => some (1, true, 27)
  | 27, 1 => some (0, true, 42)
  | 28, 0 => some (0, true, 34)
  | 28, 1 => some (1, true, 35)
  | 29, 0 => some (0, true, 36)
  | 29, 1 => some (0, false, 18)
  | 30, 0 => some (0, true, 37)
  | 30, 1 => some (1, true, 38)
  | 31, 0 => some (0, true, 39)
  | 31, 1 => some (1, true, 40)
  | 32, 0 => some (0, true, 41)
  | 32, 1 => some (1, true, 32)
  | 33, 0 => some (0, true, 42)
  | 33, 1 => some (1, true, 33)
  | 34, 0 => some (1, true, 34)
  | 34, 1 => some (0, true, 3)
  | 35, 0 => some (0, true, 44)
  | 35, 1 => some (1, true, 45)
  | 36, 0 => some (1, true, 36)
  | 36, 1 => some (0, true, 59)
  | 37, 0 => some (1, true, 37)
  | 37, 1 => some (0, true, 26)
  | 38, 0 => some (0, true, 48)
  | 38, 1 => some (0, false, 18)
  | 39, 0 => some (0, true, 49)
  | 39, 1 => some (1, true, 50)
  | 40, 0 => some (0, true, 52)
  | 40, 1 => some (1, true, 67)
  | 41, 0 => some (1, false, 53)
  | 41, 1 => some (0, true, 54)
  | 42, 0 => some (0, true, 43)
  | 42, 1 => some (1, true, 42)
  | 43, 0 => some (0, true, 3)
  | 43, 1 => some (1, true, 43)
  | 44, 0 => some (0, true, 55)
  | 44, 1 => some (1, true, 56)
  | 45, 0 => some (0, true, 57)
  | 45, 1 => some (1, true, 58)
  | 46, 0 => some (0, true, 59)
  | 46, 1 => some (1, true, 46)
  | 47, 0 => some (0, true, 26)
  | 47, 1 => some (1, true, 47)
  | 48, 0 => some (0, true, 60)
  | 48, 1 => some (1, true, 27)
  | 49, 0 => some (0, true, 61)
  | 49, 1 => some (1, true, 62)
  | 50, 0 => some (0, true, 63)
  | 50, 1 => some (1, true, 64)
  | 51, 0 => some (0, true, 37)
  | 51, 1 => some (1, true, 65)
  | 52, 0 => some (0, true, 51)
  | 52, 1 => some (1, true, 66)
  | 53, 0 => some (0, false, 68)
  | 53, 1 => some (1, false, 53)
  | 54, 0 => some (0, false, 41)
  | 54, 1 => some (1, true, 69)
  | 55, 0 => some (0, true, 37)
  | 55, 1 => some (1, true, 70)
  | 56, 0 => some (0, true, 71)
  | 56, 1 => some (1, true, 72)
  | 57, 0 => some (0, true, 63)
  | 57, 1 => some (1, true, 73)
  | 58, 0 => some (0, true, 74)
  | 58, 1 => some (1, true, 74)
  | 59, 0 => some (0, true, 47)
  | 59, 1 => some (1, true, 59)
  | 60, 0 => some (1, true, 60)
  | 60, 1 => some (0, true, 33)
  | 61, 0 => some (1, true, 61)
  | 61, 1 => some (0, true, 47)
  | 62, 0 => some (0, true, 44)
  | 62, 1 => some (1, true, 75)
  | 63, 0 => some (1, true, 63)
  | 63, 1 => some (0, true, 46)
  | 64, 0 => some (0, true, 34)
  | 64, 1 => some (0, false, 76)
  | 65, 0 => some (0, true, 77)
  | 65, 1 => some (1, true, 78)
  | 66, 0 => some (0, true, 61)
  | 66, 1 => some (1, true, 75)
  | 67, 0 => some (0, true, 36)
  | 67, 1 => none
  | 68, 0 => some (1, false, 2)
  | 68, 1 => some (1, false, 53)
  | 69, 0 => some (0, true, 79)
  | 69, 1 => some (1, true, 69)
  | 70, 0 => some (0, true, 60)
  | 70, 1 => some (0, false, 18)
  | 71, 0 => some (0, true, 61)
  | 71, 1 => some (1, true, 80)
  | 72, 0 => some (0, true, 22)
  | 72, 1 => some (1, true, 81)
  | 73, 0 => some (0, true, 60)
  | 73, 1 => some (1, true, 74)
  | 74, 0 => some (0, true, 71)
  | 74, 1 => some (1, true, 82)
  | 75, 0 => some (0, true, 29)
  | 75, 1 => some (0, false, 23)
  | 76, 0 => some (0, true, 46)
  | 76, 1 => some (0, false, 17)
  | 77, 0 => some (0, true, 1)
  | 77, 1 => some (1, true, 83)
  | 78, 0 => some (0, true, 84)
  | 78, 1 => some (0, false, 23)
  | 79, 0 => some (0, false, 85)
  | 79, 1 => some (1, true, 69)
  | 80, 0 => some (0, true, 1)
  | 80, 1 => some (0, false, 18)
  | 81, 0 => some (0, true, 86)
  | 81, 1 => some (0, false, 18)
  | 82, 0 => some (0, true, 87)
  | 82, 1 => some (1, true, 88)
  | 83, 0 => some (0, true, 89)
  | 83, 1 => some (1, true, 90)
  | 84, 0 => some (1, true, 84)
  | 84, 1 => some (0, true, 43)
  | 85, 0 => some (1, false, 91)
  | 85, 1 => some (1, false, 85)
  | 86, 0 => some (0, true, 50)
  | 86, 1 => some (1, true, 92)
  | 87, 0 => some (0, true, 93)
  | 87, 1 => some (1, true, 50)
  | 88, 0 => some (0, true, 22)
  | 88, 1 => some (1, true, 78)
  | 89, 0 => some (0, true, 94)
  | 89, 1 => some (1, true, 50)
  | 90, 0 => some (0, true, 89)
  | 90, 1 => some (1, true, 95)
  | 91, 0 => some (0, false, 12)
  | 91, 1 => some (0, false, 85)
  | 92, 0 => some (0, true, 55)
  | 92, 1 => some (1, true, 84)
  | 93, 0 => some (0, true, 37)
  | 93, 1 => some (1, true, 96)
  | 94, 0 => some (0, true, 37)
  | 94, 1 => some (1, true, 97)
  | 95, 0 => some (0, true, 98)
  | 95, 1 => some (1, true, 99)
  | 96, 0 => some (0, true, 60)
  | 96, 1 => some (1, true, 78)
  | 97, 0 => some (0, true, 100)
  | 97, 1 => some (0, false, 18)
  | 98, 0 => some (0, true, 36)
  | 98, 1 => some (1, true, 101)
  | 99, 0 => some (0, true, 63)
  | 99, 1 => some (1, true, 23)
  | 100, 0 => some (0, true, 1)
  | 100, 1 => some (1, true, 102)
  | 101, 0 => some (0, true, 103)
  | 101, 1 => some (0, false, 18)
  | 102, 0 => some (0, true, 37)
  | 102, 1 => some (1, true, 60)
  | 103, 0 => some (0, true, 36)
  | 103, 1 => some (1, true, 60)
  | _, _ => none

theorem continue1_rows : sourceTable 50 1 = some (1, true, 64) ∧
    sourceTable 64 1 = some (0, false, 76) := by decide

/-- Source50/1 writes one before source64/1 moves back onto that same cell.
The second write is at the adjacent cell and cannot erase the first write. -/
theorem continue1_read_one (tape : Int → Fin 2) (head : Int) :
    Function.update (Function.update tape head 1) (head + 1) 0 head = 1 := by
  have hne : head ≠ head + 1 := by omega
  simp [Function.update, hne]

end ConjectureMachines.Riemann104.OnePassGuard
