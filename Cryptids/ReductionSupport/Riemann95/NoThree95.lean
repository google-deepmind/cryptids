/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ControllerSchema95

@[expose] public section

namespace ConjectureMachines.Riemann95.Schema

open ConjectureMachines.Riemann104.OnePassGuard

theorem guard_append_one (xs ys : Word) :
    NoThreeZeros (xs ++ 1 :: ys) = (NoThreeZeros xs && NoThreeZeros ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases ConjectureMachines.Semantics.Riemann.Layer1.fin2_cases a with rfl | rfl
    · cases xs with
      | nil => rfl
      | cons b bs =>
        rcases ConjectureMachines.Semantics.Riemann.Layer1.fin2_cases b with rfl | rfl
        · cases bs with
          | nil => rfl
          | cons c cs =>
            rcases ConjectureMachines.Semantics.Riemann.Layer1.fin2_cases c with rfl | rfl
            · rfl
            · simpa only [List.cons_append,NoThreeZeros] using ih
        · simpa only [List.cons_append,NoThreeZeros] using ih
    · simpa only [List.cons_append,NoThreeZeros] using ih

theorem callerPrefix_noThree (d : Nat) : NoThreeZeros (callerPrefix d) = true := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change NoThreeZeros (callerPrefix d ++ 1 :: [1,1,1,0]) = true
    rw [guard_append_one,ih]
    rfl

theorem callerPrefix_reverse_noThree (d : Nat) :
    NoThreeZeros ((callerPrefix d).reverse ++ [1]) = true := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simpa only [callerPrefix,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.append_assoc,List.cons_append,List.nil_append,NoThreeZeros] using ih

theorem entry_succ (d : Nat) : entry (d+1) = callerPrefix d ++ [1,1,1,1] := by
  simp [entry,callerPrefix]

theorem entry_noThree (d : Nat) :
    NoThreeZeros (1 :: entry d) = true ∧
    NoThreeZeros (1 :: entry d).reverse = true := by
  cases d with
  | zero => exact ⟨rfl,rfl⟩
  | succ d =>
    rw [entry_succ]
    constructor
    · change NoThreeZeros (callerPrefix d ++ 1 :: [1,1,1]) = true
      rw [guard_append_one,callerPrefix_noThree]
      rfl
    · simpa only [List.reverse_cons,List.reverse_append,List.reverse_nil,List.cons_append,
        List.nil_append,List.append_assoc,NoThreeZeros] using callerPrefix_reverse_noThree d

theorem suffix_tail_guards : ∀ s : Fin 22,
    suffix s = 1 :: (suffix s).tail ∧
    NoThreeZeros (suffix s).tail = true ∧
    NoThreeZeros (suffix s).tail.reverse = true := by decide +kernel

theorem local_noThree (d : Nat) (s : Fin 22) :
    NoThreeZeros (1 :: word (.local d s)) = true ∧
    NoThreeZeros (1 :: word (.local d s)).reverse = true := by
  obtain ⟨hc,hf,hr⟩ := suffix_tail_guards s
  change NoThreeZeros (1 :: (callerPrefix d ++ suffix s)) = true ∧
    NoThreeZeros (1 :: (callerPrefix d ++ suffix s)).reverse = true
  rw [hc]
  constructor
  · change NoThreeZeros (callerPrefix d ++ 1 :: (suffix s).tail) = true
    rw [guard_append_one,callerPrefix_noThree,hf]
    rfl
  · simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]
    change NoThreeZeros ((suffix s).tail.reverse ++ 1 :: ((callerPrefix d).reverse ++ [1])) = true
    rw [guard_append_one,hr,callerPrefix_reverse_noThree]
    rfl

theorem word_noThree (w : ControlWord) :
    NoThreeZeros (1 :: word w) = true ∧
    NoThreeZeros (1 :: word w).reverse = true := by
  cases w with
  | outside s => exact outside_noThree s
  | entry d => exact entry_noThree d
  | «local» d s => exact local_noThree d s

end ConjectureMachines.Riemann95.Schema
