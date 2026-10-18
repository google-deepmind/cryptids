/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition

@[expose] public section

/-! Actual recursive95 decoder prefix. This proves arbitrary repetition and
arbitrary suffix behavior of the read-preserving rightward parser, not the
whole machine or caller-language closure. -/
namespace CryptidsResearch.Recursive95Parser

open Turing

def walkInternal (q : Fin 95) : List (Fin 2) → Option (Fin 95)
  | [] => some q
  | b :: bs =>
    match ConjectureMachines.Riemann95.machine.transition q b with
    | some (w, .right, next) =>
      if w = b then walkInternal next bs else none
    | _ => none

theorem walkInternal_append (q : Fin 95) (a b : List (Fin 2)) :
    walkInternal q (a ++ b) = (walkInternal q a).bind (fun r => walkInternal r b) := by
  induction a generalizing q with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, walkInternal]
    cases ht : ConjectureMachines.Riemann95.machine.transition q x with
    | none => rfl
    | some triple =>
      rcases triple with ⟨w, dir, next⟩
      cases dir with
      | left => rfl
      | right =>
        by_cases h : w = x
        · simp only [h, ite_true, ih]
        · simp only [h, ite_false, Option.bind_none]

def prefixBits : List (Fin 2) := [1,1,1,1,1,0]
def block : List (Fin 2) := [1,1,1,1,0]

def repetitions : Nat → List (Fin 2)
  | 0 => []
  | n + 1 => block ++ repetitions n

theorem actual_prefix : walkInternal 15 prefixBits = some 46 := by rfl
theorem actual_cycle : walkInternal 46 block = some 46 := by rfl

theorem repetitions_parse (n : Nat) (tail : List (Fin 2)) :
    walkInternal 46 (repetitions n ++ tail) = walkInternal 46 tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repetitions, List.append_assoc, walkInternal_append,
      actual_cycle, Option.bind_some, ih]

theorem prefix_parse (n : Nat) (tail : List (Fin 2)) :
    walkInternal 15 (prefixBits ++ repetitions n ++ tail) = walkInternal 46 tail := by
  rw [List.append_assoc, walkInternal_append, actual_prefix,
    Option.bind_some, repetitions_parse]

theorem repetitions_length (n : Nat) : (repetitions n).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [repetitions, List.length_append, block, List.length_cons,
      List.length_nil, ih]
    omega

theorem prefix_length (n : Nat) (tail : List (Fin 2)) :
    (prefixBits ++ repetitions n ++ tail).length = 6 + 5 * n + tail.length := by
  simp only [List.length_append, prefixBits, List.length_cons,
    List.length_nil, repetitions_length]


end CryptidsResearch.Recursive95Parser
