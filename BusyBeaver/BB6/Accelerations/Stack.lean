/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Shared Stack Encodings for `BB(6)` Accelerations (`BusyBeaver/BB6/Accelerations/Stack.lean`)

Shared half-tape encodings (`encStack`, `encStack2`, `encRun`) and head-digit update operations
(`incRun`, `bumpHead`, `bumpHeadBy`) used across the `BB(6)` multi-layer acceleration modules.
-/

@[expose] public section

namespace BusyBeaver.Stack

open Turing

/-- Encode a digit stack `s` as `1^{a + 1} 0 ...` from the tape head outward. -/
def encStack : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s => ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.cons 0 (encStack s))

/-- Encode a digit stack `s` as `1^{a + 1} 00 ...` from the tape head outward. -/
def encStack2 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.cons 0 (ListBlank.cons 0 (encStack2 s)))

/-- Encode a zero-run stack `s` as `0^k 1 ...` from the tape head outward. -/
def encRun : List ℕ → ListBlank (Fin 2)
  | [] => default
  | k :: xs => ListBlank.append (([0] : List (Fin 2)) ^ k) (ListBlank.cons 1 (encRun xs))

/-- Prepend a leading `0` to `encRun xs` (incrementing the head run on non-empty stacks). -/
def incRun : List ℕ → List ℕ
  | [] => []
  | k :: xs => (k + 1) :: xs

/-- Increment the head digit of a stack, or push `0` onto an empty stack. -/
def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | a :: s => (a + 1) :: s

/-- Iterate `bumpHead` `k` times on a stack. -/
def bumpHeadBy : ℕ → List ℕ → List ℕ
  | 0, s => s
  | k + 1, s => bumpHeadBy k (bumpHead s)

/-- Appending `0 ^ n` onto the blank half-tape yields the blank half-tape. -/
theorem zeros_append_default (n : ℕ) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ListBlank.append_pow_succ, ih]
    simp

/-- Increment the primary coordinate of the top pair-stack element, or push `(0, 0)` if empty. -/
def bumpPairHead : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: s => (a + 1, b) :: s

private def liftPairList : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs => (x, 0) :: liftPairList xs

private theorem map_fst_liftPairList : ∀ s : List ℕ, (liftPairList s).map Prod.fst = s
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (map_fst_liftPairList xs)

/-- One-digit (`List ℕ`) sufficient conditions for `HasStackReduction` (`maxSepL = maxSepR = 1`). -/
def OneDigitStackReduction {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin 2) Λ)
    (StackMode : Type)
    (encLeft1 encRight1 : List ℕ → ListBlank (Fin 2))
    (evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) Λ)
    (IsInStackSystem1 : Cfg (Fin 2) Λ → Prop) : Prop :=
  encLeft1 [] = default ∧
  encRight1 [] = default ∧
  (∀ a L, (encLeft1 (a :: L)).head = (1 : Fin 2)) ∧
  (∀ d R, (encRight1 (d :: R)).head = (1 : Fin 2)) ∧
  (∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ L : List ℕ, encLeft1 L ≠ t) ∧
  (∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ R : List ℕ, encRight1 R ≠ t) ∧
  (∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
    strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
    strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
    (∀ a L, encLeft1 (a :: L) =
      ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
        (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encLeft1 L))) ∧
    (∀ d R, encRight1 (d :: R) =
      ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
        (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encRight1 R)))) ∧
  (∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes) ∧
  IsValidStackModes encLeft1 encRight1 evalStackCfg1 ∧
  (∀ cfg, IsInStackSystem1 cfg ↔ ∃ m L R, cfg = evalStackCfg1 m L R) ∧
  (∀ m L R, IsInStackSystem1 (evalStackCfg1 m L R)) ∧
  (∃ cfg₀, ReachesPlus M (init []) cfg₀ ∧ IsInStackSystem1 cfg₀) ∧
  (∀ cfg, IsInStackSystem1 cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧ (IsInStackSystem1 cfg' ∨ (step M cfg').isNone))

/-- Lift a 1-digit (`List ℕ`) stack reduction to `HasStackReduction` (`List (ℕ × ℕ)`). -/
theorem HasStackReduction.of_oneDigit {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin 2) Λ)
    (StackMode : Type)
    (encLeft1 encRight1 : List ℕ → ListBlank (Fin 2))
    (evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) Λ)
    (IsInStackSystem1 : Cfg (Fin 2) Λ → Prop)
    (h : OneDigitStackReduction M StackMode encLeft1 encRight1 evalStackCfg1 IsInStackSystem1) :
    HasStackReduction M := by
  refine ⟨StackMode, 1, 0,
    fun (L : List (ℕ × ℕ)) => encLeft1 (L.map Prod.fst),
    fun (R : List (ℕ × ℕ)) => encRight1 (R.map Prod.fst),
    fun (m : StackMode) (L R : List (ℕ × ℕ)) => evalStackCfg1 m (L.map Prod.fst) (R.map Prod.fst),
    fun (cfg : Cfg (Fin 2) Λ) =>
      ∃ (m : StackMode) (L R : List (ℕ × ℕ)),
        cfg = evalStackCfg1 m (L.map Prod.fst) (R.map Prod.fst),
    ?_⟩
  rcases h with ⟨hnilL, hnilR, hheadL, hheadR, ⟨tL, htL, hnsL⟩, ⟨tR, htR, hnsR⟩,
    ⟨sL, oL, sepL, sR, oR, sepR, hsL, hoL, hsepL, hsR, hoR, hsepR, hblkL, hblkR⟩,
    hmodes, hvalid1, hiff1, _, ⟨cfg₀, hinit0, hsys0⟩, hclosed1⟩
  refine ⟨Or.inl ⟨rfl, rfl⟩, hnilL, hnilR,
    fun a _ L => hheadL a (L.map Prod.fst),
    fun d _ R => hheadR d (R.map Prod.fst),
    ⟨tL, htL, fun L => hnsL (L.map Prod.fst)⟩,
    ⟨tR, htR, fun R => hnsR (R.map Prod.fst)⟩,
    ⟨sL, oL, sepL, 1, sR, oR, sepR, 1,
      hsL, hoL, hsepL, le_refl 1, by decide,
      hsR, hoR, hsepR, le_refl 1, by decide,
      fun a b L => by simpa [Nat.mod_one] using hblkL a (L.map Prod.fst),
      fun d b R => by simpa [Nat.mod_one] using hblkR d (R.map Prod.fst)⟩,
    hmodes,
    fun m => ?_,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    ?_,
    ?_⟩
  · rcases hvalid1 m with ⟨q, vL, vR, h1 | h2 | h3⟩
    · exact ⟨q, vL, vR, Or.inl (fun L R => h1 (L.map Prod.fst) (R.map Prod.fst))⟩
    · exact ⟨q, vL, vR, Or.inr (Or.inl (fun L R => h2 (L.map Prod.fst) (R.map Prod.fst)))⟩
    · exact ⟨q, vL, vR, Or.inr (Or.inr (fun L R => h3 (L.map Prod.fst) (R.map Prod.fst)))⟩
  · rcases (hiff1 cfg₀).mp hsys0 with ⟨m, L1, R1, hcfg0⟩
    refine ⟨cfg₀, hinit0, m, liftPairList L1, liftPairList R1, ?_⟩
    rw [map_fst_liftPairList, map_fst_liftPairList]
    exact hcfg0
  · intro cfg ⟨m, L, R, hcfg⟩
    have hsys1 : IsInStackSystem1 cfg := (hiff1 cfg).mpr ⟨m, L.map Prod.fst, R.map Prod.fst, hcfg⟩
    rcases hclosed1 cfg hsys1 with ⟨cfg', hstep, hnext | hhalt⟩
    · rcases (hiff1 cfg').mp hnext with ⟨m', L1', R1', hcfg'⟩
      refine ⟨cfg', hstep, Or.inl ⟨m', liftPairList L1', liftPairList R1', ?_⟩⟩
      rw [map_fst_liftPairList, map_fst_liftPairList]
      exact hcfg'
    · exact ⟨cfg', hstep, Or.inr hhalt⟩

end BusyBeaver.Stack
