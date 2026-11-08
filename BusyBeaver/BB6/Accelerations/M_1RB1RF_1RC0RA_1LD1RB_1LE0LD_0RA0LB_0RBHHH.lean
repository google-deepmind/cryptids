/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Stack
public import BusyBeaver.WordRunStack

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.deprecated false
set_option linter.flexible false

/-!
# Busy Beaver Machine `1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---` — `is_segmented_cryptid` (`IsSegmentedCryptid target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

local notation "zB" => ListBlank (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

open Counter

local macro "finish" : tactic => `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
      zero_cons_default, default_head, default_tail])
local macro "step1" : tactic => `(tactic| try (any_goals (first | finish | gstep)))
local macro "execute" : tactic =>
  `(tactic| (step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1))

/-- Three head modes of Holdout `#119` (`1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---`). -/
inductive SegMode where
  | mCL
  | mAR
  | mA0
deriving DecidableEq, Repr

/-- Left half-tape word `1^(d+1) ++ [0]` (`b = false`) or `1^(2d+1) ++ [0, 0]` (`b = true`),
forbidding `[0, 0, 0, 1]`. -/
@[simp]
def lWord : ℕ × Bool → List (Fin 2)
  | (0, false) => [1, 0]
  | (d + 1, false) => 1 :: lWord (d, false)
  | (0, true) => [1, 0, 0]
  | (k + 1, true) => 1 :: 1 :: lWord (k, true)

/-- Right half-tape parameterized zero-run word `0^z ++ [1]`. -/
@[simp]
def zWord : ℕ → List (Fin 2)
  | 0 => [1]
  | z + 1 => 0 :: zWord z

@[simp]
def encLeft : List (ℕ × Bool) → zB
  | [] => default
  | p :: L => lWord p +> encLeft L

@[simp]
def encRight : List ℕ → zB
  | [] => default
  | z :: R => zWord z +> encRight R

abbrev SegState := SegMode × List (ℕ × Bool) × List ℕ

@[simp]
def modeOf (s : SegState) : SegMode := s.1

@[simp]
def ValidSeg (_ : SegState) : Prop := True

@[simp]
def segsL (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.1.map lWord)]

@[simp]
def segsR (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.2.map zWord)]

lemma append_assoc_blank (a b : List (Fin 2)) (s : zB) :
    (a ++ b) +> s = a +> (b +> s) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

lemma evalSegRegion_lWord (L : List (ℕ × Bool)) :
    evalSegRegion (.finWord (L.map lWord)) +> (default : zB) = encLeft L := by
  induction L with
  | nil => simp [evalSegRegion, encLeft, listblank_append_nil]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, encLeft, ← ih]
    exact append_assoc_blank (lWord p) (evalSegRegion (.finWord (rest.map lWord))) default

lemma evalSegRegion_zWord (R : List ℕ) :
    evalSegRegion (.finWord (R.map zWord)) +> (default : zB) = encRight R := by
  induction R with
  | nil => simp [evalSegRegion, encRight, listblank_append_nil]
  | cons z rest ih =>
    simp only [List.map_cons, evalSegRegion, encRight, ← ih]
    exact append_assoc_blank (zWord z) (evalSegRegion (.finWord (rest.map zWord))) default

@[simp]
lemma evalSegmentedHalf_segsL (m : SegMode) (L : List (ℕ × Bool)) (R : List ℕ) :
    evalSegmentedHalf (segsL (m, L, R)) = encLeft L :=
  evalSegRegion_lWord L

@[simp]
lemma evalSegmentedHalf_segsR (m : SegMode) (L : List (ℕ × Bool)) (R : List ℕ) :
    evalSegmentedHalf (segsR (m, L, R)) = encRight R :=
  evalSegRegion_zWord R

lemma encLeft_nth_zero (p : ℕ × Bool) (L : List (ℕ × Bool)) :
    (encLeft (p :: L)).nth 0 = 1 := by
  rcases p with ⟨_ | d, _ | _⟩ <;>
    simp only [encLeft, lWord, ListBlank.append, WordRunStack.nth_cons_zero]

lemma noFactor_0001_lWord_nil (d : ℕ) (b : Bool) :
    WordRunStack.NoFactor [0, 0, 0, 1] (lWord (d, b) +> (default : zB)) := by
  have hd : WordRunStack.NoFactor [0, 0, 0, 1] (default : zB) :=
    WordRunStack.noFactor_default [0, 0, 0, 1] 3 (by decide) (by decide)
  induction d with
  | zero =>
    cases b <;> (
      simp only [lWord, ListBlank.append, zero_cons_default]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) default hd 0
        (by decide) (by rw [WordRunStack.nth_cons_zero]; decide))
  | succ d ih =>
    cases b with
    | false =>
      simp only [lWord, ListBlank.append]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [lWord, ListBlank.append]
      have h1 : WordRunStack.NoFactor [0, 0, 0, 1] ((1 : Fin 2) >> (lWord (d, true) +> default)) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
          (by rw [WordRunStack.nth_cons_zero]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h1 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)

lemma noFactor_0001_lWord_cons (d : ℕ) (b : Bool) (t : zB) (ht0 : t.nth 0 = 1)
    (ht : WordRunStack.NoFactor [0, 0, 0, 1] t) :
    WordRunStack.NoFactor [0, 0, 0, 1] (lWord (d, b) +> t) := by
  induction d with
  | zero =>
    cases b with
    | false =>
      simp only [lWord, ListBlank.append]
      have h0 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) t ht 1 (by decide)
          (by rw [WordRunStack.nth_cons_succ, ht0]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h0 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [lWord, ListBlank.append]
      have h0 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) t ht 1 (by decide)
          (by rw [WordRunStack.nth_cons_succ, ht0]; decide)
      have h00 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> (0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) _ h0 2 (by decide)
          (by rw [WordRunStack.nth_cons_succ, WordRunStack.nth_cons_succ, ht0]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h00 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
  | succ d ih =>
    cases b with
    | false =>
      simp only [lWord, ListBlank.append]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [lWord, ListBlank.append]
      have h1 : WordRunStack.NoFactor [0, 0, 0, 1] ((1 : Fin 2) >> (lWord (d, true) +> t)) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
          (by rw [WordRunStack.nth_cons_zero]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h1 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)

lemma noFactor_0001_encLeft :
    ∀ L : List (ℕ × Bool), WordRunStack.NoFactor [0, 0, 0, 1] (encLeft L)
  | [] => WordRunStack.noFactor_default [0, 0, 0, 1] 3 (by decide) (by decide)
  | [(d, b)] => noFactor_0001_lWord_nil d b
  | (d, b) :: p :: L =>
    noFactor_0001_lWord_cons d b (encLeft (p :: L)) (encLeft_nth_zero p L)
      (noFactor_0001_encLeft (p :: L))

lemma segsL_nowhere_dense : IsNowhereDenseHalf ValidSeg segsL :=
  WordRunStack.isNowhereDenseHalf_of_noFactor ValidSeg segsL [0, 0, 0, 1]
    (fun ⟨_, L, _⟩ _ => by rw [evalSegmentedHalf_segsL]; exact noFactor_0001_encLeft L)

lemma segs_len_le_three (s : SegState) (_ : ValidSeg s) :
    (segsL s).length ≤ 3 ∧ (segsR s).length ≤ 3 := by
  simp [segsL, segsR]

@[simp]
def evalSegCfg : SegMode → List (ℕ × Bool) → List ℕ → Cfg (Fin 2) (Fin 6)
  | .mCL, L, R => (applyView (.id []) (encLeft L)) <{{3}} (applyView (.id []) (encRight R))
  | .mAR, L, R => (applyView (.id []) (encLeft L)) {{1}}> (applyView (.id []) (encRight R))
  | .mA0, L, R => (applyView (.id [0]) (encLeft L)) {{1}}> (applyView (.id []) (encRight R))

@[simp]
def evalCfg (s : SegState) : Cfg (Fin 2) (Fin 6) :=
  evalSegCfg s.1 s.2.1 s.2.2

lemma valid_seg_modes :
    ∀ m : SegMode, ∃ (q : Fin 6) (vL vR : HalfTapeView (Fin 2)),
      viewPrefixLen vL ≤ 8 ∧ viewPrefixLen vR ≤ 8 ∧
      ∀ s : SegState, ValidSeg s → modeOf s = m →
        (evalCfg s = ⟨some q, ⟨0,
          applyView vL (evalSegmentedHalf (segsL s)),
          applyView vR (evalSegmentedHalf (segsR s))⟩⟩) ∨
        (evalCfg s = (applyView vL (evalSegmentedHalf (segsL s))) <{{q}}
          (applyView vR (evalSegmentedHalf (segsR s)))) ∨
        (evalCfg s = (applyView vL (evalSegmentedHalf (segsL s))) {{q}}>
          (applyView vR (evalSegmentedHalf (segsR s)))) := by
  intro m
  cases m with
  | mCL =>
    refine ⟨3, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)
  | mAR =>
    refine ⟨1, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mA0 =>
    refine ⟨1, .id [0], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)

lemma segsR_boundary_aligned :
    ∀ s : SegState, ValidSeg s → ∃ q vL,
      (evalCfg s = ⟨some q, ⟨0, vL, evalSegmentedHalf (segsR s)⟩⟩) ∨
      (evalCfg s = vL <{{q}} (evalSegmentedHalf (segsR s))) ∨
      (evalCfg s = vL {{q}}> (evalSegmentedHalf (segsR s))) := by
  rintro ⟨m, L, R⟩ _
  rw [evalSegmentedHalf_segsR]
  cases m with
  | mCL => exact ⟨3, applyView (.id []) (encLeft L), Or.inr (Or.inl rfl)⟩
  | mAR => exact ⟨1, applyView (.id []) (encLeft L), Or.inr (Or.inr rfl)⟩
  | mA0 => exact ⟨1, applyView (.id [0]) (encLeft L), Or.inr (Or.inr rfl)⟩

@[simp]
def bump2L : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => [(1, false)]
  | (d, false) :: L => (d + 2, false) :: L
  | (k, true) :: L => (k + 1, true) :: L

@[simp]
def push0R : List ℕ → List ℕ
  | [] => []
  | z :: R => (z + 1) :: R

@[simp]
def cfgHalt (L : List (ℕ × Bool)) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) {{5}}> (encRight (0 :: R))

@[simp]
def s₀ : SegState := (.mAR, [(0, false)], [])

lemma zero_cons_encRight (R : List ℕ) :
    (0 : Fin 2) >> encRight R = encRight (push0R R) := by
  cases R <;> simp [push0R, encRight, zWord, ListBlank.append, zero_cons_default]

lemma pat11_cons_encLeft (L : List (ℕ × Bool)) :
    (1 : Fin 2) >> (1 : Fin 2) >> encLeft L = encLeft (bump2L L) := by
  rcases L with _ | ⟨⟨_ | d, _ | _⟩, L⟩ <;>
    simp [bump2L, encLeft, lWord, ListBlank.append, zero_cons_default]

lemma init_reaches_segmented_system :
    (init []) [target_tm]⊢⁺ evalSegCfg .mAR [(0, false)] [] := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_cfgHalt_isNone (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (step target_tm (cfgHalt L Rt)).isNone := by
  simp [cfgHalt, encRight, zWord, ListBlank.append, Turing.ListBlank.head_cons, step, target_tm]

-- Mode mCL (<2) transitions
lemma step_mCL_nil_nil :
    (evalSegCfg .mCL [] []) [target_tm]⊢⁺ evalSegCfg .mA0 [(0, false)] [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_nil_0_halt (Rt : List ℕ) :
    (evalSegCfg .mCL [] (0 :: Rt)) [target_tm]⊢⁺ cfgHalt [(0, false)] Rt := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_nil_succ (z : ℕ) (Rt : List ℕ) :
    (evalSegCfg .mCL [] ((z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0 [(0, false)] (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_0_false_nil (R : List ℕ) :
    (evalSegCfg .mCL [(0, false)] R) [target_tm]⊢⁺ evalSegCfg .mA0 [(0, false)] R := by
  simp only [evalSegCfg, applyView, encLeft, lWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_0_false_0_false (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (0, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL L (1 :: 0 :: push0R R) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_0_false_0_true (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (0, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL ((0, false) :: L) (0 :: 0 :: push0R R) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_0_false_1_false (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (1, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: (0, true) :: L) R := by
  simp only [evalSegCfg, applyView, encLeft, lWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_0_false_succ2_false (d : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (d + 2, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: (0, false) :: (d, false) :: L) R := by
  cases d <;> (
    simp only [evalSegCfg, applyView, encLeft, lWord,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]
    execute)

lemma step_mCL_0_false_succ_true (k : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (k + 1, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: (0, false) :: (k, true) :: L) R := by
  cases k <;> (
    simp only [evalSegCfg, applyView, encLeft, lWord,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]
    execute)

lemma step_mCL_0_true (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, false) :: L) R := by
  simp only [evalSegCfg, applyView, encLeft, lWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mCL_succ_false (d : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((d + 1, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL ((d, false) :: L) (push0R R) := by
  cases d <;> (
    simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft, lWord,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]
    execute)

lemma step_mCL_succ_true (k : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((k + 1, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL ((k, true) :: L) (push0R (push0R R)) := by
  cases k <;> (
    simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft, lWord,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]
    execute)

@[simp]
def push00IterR : ℕ → List ℕ → List ℕ
  | 0, R => R
  | k + 1, R => push00IterR k (push0R (push0R R))

lemma step_mCL_true_sweep (k : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((k, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, false) :: L) (push00IterR k R) := by
  induction k generalizing R with
  | zero =>
    simp only [push00IterR]
    exact step_mCL_0_true L R
  | succ k ih =>
    simp only [push00IterR]
    exact stepPlus_trans (step_mCL_succ_true k L R) (ih (push0R (push0R R)))

-- Mode mAR (0>) transitions
lemma step_mAR_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mAR L []) [target_tm]⊢⁺ evalSegCfg .mCL L [1] := by
  simp only [evalSegCfg, applyView, encRight, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mAR L [0]) [target_tm]⊢⁺ evalSegCfg .mAR ((0, false) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_0_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mAR L [0, 0]) [target_tm]⊢⁺ evalSegCfg .mA0 ((0, false) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_0_0_0_halt (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (0 :: 0 :: 0 :: Rt)) [target_tm]⊢⁺
      cfgHalt ((0, false) :: L) Rt := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_0_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (0 :: 0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, false) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_1_cons (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (1 :: Rt)) [target_tm]⊢⁺ evalSegCfg .mAR (bump2L L) Rt := by
  simp only [evalSegCfg, applyView, ← pat11_cons_encLeft, encRight, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAR_succ2 (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L ((z + 2) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mCL L (1 :: z :: Rt) := by
  simp only [evalSegCfg, applyView, encRight, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

-- Mode mA0 (0> with leading 0) transitions
lemma step_mA0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mA0 L []) [target_tm]⊢⁺ evalSegCfg .mCL ((0, false) :: L) [0] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mA0 L [0]) [target_tm]⊢⁺ evalSegCfg .mAR ((0, true) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_0_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mA0 L [0, 0]) [target_tm]⊢⁺ evalSegCfg .mA0 ((0, true) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_0_0_0_halt (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (0 :: 0 :: 0 :: Rt)) [target_tm]⊢⁺
      cfgHalt ((0, true) :: L) Rt := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_0_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (0 :: 0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, true) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, true) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_1_cons (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (1 :: Rt)) [target_tm]⊢⁺ evalSegCfg .mAR ((1, false) :: L) Rt := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mA0_succ2 (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L ((z + 2) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mCL ((0, false) :: L) (0 :: z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, lWord, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

theorem segmented_step_sound (m : SegMode) (L : List (ℕ × Bool)) (R : List ℕ) :
    ∃ cfg', ((evalSegCfg m L R) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) := by
  cases m with
  | mCL =>
    rcases L with _ | ⟨⟨_ | d, _ | _⟩, Ls⟩
    · rcases R with _ | ⟨_ | z, Rt⟩
      · exact ⟨evalCfg (.mA0, [(0, false)], []), step_mCL_nil_nil,
          Or.inl ⟨(.mA0, [(0, false)], []), trivial, rfl⟩⟩
      · exact ⟨cfgHalt [(0, false)] Rt, step_mCL_nil_0_halt Rt,
          Or.inr (step_cfgHalt_isNone [(0, false)] Rt)⟩
      · exact ⟨evalCfg (.mA0, [(0, false)], z :: Rt), step_mCL_nil_succ z Rt,
          Or.inl ⟨(.mA0, [(0, false)], z :: Rt), trivial, rfl⟩⟩
    · rcases Ls with _ | ⟨⟨_ | _ | d2, _ | _⟩, Lss⟩
      · exact ⟨evalCfg (.mA0, [(0, false)], R), step_mCL_0_false_nil R,
          Or.inl ⟨(.mA0, [(0, false)], R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mCL, Lss, 1 :: 0 :: push0R R), step_mCL_0_false_0_false Lss R,
          Or.inl ⟨(.mCL, Lss, 1 :: 0 :: push0R R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mCL, (0, false) :: Lss, 0 :: 0 :: push0R R),
          step_mCL_0_false_0_true Lss R,
          Or.inl ⟨(.mCL, (0, false) :: Lss, 0 :: 0 :: push0R R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (0, false) :: (0, true) :: Lss, R),
          step_mCL_0_false_1_false Lss R,
          Or.inl ⟨(.mAR, (0, false) :: (0, true) :: Lss, R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (0, false) :: (0, false) :: (0, true) :: Lss, R),
          step_mCL_0_false_succ_true 0 Lss R,
          Or.inl ⟨(.mAR, (0, false) :: (0, false) :: (0, true) :: Lss, R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (0, false) :: (0, false) :: (d2, false) :: Lss, R),
          step_mCL_0_false_succ2_false d2 Lss R,
          Or.inl ⟨(.mAR, (0, false) :: (0, false) :: (d2, false) :: Lss, R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (0, false) :: (0, false) :: (d2 + 1, true) :: Lss, R),
          step_mCL_0_false_succ_true (d2 + 1) Lss R,
          Or.inl ⟨(.mAR, (0, false) :: (0, false) :: (d2 + 1, true) :: Lss, R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mA0, (0, false) :: Ls, R), step_mCL_true_sweep 0 Ls R,
        Or.inl ⟨(.mA0, (0, false) :: Ls, R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL, (d, false) :: Ls, push0R R), step_mCL_succ_false d Ls R,
        Or.inl ⟨(.mCL, (d, false) :: Ls, push0R R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mA0, (0, false) :: Ls, push00IterR (d + 1) R),
        step_mCL_true_sweep (d + 1) Ls R,
        Or.inl ⟨(.mA0, (0, false) :: Ls, push00IterR (d + 1) R), trivial, rfl⟩⟩
  | mAR =>
    rcases R with _ | ⟨_ | _ | z, Rt⟩
    · exact ⟨evalCfg (.mCL, L, [1]), step_mAR_nil L, Or.inl ⟨(.mCL, L, [1]), trivial, rfl⟩⟩
    · rcases Rt with _ | ⟨_ | z2, Rt2⟩
      · exact ⟨evalCfg (.mAR, (0, false) :: L, []), step_mAR_0_nil L,
          Or.inl ⟨(.mAR, (0, false) :: L, []), trivial, rfl⟩⟩
      · rcases Rt2 with _ | ⟨_ | z3, Rt3⟩
        · exact ⟨evalCfg (.mA0, (0, false) :: L, []), step_mAR_0_0_nil L,
            Or.inl ⟨(.mA0, (0, false) :: L, []), trivial, rfl⟩⟩
        · exact ⟨cfgHalt ((0, false) :: L) Rt3, step_mAR_0_0_0_halt L Rt3,
            Or.inr (step_cfgHalt_isNone ((0, false) :: L) Rt3)⟩
        · exact ⟨evalCfg (.mA0, (0, false) :: L, z3 :: Rt3), step_mAR_0_0_succ z3 L Rt3,
            Or.inl ⟨(.mA0, (0, false) :: L, z3 :: Rt3), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (0, false) :: L, z2 :: Rt2), step_mAR_0_succ z2 L Rt2,
          Or.inl ⟨(.mAR, (0, false) :: L, z2 :: Rt2), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mAR, bump2L L, Rt), step_mAR_1_cons L Rt,
        Or.inl ⟨(.mAR, bump2L L, Rt), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL, L, 1 :: z :: Rt), step_mAR_succ2 z L Rt,
        Or.inl ⟨(.mCL, L, 1 :: z :: Rt), trivial, rfl⟩⟩
  | mA0 =>
    rcases R with _ | ⟨_ | _ | z, Rt⟩
    · exact ⟨evalCfg (.mCL, (0, false) :: L, [0]), step_mA0_nil L,
        Or.inl ⟨(.mCL, (0, false) :: L, [0]), trivial, rfl⟩⟩
    · rcases Rt with _ | ⟨_ | z2, Rt2⟩
      · exact ⟨evalCfg (.mAR, (0, true) :: L, []), step_mA0_0_nil L,
          Or.inl ⟨(.mAR, (0, true) :: L, []), trivial, rfl⟩⟩
      · rcases Rt2 with _ | ⟨_ | z3, Rt3⟩
        · exact ⟨evalCfg (.mA0, (0, true) :: L, []), step_mA0_0_0_nil L,
            Or.inl ⟨(.mA0, (0, true) :: L, []), trivial, rfl⟩⟩
        · exact ⟨cfgHalt ((0, true) :: L) Rt3, step_mA0_0_0_0_halt L Rt3,
            Or.inr (step_cfgHalt_isNone ((0, true) :: L) Rt3)⟩
        · exact ⟨evalCfg (.mA0, (0, true) :: L, z3 :: Rt3), step_mA0_0_0_succ z3 L Rt3,
            Or.inl ⟨(.mA0, (0, true) :: L, z3 :: Rt3), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (0, true) :: L, z2 :: Rt2), step_mA0_0_succ z2 L Rt2,
          Or.inl ⟨(.mAR, (0, true) :: L, z2 :: Rt2), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mAR, (1, false) :: L, Rt), step_mA0_1_cons L Rt,
        Or.inl ⟨(.mAR, (1, false) :: L, Rt), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL, (0, false) :: L, 0 :: z :: Rt), step_mA0_succ2 z L Rt,
        Or.inl ⟨(.mCL, (0, false) :: L, 0 :: z :: Rt), trivial, rfl⟩⟩

theorem segmented_system_closed (s : SegState) (_ : ValidSeg s) :
    ∃ cfg', ((evalCfg s) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) :=
  segmented_step_sound s.1 s.2.1 s.2.2
-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_segmented_cryptid : IsSegmentedCryptid target_tm := by
  exact ⟨SegState, SegMode, ValidSeg, modeOf, segsL, segsR, evalCfg,
    ⟨[.mCL, .mAR, .mA0], by decide, by decide, fun m => by cases m <;> simp⟩,
    segs_len_le_three,
    valid_seg_modes,
    Or.inl segsL_nowhere_dense,
    Or.inl segsL_nowhere_dense,
    Or.inr segsR_boundary_aligned,
    ⟨s₀, trivial, init_reaches_segmented_system⟩,
    segmented_system_closed⟩

end BusyBeaver.M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RBHHH
