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
# Busy Beaver Machine `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---` — `is_segmented_cryptid` (`IsSegmentedCryptid target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
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

/-- Six head modes of Holdout `#729` (`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`). -/
inductive SegMode where
  | mAL
  | mB0
  | mD0
  | mD1
  | mCL
  | mCL1
deriving DecidableEq, Repr

/-- Left half-tape parameterized zero-run word `0^k ++ [1]`. -/
@[simp]
def zWord : ℕ → List (Fin 2)
  | 0 => [1]
  | k + 1 => 0 :: zWord k

/-- Right half-tape `1`-run word `1^(o+2)` of length at least `2`. -/
@[simp]
def oRun : ℕ → List (Fin 2)
  | 0 => [1, 1]
  | o + 1 => 1 :: oRun o

/-- Right half-tape word `0^z ++ 1^(o+2)` avoiding isolated `1`s (`010`). -/
@[simp]
def rWord : ℕ × ℕ → List (Fin 2)
  | (0, o) => oRun o
  | (z + 1, o) => 0 :: rWord (z, o)

@[simp]
def encLeft : List ℕ → zB
  | [] => default
  | k :: L => zWord k +> encLeft L

@[simp]
def encRight : List (ℕ × ℕ) → zB
  | [] => default
  | p :: R => rWord p +> encRight R

abbrev SegState := SegMode × List ℕ × List (ℕ × ℕ)

@[simp]
def modeOf (s : SegState) : SegMode := s.1

@[simp]
def ValidSeg (_ : SegState) : Prop := True

@[simp]
def leftList : SegMode → List ℕ → List ℕ
  | .mD0, L => 1 :: L
  | .mD1, L => 1 :: L
  | _, L => L

@[simp]
def segsL (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord ((leftList s.1 s.2.1).map zWord)]

@[simp]
def segsR (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.2.map rWord)]

lemma append_assoc_blank (a b : List (Fin 2)) (s : zB) :
    (a ++ b) +> s = a +> (b +> s) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

lemma evalSegRegion_zWord (L : List ℕ) :
    evalSegRegion (.finWord (L.map zWord)) +> (default : zB) = encLeft L := by
  induction L with
  | nil => simp [evalSegRegion, encLeft, listblank_append_nil]
  | cons k rest ih =>
    simp only [List.map_cons, evalSegRegion, encLeft, ← ih]
    exact append_assoc_blank (zWord k) (evalSegRegion (.finWord (rest.map zWord))) default

lemma evalSegRegion_rWord (R : List (ℕ × ℕ)) :
    evalSegRegion (.finWord (R.map rWord)) +> (default : zB) = encRight R := by
  induction R with
  | nil => simp [evalSegRegion, encRight, listblank_append_nil]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, encRight, ← ih]
    exact append_assoc_blank (rWord p) (evalSegRegion (.finWord (rest.map rWord))) default

@[simp]
lemma evalSegmentedHalf_segsL (m : SegMode) (L : List ℕ) (R : List (ℕ × ℕ)) :
    evalSegmentedHalf (segsL (m, L, R)) = encLeft (leftList m L) :=
  evalSegRegion_zWord (leftList m L)

@[simp]
lemma evalSegmentedHalf_segsR (m : SegMode) (L : List ℕ) (R : List (ℕ × ℕ)) :
    evalSegmentedHalf (segsR (m, L, R)) = encRight R :=
  evalSegRegion_rWord R

lemma oRun_nth_one (o : ℕ) (t : zB) : (oRun o +> t).nth 1 = 1 := by
  cases o with
  | zero =>
    simp only [oRun, ListBlank.append, WordRunStack.nth_cons_succ, WordRunStack.nth_cons_zero]
  | succ o =>
    cases o <;>
      simp only [oRun, ListBlank.append, WordRunStack.nth_cons_succ, WordRunStack.nth_cons_zero]

lemma noFactor_010_oRun (o : ℕ) (t : zB) (ht : WordRunStack.NoFactor [0, 1, 0] t) :
    WordRunStack.NoFactor [0, 1, 0] (oRun o +> t) := by
  induction o with
  | zero =>
    simp only [oRun, ListBlank.append]
    have h1 := WordRunStack.noFactor_cons_of_nth_ne [0, 1, 0] (1 : Fin 2) t ht 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 1, 0] (1 : Fin 2) _ h1 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)
  | succ o ih =>
    simp only [oRun, ListBlank.append]
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 1, 0] (1 : Fin 2) _ ih 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)

lemma noFactor_010_rWord (z o : ℕ) (t : zB) (ht : WordRunStack.NoFactor [0, 1, 0] t) :
    WordRunStack.NoFactor [0, 1, 0] (rWord (z, o) +> t) := by
  induction z with
  | zero =>
    simp only [rWord]
    exact noFactor_010_oRun o t ht
  | succ z ih =>
    cases z with
    | zero =>
      simp only [rWord, ListBlank.append] at ih ⊢
      refine WordRunStack.noFactor_cons_of_nth_ne [0, 1, 0] (0 : Fin 2) _ ih 2 (by decide) ?_
      rw [WordRunStack.nth_cons_succ, oRun_nth_one]
      decide
    | succ z =>
      simp only [rWord, ListBlank.append] at ih ⊢
      refine WordRunStack.noFactor_cons_of_nth_ne [0, 1, 0] (0 : Fin 2) _ ih 1 (by decide) ?_
      simp only [WordRunStack.nth_cons_succ, WordRunStack.nth_cons_zero]
      decide

lemma noFactor_010_encRight :
    ∀ R : List (ℕ × ℕ), WordRunStack.NoFactor [0, 1, 0] (encRight R)
  | [] => WordRunStack.noFactor_default [0, 1, 0] 1 (by decide) (by decide)
  | (z, o) :: R => noFactor_010_rWord z o _ (noFactor_010_encRight R)

lemma segsR_nowhere_dense : IsNowhereDenseHalf ValidSeg segsR :=
  WordRunStack.isNowhereDenseHalf_of_noFactor ValidSeg segsR [0, 1, 0]
    (fun ⟨_, _, R⟩ _ => by rw [evalSegmentedHalf_segsR]; exact noFactor_010_encRight R)

lemma segs_len_le_three (s : SegState) (_ : ValidSeg s) :
    (segsL s).length ≤ 3 ∧ (segsR s).length ≤ 3 := by
  simp [segsL, segsR]

@[simp]
def evalSegCfg : SegMode → List ℕ → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .mAL, L, R => (applyView (.id []) (encLeft L)) <{{0}} (applyView (.id []) (encRight R))
  | .mB0, L, R => (applyView (.id []) (encLeft L)) {{1}}> (applyView (.id []) (encRight R))
  | .mD0, L, R => (applyView (.id []) (encLeft (1 :: L))) {{3}}> (applyView (.id []) (encRight R))
  | .mD1, L, R => (applyView (.id []) (encLeft (1 :: L))) {{3}}> (applyView (.id [1]) (encRight R))
  | .mCL, L, R => (applyView (.id []) (encLeft L)) <{{2}} (applyView (.id [1, 1]) (encRight R))
  | .mCL1, L, R => (applyView (.id []) (encLeft L)) <{{2}} (applyView (.id [1]) (encRight R))

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
  | mAL =>
    refine ⟨0, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)
  | mB0 =>
    refine ⟨1, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mD0 =>
    refine ⟨3, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mD1 =>
    refine ⟨3, .id [], .id [1], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mCL =>
    refine ⟨2, .id [], .id [1, 1], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)
  | mCL1 =>
    refine ⟨2, .id [], .id [1], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)

lemma segsL_boundary_aligned :
    ∀ s : SegState, ValidSeg s → ∃ q vR,
      (evalCfg s = ⟨some q, ⟨0, evalSegmentedHalf (segsL s), vR⟩⟩) ∨
      (evalCfg s = (evalSegmentedHalf (segsL s)) <{{q}} vR) ∨
      (evalCfg s = (evalSegmentedHalf (segsL s)) {{q}}> vR) := by
  rintro ⟨m, L, R⟩ _
  rw [evalSegmentedHalf_segsL]
  cases m with
  | mAL => exact ⟨0, applyView (.id []) (encRight R), Or.inr (Or.inl rfl)⟩
  | mB0 => exact ⟨1, applyView (.id []) (encRight R), Or.inr (Or.inr rfl)⟩
  | mD0 => exact ⟨3, applyView (.id []) (encRight R), Or.inr (Or.inr rfl)⟩
  | mD1 => exact ⟨3, applyView (.id [1]) (encRight R), Or.inr (Or.inr rfl)⟩
  | mCL => exact ⟨2, applyView (.id [1, 1]) (encRight R), Or.inr (Or.inl rfl)⟩
  | mCL1 => exact ⟨2, applyView (.id [1]) (encRight R), Or.inr (Or.inl rfl)⟩

@[simp]
def push0L : List ℕ → List ℕ
  | [] => []
  | k :: L => (k + 1) :: L

@[simp]
def push0IterL : ℕ → List ℕ → List ℕ
  | 0, L => L
  | n + 1, L => push0IterL n (push0L L)

@[simp]
def push0R : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (z, o) :: R => (z + 1, o) :: R

@[simp]
def cfgHalt (L : List ℕ) (o : ℕ) (R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (1 : Fin 2) >> encLeft L) {{5}}> (oRun o +> encRight R)

@[simp]
def s₀ : SegState := (.mB0, [0], [])

lemma init_reaches_segmented_system :
    (init []) [target_tm]⊢⁺ evalSegCfg .mB0 [0] [] := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

lemma step_mAL_nil (R : List (ℕ × ℕ)) :
    (evalSegCfg .mAL [] R) [target_tm]⊢⁺ evalSegCfg .mB0 [0] R := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mAL_0 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mAL (0 :: L) R) [target_tm]⊢⁺ evalSegCfg .mAL L (push0R R) := by
  rcases R with _ | ⟨⟨z, o⟩, R⟩ <;> (
    simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, push0R,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]; execute)

lemma step_mAL_succ (k : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mAL ((k + 1) :: L) R) [target_tm]⊢⁺ evalSegCfg .mB0 (0 :: k :: L) R := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mB0_nil (L : List ℕ) :
    (evalSegCfg .mB0 L []) [target_tm]⊢⁺ evalSegCfg .mCL L [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mB0_0_base (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mB0 L ((0, 0) :: R)) [target_tm]⊢⁺
      evalSegCfg .mB0 (push0L (push0L L)) R := by
  cases L <;> (
    simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun, push0L,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]; execute)

lemma step_mB0_0_step (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mB0 L ((0, o + 1) :: R)) [target_tm]⊢⁺
      evalSegCfg .mB0 (push0L L) ((0, o) :: R) := by
  cases L <;> (
    simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun, push0L,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]; execute)

lemma step_mB0_0_sweep (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mB0 L ((0, o) :: R)) [target_tm]⊢⁺
      evalSegCfg .mB0 (push0IterL (o + 2) L) R := by
  induction o generalizing L with
  | zero =>
    simp only [push0IterL]
    exact step_mB0_0_base L R
  | succ o ih =>
    simp only [Nat.succ_add, push0IterL]
    exact stepPlus_trans (step_mB0_0_step o L R) (ih (push0L L))

lemma step_mB0_1 (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mB0 L ((1, o) :: R)) [target_tm]⊢⁺
      evalSegCfg .mB0 (0 :: L) ((0, o) :: R) := by
  cases o <;> (
    simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail]; execute)

lemma step_mB0_succ2 (z o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mB0 L ((z + 2, o) :: R)) [target_tm]⊢⁺
      evalSegCfg .mCL L ((z, o) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL_nil (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL [] R) [target_tm]⊢⁺ evalSegCfg .mCL [] ((0, 0) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL_0 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL (0 :: L) R) [target_tm]⊢⁺ evalSegCfg .mAL L ((0, 1) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL_1 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL (1 :: L) R) [target_tm]⊢⁺ evalSegCfg .mD0 L ((0, 0) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL_succ2 (k : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL ((k + 2) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL (k :: L) ((0, 0) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL1_nil (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL1 [] R) [target_tm]⊢⁺ evalSegCfg .mCL1 [] ((0, 0) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL1_0 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL1 (0 :: L) R) [target_tm]⊢⁺ evalSegCfg .mAL L ((0, 0) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL1_1 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL1 (1 :: L) R) [target_tm]⊢⁺ evalSegCfg .mD1 L R := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mCL1_succ2 (k : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mCL1 ((k + 2) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL1 (k :: L) ((0, 0) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD0_nil (L : List ℕ) :
    (evalSegCfg .mD0 L []) [target_tm]⊢⁺ evalSegCfg .mCL1 (1 :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft, encRight,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD0_00 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD0 L ((0, 0) :: R)) [target_tm]⊢⁺ evalSegCfg .mD0 (1 :: L) R := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD0_01 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD0 L ((0, 1) :: R)) [target_tm]⊢⁺ evalSegCfg .mD1 (1 :: L) R := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD0_0_succ2 (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD0 L ((0, o + 2) :: R)) [target_tm]⊢⁺
      evalSegCfg .mD0 (1 :: L) ((0, o) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD0_succ (z o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD0 L ((z + 1, o) :: R)) [target_tm]⊢⁺
      evalSegCfg .mCL1 (1 :: L) ((z, o) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD1_nil (L : List ℕ) :
    (evalSegCfg .mD1 L []) [target_tm]⊢⁺ evalSegCfg .mAL L [(1, 2)] := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD1_00 (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD1 L ((0, 0) :: R)) [target_tm]⊢⁺ evalSegCfg .mD1 (1 :: L) R := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD1_0_succ (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD1 L ((0, o + 1) :: R)) [target_tm]⊢⁺
      evalSegCfg .mD0 (1 :: L) ((0, o) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_mD1_1_to_halt (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD1 L ((1, o) :: R)) [target_tm]⊢⁺ cfgHalt (1 :: L) o R := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft, encRight, zWord, rWord,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

lemma step_cfgHalt_isNone (o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (step target_tm (cfgHalt L o R)).isNone := by
  cases o <;> simp [cfgHalt, oRun, ListBlank.append, Turing.ListBlank.head_cons, step, target_tm]

lemma step_mD1_succ2 (z o : ℕ) (L : List ℕ) (R : List (ℕ × ℕ)) :
    (evalSegCfg .mD1 L ((z + 2, o) :: R)) [target_tm]⊢⁺
      evalSegCfg .mAL L ((1, 2) :: (z, o) :: R) := by
  simp only [evalSegCfg, applyView, encLeft, encRight, zWord, rWord, oRun,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]; execute

theorem segmented_step_sound (m : SegMode) (L : List ℕ) (R : List (ℕ × ℕ)) :
    ∃ cfg', ((evalSegCfg m L R) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) := by
  cases m with
  | mAL =>
    rcases L with _ | ⟨_ | k, L⟩
    · exact ⟨evalCfg (.mB0, [0], R), step_mAL_nil R, Or.inl ⟨(.mB0, [0], R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mAL, L, push0R R), step_mAL_0 L R,
        Or.inl ⟨(.mAL, L, push0R R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mB0, 0 :: k :: L, R), step_mAL_succ k L R,
        Or.inl ⟨(.mB0, 0 :: k :: L, R), trivial, rfl⟩⟩
  | mB0 =>
    rcases R with _ | ⟨⟨_ | _ | z, o⟩, R⟩
    · exact ⟨evalCfg (.mCL, L, []), step_mB0_nil L, Or.inl ⟨(.mCL, L, []), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mB0, push0IterL (o + 2) L, R), step_mB0_0_sweep o L R,
        Or.inl ⟨(.mB0, push0IterL (o + 2) L, R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mB0, 0 :: L, (0, o) :: R), step_mB0_1 o L R,
        Or.inl ⟨(.mB0, 0 :: L, (0, o) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL, L, (z, o) :: R), step_mB0_succ2 z o L R,
        Or.inl ⟨(.mCL, L, (z, o) :: R), trivial, rfl⟩⟩
  | mCL =>
    rcases L with _ | ⟨_ | _ | k, L⟩
    · exact ⟨evalCfg (.mCL, [], (0, 0) :: R), step_mCL_nil R,
        Or.inl ⟨(.mCL, [], (0, 0) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mAL, L, (0, 1) :: R), step_mCL_0 L R,
        Or.inl ⟨(.mAL, L, (0, 1) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mD0, L, (0, 0) :: R), step_mCL_1 L R,
        Or.inl ⟨(.mD0, L, (0, 0) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL, k :: L, (0, 0) :: R), step_mCL_succ2 k L R,
        Or.inl ⟨(.mCL, k :: L, (0, 0) :: R), trivial, rfl⟩⟩
  | mCL1 =>
    rcases L with _ | ⟨_ | _ | k, L⟩
    · exact ⟨evalCfg (.mCL1, [], (0, 0) :: R), step_mCL1_nil R,
        Or.inl ⟨(.mCL1, [], (0, 0) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mAL, L, (0, 0) :: R), step_mCL1_0 L R,
        Or.inl ⟨(.mAL, L, (0, 0) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mD1, L, R), step_mCL1_1 L R,
        Or.inl ⟨(.mD1, L, R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL1, k :: L, (0, 0) :: R), step_mCL1_succ2 k L R,
        Or.inl ⟨(.mCL1, k :: L, (0, 0) :: R), trivial, rfl⟩⟩
  | mD0 =>
    rcases R with _ | ⟨⟨_ | z, o⟩, R⟩
    · exact ⟨evalCfg (.mCL1, 1 :: L, []), step_mD0_nil L,
        Or.inl ⟨(.mCL1, 1 :: L, []), trivial, rfl⟩⟩
    · rcases o with _ | _ | o
      · exact ⟨evalCfg (.mD0, 1 :: L, R), step_mD0_00 L R,
          Or.inl ⟨(.mD0, 1 :: L, R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mD1, 1 :: L, R), step_mD0_01 L R,
          Or.inl ⟨(.mD1, 1 :: L, R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mD0, 1 :: L, (0, o) :: R), step_mD0_0_succ2 o L R,
          Or.inl ⟨(.mD0, 1 :: L, (0, o) :: R), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mCL1, 1 :: L, (z, o) :: R), step_mD0_succ z o L R,
        Or.inl ⟨(.mCL1, 1 :: L, (z, o) :: R), trivial, rfl⟩⟩
  | mD1 =>
    rcases R with _ | ⟨⟨_ | _ | z, o⟩, R⟩
    · exact ⟨evalCfg (.mAL, L, [(1, 2)]), step_mD1_nil L,
        Or.inl ⟨(.mAL, L, [(1, 2)]), trivial, rfl⟩⟩
    · rcases o with _ | o
      · exact ⟨evalCfg (.mD1, 1 :: L, R), step_mD1_00 L R,
          Or.inl ⟨(.mD1, 1 :: L, R), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mD0, 1 :: L, (0, o) :: R), step_mD1_0_succ o L R,
          Or.inl ⟨(.mD0, 1 :: L, (0, o) :: R), trivial, rfl⟩⟩
    · exact ⟨cfgHalt (1 :: L) o R, step_mD1_1_to_halt o L R,
        Or.inr (step_cfgHalt_isNone o (1 :: L) R)⟩
    · exact ⟨evalCfg (.mAL, L, (1, 2) :: (z, o) :: R), step_mD1_succ2 z o L R,
        Or.inl ⟨(.mAL, L, (1, 2) :: (z, o) :: R), trivial, rfl⟩⟩

theorem segmented_system_closed (s : SegState) (_ : ValidSeg s) :
    ∃ cfg', ((evalCfg s) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) :=
  segmented_step_sound s.1 s.2.1 s.2.2

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_segmented_cryptid : IsSegmentedCryptid target_tm := by
  exact ⟨SegState, SegMode, ValidSeg, modeOf, segsL, segsR, evalCfg,
    ⟨[.mAL, .mB0, .mD0, .mD1, .mCL, .mCL1], by decide, by decide, fun m => by cases m <;> simp⟩,
    segs_len_le_three,
    valid_seg_modes,
    Or.inr segsR_nowhere_dense,
    Or.inr segsL_boundary_aligned,
    Or.inl segsR_nowhere_dense,
    ⟨s₀, trivial, init_reaches_segmented_system⟩,
    segmented_system_closed⟩

end BusyBeaver.M_1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LAHHH
