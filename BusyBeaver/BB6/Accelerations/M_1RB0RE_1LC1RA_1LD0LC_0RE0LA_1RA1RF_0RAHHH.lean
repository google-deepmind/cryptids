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

/-!
# Busy Beaver Machine `1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---` (`IsSegmentedCryptid`)

Formal `IsClosedSegmentedSystem` and `IsSegmentedCryptid` proofs for
`1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---` (`target`).
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RAHHH

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => none

private theorem target_eq_target_tm : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl

local notation "zB" => ListBlank (Fin 2)

open Counter

local macro "finish" : tactic => `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus
      (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
      zero_cons_default, default_head, default_tail])
local macro "step1" : tactic => `(tactic| try (any_goals (first | finish | gstep)))
local macro "execute" : tactic =>
  `(tactic| (step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1))

/-- Three head modes of Holdout `#533` (`1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`). -/
inductive SegMode where
  | mCL
  | mAR
  | mA0
deriving DecidableEq, Repr

/-- Left half-tape word `1^(d+1) ++ [0]` (`b = false`) or `1^(2d+1) ++ [0, 0]` (`b = true`),
forbidding `[0, 0, 0, 1]`. -/
def lWord (p : ℕ × Bool) : List (Fin 2) :=
  Bool.casesOn p.2
    (Nat.rec [1, 0] (fun _ acc => 1 :: acc) p.1)
    (Nat.rec [1, 0, 0] (fun _ acc => 1 :: 1 :: acc) p.1)

@[simp] private theorem lWord_zero_false : lWord (0, false) = [1, 0] := rfl
@[simp] private theorem lWord_succ_false (d : ℕ) :
    lWord (d + 1, false) = 1 :: lWord (d, false) := rfl
@[simp] private theorem lWord_zero_true : lWord (0, true) = [1, 0, 0] := rfl
@[simp] private theorem lWord_succ_true (k : ℕ) :
    lWord (k + 1, true) = 1 :: 1 :: lWord (k, true) := rfl

/-- Right half-tape parameterized zero-run word `0^z ++ [1]`. -/
def zWord (k : ℕ) : List (Fin 2) :=
  Nat.rec [1] (fun _ acc => 0 :: acc) k

@[simp] private theorem zWord_zero : zWord 0 = [1] := rfl
@[simp] private theorem zWord_succ (k : ℕ) : zWord (k + 1) = 0 :: zWord k := rfl

def encLeft (S : List (ℕ × Bool)) : zB :=
  List.rec default (fun p _ acc => lWord p +> acc) S

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl
@[simp] private theorem encLeft_cons (p : (ℕ × Bool)) (S : List (ℕ × Bool)) :
    encLeft (p :: S) = lWord p +> encLeft S := rfl

def encRight (S : List ℕ) : zB :=
  List.rec default (fun z _ acc => zWord z +> acc) S

@[simp] private theorem encRight_nil : encRight [] = default := rfl
@[simp] private theorem encRight_cons (z : ℕ) (S : List ℕ) :
    encRight (z :: S) = zWord z +> encRight S := rfl

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

private theorem append_assoc_blank (a b : List (Fin 2)) (s : zB) :
    (a ++ b) +> s = a +> (b +> s) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

private theorem evalSegRegion_lWord (L : List (ℕ × Bool)) :
    evalSegRegion (.finWord (L.map lWord)) +> (default : zB) = encLeft L := by
  induction L with
  | nil => simp [evalSegRegion, encLeft_nil]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, encLeft_cons, ← ih]
    exact append_assoc_blank (lWord p) (evalSegRegion (.finWord (rest.map lWord))) default

private theorem evalSegRegion_zWord (R : List ℕ) :
    evalSegRegion (.finWord (R.map zWord)) +> (default : zB) = encRight R := by
  induction R with
  | nil => simp [evalSegRegion, encRight_nil]
  | cons z rest ih =>
    simp only [List.map_cons, evalSegRegion, encRight_cons, ← ih]
    exact append_assoc_blank (zWord z) (evalSegRegion (.finWord (rest.map zWord))) default

@[simp]
private theorem evalSegmentedHalf_segsL (m : SegMode) (L : List (ℕ × Bool)) (R : List ℕ) :
    evalSegmentedHalf (segsL (m, L, R)) = encLeft L :=
  evalSegRegion_lWord L

@[simp]
private theorem evalSegmentedHalf_segsR (m : SegMode) (L : List (ℕ × Bool)) (R : List ℕ) :
    evalSegmentedHalf (segsR (m, L, R)) = encRight R :=
  evalSegRegion_zWord R

private theorem encLeft_nth_zero (p : ℕ × Bool) (L : List (ℕ × Bool)) :
    (encLeft (p :: L)).nth 0 = 1 := by
  rcases p with ⟨_ | d, _ | _⟩ <;>
    simp only [encLeft_cons, lWord_zero_false, lWord_succ_false, lWord_zero_true,
      lWord_succ_true, ListBlank.append, WordRunStack.nth_cons_zero]

private theorem noFactor_0001_lWord_nil (d : ℕ) (b : Bool) :
    WordRunStack.NoFactor [0, 0, 0, 1] (lWord (d, b) +> (default : zB)) := by
  have hd : WordRunStack.NoFactor [0, 0, 0, 1] (default : zB) :=
    WordRunStack.noFactor_default [0, 0, 0, 1] 3 (by decide) (by decide)
  induction d with
  | zero =>
    cases b <;> (
      simp only [lWord_zero_false, lWord_zero_true,
        ListBlank.append, zero_cons_default]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) default hd 0
        (by decide) (by rw [WordRunStack.nth_cons_zero]; decide))
  | succ d ih =>
    cases b with
    | false =>
      simp only [lWord_succ_false,
        ListBlank.append]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [lWord_succ_true,
        ListBlank.append]
      have h1 : WordRunStack.NoFactor [0, 0, 0, 1] ((1 : Fin 2) >> (lWord (d, true) +> default)) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
          (by rw [WordRunStack.nth_cons_zero]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h1 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)

private theorem noFactor_0001_lWord_cons (d : ℕ) (b : Bool) (t : zB) (ht0 : t.nth 0 = 1)
    (ht : WordRunStack.NoFactor [0, 0, 0, 1] t) :
    WordRunStack.NoFactor [0, 0, 0, 1] (lWord (d, b) +> t) := by
  induction d with
  | zero =>
    cases b with
    | false =>
      simp only [lWord_zero_false,
        ListBlank.append]
      have h0 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) t ht 1 (by decide)
          (by rw [WordRunStack.nth_cons_succ, ht0]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h0 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [lWord_zero_true,
        ListBlank.append]
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
      simp only [lWord_succ_false,
        ListBlank.append]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [lWord_succ_true,
        ListBlank.append]
      have h1 : WordRunStack.NoFactor [0, 0, 0, 1] ((1 : Fin 2) >> (lWord (d, true) +> t)) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
          (by rw [WordRunStack.nth_cons_zero]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h1 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)

private theorem noFactor_0001_encLeft :
    ∀ L : List (ℕ × Bool), WordRunStack.NoFactor [0, 0, 0, 1] (encLeft L)
  | [] => WordRunStack.noFactor_default [0, 0, 0, 1] 3 (by decide) (by decide)
  | [(d, b)] => noFactor_0001_lWord_nil d b
  | (d, b) :: p :: L =>
    noFactor_0001_lWord_cons d b (encLeft (p :: L)) (encLeft_nth_zero p L)
      (noFactor_0001_encLeft (p :: L))

theorem segsL_nowhere_dense : IsNowhereDenseHalf ValidSeg segsL :=
  WordRunStack.isNowhereDenseHalf_of_noFactor ValidSeg segsL [0, 0, 0, 1]
    (fun ⟨_, L, _⟩ _ => by rw [evalSegmentedHalf_segsL]; exact noFactor_0001_encLeft L)

/-- Canonical mode enumeration for `1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`. -/
def modes : List SegMode := [.mCL, .mAR, .mA0]

private theorem zWord_ne_nil (k : ℕ) : zWord k ≠ [] := by
  cases k <;> simp [zWord_zero, zWord_succ]

private theorem zWord_ne_zero : ∀ k : ℕ, zWord k ≠ [(0 : Fin 2)]
  | 0 => by simp [zWord_zero]
  | n + 1 => fun h => by
      dsimp only [zWord_zero, zWord_succ] at h
      exact zWord_ne_nil n (List.cons.inj h).2

private theorem lWord_len : ∀ p : ℕ × Bool, 2 ≤ (lWord p).length
  | (0, false) => by simp [lWord_zero_false]
  | (d + 1, false) => by have := lWord_len (d, false); simp only [
    lWord_succ_false, List.length_cons]; omega
  | (0, true) => by simp [lWord_zero_true]
  | (k + 1, true) => by have := lWord_len (k, true); simp only [
   lWord_succ_true, List.length_cons]; omega

private theorem lWord_ne_nil (p : ℕ × Bool) : lWord p ≠ [] := by
  intro h; have := lWord_len p; simp [h] at this

private theorem lWord_ne_zero (p : ℕ × Bool) : lWord p ≠ [(0 : Fin 2)] := by
  intro h; have := lWord_len p; simp [h] at this

private theorem segs_wf (s : SegState) (_ : ValidSeg s) :
    (segsL s).length ≤ 3 ∧ (segsR s).length ≤ 3 ∧
    (∀ r ∈ segsL s, r.WellFormed) ∧ (∀ r ∈ segsR s, r.WellFormed) := by
  refine ⟨by simp [segsL], by simp [segsR], ?_, ?_⟩
  · simp only [segsL, List.mem_singleton]
    rintro _ rfl
    refine ⟨?_, ?_⟩
    · rintro _ hw
      rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
      exact lWord_ne_nil x
    · intro h
      rcases List.mem_map.mp (h 0) with ⟨x, _, hx⟩
      exact lWord_ne_zero x hx
  · simp only [segsR, List.mem_singleton]
    rintro _ rfl
    refine ⟨?_, ?_⟩
    · rintro _ hw
      rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
      exact zWord_ne_nil x
    · intro h
      rcases List.mem_map.mp (h 0) with ⟨x, _, hx⟩
      exact zWord_ne_zero x hx

@[simp]
def evalSegCfg : SegMode → List (ℕ × Bool) → List ℕ → Cfg (Fin 2) (Fin 6)
  | .mCL, L, R => (applyView (.id []) (encLeft L)) <{{2}} (applyView (.id []) (encRight R))
  | .mAR, L, R => (applyView (.id []) (encLeft L)) {{0}}> (applyView (.id []) (encRight R))
  | .mA0, L, R => (applyView (.id [0]) (encLeft L)) {{0}}> (applyView (.id []) (encRight R))

@[simp]
def evalCfg (s : SegState) : Cfg (Fin 2) (Fin 6) :=
  evalSegCfg s.1 s.2.1 s.2.2

theorem valid_seg_modes :
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
    refine ⟨2, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)
  | mAR =>
    refine ⟨0, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mA0 =>
    refine ⟨0, .id [0], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)

theorem segsR_boundary_aligned :
    ∀ s : SegState, ValidSeg s → ∃ q vL,
      (evalCfg s = ⟨some q, ⟨0, vL, evalSegmentedHalf (segsR s)⟩⟩) ∨
      (evalCfg s = vL <{{q}} (evalSegmentedHalf (segsR s))) ∨
      (evalCfg s = vL {{q}}> (evalSegmentedHalf (segsR s))) := by
  rintro ⟨m, L, R⟩ _
  rw [evalSegmentedHalf_segsR]
  cases m with
  | mCL => exact ⟨2, applyView (.id []) (encLeft L), Or.inr (Or.inl rfl)⟩
  | mAR => exact ⟨0, applyView (.id []) (encLeft L), Or.inr (Or.inr rfl)⟩
  | mA0 => exact ⟨0, applyView (.id [0]) (encLeft L), Or.inr (Or.inr rfl)⟩

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
def s₀ : SegState := (.mCL, [(0, false)], [0])

private theorem zero_cons_encRight (R : List ℕ) :
    (0 : Fin 2) >> encRight R = encRight (push0R R) := by
  cases R <;> simp [push0R, encRight_nil, encRight_cons, zWord_succ]

private theorem pat11_cons_encLeft (L : List (ℕ × Bool)) :
    (1 : Fin 2) >> (1 : Fin 2) >> encLeft L = encLeft (bump2L L) := by
  rcases L with _ | ⟨⟨_ | d, _ | _⟩, L⟩ <;>
    simp [bump2L, encLeft_nil, encLeft_cons, lWord_zero_false, lWord_succ_false, lWord_zero_true,
      lWord_succ_true, ListBlank.append]

private theorem init_reaches_segmented_system :
    (init []) [target_tm]⊢⁺ evalSegCfg .mCL [(0, false)] [0] := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]
  simp only [evalSegCfg, applyView, encLeft_nil, encLeft_cons, encRight_nil, encRight_cons,
    lWord_zero_false, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

private theorem step_cfgHalt_isNone (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (step target_tm (cfgHalt L Rt)).isNone := by
  simp [cfgHalt, encRight_cons, zWord_zero, ListBlank.append,
    Turing.ListBlank.head_cons, step, target_tm]

-- Mode mCL (<2) transitions
private theorem step_mCL_nil_nil :
    (evalSegCfg .mCL [] []) [target_tm]⊢⁺ evalSegCfg .mA0 [(0, false)] [] := by
  simp only [evalSegCfg, applyView, encLeft_nil, encLeft_cons, encRight_nil, 
    lWord_zero_false, 
    ListBlank.append,
    zero_cons_default, default_head, default_tail]
  execute

private theorem step_mCL_nil_0_halt (Rt : List ℕ) :
    (evalSegCfg .mCL [] (0 :: Rt)) [target_tm]⊢⁺ cfgHalt [(0, false)] Rt := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft_nil, encLeft_cons, 
    encRight_cons, lWord_zero_false, 
      zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

private theorem step_mCL_nil_succ (z : ℕ) (Rt : List ℕ) :
    (evalSegCfg .mCL [] ((z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0 [(0, false)] (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft_nil, encLeft_cons, encRight_cons,
    lWord_zero_false, zWord_succ,
    ListBlank.append,
    zero_cons_default, default_head, default_tail]
  execute

private theorem step_mCL_0_false_nil (R : List ℕ) :
    (evalSegCfg .mCL [(0, false)] R) [target_tm]⊢⁺ evalSegCfg .mA0 [(0, false)] R := by
  simp only [evalSegCfg, applyView, encLeft_nil, encLeft_cons, lWord_zero_false, 
   
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default]
  execute

private theorem step_mCL_0_false_0_false (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (0, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL L (1 :: 0 :: push0R R) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft_cons, encRight_cons,
    lWord_zero_false, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mCL_0_false_0_true (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (0, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL ((0, false) :: L) (0 :: 0 :: push0R R) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft_cons, encRight_cons,
    lWord_zero_false, lWord_zero_true, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mCL_0_false_1_false (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (1, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: (0, true) :: L) R := by
  simp only [evalSegCfg, applyView, encLeft_cons, lWord_zero_false, lWord_succ_false,
    lWord_zero_true, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mCL_0_false_succ2_false (d : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (d + 2, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: (0, false) :: (d, false) :: L) R := by
  cases d <;> (
    simp only [evalSegCfg, applyView, encLeft_cons, lWord_zero_false,
      lWord_succ_false, 
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    execute)

private theorem step_mCL_0_false_succ_true (k : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, false) :: (k + 1, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: (0, false) :: (k, true) :: L) R := by
  cases k <;> (
    simp only [evalSegCfg, applyView, encLeft_cons, lWord_zero_false,
     lWord_zero_true, lWord_succ_true,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    execute)

private theorem step_mCL_0_true (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((0, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, false) :: L) R := by
  simp only [evalSegCfg, applyView, encLeft_cons, lWord_zero_false, 
    lWord_zero_true, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mCL_succ_false (d : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((d + 1, false) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL ((d, false) :: L) (push0R R) := by
  cases d <;> (
    simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft_cons,
      lWord_zero_false, lWord_succ_false, 
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    execute)

private theorem step_mCL_succ_true (k : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
    (evalSegCfg .mCL ((k + 1, true) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mCL ((k, true) :: L) (push0R (push0R R)) := by
  cases k <;> (
    simp only [evalSegCfg, applyView, ← zero_cons_encRight, encLeft_cons,
     lWord_zero_true, lWord_succ_true,
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    execute)

@[simp]
def push00IterR : ℕ → List ℕ → List ℕ
  | 0, R => R
  | k + 1, R => push00IterR k (push0R (push0R R))

private theorem step_mCL_true_sweep (k : ℕ) (L : List (ℕ × Bool)) (R : List ℕ) :
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
private theorem step_mAR_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mAR L []) [target_tm]⊢⁺ evalSegCfg .mCL L [1] := by
  simp only [evalSegCfg, applyView, encRight_nil, encRight_cons, zWord_zero, zWord_succ,
    ListBlank.append,
   default_head, default_tail]
  execute

private theorem step_mAR_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mAR L [0]) [target_tm]⊢⁺ evalSegCfg .mAR ((0, false) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_nil, encRight_cons,
    lWord_zero_false, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute

private theorem step_mAR_0_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mAR L [0, 0]) [target_tm]⊢⁺ evalSegCfg .mA0 ((0, false) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_nil, encRight_cons,
    lWord_zero_false, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute

private theorem step_mAR_0_0_0_halt (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (0 :: 0 :: 0 :: Rt)) [target_tm]⊢⁺
      cfgHalt ((0, false) :: L) Rt := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft_cons, 
    encRight_cons, lWord_zero_false, 
      zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAR_0_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (0 :: 0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, false) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_cons,
    lWord_zero_false, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAR_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, false) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_cons,
    lWord_zero_false, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAR_1_cons (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L (1 :: Rt)) [target_tm]⊢⁺ evalSegCfg .mAR (bump2L L) Rt := by
  simp only [evalSegCfg, applyView, ← pat11_cons_encLeft, encRight_cons, zWord_zero,
    zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAR_succ2 (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mAR L ((z + 2) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mCL L (1 :: z :: Rt) := by
  simp only [evalSegCfg, applyView, encRight_cons, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

-- Mode mA0 (0> with leading 0) transitions
private theorem step_mA0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mA0 L []) [target_tm]⊢⁺ evalSegCfg .mCL ((0, false) :: L) [0] := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_nil, encRight_cons,
    lWord_zero_false, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute

private theorem step_mA0_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mA0 L [0]) [target_tm]⊢⁺ evalSegCfg .mAR ((0, true) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_nil, encRight_cons,
   lWord_zero_true, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute

private theorem step_mA0_0_0_nil (L : List (ℕ × Bool)) :
    (evalSegCfg .mA0 L [0, 0]) [target_tm]⊢⁺ evalSegCfg .mA0 ((0, true) :: L) [] := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_nil, encRight_cons,
   lWord_zero_true, zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute

private theorem step_mA0_0_0_0_halt (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (0 :: 0 :: 0 :: Rt)) [target_tm]⊢⁺
      cfgHalt ((0, true) :: L) Rt := by
  simp only [evalSegCfg, cfgHalt, applyView, encLeft_cons, 
    encRight_cons, lWord_zero_true, 
      zWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mA0_0_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (0 :: 0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0 ((0, true) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_cons,
   lWord_zero_true, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mA0_0_succ (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (0 :: (z + 1) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mAR ((0, true) :: L) (z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_cons,
   lWord_zero_true, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mA0_1_cons (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L (1 :: Rt)) [target_tm]⊢⁺ evalSegCfg .mAR ((1, false) :: L) Rt := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_cons,
    lWord_zero_false, lWord_succ_false, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mA0_succ2 (z : ℕ) (L : List (ℕ × Bool)) (Rt : List ℕ) :
    (evalSegCfg .mA0 L ((z + 2) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mCL ((0, false) :: L) (0 :: z :: Rt) := by
  simp only [evalSegCfg, applyView, encLeft_cons, encRight_cons,
    lWord_zero_false, zWord_zero, zWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem segmented_step_sound (m : SegMode) (L : List (ℕ × Bool)) (R : List ℕ) :
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

private theorem segmented_system_closed (s : SegState) (_ : ValidSeg s) :
    ∃ cfg', ((evalCfg s) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) :=
  segmented_step_sound s.1 s.2.1 s.2.2

/-- Explicit `IsClosedSegmentedSystem` witness for `1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`. -/
theorem is_closed_segmented_system :
    IsClosedSegmentedSystem target modes ValidSeg modeOf segsL segsR evalCfg := by
  rw [target_eq_target_tm]
  exact ⟨by decide, by decide, fun m => by cases m <;> simp [modes],
    segs_wf, valid_seg_modes,
    Or.inl segsL_nowhere_dense,
    Or.inl segsL_nowhere_dense,
    Or.inr segsR_boundary_aligned,
    ⟨s₀, trivial, init_reaches_segmented_system⟩,
    segmented_system_closed⟩

/-- Segmented cryptid certificate for `1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`. -/
theorem is_segmented_cryptid : IsSegmentedCryptid target :=
  ⟨SegState, SegMode, modes, ValidSeg, modeOf, segsL, segsR, evalCfg, is_closed_segmented_system⟩

end BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RAHHH
