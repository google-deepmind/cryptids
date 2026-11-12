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
# Busy Beaver Machine `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` (`IsSegmentedCryptid`)

Formal `IsClosedSegmentedSystem` and `IsSegmentedCryptid` proofs for
`1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` (`target`).
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
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

inductive SegMode where
  | mAR
  | mA0R
  | mEL
deriving DecidableEq, Repr

def onesSep0 (d : ℕ) : List (Fin 2) :=
  Nat.rec [0] (fun _ acc => 1 :: acc) d

@[simp] private theorem onesSep0_zero : onesSep0 0 = [0] := rfl
@[simp] private theorem onesSep0_succ (d : ℕ) :
    onesSep0 (d + 1) = 1 :: onesSep0 d := rfl

@[simp]
def lWord (d : ℕ) : List (Fin 2) := 1 :: onesSep0 d

def encLeft (S : List ℕ) : zB :=
  List.rec default (fun d _ acc => lWord d +> acc) S

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl
@[simp] private theorem encLeft_cons (d : ℕ) (S : List ℕ) :
    encLeft (d :: S) = lWord d +> encLeft S := rfl

def rWord (z : ℕ) : List (Fin 2) :=
  Nat.rec [1] (fun _ acc => 0 :: acc) z

@[simp] private theorem rWord_zero : rWord 0 = [1] := rfl
@[simp] private theorem rWord_succ (z : ℕ) : rWord (z + 1) = 0 :: rWord z := rfl

def encRight (S : List ℕ) : zB :=
  List.rec default (fun z _ acc => rWord z +> acc) S

@[simp] private theorem encRight_nil : encRight [] = default := rfl
@[simp] private theorem encRight_cons (z : ℕ) (S : List ℕ) :
    encRight (z :: S) = rWord z +> encRight S := rfl

abbrev SegState := SegMode × List ℕ × List ℕ

@[simp]
def modeOf (s : SegState) : SegMode := s.1

@[simp]
def ValidSeg (_ : SegState) : Prop := True

@[simp]
def segsL (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.1.map lWord)]

@[simp]
def segsR (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.2.map rWord)]

private theorem append_assoc_blank (a b : List (Fin 2)) (s : zB) :
    (a ++ b) +> s = a +> (b +> s) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

private theorem evalSegRegion_lWord (L : List ℕ) :
    evalSegRegion (.finWord (L.map lWord)) +> (default : zB) = encLeft L := by
  induction L with
  | nil => simp [evalSegRegion, encLeft_nil]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, encLeft_cons, ← ih]
    exact append_assoc_blank (lWord p) (evalSegRegion (.finWord (rest.map lWord))) default

private theorem evalSegRegion_rWord (R : List ℕ) :
    evalSegRegion (.finWord (R.map rWord)) +> (default : zB) = encRight R := by
  induction R with
  | nil => simp [evalSegRegion, encRight_nil]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, encRight_cons, ← ih]
    exact append_assoc_blank (rWord p) (evalSegRegion (.finWord (rest.map rWord))) default

@[simp]
private theorem evalSegmentedHalf_segsL (m : SegMode) (L : List ℕ) (R : List ℕ) :
    evalSegmentedHalf (segsL (m, L, R)) = encLeft L :=
  evalSegRegion_lWord L

@[simp]
private theorem evalSegmentedHalf_segsR (m : SegMode) (L : List ℕ) (R : List ℕ) :
    evalSegmentedHalf (segsR (m, L, R)) = encRight R :=
  evalSegRegion_rWord R

private theorem enc_nth_zero (d : ℕ) (L : List ℕ) :
    (encLeft (d :: L)).nth 0 = 1 := by
  simp only [encLeft_cons, lWord, ListBlank.append, WordRunStack.nth_cons_zero]

private theorem noFactor_001_nil (d : ℕ) :
    WordRunStack.NoFactor [0, 0, 1] (lWord d +> (default : zB)) := by
  have hd : WordRunStack.NoFactor [0, 0, 1] (default : zB) :=
    WordRunStack.noFactor_default [0, 0, 1] 2 (by decide) (by decide)
  induction d with
  | zero =>
    simp only [lWord, onesSep0_zero, ListBlank.append, zero_cons_default]
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 1] (1 : Fin 2) default hd 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)
  | succ d ih =>
    change WordRunStack.NoFactor [0, 0, 1] ((1 : Fin 2) >> (lWord d +> default))
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)

private theorem noFactor_001_cons (d : ℕ) (t : zB) (ht0 : t.nth 0 = 1)
    (ht : WordRunStack.NoFactor [0, 0, 1] t) :
    WordRunStack.NoFactor [0, 0, 1] (lWord d +> t) := by
  induction d with
  | zero =>
    simp only [lWord, onesSep0_zero, ListBlank.append]
    have h0 : WordRunStack.NoFactor [0, 0, 1] ((0 : Fin 2) >> t) :=
      WordRunStack.noFactor_cons_of_nth_ne [0, 0, 1] (0 : Fin 2) t ht 1 (by decide)
        (by rw [WordRunStack.nth_cons_succ, ht0]; decide)
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 1] (1 : Fin 2) _ h0 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)
  | succ d ih =>
    change WordRunStack.NoFactor [0, 0, 1] ((1 : Fin 2) >> (lWord d +> t))
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)

private theorem noFactor_enc : ∀ L : List ℕ, WordRunStack.NoFactor [0, 0, 1] (encLeft L)
  | [] => WordRunStack.noFactor_default [0, 0, 1] 2 (by decide) (by decide)
  | [d] => noFactor_001_nil d
  | d :: d2 :: L =>
    noFactor_001_cons d (encLeft (d2 :: L)) (enc_nth_zero d2 L)
      (noFactor_enc (d2 :: L))

theorem segsL_nowhere_dense : IsNowhereDenseHalf ValidSeg segsL :=
  WordRunStack.isNowhereDenseHalf_of_noFactor ValidSeg segsL [0, 0, 1]
    (fun ⟨_, L, _⟩ _ => by rw [evalSegmentedHalf_segsL]; exact noFactor_enc L)

/-- Canonical mode enumeration for `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`. -/
def modes : List SegMode := [.mAR, .mA0R, .mEL]

private theorem rWord_ne_nil (k : ℕ) : rWord k ≠ [] := by
  cases k <;> simp [rWord_zero, rWord_succ]

private theorem rWord_ne_zero : ∀ k : ℕ, rWord k ≠ [(0 : Fin 2)]
  | 0 => by simp [rWord_zero]
  | n + 1 => fun h => by
      dsimp only [rWord_zero, rWord_succ] at h
      exact rWord_ne_nil n (List.cons.inj h).2

private theorem onesSep0_len (d : ℕ) : 1 ≤ (onesSep0 d).length := by
  induction d with
  | zero => decide
  | succ _ _ => simp only [onesSep0_succ, List.length_cons]; omega

private theorem lWord_len (d : ℕ) : 2 ≤ (lWord d).length := by
  have h := onesSep0_len d
  simp only [lWord, List.length_cons]
  omega

private theorem lWord_ne_nil (d : ℕ) : lWord d ≠ [] := by
  intro h; have hlen := lWord_len d; rw [h] at hlen; contradiction

private theorem lWord_ne_zero (d : ℕ) : lWord d ≠ [(0 : Fin 2)] := by
  intro h; have hlen := lWord_len d; rw [h] at hlen; simp at hlen

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
      exact rWord_ne_nil x
    · intro h
      rcases List.mem_map.mp (h 0) with ⟨x, _, hx⟩
      exact rWord_ne_zero x hx

@[simp]
def evalSegCfg : SegMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .mAR, L, R => (applyView (.id []) (encLeft L)) {{0}}> (applyView (.id []) (encRight R))
  | .mA0R, L, R => (applyView (.id [0]) (encLeft L)) {{0}}> (applyView (.id []) (encRight R))
  | .mEL, L, R => (applyView (.id []) (encLeft L)) <{{4}} (applyView (.id []) (encRight R))

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
  | mAR =>
    refine ⟨0, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mA0R =>
    refine ⟨0, .id [0], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mEL =>
    refine ⟨4, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, R⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)

theorem segsR_boundary_aligned :
    ∀ s : SegState, ValidSeg s → ∃ q vL,
      (evalCfg s = ⟨some q, ⟨0, vL, evalSegmentedHalf (segsR s)⟩⟩) ∨
      (evalCfg s = vL <{{q}} (evalSegmentedHalf (segsR s))) ∨
      (evalCfg s = vL {{q}}> (evalSegmentedHalf (segsR s))) := by
  rintro ⟨m, L, R⟩ _
  rw [evalSegmentedHalf_segsR]
  cases m with
  | mAR => exact ⟨0, applyView (.id []) (encLeft L), Or.inr (Or.inr rfl)⟩
  | mA0R => exact ⟨0, applyView (.id [0]) (encLeft L), Or.inr (Or.inr rfl)⟩
  | mEL => exact ⟨4, applyView (.id []) (encLeft L), Or.inr (Or.inl rfl)⟩

@[simp]
def bump1L : List ℕ → List ℕ
  | [] => [0]
  | d :: xs => (d + 1) :: xs

private theorem one_cons_encLeft (xs : List ℕ) :
    (1 : Fin 2) >> encLeft xs = encLeft (bump1L xs) := by
  cases xs <;> simp [bump1L, encLeft_nil, encLeft_cons, lWord, onesSep0_zero, onesSep0_succ,
    ListBlank.append]
@[simp]
def push0R : List ℕ → List ℕ
  | [] => []
  | z :: xs => (z + 1) :: xs

private theorem zero_cons_encRight (xs : List ℕ) :
    (0 : Fin 2) >> encRight xs = encRight (push0R xs) := by
  cases xs <;> simp [push0R, encRight_nil, encRight_cons, rWord_succ]

@[simp]
def s₀ : SegState := (.mAR, (0 :: []), (1 :: []))

private theorem init_reaches_segmented_system :
    (init []) [target_tm]⊢⁺ evalSegCfg .mAR (0 :: []) (1 :: []) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]
  simp only [evalSegCfg, applyView, encLeft_nil, encLeft_cons, encRight_nil, encRight_cons, lWord,
    rWord_zero, rWord_succ, onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute

private theorem stepOut_trans {c1 c2 : Cfg (Fin 2) (Fin 6)}
    (h1 : c1 [target_tm]⊢⁺ c2)
    (h2 : ∃ cfg', (c2 [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone)) :
    ∃ cfg', (c1 [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) := by
  rcases h2 with ⟨cfg', h2p, hend⟩
  exact ⟨cfg', stepPlus_trans h1 h2p, hend⟩

private theorem step_mAR_2_loop (L : List ℕ) (Rt : List ℕ) :
    (evalSegCfg .mAR L (2 :: Rt)) [target_tm]⊢⁺ evalSegCfg .mAR (0 :: bump1L L) Rt := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft,
   encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_1 (L : List ℕ) :
    (evalSegCfg .mAR L []) [target_tm]⊢⁺
      evalSegCfg .mAR (bump1L L) (1 :: []) := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft,
   encRight_nil, encRight_cons, rWord_zero, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute
private theorem step_mAR_2 (Rt : List ℕ) :
    (evalSegCfg .mAR [] (0 :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mEL [] (0 :: (push0R Rt)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
    encLeft_nil, encRight_cons, rWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute
private theorem step_mAR_3 (lt2 : List ℕ) (Rt : List ℕ) :
    (evalSegCfg .mAR (0 :: lt2) (0 :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mA0R (bump1L lt2) (push0R Rt) := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_4 (lt2 : List ℕ) (Rt : List ℕ) :
    (evalSegCfg .mAR (1 :: lt2) (0 :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mEL (0 :: lt2) (push0R (push0R Rt)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, 
      onesSep0_zero, onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_5 (l3 : ℕ) (lt2 : List ℕ) (Rt : List ℕ) :
    (evalSegCfg .mAR ((l3 + 2) :: lt2) (0 :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mEL ((l3 + 1) :: lt2) (push0R (push0R Rt)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, 
     onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_6 (L : List ℕ) :
    (evalSegCfg .mAR L (1 :: [])) [target_tm]⊢⁺
      evalSegCfg .mEL (bump1L (bump1L L)) (0 :: []) := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft,
   encRight_nil, encRight_cons, rWord_zero, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_7 (L : List ℕ) (rt3 : List ℕ) :
    (evalSegCfg .mAR L (1 :: (0 :: rt3))) [target_tm]⊢⁺
      evalSegCfg .mEL (bump1L (bump1L L)) (push0R rt3) := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft, ← zero_cons_encRight,
  encRight_cons, rWord_zero, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_8 (L : List ℕ) (r3 : ℕ) (rt3 : List ℕ) :
    (evalSegCfg .mAR L (1 :: ((r3 + 1) :: rt3))) [target_tm]⊢⁺
      evalSegCfg .mEL (bump1L (bump1L L)) (0 :: (r3 :: rt3)) := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft, 
  encRight_cons, rWord_zero, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mAR_9 (L : List ℕ) (r3 : ℕ) (Rt : List ℕ) :
    (evalSegCfg .mAR L ((r3 + 3) :: Rt)) [target_tm]⊢⁺
      evalSegCfg .mAR (bump1L L) (1 :: (r3 :: Rt)) := by
  simp only [evalSegCfg, applyView, ← one_cons_encLeft, 
  encRight_cons, rWord_zero, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_10 (L : List ℕ) :
    (evalSegCfg .mA0R L []) [target_tm]⊢⁺
      evalSegCfg .mAR (0 :: L) (1 :: []) := by
  simp only [evalSegCfg, applyView,
   encLeft_cons, encRight_nil, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute
private theorem step_mA0R_11 (rt1 : List ℕ) :
    (evalSegCfg .mA0R [] (0 :: rt1)) [target_tm]⊢⁺
      evalSegCfg .mEL [] (0 :: (push0R rt1)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
    encLeft_nil, encRight_cons, rWord_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute
private theorem step_mA0R_12 (lt2 : List ℕ) (rt1 : List ℕ) :
    (evalSegCfg .mA0R (0 :: lt2) (0 :: rt1)) [target_tm]⊢⁺
      evalSegCfg .mEL (0 :: lt2) (0 :: (push0R rt1)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, 
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_13 (l2 : ℕ) (lt2 : List ℕ) (rt1 : List ℕ) :
    (evalSegCfg .mA0R ((l2 + 1) :: lt2) (0 :: rt1)) [target_tm]⊢⁺
      evalSegCfg .mEL ((l2 + 1) :: lt2) (0 :: (push0R rt1)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, 
     onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_14 (L : List ℕ) :
    (evalSegCfg .mA0R L (1 :: [])) [target_tm]⊢⁺
      evalSegCfg .mEL (1 :: L) (0 :: []) := by
  simp only [evalSegCfg, applyView,
   encLeft_cons, encRight_nil, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_15 (L : List ℕ) (rt3 : List ℕ) :
    (evalSegCfg .mA0R L (1 :: (0 :: rt3))) [target_tm]⊢⁺
      evalSegCfg .mEL (1 :: L) (push0R rt3) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_16 (L : List ℕ) (r3 : ℕ) (rt3 : List ℕ) :
    (evalSegCfg .mA0R L (1 :: ((r3 + 1) :: rt3))) [target_tm]⊢⁺
      evalSegCfg .mEL (1 :: L) (0 :: (r3 :: rt3)) := by
  simp only [evalSegCfg, applyView, 
   encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_17 (L : List ℕ) :
    (evalSegCfg .mA0R L (2 :: [])) [target_tm]⊢⁺
      evalSegCfg .mAR (0 :: (0 :: L)) [] := by
  simp only [evalSegCfg, applyView,
   encLeft_cons, encRight_nil, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
   default_head, default_tail]
  execute
private theorem step_mA0R_18 (L : List ℕ) (rt4 : List ℕ) :
    (evalSegCfg .mA0R L (2 :: (0 :: rt4))) [target_tm]⊢⁺
      evalSegCfg .mAR (0 :: (0 :: L)) (0 :: rt4) := by
  simp only [evalSegCfg, applyView, 
   encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_19 (L : List ℕ) (r4 : ℕ) (rt4 : List ℕ) :
    (evalSegCfg .mA0R L (2 :: ((r4 + 1) :: rt4))) [target_tm]⊢⁺
      evalSegCfg .mAR (0 :: (0 :: L)) ((r4 + 1) :: rt4) := by
  simp only [evalSegCfg, applyView, 
   encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mA0R_20 (L : List ℕ) (r3 : ℕ) (rt1 : List ℕ) :
    (evalSegCfg .mA0R L ((r3 + 3) :: rt1)) [target_tm]⊢⁺
      evalSegCfg .mAR (0 :: L) (1 :: (r3 :: rt1)) := by
  simp only [evalSegCfg, applyView, 
   encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mEL_21 :
    (evalSegCfg .mEL [] []) [target_tm]⊢⁺
      evalSegCfg .mA0R (0 :: []) [] := by
  simp only [evalSegCfg, applyView,
    encLeft_nil, encLeft_cons, encRight_nil, lWord, onesSep0_zero, 
    ListBlank.append,
    zero_cons_default, default_head, default_tail]
  execute
private theorem step_mEL_22_halt (rt2 : List ℕ) :
    ∃ cfg_h, ((evalSegCfg .mEL [] (0 :: rt2)) [target_tm]⊢⁺ cfg_h) ∧
      (step target_tm cfg_h).isNone := by
  have h1 : (evalSegCfg .mEL [] (0 :: rt2)) [target_tm]⊢⁺
      (((1 : Fin 2) >> (encLeft [])) {{5}}> ((1 : Fin 2) >> (encRight rt2))) := by
    simp only [evalSegCfg, applyView, encLeft_nil, encRight_cons,
      rWord_zero, 
      ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
     default_head, default_tail]
    execute
  refine ⟨_, h1, ?_⟩
  simp [step, target_tm, Turing.ListBlank.head_cons]
private theorem step_mEL_23 (rt2 : List ℕ) :
    (evalSegCfg .mEL [] (1 :: rt2)) [target_tm]⊢⁺
      evalSegCfg .mA0R (0 :: []) (0 :: rt2) := by
  simp only [evalSegCfg, applyView,
    encLeft_nil, encLeft_cons, encRight_cons, lWord, rWord_zero, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute
private theorem step_mEL_24 (r3 : ℕ) (rt2 : List ℕ) :
    (evalSegCfg .mEL [] ((r3 + 2) :: rt2)) [target_tm]⊢⁺
      evalSegCfg .mA0R (0 :: []) ((r3 + 1) :: rt2) := by
  simp only [evalSegCfg, applyView,
    encLeft_nil, encLeft_cons, encRight_cons, lWord, rWord_succ,
      onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  execute
private theorem step_mEL_25 (lt1 : List ℕ) (R : List ℕ) :
    (evalSegCfg .mEL (0 :: lt1) R) [target_tm]⊢⁺
      evalSegCfg .mAR lt1 (push0R (push0R R)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, lWord, onesSep0_zero, 
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mEL_26 (lt1 : List ℕ) (R : List ℕ) :
    (evalSegCfg .mEL (1 :: lt1) R) [target_tm]⊢⁺
      evalSegCfg .mA0R lt1 (0 :: (push0R R)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, 
      onesSep0_zero, onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute
private theorem step_mEL_27 (l2 : ℕ) (lt1 : List ℕ) (R : List ℕ) :
    (evalSegCfg .mEL ((l2 + 2) :: lt1) R) [target_tm]⊢⁺
      evalSegCfg .mAR (l2 :: lt1) (0 :: (push0R R)) := by
  simp only [evalSegCfg, applyView, ← zero_cons_encRight,
   encLeft_cons, encRight_cons, lWord, rWord_zero, 
     onesSep0_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAR_drain (L : List ℕ) (R : List ℕ) :
    ∃ cfg', ((evalSegCfg .mAR L R) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) := by
  induction R generalizing L with
  | nil =>
    exact ⟨evalCfg (.mAR, (bump1L L), (1 :: [])),
      step_mAR_1 L,
      Or.inl ⟨(.mAR, (bump1L L), (1 :: [])), trivial, rfl⟩⟩
  | cons hd Rt ih =>
    rcases hd with _ | _ | _ | r3
    · rcases L with _ | ⟨_ | l2, lt2⟩
      · exact ⟨evalCfg (.mEL, [], (0 :: (push0R Rt))),
          step_mAR_2 Rt,
          Or.inl ⟨(.mEL, [], (0 :: (push0R Rt))), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mA0R, (bump1L lt2), (push0R Rt)),
          step_mAR_3 lt2 Rt,
          Or.inl ⟨(.mA0R, (bump1L lt2), (push0R Rt)), trivial, rfl⟩⟩
      · rcases l2 with _ | l3
        · exact ⟨evalCfg (.mEL, (0 :: lt2), (push0R (push0R Rt))),
            step_mAR_4 lt2 Rt,
            Or.inl ⟨(.mEL, (0 :: lt2), (push0R (push0R Rt))), trivial, rfl⟩⟩
        · exact ⟨evalCfg (.mEL, ((l3 + 1) :: lt2), (push0R (push0R Rt))),
            step_mAR_5 l3 lt2 Rt,
            Or.inl ⟨(.mEL, ((l3 + 1) :: lt2), (push0R (push0R Rt))), trivial, rfl⟩⟩
    · rcases Rt with _ | ⟨_ | r3, rt3⟩
      · exact ⟨evalCfg (.mEL, (bump1L (bump1L L)), (0 :: [])),
          step_mAR_6 L,
          Or.inl ⟨(.mEL, (bump1L (bump1L L)), (0 :: [])), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mEL, (bump1L (bump1L L)), (push0R rt3)),
          step_mAR_7 L rt3,
          Or.inl ⟨(.mEL, (bump1L (bump1L L)), (push0R rt3)), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mEL, (bump1L (bump1L L)), (0 :: (r3 :: rt3))),
          step_mAR_8 L r3 rt3,
          Or.inl ⟨(.mEL, (bump1L (bump1L L)), (0 :: (r3 :: rt3))), trivial, rfl⟩⟩
    · exact stepOut_trans (step_mAR_2_loop L Rt) (ih (0 :: bump1L L))
    · exact ⟨evalCfg (.mAR, (bump1L L), (1 :: (r3 :: Rt))),
        step_mAR_9 L r3 Rt,
        Or.inl ⟨(.mAR, (bump1L L), (1 :: (r3 :: Rt))), trivial, rfl⟩⟩

private theorem segmented_step_sound (m : SegMode) (L : List ℕ) (R : List ℕ) :
    ∃ cfg', ((evalSegCfg m L R) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) := by
  cases m with
  | mAR => exact step_mAR_drain L R
  | mA0R =>
    rcases R with _ | ⟨_ | r1, rt1⟩
    · exact ⟨evalCfg (.mAR, (0 :: L), (1 :: [])),
        step_mA0R_10 L,
        Or.inl ⟨(.mAR, (0 :: L), (1 :: [])), trivial, rfl⟩⟩
    · rcases L with _ | ⟨_ | l2, lt2⟩
      · exact ⟨evalCfg (.mEL, [], (0 :: (push0R rt1))),
          step_mA0R_11 rt1,
          Or.inl ⟨(.mEL, [], (0 :: (push0R rt1))), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mEL, (0 :: lt2), (0 :: (push0R rt1))),
          step_mA0R_12 lt2 rt1,
          Or.inl ⟨(.mEL, (0 :: lt2), (0 :: (push0R rt1))), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mEL, ((l2 + 1) :: lt2), (0 :: (push0R rt1))),
          step_mA0R_13 l2 lt2 rt1,
          Or.inl ⟨(.mEL, ((l2 + 1) :: lt2), (0 :: (push0R rt1))), trivial, rfl⟩⟩
    · rcases r1 with _ | r2
      · rcases rt1 with _ | ⟨_ | r3, rt3⟩
        · exact ⟨evalCfg (.mEL, (1 :: L), (0 :: [])),
            step_mA0R_14 L,
            Or.inl ⟨(.mEL, (1 :: L), (0 :: [])), trivial, rfl⟩⟩
        · exact ⟨evalCfg (.mEL, (1 :: L), (push0R rt3)),
            step_mA0R_15 L rt3,
            Or.inl ⟨(.mEL, (1 :: L), (push0R rt3)), trivial, rfl⟩⟩
        · exact ⟨evalCfg (.mEL, (1 :: L), (0 :: (r3 :: rt3))),
            step_mA0R_16 L r3 rt3,
            Or.inl ⟨(.mEL, (1 :: L), (0 :: (r3 :: rt3))), trivial, rfl⟩⟩
      · rcases r2 with _ | r3
        · rcases rt1 with _ | ⟨_ | r4, rt4⟩
          · exact ⟨evalCfg (.mAR, (0 :: (0 :: L)), []),
              step_mA0R_17 L,
              Or.inl ⟨(.mAR, (0 :: (0 :: L)), []), trivial, rfl⟩⟩
          · exact ⟨evalCfg (.mAR, (0 :: (0 :: L)), (0 :: rt4)),
              step_mA0R_18 L rt4,
              Or.inl ⟨(.mAR, (0 :: (0 :: L)), (0 :: rt4)), trivial, rfl⟩⟩
          · exact ⟨evalCfg (.mAR, (0 :: (0 :: L)), ((r4 + 1) :: rt4)),
              step_mA0R_19 L r4 rt4,
              Or.inl ⟨(.mAR, (0 :: (0 :: L)), ((r4 + 1) :: rt4)), trivial, rfl⟩⟩
        · exact ⟨evalCfg (.mAR, (0 :: L), (1 :: (r3 :: rt1))),
            step_mA0R_20 L r3 rt1,
            Or.inl ⟨(.mAR, (0 :: L), (1 :: (r3 :: rt1))), trivial, rfl⟩⟩
  | mEL =>
    rcases L with _ | ⟨_ | l1, lt1⟩
    · rcases R with _ | ⟨_ | r2, rt2⟩
      · exact ⟨evalCfg (.mA0R, (0 :: []), []),
          step_mEL_21,
          Or.inl ⟨(.mA0R, (0 :: []), []), trivial, rfl⟩⟩
      · rcases step_mEL_22_halt rt2 with ⟨cfg_h, hp, hh⟩; exact ⟨cfg_h, hp, Or.inr hh⟩
      · rcases r2 with _ | r3
        · exact ⟨evalCfg (.mA0R, (0 :: []), (0 :: rt2)),
            step_mEL_23 rt2,
            Or.inl ⟨(.mA0R, (0 :: []), (0 :: rt2)), trivial, rfl⟩⟩
        · exact ⟨evalCfg (.mA0R, (0 :: []), ((r3 + 1) :: rt2)),
            step_mEL_24 r3 rt2,
            Or.inl ⟨(.mA0R, (0 :: []), ((r3 + 1) :: rt2)), trivial, rfl⟩⟩
    · exact ⟨evalCfg (.mAR, lt1, (push0R (push0R R))),
        step_mEL_25 lt1 R,
        Or.inl ⟨(.mAR, lt1, (push0R (push0R R))), trivial, rfl⟩⟩
    · rcases l1 with _ | l2
      · exact ⟨evalCfg (.mA0R, lt1, (0 :: (push0R R))),
          step_mEL_26 lt1 R,
          Or.inl ⟨(.mA0R, lt1, (0 :: (push0R R))), trivial, rfl⟩⟩
      · exact ⟨evalCfg (.mAR, (l2 :: lt1), (0 :: (push0R R))),
          step_mEL_27 l2 lt1 R,
          Or.inl ⟨(.mAR, (l2 :: lt1), (0 :: (push0R R))), trivial, rfl⟩⟩

private theorem segmented_system_closed (s : SegState) (_ : ValidSeg s) :
    ∃ cfg', ((evalCfg s) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) :=
  segmented_step_sound s.1 s.2.1 s.2.2

/-- Explicit `IsClosedSegmentedSystem` witness for `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`. -/
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

/-- Segmented cryptid certificate for `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`. -/
theorem is_segmented_cryptid : IsSegmentedCryptid target :=
  ⟨SegState, SegMode, modes, ValidSeg, modeOf, segsL, segsR, evalCfg, is_closed_segmented_system⟩

end BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH
