/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LE_1RC0LF_0LD0RC_1RA1LD_1LB0LE_---0RE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LE_1RC0LF_0LD0RC_1RA1LD_1LB0LE_---0RE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1RC0LF_0LD0RC_1RA1LD_1LB0LE_HHH0RE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LE_1RC0LF_0LD0RC_1RA1LD_1LB0LE_---0RE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 4, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

/-- Anchor machine `TM24` (`1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_---0RE`) for Holdout `#306`. -/
def tm24 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 4, Stmt.write 0 Dir.right)

abbrev z0 : zF := [0]
abbrev z1 : zF := [1]

@[simp] lemma zMz (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma z00 : Turing.ListBlank.cons (0 : Fin 2) default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = Turing.ListBlank.cons a (l +> s) := rfl
@[simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

lemma zSm (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z01 (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa (tm : Machine (Fin 2) (Fin 6)) (c_1 : Cfg (Fin 2) (Fin 6)) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zPs {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 : Cfg (Fin 2) (Fin 6)} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z02 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSp {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z03 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂

macro "finish" : tactic =>
  `(tactic| exact ⟨0, rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

@[simp] lemma zLp_zero {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zLp_succ {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] lemma zLp_succ' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] lemma zLp_one {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

lemma zLp_add {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n :=
  BusyBeaver.list_pow_add l m n

lemma zLp_shift {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ^ n ++ l := by
  rw [Nat.add_comm 1 n, BusyBeaver.list_pow_succ']

lemma z07 (l : zF) (n : Nat) (s : zB) : (l ^ (1 + n)) +> s = l +> ((l ^ n) +> s) := by
  rw [zLp_succ', append_assoc]

lemma z09 (l : zF) (n : Nat) (s : zB) : (l ^ n) +> (l +> s) = (l ^ (1 + n)) +> s := by
  rw [zLp_shift, append_assoc]

lemma rot_0 (n : Nat) (r : zB) :
    (z0 ^ n) +> ([0] +> r) = [0] +> ((z0 ^ n) +> r) := by
  rw [z09 z0 n r, z07 z0 n r]

lemma rot_0_3 (n : Nat) (r : zB) :
    (z0 ^ n) +> ([0, 0, 0] +> r) = [0, 0, 0] +> ((z0 ^ n) +> r) := by
  have h1 : ([0, 0, 0] : zF) +> r = [0] +> ([0] +> ([0] +> r)) := rfl
  rw [h1, rot_0, rot_0, rot_0]
  rfl

-- ============================================================================
-- Section 1: Directed-Head Configurations & Local Tape Sweeps (Others_v1.v:13-176)
-- ============================================================================

def stepCfg (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  ([0] +> l) {{D}}> r

def root (r : zB) : Cfg (Fin 2) (Fin 6) :=
  stepCfg ([1] +> default) r

def backCfg (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  l <{{E}} ([0, 0, 0] +> r)

def returnCfg (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  l <{{E}} ([0, 0] +> r)

lemma shiftL_E_1_step (l r : zB) :
    (([1] +> l) <{{E}} r) [tm24]⊢* (l <{{E}} ([0] +> r)) := by
  simp only [append_cons, append_nil]
  execute

lemma shiftL_E_1 (n : Nat) (l r : zB) :
    (((z1 ^ n) +> l) <{{E}} r) [tm24]⊢* (l <{{E}} ((z0 ^ n) +> r)) := by
  induction n generalizing r with
  | zero =>
    simp only [zLp_zero, append_nil]
    finish
  | succ n ih =>
    have hn : n + 1 = 1 + n := by omega
    rw [hn, z07 z1 n l]
    refine zSt (shiftL_E_1_step ((z1 ^ n) +> l) r) ?_
    simpa only [z09 z0 n r] using ih ([0] +> r)

lemma back_digit_head (l r : zB) :
    (backCfg ([0] +> ([1, 1] +> l)) r) [tm24]⊢* (l <{{E}} ([0, 0, 0] +> ([1, 1, 0] +> r))) := by
  unfold backCfg
  simp only [append_cons, append_nil]
  execute

lemma back_digit (n : Nat) (l r : zB) :
    (backCfg ([0] +> ((z1 ^ (2 + n)) +> l)) r) [tm24]⊢*
      (backCfg l (((z0 ^ n) ++ [1, 1, 0]) +> r)) := by
  have h1 : (z1 ^ (2 + n)) +> l = [1, 1] +> ((z1 ^ n) +> l) := by
    have h2n : 2 + n = 1 + (1 + n) := by omega
    rw [h2n, z07 z1 (1 + n) l, z07 z1 n l]
    rfl
  rw [h1]
  refine zSt (back_digit_head ((z1 ^ n) +> l) r) ?_
  refine zSt (shiftL_E_1 n l ([0, 0, 0] +> ([1, 1, 0] +> r))) ?_
  unfold backCfg
  rw [rot_0_3 n ([1, 1, 0] +> r), append_assoc]
  finish

lemma start_back_head (l r : zB) :
    (stepCfg ([0] +> ([1, 1] +> l)) ([0, 0, 0] +> r)) [tm24]⊢⁺
      (l <{{E}} ([0, 0, 0] +> ([0] +> ([1, 1, 0] +> r)))) := by
  unfold stepCfg
  simp only [append_cons, append_nil]
  execute

lemma start_back (n : Nat) (l r : zB) :
    (stepCfg ([0] +> ((z1 ^ (2 + n)) +> l)) ([0, 0, 0] +> r)) [tm24]⊢⁺
      (backCfg l ((z0 ^ (1 + n)) +> ([1, 1, 0] +> r))) := by
  have h1 : (z1 ^ (2 + n)) +> l = [1, 1] +> ((z1 ^ n) +> l) := by
    have h2n : 2 + n = 1 + (1 + n) := by omega
    rw [h2n, z07 z1 (1 + n) l, z07 z1 n l]
    rfl
  rw [h1]
  refine z02 (start_back_head ((z1 ^ n) +> l) r) ?_
  refine zSt (shiftL_E_1 n l ([0, 0, 0] +> ([0] +> ([1, 1, 0] +> r)))) ?_
  unfold backCfg
  rw [rot_0_3 n ([0] +> ([1, 1, 0] +> r)), z09 z0 n ([1, 1, 0] +> r)]
  finish

def pending (hs : List Nat) (l : zB) : zB :=
  hs.foldl (fun l h => [0] +> ((z1 ^ (2 + h)) +> l)) l

@[simp] lemma pending_nil (l : zB) : pending [] l = l := rfl
@[simp] lemma pending_cons (h : Nat) (hs : List Nat) (l : zB) :
    pending (h :: hs) l = pending hs ([0] +> ((z1 ^ (2 + h)) +> l)) := rfl

def back_word (hs : List Nat) : zF :=
  hs.flatMap (fun h => (z0 ^ h) ++ [1, 1, 0])

@[simp] lemma back_word_nil : back_word [] = [] := rfl
@[simp] lemma back_word_cons (h : Nat) (hs : List Nat) :
    back_word (h :: hs) = (z0 ^ h) ++ [1, 1, 0] ++ back_word hs := rfl

lemma pending_back (hs : List Nat) (l r : zB) :
    (backCfg (pending hs l) r) [tm24]⊢* (backCfg l (back_word hs +> r)) := by
  induction hs generalizing l r with
  | nil =>
    simp only [pending_nil, back_word_nil, append_nil]
    finish
  | cons h hs ih =>
    simp only [pending_cons, back_word_cons, append_assoc]
    refine zSt (ih ([0] +> ((z1 ^ (2 + h)) +> l)) r) ?_
    refine zSt (back_digit h l (back_word hs +> r)) ?_
    rw [append_assoc]
    finish

def digits (ds : List Nat) : zF :=
  ds.flatMap (fun d => (z0 ^ (1 + d)) ++ [1, 1])

@[simp] lemma digits_nil : digits [] = [] := rfl
@[simp] lemma digits_cons (d : Nat) (ds : List Nat) :
    digits (d :: ds) = (z0 ^ (1 + d)) ++ [1, 1] ++ digits ds := rfl

inductive IsBinary : List Nat → Prop where
  | nil : IsBinary []
  | cons {d : Nat} {ds : List Nat} : d ≤ 1 → IsBinary ds → IsBinary (d :: ds)

lemma isBinary_append {u v : List Nat} : IsBinary (u ++ v) ↔ IsBinary u ∧ IsBinary v := by
  induction u with
  | nil =>
    simp only [List.nil_append, true_and]
    exact ⟨fun h => ⟨IsBinary.nil, h⟩, fun ⟨_, h⟩ => h⟩
  | cons d u ih =>
    constructor
    · intro h
      cases h with
      | cons hd hrest =>
        rcases ih.mp hrest with ⟨hu, hv⟩
        exact ⟨IsBinary.cons hd hu, hv⟩
    · rintro ⟨hu, hv⟩
      cases hu with
      | cons hd hu' =>
        exact IsBinary.cons hd (ih.mpr ⟨hu', hv⟩)

lemma scan_digit_one {d : Nat} (hd : d ≤ 1) (l r : zB) :
    (stepCfg l ((z0 ^ (1 + d)) +> ([1, 1] +> r))) [tm24]⊢*
      (stepCfg ([0] +> ((z1 ^ (2 + d)) +> l)) r) := by
  rcases d with _ | _ | d
  · unfold stepCfg
    simp only [Nat.add_zero, zLp_one, zLp_succ, zLp_zero, z0, z1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  · unfold stepCfg
    simp only [zLp_succ, zLp_zero, z0, z1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  · omega

lemma scan_digits {ds : List Nat} (hds : IsBinary ds) (l r : zB) :
    (stepCfg l (digits ds +> r)) [tm24]⊢* (stepCfg (pending ds l) r) := by
  induction hds generalizing l r with
  | nil =>
    simp only [digits_nil, append_nil, pending_nil]
    finish
  | @cons d ds hd hds ih =>
    simp only [digits_cons, pending_cons, append_assoc]
    refine zSt (scan_digit_one hd l (digits ds +> r)) ?_
    exact ih ([0] +> ((z1 ^ (2 + d)) +> l)) r

lemma ordinary_return {ds : List Nat} {n : Nat} (hds : IsBinary ds) (hn : n ≤ 1) (l r : zB) :
    (stepCfg l (digits ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0, 0, 0] +> r)))) [tm24]⊢⁺
      (backCfg l (back_word ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0] +> r)))) := by
  refine zSp (scan_digits hds l ((z0 ^ (1 + n)) +> ([1, 1, 0, 0, 0] +> r))) ?_
  have hsplit : ([1, 1, 0, 0, 0] : zF) +> r = [1, 1] +> ([0, 0, 0] +> r) := rfl
  rw [hsplit]
  refine zSp (scan_digit_one hn (pending ds l) ([0, 0, 0] +> r)) ?_
  refine z02 (start_back n (pending ds l) r) ?_
  exact pending_back ds l ((z0 ^ (1 + n)) +> ([1, 1, 0] +> r))

lemma zero_back_word (ds : List Nat) (r : zB) :
    [0] +> (back_word ds +> r) = digits ds +> ([0] +> r) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [back_word_cons, digits_cons, append_assoc]
    have h1 : ([1, 1, 0] : zF) +> (back_word ds +> r) = [1, 1] +> ([0] +> (back_word ds +> r)) := rfl
    rw [h1, ih, ← rot_0 d ([1, 1] +> (digits ds +> ([0] +> r))), ← z09 z0 d]

lemma close6 (l r : zB) :
    (backCfg ((z0 ^ 6) +> l) r) [tm24]⊢*
      (stepCfg ([1] +> ([0] +> l)) ([0, 0, 1, 1, 1, 0] +> r)) := by
  unfold backCfg stepCfg
  simp only [zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma close2 (l r : zB) :
    (backCfg ([0, 0] +> ((z1 ^ 4) +> l)) r) [tm24]⊢*
      (l <{{A}} ((z1 ^ 8) +> ([0] +> r))) := by
  unfold backCfg
  simp only [zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma block_back_head (l r : zB) :
    (([0] +> ([1, 1] +> l)) <{{A}} ((z1 ^ 8) +> r)) [tm24]⊢*
      (l <{{E}} ([0, 0, 0] +> ([0] +> ((z1 ^ 7) +> r)))) := by
  simp only [zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma block_back_one (n : Nat) (l r : zB) :
    (([0] +> ((z1 ^ (2 + n)) +> l)) <{{A}} ((z1 ^ 8) +> r)) [tm24]⊢*
      (backCfg l ((z0 ^ (1 + n)) +> ((z1 ^ 7) +> r))) := by
  have h1 : (z1 ^ (2 + n)) +> l = [1, 1] +> ((z1 ^ n) +> l) := by
    have h2n : 2 + n = 1 + (1 + n) := by omega
    rw [h2n, z07 z1 (1 + n) l, z07 z1 n l]
    rfl
  rw [h1]
  refine zSt (block_back_head ((z1 ^ n) +> l) r) ?_
  refine zSt (shiftL_E_1 n l ([0, 0, 0] +> ([0] +> ((z1 ^ 7) +> r)))) ?_
  unfold backCfg
  rw [rot_0_3 n ([0] +> ((z1 ^ 7) +> r)), z09 z0 n ((z1 ^ 7) +> r)]
  finish

lemma block_back (hs : List Nat) (n : Nat) (l r : zB) :
    (([0] +> ((z1 ^ (2 + n)) +> pending hs l)) <{{A}} ((z1 ^ 8) +> r)) [tm24]⊢*
      (backCfg l (back_word hs +> ((z0 ^ (1 + n)) +> ((z1 ^ 7) +> r)))) := by
  refine zSt (block_back_one n (pending hs l) r) ?_
  exact pending_back hs l ((z0 ^ (1 + n)) +> ((z1 ^ 7) +> r))

lemma scan_seven {b : Nat} (hb : b = 1 ∨ b = 2) (l r : zB) :
    (stepCfg l ((z0 ^ b) +> ((z1 ^ 7) +> r))) [tm24]⊢*
      (stepCfg ((z0 ^ 6) +> ((z1 ^ (1 + b)) +> l)) r) := by
  rcases hb with rfl | rfl <;> {
    unfold stepCfg
    simp only [zLp_succ, zLp_zero, z0, z1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  }

lemma last7 (b : Nat) (ds : List Nat) (n : Nat) (l r : zB)
    (hb : b = 1 ∨ b = 2) (hds : IsBinary ds) (hn : n ≤ 1) :
    (stepCfg l ((z0 ^ b) +> ((z1 ^ 7) +> (digits ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0, 0, 0] +> r)))))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((z1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits ds +> ((z0 ^ (2 + n)) +> ([1, 1, 0] +> r))))) := by
  refine zSp (scan_seven hb l (digits ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0, 0, 0] +> r)))) ?_
  refine z02 (ordinary_return hds hn ((z0 ^ 6) +> ((z1 ^ (1 + b)) +> l)) r) ?_
  refine zSt (close6 ((z1 ^ (1 + b)) +> l) (back_word ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0] +> r)))) ?_
  have h1 : ([0, 0, 1, 1, 1, 0] : zF) +> (back_word ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0] +> r))) =
      [0, 0, 1, 1, 1] +> ([0] +> (back_word ds +> ((z0 ^ (1 + n)) +> ([1, 1, 0] +> r)))) := rfl
  have h2n : 2 + n = 1 + (1 + n) := by omega
  rw [h1, zero_back_word, h2n, z07 z0 (1 + n) ([1, 1, 0] +> r)]
  finish

lemma active_scan (l r : zB) :
    (stepCfg ([1] +> l) ([0, 0, 1, 1, 1] +> r)) [tm24]⊢*
      (stepCfg ([0, 0] +> ((z1 ^ 4) +> l)) r) := by
  unfold stepCfg
  simp only [zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma active_turn (l r : zB) :
    (stepCfg ([1] +> l) ([0, 0, 1, 1, 1, 0, 0, 0] +> r)) [tm24]⊢⁺
      (stepCfg ([0] +> ((z1 ^ 3) +> l)) ([0, 0, 1, 1, 0] +> r)) := by
  unfold stepCfg
  simp only [zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

def payload (ds : List Nat) : zF :=
  ds.flatMap (fun d => (z0 ^ d) ++ [1, 1])

def put_left (hs : List Nat) (l : zB) : zB :=
  hs.foldl (fun l h => [0] +> ((z1 ^ h) +> l)) l

def seed : List Nat := [2, 2, 1, 2, 2, 1, 2]

def cap_entry (ds : List Nat) (h : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  root ([0, 0] +> (payload ds +> ((z0 ^ h) +> ((z1 ^ 7) +> r))))

lemma bridge0 (r : zB) :
    (cap_entry [] 4 r) [tm24]⊢⁺
      (stepCfg (put_left [3] default) (payload [2] +> ([0, 0] +> ((z1 ^ 7) +> r)))) := by
  unfold cap_entry root stepCfg payload put_left
  simp only [List.flatMap_nil, List.flatMap_cons, List.foldl_cons, List.foldl_nil,
    zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma bridge1 (r : zB) :
    (cap_entry [2, 2] 3 r) [tm24]⊢⁺
      (stepCfg (put_left [4, 3] default) (payload [2, 1, 1] +> ([0] +> ((z1 ^ 7) +> r)))) := by
  unfold cap_entry root stepCfg payload put_left
  simp only [List.flatMap_nil, List.flatMap_cons, List.foldl_cons, List.foldl_nil,
    zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma bridge2 (r : zB) :
    (cap_entry [3, 2, 2, 1, 1] 2 r) [tm24]⊢⁺
      (stepCfg (put_left [3] default) (payload [2, 1, 2, 2, 1, 1] +> ([0, 0] +> ((z1 ^ 7) +> r)))) := by
  unfold cap_entry root stepCfg payload put_left
  simp only [List.flatMap_nil, List.flatMap_cons, List.foldl_cons, List.foldl_nil,
    zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

lemma bridge3 (r : zB) :
    (cap_entry [2, 2, 1, 2, 2, 1, 1] 3 r) [tm24]⊢⁺
      (root ([0, 0] +> ((z1 ^ 7) +> (payload seed +> ([0] +> ((z1 ^ 7) +> r)))))) := by
  unfold cap_entry root stepCfg payload seed
  simp only [List.flatMap_nil, List.flatMap_cons,
    zLp_succ, zLp_zero, z0, z1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

-- ============================================================================
-- Section 2: Prefix Value, Tail, Num, Tags, Segment, Block, Carry, Advance
-- (Others_v1.v:180-665)
-- ============================================================================

def prefix_value : Nat → List Nat → Nat
  | k + 1, d :: ds => d * 2 ^ k + prefix_value k ds
  | _, _ => 0

lemma prefix_carry (n : Nat) (u : List Nat) (a : Nat) (t : List Nat) :
    prefix_value n (u ++ [a, 3] ++ t) ≤ prefix_value n (u ++ [1 + a, 1] ++ t) ∧
    prefix_value n (u ++ [1 + a, 1] ++ t) ≤ 1 + prefix_value n (u ++ [a, 3] ++ t) := by
  induction u generalizing n with
  | nil =>
    rcases n with _ | _ | k
    · simp [prefix_value]
    · simp [prefix_value]
    · simp only [List.nil_append, List.cons_append, prefix_value]
      have heq : (1 + a) * 2 ^ (k + 1) + (1 * 2 ^ k + prefix_value k t) =
          a * 2 ^ (k + 1) + (3 * 2 ^ k + prefix_value k t) := by
        rw [Nat.pow_succ]
        ring
      omega
  | cons d u ih =>
    rcases n with _ | k
    · simp [prefix_value]
    · simp only [List.cons_append, prefix_value]
      have h := ih k
      simp only [List.append_assoc] at h ⊢
      omega

lemma prefix_last (n : Nat) (u : List Nat) (a : Nat) (h : n ≤ 1 + u.length) :
    prefix_value n (u ++ [a]) ≤ prefix_value n (u ++ [1 + a]) ∧
    prefix_value n (u ++ [1 + a]) ≤ 1 + prefix_value n (u ++ [a]) := by
  induction u generalizing n with
  | nil =>
    rcases n with _ | _ | k
    · simp [prefix_value]
    · simp [prefix_value]
    · simp at h
  | cons d u ih =>
    rcases n with _ | k
    · simp [prefix_value]
    · simp only [List.length_cons] at h
      simp only [List.cons_append, prefix_value]
      have h' := ih k (by omega)
      omega

inductive Tail : List Nat → Prop where
  | nil : Tail []
  | zero (ds : List Nat) : Tail ds → Tail (0 :: ds)
  | one (ds : List Nat) : Tail ds → Tail (1 :: ds)
  | two (n : Nat) : Tail (2 :: List.replicate n 0)

inductive Num : Bool → List Nat → Prop where
  | nil (p : Bool) : Num p []
  | zero (p : Bool) (ds : List Nat) : Tail ds → Num p (0 :: ds)
  | one (p : Bool) (ds : List Nat) : Num (!p) ds → Num p (1 :: ds)
  | two (n : Nat) : Num false (2 :: List.replicate n 0)

lemma tail_zeros (n : Nat) : Tail (List.replicate n 0) := by
  induction n with
  | zero => exact Tail.nil
  | succ n ih => exact Tail.zero (List.replicate n 0) ih

lemma tail_prefix {u t : List Nat} (hu : IsBinary u) (ht : Tail t) : Tail (u ++ t) := by
  induction hu with
  | nil => exact ht
  | @cons d ds hd _ ih =>
    rcases d with _ | _ | d
    · exact Tail.zero (ds ++ t) ih
    · exact Tail.one (ds ++ t) ih
    · omega

lemma tail_binary {u : List Nat} (hu : IsBinary u) : Tail u := by
  simpa using tail_prefix hu Tail.nil

lemma num_binary {u : List Nat} (hu : IsBinary u) (p : Bool) : Num p u := by
  induction hu generalizing p with
  | nil => exact Num.nil p
  | @cons d ds hd hds ih =>
    rcases d with _ | _ | d
    · exact Num.zero p ds (tail_binary hds)
    · exact Num.one p ds (ih (!p))
    · omega

lemma num_tail {p : Bool} {ds : List Nat} (h : Num p ds) : Tail ds := by
  induction h with
  | nil => exact Tail.nil
  | zero _ ds ht => exact Tail.zero ds ht
  | one _ ds _ ih => exact Tail.one ds ih
  | two n => exact Tail.two n

lemma num_one {p : Bool} {ds : List Nat} (h : Num p (1 :: ds)) : Num (!p) ds := by
  cases h with
  | one _ _ h' => exact h'

lemma num_two {p : Bool} {ds : List Nat} (h : Num p (2 :: ds)) : p = false := by
  cases h
  rfl

lemma tail_bump {u : List Nat} (a n : Nat) (hu : IsBinary u) (ha : a ≤ 1) :
    Tail (u ++ [1 + a] ++ List.replicate n 0) := by
  rw [List.append_assoc]
  refine tail_prefix hu ?_
  rcases a with _ | _ | a
  · exact Tail.one (List.replicate n 0) (tail_zeros n)
  · exact Tail.two n
  · omega

lemma num_carry (p : Bool) {u : List Nat} (a n : Nat)
    (hu : IsBinary u) (ha : a ≤ 1)
    (h : Num p (u ++ [a, 2] ++ List.replicate n 0)) :
    Num (!p) (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  induction hu generalizing p with
  | nil =>
    rcases a with _ | _ | a
    · exact Num.one (!p) (0 :: List.replicate n 0) (Num.zero (!!p) (List.replicate n 0) (tail_zeros n))
    · simp only [List.nil_append, List.cons_append] at h ⊢
      have hp : (!p) = false := num_two (num_one h)
      rcases p with _ | _
      · cases hp
      · exact Num.two (n + 1)
    · omega
  | @cons d ds hd hds ih =>
    rcases d with _ | _ | d
    · simp only [List.cons_append]
      have hrep : [1 + a, 0] ++ List.replicate n 0 = [1 + a] ++ List.replicate (n + 1) 0 := rfl
      rw [List.append_assoc, hrep, ← List.append_assoc]
      exact Num.zero (!p) _ (tail_bump a (n + 1) hds ha)
    · simp only [List.cons_append] at h ⊢
      refine Num.one (!p) _ ?_
      have h' := ih (!p) (num_one h)
      simpa using h'
    · omega

def mass : List Nat → Nat
  | [] => 0
  | d :: ds => 1 + d + mass ds

lemma mass_app (u v : List Nat) : mass (u ++ v) = mass u + mass v := by
  induction u with
  | nil => simp [mass]
  | cons d u ih => simp only [List.cons_append, mass, ih]; omega

lemma mass_zeros (n : Nat) : mass (List.replicate n 0) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, mass, ih]; omega

def oddB : Nat → Bool
  | 0 => false
  | n + 1 => !(oddB n)

lemma odd_next (n : Nat) : oddB (1 + n) = !(oddB n) := by
  rw [Nat.add_comm 1 n]; rfl

lemma odd_succ (n : Nat) : oddB (n + 1) = !(oddB n) := rfl

lemma odd_add (a b : Nat) : oddB (a + b) = xor (oddB a) (oddB b) := by
  induction a with
  | zero => simp [oddB]
  | succ a ih =>
    rw [Nat.succ_add, odd_succ, odd_succ, ih]
    cases oddB a <;> cases oddB b <;> rfl

inductive AllOnes : List Nat → Prop where
  | nil : AllOnes []
  | cons {ds : List Nat} : AllOnes ds → AllOnes (1 :: ds)

lemma mass_ones {u : List Nat} (h : AllOnes u) : oddB (mass u) = false := by
  induction h with
  | nil => rfl
  | @cons ds _ ih =>
    simp only [mass]
    have h1 : 1 + 1 + mass ds = 1 + (1 + mass ds) := by omega
    rw [h1, odd_next, odd_next, Bool.not_not, ih]

def Tags (p : Bool) (b : Nat) (ds : List Nat) : Prop :=
  oddB ds.length = !(b == 0) ∧ oddB (mass ds + b) = p

def Head (p : Bool) (ds : List Nat) : Prop :=
  match ds with
  | [] => False
  | d :: _ => d = 1 ∨ (d = 2 ∧ p = false)

def Segment (p : Bool) (b : Nat) (ds : List Nat) : Prop :=
  Num p ds ∧ Head p ds ∧ Tags p b ds ∧
  7 + (if b == 0 then 1 else 0) ≤ ds.length

lemma num_end (p : Bool) {u : List Nat} (hu : IsBinary u)
    (h : AllOnes u → p = oddB u.length) :
    Num p (u ++ [2]) := by
  induction hu generalizing p with
  | nil =>
    have hp := h AllOnes.nil
    subst hp
    exact Num.two 0
  | @cons d ds hd hds ih =>
    rcases d with _ | _ | d
    · exact Num.zero p (ds ++ [2]) (tail_prefix hds (Tail.two 0))
    · refine Num.one p (ds ++ [2]) (ih (!p) ?_)
      intro hone
      have hp := h (AllOnes.cons hone)
      simp only [List.length_cons, odd_succ] at hp
      rw [hp, Bool.not_not]
    · omega

lemma num_last_tags (p : Bool) (b : Nat) {u : List Nat} (a : Nat)
    (hu : IsBinary u) (ha : a ≤ 1)
    (ht : Tags p b (u ++ [a])) (hb : b = 0 ∨ b = 3) :
    Num (!p) (u ++ [1 + a]) := by
  rcases ht with ⟨hlen, hsum⟩
  rcases a with _ | _ | a
  · exact num_binary (isBinary_append.mpr ⟨hu, IsBinary.cons (by omega) IsBinary.nil⟩) (!p)
  · refine num_end (!p) hu ?_
    intro hone
    rw [mass_app] at hsum
    simp only [mass] at hsum
    have hlen' : (u ++ [1]).length = u.length + 1 := by simp
    rw [hlen', odd_succ] at hlen
    have hmass1 : mass u + (1 + 1 + 0) + b = mass u + (2 + b) := by omega
    rw [hmass1, odd_add, mass_ones hone] at hsum
    rcases hb with rfl | rfl
    · simp only [Bool.false_xor] at hsum
      have ho2 : oddB 2 = false := rfl
      rw [ho2] at hsum
      subst hsum
      simpa using hlen.symm
    · simp only [Bool.false_xor] at hsum
      have ho5 : oddB 5 = true := rfl
      rw [ho5] at hsum
      subst hsum
      simpa using hlen.symm
  · omega

lemma odd_adjacent (x y : Nat) (h : x = 1 + y ∨ y = 1 + x) :
    oddB y = !(oddB x) := by
  rcases h with rfl | rfl
  · rw [odd_next, Bool.not_not]
  · rw [odd_next]

lemma tags_carry {p : Bool} {b : Nat} {u : List Nat} {a n : Nat}
    (ht : Tags p b (u ++ [a, 2] ++ List.replicate n 0)) :
    Tags (!p) b (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  rcases ht with ⟨hlen, hsum⟩
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    exact hlen
  · rw [← hsum]
    apply odd_adjacent
    left
    simp only [List.append_assoc, mass_app, mass]
    omega

lemma head_carry {p : Bool} {u : List Nat} {a n : Nat}
    (hu : IsBinary u) (ha : a ≤ 1)
    (hnum : Num p (u ++ [a, 2] ++ List.replicate n 0))
    (hhead : Head p (u ++ [a, 2] ++ List.replicate n 0)) :
    Head (!p) (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  cases hu with
  | nil =>
    simp only [List.nil_append, List.cons_append, Head] at hnum hhead ⊢
    have ha1 : a = 1 := by rcases hhead with h | ⟨h, _⟩ <;> omega
    subst ha1
    right
    exact ⟨rfl, num_two (num_one hnum)⟩
  | @cons d ds hd _ =>
    simp only [List.cons_append, Head] at hhead ⊢
    left
    rcases hhead with h | ⟨h, _⟩ <;> omega

lemma segment_carry {p : Bool} {b : Nat} {u : List Nat} {a n : Nat}
    (hu : IsBinary u) (ha : a ≤ 1)
    (hs : Segment p b (u ++ [a, 2] ++ List.replicate n 0)) :
    Segment (!p) b (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  rcases hs with ⟨hn, hh, ht, hl⟩
  refine ⟨num_carry p a n hu ha hn, head_carry hu ha hn hh, tags_carry ht, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢
  exact hl

lemma tags_last {p : Bool} {b : Nat} {u : List Nat} {a : Nat}
    (ht : Tags p b (u ++ [a])) (hb : b = 0 ∨ b = 3) :
    Tags (!p) (b - 2) (u ++ [1 + a]) := by
  rcases ht with ⟨hlen, hsum⟩
  refine ⟨?_, ?_⟩
  · rcases hb with rfl | rfl <;> {
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      exact hlen
    }
  · rw [← hsum]
    apply odd_adjacent
    rcases hb with rfl | rfl
    · right; simp only [mass_app, mass]; omega
    · left; simp only [mass_app, mass]; omega

lemma segment_last {p : Bool} {b : Nat} {u : List Nat} {a : Nat}
    (hu : IsBinary u) (ha : a ≤ 1)
    (hs : Segment p b (u ++ [a])) (hb : b = 0 ∨ b = 3) :
    Segment (!p) (b - 2) (u ++ [1 + a]) := by
  rcases hs with ⟨hn, hh, ht, hl⟩
  refine ⟨num_last_tags p b a hu ha ht hb, ?_, tags_last ht hb, ?_⟩
  · cases hu with
    | nil =>
      simp only [List.nil_append, List.length_singleton] at hl
      rcases hb with rfl | rfl <;> omega
    | @cons d ds hd _ =>
      simp only [List.cons_append, Head] at hh ⊢
      left
      rcases hh with h | ⟨h, _⟩ <;> omega
  · rcases hb with rfl | rfl <;> {
      simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢
      exact hl
    }

lemma head_binary {p : Bool} {ds : List Nat} (h : IsBinary ds) (hh : Head p ds) :
    Head true ds := by
  cases h with
  | nil => exact hh
  | @cons d ds hd _ =>
    simp only [Head] at hh ⊢
    left
    rcases hh with h1 | ⟨h2, _⟩ <;> omega

lemma head_any (p : Bool) {ds : List Nat} (hh : Head true ds) : Head p ds := by
  rcases ds with _ | ⟨d, ds⟩
  · exact hh
  · simp only [Head] at hh ⊢
    rcases hh with h1 | ⟨_, h2⟩
    · exact Or.inl h1
    · cases h2

def Block (p : Bool) (x : List Nat × Nat) : Prop :=
  IsBinary x.1 ∧ x.2 ≤ 1 ∧ Head true x.1 ∧
  Tags p (1 + x.2) x.1 ∧ 7 ≤ x.1.length

lemma block_length {p : Bool} {ds : List Nat} {n : Nat} (h : Block p (ds, n)) :
    7 ≤ ds.length := h.2.2.2.2

lemma scanned_block (p : Bool) (b : Nat) {ds : List Nat}
    (hs : Segment p b ds) (hu : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    Block p (ds, b - 1) := by
  rcases hs with ⟨_, hh, ⟨hlen, hsum⟩, hl⟩
  dsimp only [Block]
  rcases hb with rfl | rfl <;> {
    refine ⟨hu, by omega, head_binary hu hh, ⟨hlen, hsum⟩, by omega⟩
  }

lemma emitted_segment {p : Bool} {ds : List Nat} {n : Nat}
    (hb : Block p (ds, n)) : Segment (!p) (2 + n) ds := by
  dsimp only [Block] at hb
  rcases hb with ⟨hu, hn, hh, ⟨hlen, hsum⟩, hl⟩
  have h1 : (1 + n == 0) = false := by cases n <;> rfl
  have h2 : (2 + n == 0) = false := by cases n <;> rfl
  refine ⟨num_binary hu (!p), head_any (!p) hh, ⟨?_, ?_⟩, ?_⟩
  · rw [h1] at hlen
    rw [h2]
    exact hlen
  · rw [← hsum]
    apply odd_adjacent
    right
    omega
  · rw [h2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

lemma tail_split {ds : List Nat} (ht : Tail ds) :
    IsBinary ds ∨ ∃ u n, IsBinary u ∧ ds = u ++ 2 :: List.replicate n 0 := by
  induction ht with
  | nil => exact Or.inl IsBinary.nil
  | zero ds _ ih =>
    rcases ih with hb | ⟨u, n, hu, rfl⟩
    · exact Or.inl (IsBinary.cons (by omega) hb)
    · exact Or.inr ⟨0 :: u, n, IsBinary.cons (by omega) hu, rfl⟩
  | one ds _ ih =>
    rcases ih with hb | ⟨u, n, hu, rfl⟩
    · exact Or.inl (IsBinary.cons (by omega) hb)
    · exact Or.inr ⟨1 :: u, n, IsBinary.cons (by omega) hu, rfl⟩
  | two n =>
    exact Or.inr ⟨[], n, IsBinary.nil, rfl⟩

inductive Carry : List Nat → Nat → List Nat → Nat → Prop where
  | inside (u : List Nat) (a n b : Nat) :
      IsBinary u → a ≤ 1 →
      Carry (u ++ [a, 2] ++ List.replicate n 0) b (u ++ [1 + a, 0] ++ List.replicate n 0) b
  | last (u : List Nat) (a b : Nat) :
      IsBinary u → a ≤ 1 → (b = 0 ∨ b = 3) →
      Carry (u ++ [a]) b (u ++ [1 + a]) (b - 2)

lemma carry_segment (p : Bool) {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hs : Segment p b ds) :
    Segment (!p) b' ds' := by
  cases hc with
  | inside u a n b hu ha => exact segment_carry hu ha hs
  | last u a b hu ha hb => exact segment_last hu ha hs hb

lemma carry_zero {ds ds' : List Nat} {b' : Nat} (hc : Carry ds 0 ds' b') : b' = 0 := by
  cases hc <;> rfl

lemma carry_header {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hb : 1 ≤ b ∧ b ≤ 3) : 1 ≤ b' ∧ b' ≤ 3 := by
  cases hc with
  | inside => exact hb
  | last _ _ _ _ _ hb' => omega

lemma list_snoc {α : Type*} (ds : List α) (hne : ds ≠ []) :
    ∃ u a, ds = u ++ [a] := by
  induction ds with
  | nil => contradiction
  | cons d ds ih =>
    rcases ds with _ | ⟨x, xs⟩
    · exact ⟨[], d, rfl⟩
    · rcases ih (by simp) with ⟨u, a, h⟩
      exact ⟨d :: u, a, by simp [h]⟩

lemma word_progress (b : Nat) (ds : List Nat)
    (ht : Tail ds) (hh : Head true ds) (hb : b ≤ 3) :
    (∃ ds' b', Carry ds b ds' b') ∨ (IsBinary ds ∧ (b = 1 ∨ b = 2)) := by
  rcases tail_split ht with hd | ⟨u, n, hu, rfl⟩
  · have hb' : (b = 0 ∨ b = 3) ∨ (b = 1 ∨ b = 2) := by omega
    rcases hb' with hb' | hb'
    · left
      have hne : ds ≠ [] := by rintro rfl; exact hh
      rcases list_snoc ds hne with ⟨u, a, rfl⟩
      rcases isBinary_append.mp hd with ⟨hu, ha1⟩
      cases ha1 with
      | cons ha _ => exact ⟨u ++ [1 + a], b - 2, Carry.last u a b hu ha hb'⟩
    · exact Or.inr ⟨hd, hb'⟩
  · left
    have hne : u ≠ [] := by
      rintro rfl
      simp only [List.nil_append, Head] at hh
      rcases hh with h | ⟨_, h⟩ <;> cases h
    rcases list_snoc u hne with ⟨v, a, rfl⟩
    rcases isBinary_append.mp hu with ⟨hv, ha1⟩
    cases ha1 with
    | cons ha _ =>
      have heq : (v ++ [a]) ++ 2 :: List.replicate n 0 = v ++ [a, 2] ++ List.replicate n 0 := by
        simp [List.append_assoc]
      rw [heq]
      exact ⟨v ++ [1 + a, 0] ++ List.replicate n 0, b, Carry.inside v a n b hv ha⟩

lemma record_progress (b : Nat) (ds : List Nat)
    (hs : Segment true b ds) (hb : b ≤ 3) :
    (∃ ds' b', Carry ds b ds' b') ∨ (IsBinary ds ∧ (b = 1 ∨ b = 2)) :=
  word_progress b ds (num_tail hs.1) hs.2.1 hb

lemma segment_progress (b : Nat) (ds : List Nat)
    (hs : Segment false b ds) (hb : b ≤ 3) :
    (∃ k, ds = 2 :: List.replicate k 0) ∨
    (∃ ds' b', Carry ds b ds' b') ∨
    (IsBinary ds ∧ (b = 1 ∨ b = 2)) := by
  rcases hs with ⟨hn, hh, _⟩
  rcases ds with _ | ⟨d, ds⟩
  · contradiction
  · rcases hh with rfl | ⟨rfl, _⟩
    · exact Or.inr (word_progress b (1 :: ds) (num_tail hn) (Or.inl rfl) hb)
    · left
      cases hn with
      | two k => exact ⟨k, rfl⟩

inductive Records where
  | REnd (ds : List Nat)
  | RMore (ds : List Nat) (b : Nat) (rs : Records)

open Records

def Good : Bool → Records → Prop
  | p, REnd ds => Segment p 0 ds
  | p, RMore ds b rs => Segment p b ds ∧ (1 ≤ b ∧ b ≤ 3) ∧ Good true rs

inductive Advance : Records → List (List Nat × Nat) → Records → Prop where
  | AEnd (ds ds' : List Nat) :
      Carry ds 0 ds' 0 → Advance (REnd ds) [] (REnd ds')
  | AStop (ds : List Nat) (b : Nat) (ds' : List Nat) (b' : Nat) (rs : Records) :
      0 < b → Carry ds b ds' b' →
      Advance (RMore ds b rs) [] (RMore ds' b' rs)
  | AGo (ds : List Nat) (b : Nat) (rs : Records) (bs : List (List Nat × Nat)) (rs' : Records) :
      IsBinary ds → (b = 1 ∨ b = 2) →
      Advance rs bs rs' →
      Advance (RMore ds b rs) ((ds, b - 1) :: bs) rs'

inductive AllBlocks (p : Bool) : List (List Nat × Nat) → Prop where
  | nil : AllBlocks p []
  | cons {x : List Nat × Nat} {bs : List (List Nat × Nat)} :
      Block p x → AllBlocks p bs → AllBlocks p (x :: bs)

lemma advance_total (rs : Records) (h : Good true rs) :
    ∃ bs rs', Advance rs bs rs' ∧ AllBlocks true bs ∧ Good false rs' := by
  induction rs with
  | REnd ds =>
    rcases record_progress 0 ds h (by omega) with ⟨ds', b', hc⟩ | ⟨_, hb⟩
    · have hb' := carry_zero hc
      subst hb'
      exact ⟨[], REnd ds', Advance.AEnd ds ds' hc, AllBlocks.nil, carry_segment true hc h⟩
    · omega
  | RMore ds b rs ih =>
    rcases h with ⟨hs, hb, hr⟩
    rcases record_progress b ds hs hb.2 with ⟨ds', b', hc⟩ | ⟨hd, hb12⟩
    · exact ⟨[], RMore ds' b' rs, Advance.AStop ds b ds' b' rs (by omega) hc,
        AllBlocks.nil, carry_segment true hc hs, carry_header hc hb, hr⟩
    · rcases ih hr with ⟨bs, rs', ha, hbs, hg⟩
      exact ⟨(ds, b - 1) :: bs, rs', Advance.AGo ds b rs bs rs' hd hb12 ha,
        AllBlocks.cons (scanned_block true b hs hd hb12) hbs, hg⟩

def measure (ds : List Nat) : Nat := prefix_value 7 (ds.map Nat.succ)

def first_digits : Records → List Nat
  | REnd ds => ds
  | RMore ds _ _ => ds

def protected_digits (bs : List (List Nat × Nat)) (rs : Records) : List Nat :=
  match bs with
  | [] => first_digits rs
  | (ds, _) :: _ => ds

lemma segment_length {p : Bool} {b : Nat} {ds : List Nat} (h : Segment p b ds) :
    7 ≤ ds.length := by
  have hl := h.2.2.2
  omega

lemma carry_bound {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hl : 7 ≤ ds.length) :
    measure ds' ≤ 1 + measure ds := by
  cases hc with
  | inside u a n b hu ha =>
    unfold measure
    simp only [List.map_append, List.map_cons, List.map_nil]
    have ha1 : (1 + a).succ = 1 + (a + 1) := by omega
    rw [ha1]
    have h := (prefix_carry 7 (u.map Nat.succ) (a + 1) ((List.replicate n 0).map Nat.succ)).2
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  | last u a b hu ha hb =>
    unfold measure
    simp only [List.map_append, List.map_cons, List.map_nil]
    have ha1 : (1 + a).succ = 1 + (a + 1) := by omega
    rw [ha1]
    refine (prefix_last 7 (u.map Nat.succ) (a + 1) ?_).2
    simp only [List.length_append, List.length_singleton] at hl
    simp only [List.length_map]
    omega

lemma advance_bound {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (ha : Advance rs bs rs') (hg : Good true rs) :
    measure (protected_digits bs rs') ≤ 1 + measure (first_digits rs) := by
  cases ha with
  | AEnd ds ds' hc =>
    exact carry_bound hc (segment_length hg)
  | AStop ds b ds' b' rs _ hc =>
    exact carry_bound hc (segment_length hg.1)
  | AGo =>
    simp only [protected_digits, first_digits]
    omega

lemma carry_not_scan {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) : False := by
  cases hc with
  | inside u a n b _ _ =>
    rcases isBinary_append.mp hd with ⟨hu2, _⟩
    rcases isBinary_append.mp hu2 with ⟨_, ha2⟩
    cases ha2 with
    | cons _ h2 =>
      cases h2 with
      | cons hbad _ => omega
  | last _ _ _ _ _ hb' => omega

lemma advance_go {ds : List Nat} {b : Nat} {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (ha : Advance (RMore ds b rs) bs rs') (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    ∃ bs', bs = (ds, b - 1) :: bs' ∧ Advance rs bs' rs' := by
  cases ha with
  | AStop _ _ _ _ _ _ hc =>
    exact False.elim (carry_not_scan hc hd hb)
  | AGo _ _ _ bs' _ _ _ ha' =>
    exact ⟨bs', rfl, ha'⟩

def seed_offset : List Nat := [1, 1, 0, 1, 1, 0, 1]

lemma seed_binary : IsBinary seed_offset := by
  repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)

lemma seed_segment : Segment true 1 seed_offset := by
  refine ⟨num_binary seed_binary true, Or.inl rfl, ⟨by decide, by decide⟩, by decide⟩

lemma seed_measure : measure seed_offset = 236 := rfl

-- ============================================================================
-- Section 3: Record Chains, Cap Rules, Stack & Ready Progress (Others_v1.v:666-1510)
-- ============================================================================

lemma digits_app (u v : List Nat) : digits (u ++ v) = digits u ++ digits v := by
  unfold digits
  exact List.flatMap_append

lemma last7_snoc (b : Nat) {u : List Nat} (a : Nat) (l r : zB)
    (hb : b = 1 ∨ b = 2) (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l ((z0 ^ b) +> ((z1 ^ 7) +> (digits (u ++ [a]) +> ([0, 0, 0] +> r))))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((z1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits (u ++ [1 + a]) +> ([0] +> r)))) := by
  have h_lhs : digits (u ++ [a]) +> ([0, 0, 0] +> r) =
      digits u +> ((z0 ^ (1 + a)) +> ([1, 1, 0, 0, 0] +> r)) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, List.append_nil, append_assoc, append_cons, append_nil]
  have h_rhs : digits (u ++ [1 + a]) +> ([0] +> r) =
      digits u +> ((z0 ^ (2 + a)) +> ([1, 1, 0] +> r)) := by
    rw [digits_app]
    have h2a : 2 + a = 1 + (1 + a) := by omega
    simp only [digits_cons, digits_nil, List.append_nil, append_assoc, append_cons, append_nil, h2a]
  rw [h_lhs, h_rhs]
  exact last7 b u a l r hb hu ha

lemma last7_inside (b : Nat) {u : List Nat} (a n : Nat) (l r : zB)
    (hb : b = 1 ∨ b = 2) (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l ((z0 ^ b) +> ((z1 ^ 7) +> (digits (u ++ [a, 2] ++ List.replicate n 0) +> r)))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((z1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r))) := by
  have h_lhs : digits (u ++ [a, 2] ++ List.replicate n 0) +> r =
      digits (u ++ [a]) +> ([0, 0, 0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, zLp_succ, zLp_zero, z0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  have h_rhs : digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r =
      digits (u ++ [1 + a]) +> ([0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, zLp_succ, zLp_zero, z0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h_lhs, h_rhs]
  exact last7_snoc b a l ([1, 1] +> (digits (List.replicate n 0) +> r)) hb hu ha

lemma last7_blank (b : Nat) {u : List Nat} (a : Nat) (l : zB)
    (hb : b = 1 ∨ b = 2) (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l ((z0 ^ b) +> ((z1 ^ 7) +> (digits (u ++ [a]) +> default)))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((z1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits (u ++ [1 + a]) +> default))) := by
  have h := last7_snoc b a l default hb hu ha
  simpa only [append_cons, append_nil, z00] using h

def records_side : Records → zB
  | REnd ds => digits ds +> default
  | RMore ds b rs => digits ds +> ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs))

def record_stack (bs : List (List Nat × Nat)) (l : zB) : zB :=
  bs.foldl (fun l x => [0] +> ((z1 ^ (2 + x.2)) +> pending x.1 ((z0 ^ 5) +> l))) l

lemma advance_spec {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (ha : Advance rs bs rs') (h : Nat) (l : zB) (hh : h = 1 ∨ h = 2) :
    (stepCfg l ((z0 ^ h) +> ((z1 ^ 7) +> records_side rs))) [tm24]⊢⁺
      (stepCfg ([1] +> record_stack bs ([0] +> ((z1 ^ (1 + h)) +> l)))
        ([0, 0, 1, 1, 1] +> records_side rs')) := by
  induction ha generalizing h l with
  | AEnd ds ds' hc =>
    simp only [records_side, record_stack, List.foldl_nil]
    cases hc with
    | inside u a n _ hu ha => exact last7_inside h a n l default hh hu ha
    | last u a _ hu ha _ => exact last7_blank h a l hh hu ha
  | AStop ds b ds' b' rs hbpos hc =>
    simp only [records_side, record_stack, List.foldl_nil]
    cases hc with
    | inside u a n _ hu ha =>
      exact last7_inside h a n l ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs)) hh hu ha
    | last u a _ hu ha hb03 =>
      have hb3 : b = 3 := by omega
      subst hb3
      exact last7_snoc h a l ((z1 ^ 7) +> records_side rs) hh hu ha
  | AGo ds b rs bs rs' hd hb12 _ ih =>
    simp only [records_side, record_stack, List.foldl_cons]
    refine zSp (scan_seven hh l (digits ds +> ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs)))) ?_
    refine zSp (scan_digits hd ((z0 ^ 6) +> ((z1 ^ (1 + h)) +> l)) ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs))) ?_
    have hstep := ih b (pending ds ((z0 ^ 6) +> ((z1 ^ (1 + h)) +> l))) hb12
    have h6 : (z0 ^ 6) +> ((z1 ^ (1 + h)) +> l) = (z0 ^ 5) +> ([0] +> ((z1 ^ (1 + h)) +> l)) := by
      simp [zLp_succ, z0, append_assoc]
    have hb2 : 2 + (b - 1) = 1 + b := by omega
    rw [h6] at hstep
    rw [hb2]
    exact hstep

lemma reset_rule {rs : Records} (hr : Good true rs) :
    ∃ bs rs', AllBlocks true ((seed_offset, 0) :: bs) ∧ Good false rs' ∧
      (cap_entry [2, 2, 1, 2, 2, 1, 1] 3 (records_side rs)) [tm24]⊢⁺
        (stepCfg ([1] +> record_stack ((seed_offset, 0) :: bs) (put_left [4] default))
          ([0, 0, 1, 1, 1] +> records_side rs')) := by
  have hg : Good true (RMore seed_offset 1 rs) := ⟨seed_segment, ⟨by omega, by omega⟩, hr⟩
  rcases advance_total (RMore seed_offset 1 rs) hg with ⟨bs, rs', ha, hb, hg'⟩
  rcases advance_go ha seed_binary (Or.inl rfl) with ⟨bs', rfl, _⟩
  refine ⟨bs', rs', hb, hg', ?_⟩
  refine zPt (bridge3 (records_side rs)) ?_
  exact advance_spec ha 2 ([1] +> default) (Or.inr rfl)

inductive Cap where
  | C0
  | C1
  | C2
  | C3
  deriving DecidableEq

open Cap

def cap_word : Cap → List Nat
  | C0 => [4]
  | C1 => [3, 3, 3]
  | C2 => [4, 3, 3, 2, 2, 2]
  | C3 => [3, 3, 2, 3, 3, 2, 2, 3]

def cap_prefix : Cap → List Nat
  | C0 => []
  | C1 => [2, 2]
  | C2 => [3, 2, 2, 1, 1]
  | C3 => [2, 2, 1, 2, 2, 1, 1]

def cap_height : Cap → Nat
  | C0 => 4
  | C1 => 3
  | C2 => 2
  | C3 => 3

def cap_bound : Cap → Nat
  | C0 => 236
  | C1 => 238
  | C2 => 240
  | C3 => 242

def next_cap : Cap → Cap
  | C0 => C1
  | C1 => C2
  | C2 => C3
  | C3 => C0

lemma cap_prefix_spec (c : Cap) {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (hc : c ≠ C3) (ha : Advance rs bs rs') :
    (cap_entry (cap_prefix c) (cap_height c) (records_side rs)) [tm24]⊢⁺
      (stepCfg ([1] +> record_stack bs (put_left (cap_word (next_cap c)) default))
        ([0, 0, 1, 1, 1] +> records_side rs')) := by
  cases c with
  | C0 =>
    refine zPt (bridge0 (records_side rs)) ?_
    have hb1 : IsBinary [1] := IsBinary.cons (by decide) IsBinary.nil
    refine zSp (scan_digits hb1 (put_left [3] default) ([0, 0] +> ((z1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 2 (pending [1] (put_left [3] default)) (Or.inr rfl)
  | C1 =>
    refine zPt (bridge1 (records_side rs)) ?_
    have hb100 : IsBinary [1, 0, 0] :=
      IsBinary.cons (by decide) (IsBinary.cons (by decide) (IsBinary.cons (by decide) IsBinary.nil))
    refine zSp (scan_digits hb100 (put_left [4, 3] default) ([0] +> ((z1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 1 (pending [1, 0, 0] (put_left [4, 3] default)) (Or.inl rfl)
  | C2 =>
    refine zPt (bridge2 (records_side rs)) ?_
    have hb101100 : IsBinary [1, 0, 1, 1, 0, 0] := by
      repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)
    refine zSp (scan_digits hb101100 (put_left [3] default) ([0, 0] +> ((z1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 2 (pending [1, 0, 1, 1, 0, 0] (put_left [3] default)) (Or.inr rfl)
  | C3 => contradiction

lemma cap_rule (c : Cap) {rs : Records}
    (hg : Good true rs) (hm : measure (first_digits rs) ≤ 1 + cap_bound c) :
    ∃ bs rs', AllBlocks true bs ∧ Good false rs' ∧
      measure (protected_digits bs rs') ≤ cap_bound (next_cap c) ∧
      (cap_entry (cap_prefix c) (cap_height c) (records_side rs)) [tm24]⊢⁺
        (stepCfg ([1] +> record_stack bs (put_left (cap_word (next_cap c)) default))
          ([0, 0, 1, 1, 1] +> records_side rs')) := by
  cases c with
  | C0 =>
    rcases advance_total rs hg with ⟨bs, rs', ha, hb, hr⟩
    have hmb := advance_bound ha hg
    exact ⟨bs, rs', hb, hr, by simp [cap_bound, next_cap] at hm ⊢; omega, cap_prefix_spec C0 (by decide) ha⟩
  | C1 =>
    rcases advance_total rs hg with ⟨bs, rs', ha, hb, hr⟩
    have hmb := advance_bound ha hg
    exact ⟨bs, rs', hb, hr, by simp [cap_bound, next_cap] at hm ⊢; omega, cap_prefix_spec C1 (by decide) ha⟩
  | C2 =>
    rcases advance_total rs hg with ⟨bs, rs', ha, hb, hr⟩
    have hmb := advance_bound ha hg
    exact ⟨bs, rs', hb, hr, by simp [cap_bound, next_cap] at hm ⊢; omega, cap_prefix_spec C2 (by decide) ha⟩
  | C3 =>
    rcases reset_rule hg with ⟨bs, rs', hb, hr, hs⟩
    refine ⟨(seed_offset, 0) :: bs, rs', hb, hr, ?_, hs⟩
    simp only [protected_digits, cap_bound, next_cap, seed_measure, le_refl]

lemma records_zero {p : Bool} {rs : Records} (h : Good p rs) :
    ∃ r, records_side rs = [0] +> r := by
  cases rs with
  | REnd ds =>
    rcases ds with _ | ⟨d, ds⟩
    · exact False.elim h.2.1
    · refine ⟨((z0 ^ d) ++ [1, 1] ++ digits ds) +> default, ?_⟩
      simp only [records_side, digits_cons, zLp_succ', z0,
        List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil, append_assoc]
  | RMore ds b rs =>
    rcases ds with _ | ⟨d, ds⟩
    · exact False.elim h.1.2.1
    · refine ⟨((z0 ^ d) ++ [1, 1] ++ digits ds) +> ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs)), ?_⟩
      simp only [records_side, digits_cons, zLp_succ', z0,
        List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil, append_assoc]

lemma return_separator (l r : zB) (hr : ∃ r', r = [0] +> r') :
    (returnCfg ([0, 0] +> ((z1 ^ 4) +> l)) r) [tm24]⊢*
      (l <{{A}} ((z1 ^ 8) +> r)) := by
  rcases hr with ⟨r', rfl⟩
  exact close2 l r'

lemma return_six (l r : zB) (hr : ∃ r', r = [0] +> r') :
    (returnCfg ((z0 ^ 6) +> l) r) [tm24]⊢*
      (stepCfg ([1] +> ([0] +> l)) ([0, 0, 1, 1, 1] +> r)) := by
  rcases hr with ⟨r', rfl⟩
  exact close6 l r'

lemma emit_block (ds : List Nat) (n : Nat) (l r : zB) :
    (([0] +> ((z1 ^ (2 + n)) +> pending ds l)) <{{A}} ((z1 ^ 8) +> r)) [tm24]⊢*
      (returnCfg l (digits ds +> ((z0 ^ (2 + n)) +> ((z1 ^ 7) +> r)))) := by
  refine zSt (block_back ds n l r) ?_
  unfold backCfg returnCfg
  have h1 : ([0, 0, 0] : zF) +> (back_word ds +> ((z0 ^ (1 + n)) +> ((z1 ^ 7) +> r))) =
      [0, 0] +> ([0] +> (back_word ds +> ((z0 ^ (1 + n)) +> ((z1 ^ 7) +> r)))) := rfl
  have h2n : 2 + n = 1 + (1 + n) := by omega
  rw [h1, zero_back_word, h2n, z07 z0 (1 + n) ((z1 ^ 7) +> r)]
  finish

inductive Stack where
  | SCap (c : Cap)
  | SPush (six : Bool) (older : Stack) (ds : List Nat) (n : Nat)

open Stack

def stack_good : Stack → Prop
  | SCap _ => True
  | SPush six older ds n => stack_good older ∧ Block six (ds, n)

def stack_side : Stack → zB
  | SCap c => put_left (cap_word c) default
  | SPush six older ds n =>
      [0] +> ((z1 ^ (2 + n)) +> pending ds
        (if six then (z0 ^ 5) +> stack_side older
         else [0, 0] +> ((z1 ^ 4) +> stack_side older)))

def stack_cap : Stack → Cap
  | SCap c => c
  | SPush _ older _ _ => stack_cap older

def stack_protected : Stack → List Nat → List Nat
  | SCap _, ds => ds
  | SPush _ older pfx _, _ => stack_protected older pfx

lemma stack_zero (st : Stack) : ∃ l, stack_side st = [0] +> l := by
  rcases st with ⟨_ | _ | _ | _⟩ | ⟨six, older, ds, n⟩ <;> {
    dsimp only [stack_side, cap_word, put_left, List.foldl]
    exact ⟨_, rfl⟩
  }

def active (st : Stack) (rs : Records) : Cfg (Fin 2) (Fin 6) :=
  stepCfg ([1] +> stack_side st) ([0, 0, 1, 1, 1] +> records_side rs)

def restored : Stack → Records → Cfg (Fin 2) (Fin 6)
  | SCap c, rs => cap_entry (cap_prefix c) (cap_height c) (records_side rs)
  | SPush true older ds n, rs => active older (RMore ds (2 + n) rs)
  | SPush false older ds n, rs => restored older (RMore ds (2 + n) rs)

lemma emitted_good (p : Bool) {ds : List Nat} {n : Nat} {rs : Records}
    (hb : Block p (ds, n)) (hr : Good true rs) :
    Good (!p) (RMore ds (2 + n) rs) := by
  refine ⟨emitted_segment hb, ⟨by omega, ?_⟩, hr⟩
  have hn := hb.2.1
  dsimp only at hn
  omega

lemma cap_emit (c : Cap) (r : zB) :
    ((put_left (cap_word c) default) <{{A}} ((z1 ^ 8) +> r)) [tm24]⊢*
      (cap_entry (cap_prefix c) (cap_height c) r) := by
  cases c <;> {
    unfold put_left cap_word cap_entry cap_prefix cap_height root stepCfg payload
    simp only [List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.flatMap_nil,
      zLp_succ, zLp_zero, z0, z1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  }

lemma stack_return (st : Stack) (rs : Records)
    (hl : stack_good st) (hr : Good true rs) :
    ((stack_side st) <{{A}} ((z1 ^ 8) +> records_side rs)) [tm24]⊢* (restored st rs) := by
  induction st generalizing rs with
  | SCap c => exact cap_emit c (records_side rs)
  | SPush six older ds n ih =>
    rcases hl with ⟨hl', hb⟩
    rcases six with _ | _
    · simp only [stack_side, restored, ↓reduceIte]
      refine zSt (emit_block ds n ([0, 0] +> ((z1 ^ 4) +> stack_side older)) (records_side rs)) ?_
      have hg' := emitted_good false hb hr
      refine zSt (return_separator (stack_side older) (records_side (RMore ds (2 + n) rs)) (records_zero hg')) ?_
      exact ih (RMore ds (2 + n) rs) hl' hg'
    · simp only [stack_side, restored, ↓reduceIte]
      refine zSt (emit_block ds n ((z0 ^ 5) +> stack_side older) (records_side rs)) ?_
      have hg' := emitted_good true hb hr
      rcases stack_zero older with ⟨l, hst⟩
      unfold active
      rw [hst]
      have h6 : (z0 ^ 5) +> ([0] +> l) = (z0 ^ 6) +> l := by
        simp [zLp_succ, z0, append_assoc]
      rw [h6]
      exact return_six l (records_side (RMore ds (2 + n) rs)) (records_zero hg')

lemma restored_good (st : Stack) (rs : Records)
    (hl : stack_good st) (hr : Good true rs) :
    (∃ st' rs', restored st rs = active st' rs' ∧
      stack_good st' ∧ Good false rs' ∧ stack_cap st' = stack_cap st ∧
      stack_protected st' (first_digits rs') = stack_protected st (first_digits rs)) ∨
    (∃ rs', restored st rs =
      cap_entry (cap_prefix (stack_cap st)) (cap_height (stack_cap st)) (records_side rs') ∧
      Good true rs' ∧ first_digits rs' = stack_protected st (first_digits rs)) := by
  induction st generalizing rs with
  | SCap c =>
    exact Or.inr ⟨rs, rfl, hr, rfl⟩
  | SPush six older ds n ih =>
    rcases hl with ⟨hl', hb⟩
    rcases six with _ | _
    · exact ih (RMore ds (2 + n) rs) hl' (emitted_good false hb hr)
    · exact Or.inl ⟨older, RMore ds (2 + n) rs, rfl, hl', emitted_good true hb hr, rfl, rfl⟩

lemma carry_word {u : List Nat} (a : Nat) (l r : zB)
    (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l (digits (u ++ [a]) +> ([0, 0, 0] +> r))) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a]) +> ([0] +> r))) := by
  have h_lhs : digits (u ++ [a]) +> ([0, 0, 0] +> r) =
      digits u +> ((z0 ^ (1 + a)) +> ([1, 1, 0, 0, 0] +> r)) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h_lhs]
  have h1 := ordinary_return hu ha l r
  refine z02 h1 ?_
  unfold backCfg returnCfg
  have h2 : ([0, 0, 0] : zF) +> (back_word u +> ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      [0, 0] +> ([0] +> (back_word u +> ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r)))) := rfl
  have h_rhs : digits u +> ([0] +> ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      digits (u ++ [1 + a]) +> ([0] +> r) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, zLp_succ', z0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h2, zero_back_word, h_rhs]
  finish

lemma carry_inside {u : List Nat} (a n : Nat) (l r : zB)
    (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l (digits (u ++ [a, 2] ++ List.replicate n 0) +> r)) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r)) := by
  have h_lhs : digits (u ++ [a, 2] ++ List.replicate n 0) +> r =
      digits (u ++ [a]) +> ([0, 0, 0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, zLp_succ, zLp_zero, z0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  have h_rhs : digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r =
      digits (u ++ [1 + a]) +> ([0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, zLp_succ, zLp_zero, z0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h_lhs, h_rhs]
  exact carry_word a l ([1, 1] +> (digits (List.replicate n 0) +> r)) hu ha

lemma carry_blank {u : List Nat} (a : Nat) (l : zB)
    (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l (digits (u ++ [a]) +> default)) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a]) +> default)) := by
  have h := carry_word a l default hu ha
  simpa only [append_cons, append_nil, z00] using h

lemma carry_records_spec {rs rs' : Records} (ha : Advance rs [] rs') (l : zB) :
    (stepCfg l (records_side rs)) [tm24]⊢⁺ (returnCfg l (records_side rs')) := by
  cases ha with
  | AEnd ds ds' hc =>
    simp only [records_side]
    cases hc with
    | inside u a n _ hu ha => exact carry_inside a n l default hu ha
    | last u a _ hu ha _ => exact carry_blank a l hu ha
  | AStop ds b ds' b' tail _ hc =>
    simp only [records_side]
    cases hc with
    | inside u a n _ hu ha =>
      exact carry_inside a n l ((z0 ^ b) +> ((z1 ^ 7) +> records_side tail)) hu ha
    | last u a _ hu ha hb03 =>
      have hb3 : b = 3 := by omega
      subst hb3
      exact carry_word a l ((z1 ^ 7) +> records_side tail) hu ha

lemma carry_records_good (p : Bool) {rs rs' : Records}
    (ha : Advance rs [] rs') (hg : Good p rs) : Good (!p) rs' := by
  cases ha with
  | AEnd ds ds' hc => exact carry_segment p hc hg
  | AStop ds b ds' b' tail _ hc =>
    rcases hg with ⟨hs, hb, hr⟩
    exact ⟨carry_segment p hc hs, carry_header hc hb, hr⟩

lemma active_return {st : Stack} {rs rs' : Records}
    (hl : stack_good st) (hr : Good false rs) (ha : Advance rs [] rs') :
    (active st rs) [tm24]⊢⁺ (restored st rs') := by
  have hg : Good true rs' := carry_records_good false ha hr
  unfold active
  refine zSp (active_scan (stack_side st) (records_side rs)) ?_
  refine z02 (carry_records_spec ha ([0, 0] +> ((z1 ^ 4) +> stack_side st))) ?_
  refine zSt (return_separator (stack_side st) (records_side rs') (records_zero hg)) ?_
  exact stack_return st rs' hl hg

def extend_stack (bs : List (List Nat × Nat)) (st : Stack) : Stack :=
  bs.foldl (fun st x => SPush true st x.1 x.2) st

@[simp] lemma record_stack_nil (l : zB) : record_stack [] l = l := rfl
@[simp] lemma record_stack_cons (x : List Nat × Nat) (bs : List (List Nat × Nat)) (l : zB) :
    record_stack (x :: bs) l =
      record_stack bs ([0] +> ((z1 ^ (2 + x.2)) +> pending x.1 ((z0 ^ 5) +> l))) := rfl
@[simp] lemma extend_stack_nil (st : Stack) : extend_stack [] st = st := rfl
@[simp] lemma extend_stack_cons (x : List Nat × Nat) (bs : List (List Nat × Nat)) (st : Stack) :
    extend_stack (x :: bs) st = extend_stack bs (SPush true st x.1 x.2) := rfl

lemma extend_side (bs : List (List Nat × Nat)) (st : Stack) :
    stack_side (extend_stack bs st) = record_stack bs (stack_side st) := by
  induction bs generalizing st with
  | nil => rfl
  | cons x bs ih =>
    rw [extend_stack_cons, record_stack_cons, ih (SPush true st x.1 x.2)]
    rfl

lemma extend_good {bs : List (List Nat × Nat)} {st : Stack}
    (hb : AllBlocks true bs) (hl : stack_good st) :
    stack_good (extend_stack bs st) := by
  induction hb generalizing st with
  | nil => exact hl
  | @cons x bs hbx _ ih => exact ih ⟨hl, hbx⟩

lemma extend_cap (bs : List (List Nat × Nat)) (st : Stack) :
    stack_cap (extend_stack bs st) = stack_cap st := by
  induction bs generalizing st with
  | nil => rfl
  | cons x bs ih => exact ih (SPush true st x.1 x.2)

lemma extend_protected (bs : List (List Nat × Nat)) (st : Stack) (rs : Records) :
    stack_protected (extend_stack bs st) (first_digits rs) =
    stack_protected st (protected_digits bs rs) := by
  induction bs generalizing st with
  | nil => rfl
  | cons x bs ih => exact ih (SPush true st x.1 x.2)

lemma active_constructor {st : Stack} {ds : List Nat} {b : Nat} {rs : Records}
    (hl : stack_good st) (hs : Segment false b ds) (hr : Good true rs)
    (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    ∃ st' rs', stack_good st' ∧ Good false rs' ∧
      stack_cap st' = stack_cap st ∧
      stack_protected st' (first_digits rs') = stack_protected st ds ∧
      (active st (RMore ds b rs)) [tm24]⊢⁺ (active st' rs') := by
  rcases advance_total rs hr with ⟨bs, rs', ha, hbs, hg⟩
  refine ⟨extend_stack bs (SPush false st ds (b - 1)), rs',
    extend_good hbs ⟨hl, scanned_block false b hs hd hb⟩, hg,
    extend_cap bs (SPush false st ds (b - 1)),
    extend_protected bs (SPush false st ds (b - 1)) rs', ?_⟩
  unfold active
  rw [extend_side]
  simp only [records_side, stack_side, ↓reduceIte]
  refine zSp (active_scan (stack_side st) (digits ds +> ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs)))) ?_
  refine zSp (scan_digits hd ([0, 0] +> ((z1 ^ 4) +> stack_side st)) ((z0 ^ b) +> ((z1 ^ 7) +> records_side rs))) ?_
  have hstep := advance_spec ha b (pending ds ([0, 0] +> ((z1 ^ 4) +> stack_side st))) hb
  have hb2 : 2 + (b - 1) = 1 + b := by omega
  rw [hb2]
  exact hstep

def Source (st : Stack) (rs : Records) : Prop :=
  stack_good st ∧ Good false rs ∧
  measure (stack_protected st (first_digits rs)) ≤ cap_bound (stack_cap st)

lemma prefix_app (n : Nat) (u v : List Nat) (h : n ≤ u.length) :
    prefix_value n (u ++ v) = prefix_value n u := by
  induction u generalizing n with
  | nil =>
    have hn : n = 0 := by simpa using h
    subst hn
    rfl
  | cons d u ih =>
    rcases n with _ | k
    · rfl
    · simp only [List.length_cons] at h
      simp only [List.cons_append, prefix_value, ih k (by omega)]

lemma measure_app (u v : List Nat) (h : 7 ≤ u.length) :
    measure (u ++ v) = measure u := by
  unfold measure
  rw [List.map_append]
  exact prefix_app 7 (u.map Nat.succ) (v.map Nat.succ) (by simpa using h)

lemma long_measure (k : Nat) (hk : 6 ≤ k) :
    measure (2 :: List.replicate k 0) = 255 := by
  have hk' : k = 6 + (k - 6) := by omega
  rw [hk', List.replicate_add, ← List.cons_append]
  rw [measure_app (2 :: List.replicate 6 0) (List.replicate (k - 6) 0) (by decide)]
  rfl

lemma long_segment (b k : Nat) (hs : Segment false b (2 :: List.replicate k 0)) (hb : b ≤ 3) :
    (b = 0 ∧ oddB k = true) ∨ ((b = 1 ∨ b = 3) ∧ oddB k = false) := by
  rcases hs with ⟨_, _, ⟨hl, hm⟩, _⟩
  simp only [List.length_cons, List.length_replicate, mass, mass_zeros] at hl hm
  rw [odd_succ] at hl
  have hm' : 1 + 2 + k + b = k + (3 + b) := by omega
  rw [hm', odd_add] at hm
  rcases b with _ | _ | _ | _ | b
  · cases hodd : oddB k <;> simp_all [oddB]
  · cases hodd : oddB k <;> simp_all [oddB]
  · cases hodd : oddB k <;> simp_all [oddB]
  · cases hodd : oddB k <;> simp_all [oddB]
  · omega

lemma source_long_marked (st : Stack) (b k : Nat)
    (hs : Segment false b (2 :: List.replicate k 0))
    (hm : measure (stack_protected st (2 :: List.replicate k 0)) ≤ cap_bound (stack_cap st)) :
    ∃ six older ds n, st = SPush six older ds n := by
  rcases st with ⟨c⟩ | ⟨six, older, ds, n⟩
  · have hl := segment_length hs
    simp only [List.length_cons, List.length_replicate] at hl
    simp only [stack_protected, stack_cap] at hm
    rw [long_measure k (by omega)] at hm
    cases c <;> simp [cap_bound] at hm
  · exact ⟨six, older, ds, n, rfl⟩

def merged (ds : List Nat) (n k : Nat) : List Nat :=
  ds ++ [n, 1, 1, 0] ++ List.replicate k 0

lemma merged_succ (ds : List Nat) (n k : Nat) :
    merged ds n (1 + k) = merged ds n k ++ [0] := by
  unfold merged
  have hk : 1 + k = k + 1 := by omega
  rw [hk, List.replicate_add]
  simp [List.append_assoc]

lemma zeros_binary (k : Nat) : IsBinary (List.replicate k 0) := by
  induction k with
  | zero => exact IsBinary.nil
  | succ k ih => exact IsBinary.cons (by omega) ih

lemma merged_binary {ds : List Nat} {n : Nat} (k : Nat)
    (hd : IsBinary ds) (hn : n ≤ 1) : IsBinary (merged ds n k) := by
  unfold merged
  refine isBinary_append.mpr ⟨isBinary_append.mpr ⟨hd, ?_⟩, zeros_binary k⟩
  exact IsBinary.cons hn (IsBinary.cons (by decide) (IsBinary.cons (by decide) (IsBinary.cons (by decide) IsBinary.nil)))

lemma merged_length (ds : List Nat) (n k : Nat) :
    (merged ds n k).length = ds.length + 4 + k := by
  unfold merged
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]

lemma merged_mass (ds : List Nat) (n k : Nat) :
    mass (merged ds n k) = mass ds + 6 + n + k := by
  unfold merged
  rw [mass_app, mass_app, mass_zeros]
  simp only [mass]
  omega

lemma merged_segment (p : Bool) {ds : List Nat} {n : Nat} (b k : Nat)
    (hb : Block p (ds, n)) (hs : Segment false b (2 :: List.replicate k 0)) :
    Segment p b (merged ds n k) := by
  dsimp only [Block] at hb
  rcases hb with ⟨hd, hn, hh, ⟨hl, hm⟩, hmin⟩
  rcases hs with ⟨_, _, ⟨hk, hsum⟩, _⟩
  have h1 : (1 + n == 0) = false := by cases n <;> rfl
  rw [h1] at hl
  simp only [List.length_cons, List.length_replicate, mass, mass_zeros] at hk hsum
  refine ⟨num_binary (merged_binary k hd hn) p, ?_, ⟨?_, ?_⟩, ?_⟩
  · rcases ds with _ | ⟨d, ds⟩
    · exact False.elim hh
    · simp only [Head, merged, List.cons_append] at hh ⊢
      rcases hh with h | ⟨_, h⟩
      · exact Or.inl h
      · cases h
  · rw [merged_length]
    have hlen_eq : ds.length + 4 + k = k + (1 + (1 + (1 + (1 + ds.length)))) := by omega
    rw [hlen_eq, odd_add, odd_next, odd_next, odd_next, odd_next, Bool.not_not, Bool.not_not, hl]
    have h2 : (!false) = true := rfl
    rw [h2, Bool.xor_true]
    rw [odd_succ] at hk
    exact hk
  · have hmass_eq : mass (merged ds n k) + b = (mass ds + (1 + n)) + (1 + (1 + (1 + 2 + k + b))) := by
      rw [merged_mass]; omega
    rw [hmass_eq, odd_add, hm, odd_next, odd_next, Bool.not_not, hsum, Bool.xor_false]
  · rw [merged_length]
    cases (b == 0) <;> { simp only [Bool.false_eq_true, ↓reduceIte]; omega }

lemma merged_block (p : Bool) {ds : List Nat} {n : Nat} (k : Nat)
    (hb : Block p (ds, n)) (hs : Segment false 1 (2 :: List.replicate k 0)) :
    Block p (merged ds n k, 0) :=
  scanned_block p 1 (merged_segment p 1 k hb hs) (merged_binary k hb.1 hb.2.1) (Or.inl rfl)

lemma merged_bump_segment (p : Bool) {ds : List Nat} {n : Nat} (b k : Nat)
    (hb : Block p (ds, n)) (hs : Segment false b (2 :: List.replicate (1 + k) 0))
    (hb03 : b = 0 ∨ b = 3) :
    Segment (!p) (b - 2) (merged ds n k ++ [1]) := by
  have hs' := merged_segment p b (1 + k) hb hs
  rw [merged_succ] at hs'
  exact segment_last (merged_binary k hb.1 hb.2.1) (by omega) hs' hb03

lemma stack_measure (st : Stack) {u v : List Nat} (h : measure u = measure v) :
    measure (stack_protected st u) = measure (stack_protected st v) := by
  cases st <;> simp [stack_protected, h]

lemma merged_measure (ds : List Nat) (n k : Nat) (h : 7 ≤ ds.length) :
    measure (merged ds n k) = measure ds := by
  unfold merged
  rw [List.append_assoc]
  exact measure_app ds ([n, 1, 1, 0] ++ List.replicate k 0) h

lemma bumped_measure (ds : List Nat) (n k : Nat) (h : 7 ≤ ds.length) :
    measure (merged ds n k ++ [1]) = measure ds := by
  unfold merged
  simp only [List.append_assoc]
  exact measure_app ds ([n, 1, 1, 0] ++ (List.replicate k 0 ++ [1])) h

lemma pending_app (u v : List Nat) (l : zB) :
    pending (u ++ v) l = pending v (pending u l) := by
  unfold pending
  exact List.foldl_append

lemma merged_pending (ds : List Nat) (n k : Nat) (l : zB) :
    pending (merged ds n k) l =
    pending ([1, 0] ++ List.replicate k 0)
      ([0] +> ((z1 ^ 3) +> ([0] +> ((z1 ^ (2 + n)) +> pending ds l)))) := by
  unfold merged
  rw [pending_app, pending_app, pending_app]
  simp only [pending_cons, pending_nil]

lemma long_scan (k : Nat) (l r : zB) :
    (stepCfg ([1] +> l) ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate k 0) +> r))) [tm24]⊢⁺
      (stepCfg (pending ([1, 0] ++ List.replicate k 0) ([0] +> ((z1 ^ 3) +> l))) r) := by
  have hd : ([0, 0, 1, 1, 1] : zF) +> (digits (2 :: List.replicate k 0) +> r) =
      [0, 0, 1, 1, 1, 0, 0, 0] +> ([1, 1] +> (digits (List.replicate k 0) +> r)) := by
    simp only [digits_cons, zLp_succ, zLp_zero, z0, List.cons_append, List.nil_append, append_assoc]
    rfl
  rw [hd]
  refine z02 (active_turn l ([1, 1] +> (digits (List.replicate k 0) +> r))) ?_
  have hd2 : ([0, 0, 1, 1, 0] : zF) +> ([1, 1] +> (digits (List.replicate k 0) +> r)) =
      digits ([1, 0] ++ List.replicate k 0) +> r := by
    simp only [List.cons_append, List.nil_append, digits_cons, zLp_succ, zLp_zero, z0, append_assoc]
    rfl
  rw [hd2]
  have hbin : IsBinary ([1, 0] ++ List.replicate k 0) :=
    IsBinary.cons (by decide) (IsBinary.cons (by decide) (zeros_binary k))
  exact scan_digits hbin ([0] +> ((z1 ^ 3) +> l)) r

lemma long_pending (ds : List Nat) (n k : Nat) (l r : zB) :
    (stepCfg ([1] +> ([0] +> ((z1 ^ (2 + n)) +> pending ds l)))
      ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate k 0) +> r))) [tm24]⊢⁺
      (stepCfg (pending (merged ds n k) l) r) := by
  rw [merged_pending]
  exact long_scan k ([0] +> ((z1 ^ (2 + n)) +> pending ds l)) r

lemma pending_carry (u : List Nat) (a : Nat) (l r : zB) :
    (stepCfg (pending (u ++ [a]) l) ([0, 0, 0] +> r)) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a]) +> ([0] +> r))) := by
  rw [pending_app]
  simp only [pending_cons, pending_nil]
  refine z02 (start_back a (pending u l) r) ?_
  refine zSt (pending_back u l ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r))) ?_
  unfold backCfg returnCfg
  have h1 : ([0, 0, 0] : zF) +> (back_word u +> ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      [0, 0] +> ([0] +> (back_word u +> ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r)))) := rfl
  have h_rhs : digits u +> ([0] +> ((z0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      digits (u ++ [1 + a]) +> ([0] +> r) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, zLp_succ', z0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h1, zero_back_word, h_rhs]
  finish

lemma long_pending_return (ds : List Nat) (n k : Nat) (l r : zB) :
    (stepCfg ([1] +> ([0] +> ((z1 ^ (2 + n)) +> pending ds l)))
      ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate (1 + k) 0) +> ([0, 0, 0] +> r)))) [tm24]⊢⁺
      (returnCfg l (digits (merged ds n k ++ [1]) +> ([0] +> r))) := by
  refine zPt (long_pending ds n (1 + k) l ([0, 0, 0] +> r)) ?_
  rw [merged_succ]
  exact pending_carry (merged ds n k) 0 l r

lemma long_pending_blank (ds : List Nat) (n k : Nat) (l : zB) :
    (stepCfg ([1] +> ([0] +> ((z1 ^ (2 + n)) +> pending ds l)))
      ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate (1 + k) 0) +> default))) [tm24]⊢⁺
      (returnCfg l (digits (merged ds n k ++ [1]) +> default)) := by
  have h := long_pending_return ds n k l default
  simpa only [append_cons, append_nil, z00] using h

def return_to (six : Bool) (older : Stack) (rs : Records) : Cfg (Fin 2) (Fin 6) :=
  if six then active older rs else restored older rs

lemma finish_return (six : Bool) (older : Stack) (rs : Records)
    (hl : stack_good older) (hr : Good (!six) rs) :
    (returnCfg
      (if six then (z0 ^ 5) +> stack_side older else [0, 0] +> ((z1 ^ 4) +> stack_side older))
      (records_side rs)) [tm24]⊢* (return_to six older rs) := by
  rcases six with _ | _
  · simp only [return_to, ↓reduceIte]
    refine zSt (return_separator (stack_side older) (records_side rs) (records_zero hr)) ?_
    exact stack_return older rs hl hr
  · simp only [return_to, ↓reduceIte]
    unfold active
    rcases stack_zero older with ⟨l, hst⟩
    rw [hst]
    have h6 : (z0 ^ 5) +> ([0] +> l) = (z0 ^ 6) +> l := by
      simp [zLp_succ, z0, append_assoc]
    rw [h6]
    exact return_six l (records_side rs) (records_zero hr)

inductive Ready : Cfg (Fin 2) (Fin 6) → Prop where
  | ReadyP (st : Stack) (rs : Records) : Source st rs → Ready (active st rs)
  | ReadyCap (c : Cap) (rs : Records) :
      Good true rs → measure (first_digits rs) ≤ 1 + cap_bound c →
      Ready (cap_entry (cap_prefix c) (cap_height c) (records_side rs))

open Ready

lemma cap_progress (c : Cap) (rs : Records)
    (hr : Good true rs) (hm : measure (first_digits rs) ≤ 1 + cap_bound c) :
    ∃ q, Ready q ∧ (cap_entry (cap_prefix c) (cap_height c) (records_side rs)) [tm24]⊢⁺ q := by
  rcases cap_rule c hr hm with ⟨bs, rs', hb, hg, hv, hs⟩
  refine ⟨active (extend_stack bs (SCap (next_cap c))) rs', ?_, ?_⟩
  · refine ReadyP _ _ ⟨extend_good hb trivial, hg, ?_⟩
    rw [extend_protected, extend_cap]
    exact hv
  · unfold active
    rw [extend_side]
    exact hs

lemma restored_ready (st : Stack) (rs : Records)
    (hl : stack_good st) (hr : Good true rs)
    (hm : measure (stack_protected st (first_digits rs)) ≤ cap_bound (stack_cap st)) :
    Ready (restored st rs) := by
  rcases restored_good st rs hl hr with ⟨st', rs', he, hl', hr', hc, hp⟩ | ⟨rs', he, hr', hp⟩
  · rw [he]
    refine ReadyP st' rs' ⟨hl', hr', ?_⟩
    rw [hc, hp]
    exact hm
  · rw [he]
    refine ReadyCap (stack_cap st) rs' hr' ?_
    rw [hp]
    omega

lemma carry_records_bound (p : Bool) {rs rs' : Records}
    (ha : Advance rs [] rs') (hg : Good p rs) :
    measure (first_digits rs') ≤ 1 + measure (first_digits rs) := by
  cases ha with
  | AEnd ds ds' hc => exact carry_bound hc (segment_length hg)
  | AStop ds b ds' b' tail _ hc => exact carry_bound hc (segment_length hg.1)

lemma ordinary_progress (st : Stack) (rs rs' : Records)
    (hs : Source st rs) (ha : Advance rs [] rs') :
    Ready (restored st rs') ∧ (active st rs) [tm24]⊢⁺ (restored st rs') := by
  rcases hs with ⟨hl, hr, hm⟩
  refine ⟨?_, active_return hl hr ha⟩
  have hg : Good true rs' := carry_records_good false ha hr
  rcases st with ⟨c⟩ | ⟨six, older, ds, n⟩
  · refine ReadyCap c rs' hg ?_
    have hb := carry_records_bound false ha hr
    simp only [stack_protected, stack_cap] at hm
    omega
  · exact restored_ready (SPush six older ds n) rs' hl hg hm

lemma constructor_progress (st : Stack) (ds : List Nat) (b : Nat) (rs : Records)
    (hs : Source st (RMore ds b rs)) (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    ∃ q, Ready q ∧ (active st (RMore ds b rs)) [tm24]⊢⁺ q := by
  rcases hs with ⟨hl, ⟨hseg, hb13, hr⟩, hm⟩
  rcases active_constructor hl hseg hr hd hb with ⟨st', rs', hl', hr', hc, hp, ht⟩
  refine ⟨active st' rs', ReadyP st' rs' ⟨hl', hr', ?_⟩, ht⟩
  rw [hc, hp]
  exact hm

lemma return_to_ready (six : Bool) (older : Stack) (rs : Records)
    (hl : stack_good older) (hr : Good (!six) rs)
    (hm : measure (stack_protected older (first_digits rs)) ≤ cap_bound (stack_cap older)) :
    Ready (return_to six older rs) := by
  rcases six with _ | _
  · exact restored_ready older rs hl hr hm
  · exact ReadyP older rs ⟨hl, hr, hm⟩

lemma long_constructor_progress (six : Bool) (older : Stack) (ds : List Nat) (n k : Nat) (rs : Records)
    (hs : Source (SPush six older ds n) (RMore (2 :: List.replicate k 0) 1 rs)) :
    ∃ q, Ready q ∧ (active (SPush six older ds n) (RMore (2 :: List.replicate k 0) 1 rs)) [tm24]⊢⁺ q := by
  rcases hs with ⟨⟨hl, hb⟩, ⟨hseg, _, hr⟩, hm⟩
  rcases advance_total rs hr with ⟨bs, rs', ha, hbs, hg⟩
  refine ⟨active (extend_stack bs (SPush six older (merged ds n k) 0)) rs', ?_, ?_⟩
  · refine ReadyP _ _ ⟨extend_good hbs ⟨hl, merged_block six k hb hseg⟩, hg, ?_⟩
    rw [extend_cap, extend_protected]
    simp only [stack_cap, stack_protected] at hm ⊢
    rw [stack_measure older (merged_measure ds n k (block_length hb))]
    exact hm
  · unfold active
    rw [extend_side]
    simp only [stack_side, records_side]
    refine zPt (long_pending ds n k
      (if six then (z0 ^ 5) +> stack_side older else [0, 0] +> ((z1 ^ 4) +> stack_side older))
      ((z0 ^ 1) +> ((z1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 1 (pending (merged ds n k)
      (if six then (z0 ^ 5) +> stack_side older else [0, 0] +> ((z1 ^ 4) +> stack_side older))) (Or.inl rfl)

lemma long_end_progress (six : Bool) (older : Stack) (ds : List Nat) (n k : Nat)
    (hs : Source (SPush six older ds n) (REnd (2 :: List.replicate (1 + k) 0))) :
    ∃ q, Ready q ∧ (active (SPush six older ds n) (REnd (2 :: List.replicate (1 + k) 0))) [tm24]⊢⁺ q := by
  rcases hs with ⟨⟨hl, hb⟩, hseg, hm⟩
  have hg : Good (!six) (REnd (merged ds n k ++ [1])) :=
    merged_bump_segment six 0 k hb hseg (Or.inl rfl)
  refine ⟨return_to six older (REnd (merged ds n k ++ [1])), ?_, ?_⟩
  · refine return_to_ready six older (REnd (merged ds n k ++ [1])) hl hg ?_
    simp only [first_digits, stack_protected, stack_cap] at hm ⊢
    rw [stack_measure older (bumped_measure ds n k (block_length hb))]
    exact hm
  · unfold active
    simp only [stack_side, records_side]
    refine z02 (long_pending_blank ds n k
      (if six then (z0 ^ 5) +> stack_side older else [0, 0] +> ((z1 ^ 4) +> stack_side older))) ?_
    exact finish_return six older (REnd (merged ds n k ++ [1])) hl hg

lemma long_three_progress (six : Bool) (older : Stack) (ds : List Nat) (n k : Nat) (rs : Records)
    (hs : Source (SPush six older ds n) (RMore (2 :: List.replicate (1 + k) 0) 3 rs)) :
    ∃ q, Ready q ∧ (active (SPush six older ds n) (RMore (2 :: List.replicate (1 + k) 0) 3 rs)) [tm24]⊢⁺ q := by
  rcases hs with ⟨⟨hl, hb⟩, ⟨hseg, _, hr⟩, hm⟩
  have hg : Good (!six) (RMore (merged ds n k ++ [1]) 1 rs) :=
    ⟨merged_bump_segment six 3 k hb hseg (Or.inr rfl), ⟨by omega, by omega⟩, hr⟩
  refine ⟨return_to six older (RMore (merged ds n k ++ [1]) 1 rs), ?_, ?_⟩
  · refine return_to_ready six older (RMore (merged ds n k ++ [1]) 1 rs) hl hg ?_
    simp only [first_digits, stack_protected, stack_cap] at hm ⊢
    rw [stack_measure older (bumped_measure ds n k (block_length hb))]
    exact hm
  · unfold active
    simp only [stack_side, records_side]
    have h03 : (z0 ^ 3) +> ((z1 ^ 7) +> records_side rs) = [0, 0, 0] +> ((z1 ^ 7) +> records_side rs) := rfl
    rw [h03]
    refine z02 (long_pending_return ds n k
      (if six then (z0 ^ 5) +> stack_side older else [0, 0] +> ((z1 ^ 4) +> stack_side older))
      ((z1 ^ 7) +> records_side rs)) ?_
    exact finish_return six older (RMore (merged ds n k ++ [1]) 1 rs) hl hg

lemma source_progress (st : Stack) (rs : Records) (h : Source st rs) :
    ∃ q, Ready q ∧ (active st rs) [tm24]⊢⁺ q := by
  cases rs with
  | REnd ds =>
    rcases h.2 with ⟨hs, hm⟩
    rcases segment_progress 0 ds hs (by omega) with ⟨k, rfl⟩ | ⟨ds', b', hc⟩ | ⟨_, hb⟩
    · rcases source_long_marked st 0 k hs hm with ⟨six, older, ds, n, rfl⟩
      rcases k with _ | k
      · have hl := segment_length hs
        simp at hl
      · have hk1 : k + 1 = 1 + k := by omega
        rw [hk1] at h ⊢
        exact long_end_progress six older ds n k h
    · have hb' := carry_zero hc
      subst hb'
      rcases ordinary_progress st (REnd ds) (REnd ds') h (Advance.AEnd ds ds' hc) with ⟨hr, hstep⟩
      exact ⟨restored st (REnd ds'), hr, hstep⟩
    · omega
  | RMore ds b rs =>
    rcases h.2 with ⟨⟨hs, hb, hr⟩, hm⟩
    rcases segment_progress b ds hs hb.2 with ⟨k, rfl⟩ | ⟨ds', b', hc⟩ | ⟨hd, hb12⟩
    · rcases source_long_marked st b k hs hm with ⟨six, older, ds, n, rfl⟩
      rcases long_segment b k hs hb.2 with ⟨rfl, _⟩ | ⟨hb13, _⟩
      · omega
      · rcases hb13 with rfl | rfl
        · exact long_constructor_progress six older ds n k rs h
        · rcases k with _ | k
          · have hl := segment_length hs
            simp at hl
          · have hk1 : k + 1 = 1 + k := by omega
            rw [hk1] at h ⊢
            exact long_three_progress six older ds n k rs h
    · rcases ordinary_progress st (RMore ds b rs) (RMore ds' b' rs) h
        (Advance.AStop ds b ds' b' rs (by omega) hc) with ⟨hr', hstep⟩
      exact ⟨restored st (RMore ds' b' rs), hr', hstep⟩
    · exact constructor_progress st ds b rs h hd hb12

lemma ready_progress (q : Cfg (Fin 2) (Fin 6)) (h : Ready q) :
    ∃ q', Ready q' ∧ q [tm24]⊢⁺ q' := by
  cases h with
  | ReadyP st rs hs => exact source_progress st rs hs
  | ReadyCap c rs hr hm => exact cap_progress c rs hr hm

lemma source_nonhalt {st : Stack} {rs : Records} (h : Source st rs) :
    NeverHaltsFrom tm24 (active st rs) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant ?_ (ReadyP st rs h)
  intro c hc
  rcases ready_progress c hc with ⟨c', hc', hstep⟩
  exact ⟨c', hstep, hc'⟩

lemma neverHaltsFrom_of_reachesStar {M : Machine (Fin 2) (Fin 6)} {c₁ c₀ : Cfg (Fin 2) (Fin 6)}
    (hinit : c₁ [M]⊢* c₀) (h_never : NeverHaltsFrom M c₀) : NeverHaltsFrom M c₁ := by
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M c₁ k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, BusyBeaver.multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never cfg ⟨k - k₀, hk⟩

-- ============================================================================
-- Section 4: State-Permutation Reduction from `TM25` (`#306`) to `TM24`
-- (`Others_v1.v:1512-1570`)
-- ============================================================================

local infixr:67 " ::ᵇ " => Turing.ListBlank.cons

def state_map : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0
  | 4 => 4
  | 5 => 5

def mapCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map state_map, c.tape⟩

lemma step_mapCfg (c : Cfg (Fin 2) (Fin 6)) :
    step tm24 (mapCfg c) = (step target_tm c).map mapCfg := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    (try rfl) <;>
    omega

lemma multiStep_mapCfg (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep tm24 (mapCfg c) n = (multiStep target_tm c n).map mapCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [zMs, zMs, ih]
    rcases multiStep target_tm c n with _ | c'
    · rfl
    · exact step_mapCfg c'

lemma neverHaltsFrom_of_mapCfg {c₀ : Cfg (Fin 2) (Fin 6)}
    (h : NeverHaltsFrom tm24 (mapCfg c₀)) : NeverHaltsFrom target_tm c₀ := by
  intro cfg ⟨n, hn⟩
  have hm : (mapCfg c₀) [tm24]⊢* (mapCfg cfg) := by
    refine ⟨n, ?_⟩
    rw [multiStep_mapCfg, hn]
    rfl
  have hstep := h (mapCfg cfg) hm
  rcases hst : step target_tm cfg with _ | c'
  · rw [step_mapCfg, hst] at hstep
    cases hstep
  · rfl

def entry_stack : Stack :=
  SPush false (SCap C2) [1, 1, 0, 1, 1, 1, 0] 1

def entry_records : Records :=
  REnd [1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1]

lemma entry_source : Source entry_stack entry_records := by
  have hb1 : IsBinary [1, 1, 0, 1, 1, 1, 0] := by
    repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)
  have hb2 : IsBinary [1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1] := by
    repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)
  refine ⟨⟨trivial, hb1, by decide, Or.inl rfl, ⟨by decide, by decide⟩, by decide⟩,
    ⟨num_binary hb2 false, Or.inl rfl, ⟨by decide, by decide⟩, by decide⟩,
    by decide⟩

def init_cfg_0 : Cfg (Fin 2) (Fin 6) :=
  (default {{B}}> default)

def init_cfg_1 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))

def init_cfg_2 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))

def init_cfg_3 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))

def init_cfg_4 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_5 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))

def init_cfg_6 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_7 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))

def init_cfg_8 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_9 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))

def init_cfg_10 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_11 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))

def init_cfg_12 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_13 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_14 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_15 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))

def init_cfg_16 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_17 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))

def init_cfg_18 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_19 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_20 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))

def init_cfg_21 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_22 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))

def init_cfg_23 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_24 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_25 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_26 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ default)) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_27 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_28 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_29 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_30 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def init_cfg_31 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))

def init_cfg_32 : Cfg (Fin 2) (Fin 6) :=
  ((0 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ default)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) {{D}}> (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ (0 ::ᵇ (0 ::ᵇ (1 ::ᵇ (1 ::ᵇ default))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

lemma init_step_0 : init_cfg_0 [tm24]⊢* init_cfg_1 := by
  dsimp only [init_cfg_0, init_cfg_1]
  execute

lemma init_step_1 : init_cfg_1 [tm24]⊢* init_cfg_2 := by
  dsimp only [init_cfg_1, init_cfg_2]
  execute

lemma init_step_2 : init_cfg_2 [tm24]⊢* init_cfg_3 := by
  dsimp only [init_cfg_2, init_cfg_3]
  execute

lemma init_step_3 : init_cfg_3 [tm24]⊢* init_cfg_4 := by
  dsimp only [init_cfg_3, init_cfg_4]
  execute

lemma init_step_4 : init_cfg_4 [tm24]⊢* init_cfg_5 := by
  dsimp only [init_cfg_4, init_cfg_5]
  execute

lemma init_step_5 : init_cfg_5 [tm24]⊢* init_cfg_6 := by
  dsimp only [init_cfg_5, init_cfg_6]
  execute

lemma init_step_6 : init_cfg_6 [tm24]⊢* init_cfg_7 := by
  dsimp only [init_cfg_6, init_cfg_7]
  execute

lemma init_step_7 : init_cfg_7 [tm24]⊢* init_cfg_8 := by
  dsimp only [init_cfg_7, init_cfg_8]
  execute

lemma init_step_8 : init_cfg_8 [tm24]⊢* init_cfg_9 := by
  dsimp only [init_cfg_8, init_cfg_9]
  execute

lemma init_step_9 : init_cfg_9 [tm24]⊢* init_cfg_10 := by
  dsimp only [init_cfg_9, init_cfg_10]
  execute

lemma init_step_10 : init_cfg_10 [tm24]⊢* init_cfg_11 := by
  dsimp only [init_cfg_10, init_cfg_11]
  execute

lemma init_step_11 : init_cfg_11 [tm24]⊢* init_cfg_12 := by
  dsimp only [init_cfg_11, init_cfg_12]
  execute

lemma init_step_12 : init_cfg_12 [tm24]⊢* init_cfg_13 := by
  dsimp only [init_cfg_12, init_cfg_13]
  execute

lemma init_step_13 : init_cfg_13 [tm24]⊢* init_cfg_14 := by
  dsimp only [init_cfg_13, init_cfg_14]
  execute

lemma init_step_14 : init_cfg_14 [tm24]⊢* init_cfg_15 := by
  dsimp only [init_cfg_14, init_cfg_15]
  execute

lemma init_step_15 : init_cfg_15 [tm24]⊢* init_cfg_16 := by
  dsimp only [init_cfg_15, init_cfg_16]
  execute

lemma init_step_16 : init_cfg_16 [tm24]⊢* init_cfg_17 := by
  dsimp only [init_cfg_16, init_cfg_17]
  execute

lemma init_step_17 : init_cfg_17 [tm24]⊢* init_cfg_18 := by
  dsimp only [init_cfg_17, init_cfg_18]
  execute

lemma init_step_18 : init_cfg_18 [tm24]⊢* init_cfg_19 := by
  dsimp only [init_cfg_18, init_cfg_19]
  execute

lemma init_step_19 : init_cfg_19 [tm24]⊢* init_cfg_20 := by
  dsimp only [init_cfg_19, init_cfg_20]
  execute

lemma init_step_20 : init_cfg_20 [tm24]⊢* init_cfg_21 := by
  dsimp only [init_cfg_20, init_cfg_21]
  execute

lemma init_step_21 : init_cfg_21 [tm24]⊢* init_cfg_22 := by
  dsimp only [init_cfg_21, init_cfg_22]
  execute

lemma init_step_22 : init_cfg_22 [tm24]⊢* init_cfg_23 := by
  dsimp only [init_cfg_22, init_cfg_23]
  execute

lemma init_step_23 : init_cfg_23 [tm24]⊢* init_cfg_24 := by
  dsimp only [init_cfg_23, init_cfg_24]
  execute

lemma init_step_24 : init_cfg_24 [tm24]⊢* init_cfg_25 := by
  dsimp only [init_cfg_24, init_cfg_25]
  execute

lemma init_step_25 : init_cfg_25 [tm24]⊢* init_cfg_26 := by
  dsimp only [init_cfg_25, init_cfg_26]
  execute

lemma init_step_26 : init_cfg_26 [tm24]⊢* init_cfg_27 := by
  dsimp only [init_cfg_26, init_cfg_27]
  execute

lemma init_step_27 : init_cfg_27 [tm24]⊢* init_cfg_28 := by
  dsimp only [init_cfg_27, init_cfg_28]
  execute

lemma init_step_28 : init_cfg_28 [tm24]⊢* init_cfg_29 := by
  dsimp only [init_cfg_28, init_cfg_29]
  execute

lemma init_step_29 : init_cfg_29 [tm24]⊢* init_cfg_30 := by
  dsimp only [init_cfg_29, init_cfg_30]
  execute

lemma init_step_30 : init_cfg_30 [tm24]⊢* init_cfg_31 := by
  dsimp only [init_cfg_30, init_cfg_31]
  execute

lemma init_step_31 : init_cfg_31 [tm24]⊢* init_cfg_32 := by
  dsimp only [init_cfg_31, init_cfg_32]
  execute

set_option maxRecDepth 20000 in
lemma mapped_entry : init_cfg_32 = active entry_stack entry_records := rfl

lemma init_to_entry :
    (mapCfg (init [])) [tm24]⊢* active entry_stack entry_records := by
  have h0 : (mapCfg (init []) : Cfg (Fin 2) (Fin 6)) = init_cfg_0 := rfl
  rw [h0, ← mapped_entry]
  refine zSt init_step_0 ?_
  refine zSt init_step_1 ?_
  refine zSt init_step_2 ?_
  refine zSt init_step_3 ?_
  refine zSt init_step_4 ?_
  refine zSt init_step_5 ?_
  refine zSt init_step_6 ?_
  refine zSt init_step_7 ?_
  refine zSt init_step_8 ?_
  refine zSt init_step_9 ?_
  refine zSt init_step_10 ?_
  refine zSt init_step_11 ?_
  refine zSt init_step_12 ?_
  refine zSt init_step_13 ?_
  refine zSt init_step_14 ?_
  refine zSt init_step_15 ?_
  refine zSt init_step_16 ?_
  refine zSt init_step_17 ?_
  refine zSt init_step_18 ?_
  refine zSt init_step_19 ?_
  refine zSt init_step_20 ?_
  refine zSt init_step_21 ?_
  refine zSt init_step_22 ?_
  refine zSt init_step_23 ?_
  refine zSt init_step_24 ?_
  refine zSt init_step_25 ?_
  refine zSt init_step_26 ?_
  refine zSt init_step_27 ?_
  refine zSt init_step_28 ?_
  refine zSt init_step_29 ?_
  refine zSt init_step_30 ?_
  exact init_step_31


-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  neverHaltsFrom_of_mapCfg (neverHaltsFrom_of_reachesStar init_to_entry (source_nonhalt entry_source))

end BusyBeaver.M_1RB0LE_1RC0LF_0LD0RC_1RA1LD_1LB0LE_HHH0RE
