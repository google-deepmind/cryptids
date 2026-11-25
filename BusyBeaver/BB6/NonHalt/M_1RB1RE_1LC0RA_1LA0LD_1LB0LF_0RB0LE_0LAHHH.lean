/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat

/-!
# Busy Beaver Machine `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

@[expose] public section

/-- Transition function for `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-! ### Local Counted-Stepping Tactics -/

private theorem rcast {M : Machine Γ Λ} {m n : ℕ} {c₁ c₂ : Cfg Γ Λ}
    (h : ReachesIn M m c₁ c₂) (e : m = n) : ReachesIn M n c₁ c₂ :=
  e ▸ h

local macro "bb_refl_in" : tactic =>
  `(tactic| (
    try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
      List.cons_append, List.nil_append, List.append_nil,
      ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_default_default, ListBlank.cons_zero_default]
    exact ReachesIn.zero _ _))

local macro "bb_step_in" : tactic =>
  `(tactic| (
    refine ReachesIn.step_left (by
        try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
          List.cons_append, List.nil_append, List.append_nil,
          ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
          ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
          ListBlank.cons_default_default, ListBlank.cons_zero_default]
        rfl) ?_
    try simp only [Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_default_default, ListBlank.cons_zero_default]))

local macro "bb_steps_in" : tactic =>
  `(tactic| repeat (first | bb_refl_in | bb_step_in))

/-! ### Part 1: Tape Words, Transitions, Towers, & Era Lemmas -/
inductive Mode : Type
  | mA
  | mD
  | mE
  | mHalt
  deriving DecidableEq, Repr


inductive RTok : Type
  | pair (z o c : ℕ)
  | mid (c : ℕ)
  deriving DecidableEq, Repr


def pWord (z o : ℕ) : List (Fin 2) :=
  List.replicate z 0 ++ List.replicate (o + 1) 1

def wZ : List (Fin 2) := [0, 0, 1]

def wT : List (Fin 2) := [0, 1, 1]

def wLM : List (Fin 2) := [0, 1, 1, 0, 0, 1, 0, 0, 1]

def wRM : List (Fin 2) := [0, 1, 1, 0, 1, 1, 0, 0, 1]


def encR : List RTok → ListBlank (Fin 2)
  | [] => default
  | .pair z o c :: ts => ((pWord z o) ^ (c + 1)) +> encR ts
  | .mid c :: ts => (wRM ^ (c + 1)) +> encR ts

def cfgA (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight 0 l r

def cfgD (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft 3 l r

def cfgE (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft 4 l r

def cfgHalt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft 5 ((1 : Fin 2) >> l) r


private theorem pow_zero_list {α : Type*} (u : List α) : u ^ 0 = [] := rfl

private theorem pow_one_list {α : Type*} (u : List α) : u ^ 1 = u := by
  rw [pow_succ_list, pow_zero_list, List.append_nil]


def decPairR (z o c : ℕ) (ts : List RTok) : List RTok :=
  match c with
  | 0 => ts
  | c' + 1 => .pair z o c' :: ts

def decMidR (c : ℕ) (ts : List RTok) : List RTok :=
  match c with
  | 0 => ts
  | c' + 1 => .mid c' :: ts


def pushRM (k : ℕ) (R : List RTok) : List RTok :=
  match k with
  | 0 => R
  | k' + 1 =>
    match R with
    | .mid c :: ts => .mid (c + k' + 1) :: ts
    | ts => .mid k' :: ts

def coalesceR : List RTok → List RTok
  | .pair 1 1 1 :: .pair 2 0 c1 :: rest =>
    pushRM 1 (decPairR 2 0 c1 rest)
  | R => R

def pushRPPre (z o k' : ℕ) : List RTok → List RTok
  | .pair z' o' c :: ts =>
    if z == z' && o == o' then .pair z o (c + k' + 1) :: ts
    else .pair z o k' :: .pair z' o' c :: ts
  | ts => .pair z o k' :: ts

def pushRP (z o k : ℕ) (R : List RTok) : List RTok :=
  match k with
  | 0 => R
  | k' + 1 => coalesceR (pushRPPre z o k' R)


def pushWRMSem (k : ℕ) (R : List RTok) : List RTok :=
  match k with
  | 0 => R
  | k' + 1 =>
    pushRM k' (pushRP 1 1 2 (pushRP 2 0 1 R))


private theorem pWord_2_0 : pWord 2 0 = wZ := rfl
private theorem pWord_1_1 : pWord 1 1 = wT := rfl
private theorem pWord_1_2 : pWord 1 2 = [0, 1, 1, 1] := rfl
private theorem pWord_1_0 : pWord 1 0 = [0, 1] := rfl
private theorem pWord_0_0 : pWord 0 0 = [1] := rfl
private theorem pWord_0_1 : pWord 0 1 = [1, 1] := rfl


private theorem encR_decPairR (z o c : ℕ) (ts : List RTok) :
    (pWord z o) +> encR (decPairR z o c ts) = encR (.pair z o c :: ts) := by
  cases c with
  | zero => simp [decPairR, encR, pow_one_list]
  | succ c' =>
    simp only [decPairR, encR]
    rw [← ListBlank.append_pow_succ]

private theorem encR_decMidR (c : ℕ) (ts : List RTok) :
    wRM +> encR (decMidR c ts) = encR (.mid c :: ts) := by
  cases c with
  | zero => simp [decMidR, encR, pow_one_list]
  | succ c' =>
    simp only [decMidR, encR]
    rw [← ListBlank.append_pow_succ]


private theorem replicate_eq_pow {α : Type*} (n : ℕ) (a : α) :
    List.replicate n a = ([a] : List α) ^ n :=
  (singleton_pow a n).symm


private theorem pWord_zero_eq (o : ℕ) : pWord 0 o = ([1] : List (Fin 2)) ^ (o + 1) := by
  simp [pWord, replicate_eq_pow, pow_zero_list]


private theorem encR_pushRM (k : ℕ) (R : List RTok) :
    encR (pushRM k R) = (wRM ^ k) +> encR R := by
  cases k with
  | zero => rfl
  | succ k' =>
    cases R with
    | nil => simp [pushRM, encR]
    | cons t ts =>
      cases t with
      | pair z' o' c => simp [pushRM, encR]
      | mid c =>
        simp only [pushRM, encR, pow_append_pow]
        congr 2; omega

private theorem encR_coalesceR (R : List RTok) :
    encR (coalesceR R) = encR R := by
  unfold coalesceR
  split
  · rename_i c1 rest
    rw [encR_pushRM, pow_one_list]
    have htail := encR_decPairR 2 0 c1 rest
    rw [pWord_2_0] at htail
    have hrhs : encR (.pair 1 1 1 :: .pair 2 0 c1 :: rest) =
        (wT ^ 2) +> (wZ +> encR (decPairR 2 0 c1 rest)) := by
      rw [encR, htail, pWord_1_1]
    rw [hrhs]
    rfl
  · rfl

private theorem encR_pushRP (z o k : ℕ) (R : List RTok) :
    encR (pushRP z o k R) = ((pWord z o) ^ k) +> encR R := by
  cases k with
  | zero => rfl
  | succ k' =>
    simp only [pushRP, encR_coalesceR]
    cases R with
    | nil => simp [pushRPPre, encR]
    | cons t ts =>
      cases t with
      | mid _ => simp [pushRPPre, encR]
      | pair z' o' c =>
        simp only [pushRPPre]
        by_cases heq : ((z == z') && (o == o')) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true heq))]
          simp only [Bool.and_eq_true, beq_iff_eq] at heq
          rcases heq with ⟨rfl, rfl⟩
          simp only [encR, pow_append_pow]
          congr 2; omega
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false heq))]
          simp [encR]



private theorem encR_pushWRMSem (k : ℕ) (R : List RTok) :
    encR (pushWRMSem k R) = (wRM ^ k) +> encR R := by
  cases k with
  | zero => rfl
  | succ k' =>
    simp only [pushWRMSem, encR_pushRM, encR_pushRP, pWord_1_1, pWord_2_0]
    have h1 : (wT ^ 2) +> ((wZ ^ 1) +> encR R) = (wRM ^ 1) +> encR R := rfl
    rw [h1, pow_append_pow]


private theorem step_a_01 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2 (cfgA l ([0, 1] +> r)) (cfgA ([0, 1] +> l) r) := by
  dsimp only [cfgA]
  bb_steps_in

private theorem step_a_01_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (2 * k)
      (cfgA l ((([0, 1] : List (Fin 2)) ^ k) +> r))
      (cfgA ((([0, 1] : List (Fin 2)) ^ k) +> l) r)
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_a_01 l ((([0, 1] : List (Fin 2)) ^ k) +> r)
    have h2 := step_a_01_pow k ([0, 1] +> l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_a_101 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 3 (cfgA l ([1, 0, 1] +> r)) (cfgA (wZ +> l) r) := by
  dsimp only [cfgA, wZ]
  bb_steps_in

private theorem step_a_101_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (3 * k)
      (cfgA l ([1] +> ((wT ^ k) +> r)))
      (cfgA ((wZ ^ k) +> l) ([1] +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have heq : [1] +> (wT +> ((wT ^ k) +> r)) = [1, 0, 1] +> ([1] +> ((wT ^ k) +> r)) := rfl
    rw [heq]
    have h1 := step_a_101 l ([1] +> ((wT ^ k) +> r))
    have h2 := step_a_101_pow k (wZ +> l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_d_001 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 3 (cfgD (wZ +> l) r) (cfgD l (wT +> r)) := by
  dsimp only [cfgD, wZ, wT]
  bb_steps_in

private theorem step_d_001_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (3 * k)
      (cfgD ((wZ ^ k) +> l) r)
      (cfgD l ((wT ^ k) +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_d_001 ((wZ ^ k) +> l) r
    have h2 := step_d_001_pow k l (wT +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_e_one (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 1 (cfgE ([1] +> l) r) (cfgE l ([0] +> r)) := by
  dsimp only [cfgE]
  bb_steps_in

private theorem step_e_ones : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm k
      (cfgE ((([1] : List (Fin 2)) ^ k) +> l) r)
      (cfgE l ((([0] : List (Fin 2)) ^ k) +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_e_one ((([1] : List (Fin 2)) ^ k) +> l) r
    have h2 := step_e_ones k l ([0] +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)


private theorem exit_a_00 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 3 (cfgA l ([0, 0] +> r)) (cfgD l ([0, 1] +> r)) := by
  dsimp only [cfgA, cfgD]; bb_steps_in

private theorem exit_a_11 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2 (cfgA l ([1, 1] +> r)) (cfgE ([1] +> l) ([0] +> r)) := by
  dsimp only [cfgA, cfgE]; bb_steps_in

private theorem exit_a_100 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 6 (cfgA l ([1, 0, 0] +> r)) (cfgE ([1] +> l) ([0, 1] +> r)) := by
  dsimp only [cfgA, cfgE]; bb_steps_in

private theorem exit_d_11_halt (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 1 (cfgD ([1, 1] +> l) r) (cfgHalt l ([0] +> r)) := by
  dsimp only [cfgD, cfgHalt]; bb_steps_in

private theorem exit_d_100 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5 (cfgD ([1, 0, 0] +> l) r) (cfgD l ([0, 1, 0] +> r)) := by
  dsimp only [cfgD]; bb_steps_in

private theorem exit_d_101 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 8 (cfgD ([1, 0, 1] +> l) r) (cfgE ([1] +> l) ([0, 1] +> r)) := by
  dsimp only [cfgD, cfgE]; bb_steps_in

private theorem exit_d_01 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2 (cfgD ([0, 1] +> l) r) (cfgA ([0] +> l) ([1] +> r)) := by
  dsimp only [cfgD, cfgA]; bb_steps_in

private theorem exit_d_0000 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5 (cfgD ([0, 0, 0, 0] +> l) r) (cfgA ([0, 1] +> l) ([1, 1] +> r)) := by
  dsimp only [cfgD, cfgA]; bb_steps_in

private theorem exit_d_0001 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5 (cfgD ([0, 0, 0, 1] +> l) r) (cfgE ([1] +> l) ([0, 1, 1] +> r)) := by
  dsimp only [cfgD, cfgE]; bb_steps_in

private theorem exit_e_0_r1 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2 (cfgE ([0] +> l) ([1] +> r)) (cfgA ([0, 0] +> l) r) := by
  dsimp only [cfgE, cfgA]; bb_steps_in

private theorem exit_e_00_r0 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5 (cfgE ([0, 0] +> l) ([0] +> r)) (cfgA ([0, 1] +> l) ([1] +> r)) := by
  dsimp only [cfgE, cfgA]; bb_steps_in

private theorem exit_e_01_r0 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5 (cfgE ([0, 1] +> l) ([0] +> r)) (cfgE ([1] +> l) ([0, 1] +> r)) := by
  dsimp only [cfgE]; bb_steps_in


private theorem step_a_1011_wT (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 3 (cfgA l ([1, 0, 1, 1] +> (wT +> r)))
      (cfgA (wZ +> l) ([1, 0, 1, 1] +> r)) := by
  dsimp only [cfgA, wT, wZ]; bb_steps_in

private theorem step_a_1011_wT_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (3 * k)
      (cfgA l ([1, 0, 1, 1] +> ((wT ^ k) +> r)))
      (cfgA ((wZ ^ k) +> l) ([1, 0, 1, 1] +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_a_1011_wT l ((wT ^ k) +> r)
    have h2 := step_a_1011_wT_pow k (wZ +> l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_a_1011_wZ (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 15 (cfgA l ([1, 0, 1, 1] +> (wZ +> r)))
      (cfgA (wT +> l) ([1, 0, 1, 1] +> r)) := by
  dsimp only [cfgA, wZ, wT]; bb_steps_in

private theorem step_a_1011_wZ_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (15 * k)
      (cfgA l ([1, 0, 1, 1] +> ((wZ ^ k) +> r)))
      (cfgA ((wT ^ k) +> l) ([1, 0, 1, 1] +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_a_1011_wZ l ((wZ ^ k) +> r)
    have h2 := step_a_1011_wZ_pow k (wT +> l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_a_1011_wRM (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 21 (cfgA l ([1, 0, 1, 1] +> (wRM +> r)))
      (cfgA (wLM +> l) ([1, 0, 1, 1] +> r)) := by
  have heq : wRM +> r = wT +> (wT +> (wZ +> r)) := rfl
  rw [heq]
  have h1 := step_a_1011_wT l (wT +> (wZ +> r))
  have h2 := step_a_1011_wT (wZ +> l) (wZ +> r)
  have h3 := step_a_1011_wZ (wZ +> (wZ +> l)) r
  exact rcast (((h1.trans h2).trans h3)) (by omega)

private theorem step_a_1011_wRM_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (21 * k)
      (cfgA l ([1, 0, 1, 1] +> ((wRM ^ k) +> r)))
      (cfgA ((wLM ^ k) +> l) ([1, 0, 1, 1] +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_a_1011_wRM l ((wRM ^ k) +> r)
    have h2 := step_a_1011_wRM_pow k (wLM +> l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_e_1011_wZ (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 19 (cfgE ([1, 0, 1, 1] +> (wZ +> l)) r)
      (cfgE ([1, 0, 1, 1] +> l) (wT +> r)) := by
  dsimp only [cfgE, wZ, wT]; bb_steps_in

private theorem step_e_1011_wZ_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (19 * k)
      (cfgE ([1, 0, 1, 1] +> ((wZ ^ k) +> l)) r)
      (cfgE ([1, 0, 1, 1] +> l) ((wT ^ k) +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_e_1011_wZ ((wZ ^ k) +> l) r
    have h2 := step_e_1011_wZ_pow k l (wT +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_e_1011_wT (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 7 (cfgE ([1, 0, 1, 1] +> (wT +> l)) r)
      (cfgE ([1, 0, 1, 1] +> l) (wZ +> r)) := by
  dsimp only [cfgE, wT, wZ]; bb_steps_in

private theorem step_e_1011_wT_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (7 * k)
      (cfgE ([1, 0, 1, 1] +> ((wT ^ k) +> l)) r)
      (cfgE ([1, 0, 1, 1] +> l) ((wZ ^ k) +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_e_1011_wT ((wT ^ k) +> l) r
    have h2 := step_e_1011_wT_pow k l (wZ +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)

private theorem step_e_1011_wLM (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 45 (cfgE ([1, 0, 1, 1] +> (wLM +> l)) r)
      (cfgE ([1, 0, 1, 1] +> l) (wRM +> r)) := by
  have heq : wLM +> l = wT +> (wZ +> (wZ +> l)) := rfl
  rw [heq]
  have h1 := step_e_1011_wT (wZ +> (wZ +> l)) r
  have h2 := step_e_1011_wZ (wZ +> l) (wZ +> r)
  have h3 := step_e_1011_wZ l (wT +> (wZ +> r))
  exact rcast (((h1.trans h2).trans h3)) (by omega)

private theorem step_e_1011_wLM_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (45 * k)
      (cfgE ([1, 0, 1, 1] +> ((wLM ^ k) +> l)) r)
      (cfgE ([1, 0, 1, 1] +> l) ((wRM ^ k) +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_e_1011_wLM ((wLM ^ k) +> l) r
    have h2 := step_e_1011_wLM_pow k l (wRM +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)


private theorem step_dl_1_wZ (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5 (cfgD ([1] +> (wZ +> l)) ([0, 1] +> r))
      (cfgD ([1] +> l) ([0, 1] +> (wZ +> r))) := by
  dsimp only [cfgD, wZ]; bb_steps_in

private theorem step_dl_1_wZ_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (5 * k)
      (cfgD ([1] +> ((wZ ^ k) +> l)) ([0, 1] +> r))
      (cfgD ([1] +> l) ([0, 1] +> ((wZ ^ k) +> r)))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_dl_1_wZ ((wZ ^ k) +> l) r
    have h2 := step_dl_1_wZ_pow k l (wZ +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)


private theorem step_el_11_01 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 7 (cfgE ([1, 1] +> (wT +> l)) ([0, 1] +> r))
      (cfgE ([1, 1] +> l) ([0, 1] +> (wZ +> r))) := by
  dsimp only [cfgE, wT, wZ]; bb_steps_in

private theorem step_el_11_01_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (7 * k)
      (cfgE ([1, 1] +> ((wT ^ k) +> l)) ([0, 1] +> r))
      (cfgE ([1, 1] +> l) ([0, 1] +> ((wZ ^ k) +> r)))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_el_11_01 ((wT ^ k) +> l) r
    have h2 := step_el_11_01_pow k l (wZ +> r)
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)


private theorem step_ar_10101_wZ (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 31 (cfgA l ([1, 0, 1, 0, 1, 0, 1, 1] +> (wZ +> r)))
      (cfgA (wT +> l) ([1, 0, 1, 0, 1, 0, 1, 1] +> r)) := by
  dsimp only [cfgA, wZ, wT]; bb_steps_in

private theorem step_ar_10101_wZ_pow : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (31 * k)
      (cfgA l ([1, 0, 1, 0, 1, 0, 1, 1] +> ((wZ ^ k) +> r)))
      (cfgA ((wT ^ k) +> l) ([1, 0, 1, 0, 1, 0, 1, 1] +> r))
  | 0, l, r => ReachesIn.zero _ _
  | k + 1, l, r => by
    rw [ListBlank.append_pow_succ]
    have h1 := step_ar_10101_wZ l ((wZ ^ k) +> r)
    have h2 := step_ar_10101_wZ_pow k (wT +> l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    exact rcast ((h1.trans h2)) (by omega)


inductive MidItem : Type
  | mid (cnt : ℕ)
  | t (cnt : ℕ)
  | z (cnt : ℕ)
  deriving DecidableEq, Repr

def w3Item : MidItem → ℕ
  | .mid k => 3 * k
  | .t k => k
  | .z k => k

def w3Mid : List MidItem → ℕ
  | [] => 0
  | m :: ms => w3Item m + w3Mid ms

private theorem w3Mid_append : ∀ (xs ys : List MidItem),
    w3Mid (xs ++ ys) = w3Mid xs + w3Mid ys
  | [], ys => by simp [w3Mid]
  | m :: xs, ys => by
    simp only [List.cons_append, w3Mid, w3Mid_append xs ys]
    omega

def encMidItemR : MidItem → ListBlank (Fin 2) → ListBlank (Fin 2)
  | .mid k, r => (wRM ^ k) +> r
  | .t k, r => (wT ^ k) +> r
  | .z k, r => (wZ ^ k) +> r

def encMidR : List MidItem → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | m :: ms, r => encMidItemR m (encMidR ms r)

private theorem encMidR_append : ∀ (xs ys : List MidItem) (r : ListBlank (Fin 2)),
    encMidR (xs ++ ys) r = encMidR xs (encMidR ys r)
  | [], _, _ => rfl
  | _ :: xs, ys, r => by
    simp only [List.cons_append, encMidR, encMidR_append xs ys r]

def rebuildMR : List MidItem → List RTok → List RTok
  | [], tail => tail
  | .mid k :: ms, tail => pushWRMSem k (rebuildMR ms tail)
  | .t k :: ms, tail => pushRP 1 1 k (rebuildMR ms tail)
  | .z k :: ms, tail => pushRP 2 0 k (rebuildMR ms tail)

private theorem encR_rebuildMR : ∀ (ms : List MidItem) (tail : List RTok),
    encR (rebuildMR ms tail) = encMidR ms (encR tail)
  | [], _ => rfl
  | .mid k :: ms, tail => by
    simp [rebuildMR, encMidR, encMidItemR, encR_pushWRMSem, encR_rebuildMR ms tail]
  | .t k :: ms, tail => by
    simp [rebuildMR, encMidR, encMidItemR, encR_pushRP, pWord_1_1, encR_rebuildMR ms tail]
  | .z k :: ms, tail => by
    simp [rebuildMR, encMidR, encMidItemR, encR_pushRP, pWord_2_0, encR_rebuildMR ms tail]

def encMidItemL : MidItem → ListBlank (Fin 2) → ListBlank (Fin 2)
  | .mid k, l => (wLM ^ k) +> l
  | .t k, l => (wT ^ k) +> l
  | .z k, l => (wZ ^ k) +> l

def encMidL : List MidItem → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], l => l
  | m :: ms, l => encMidItemL m (encMidL ms l)



private theorem bounce_M_thm {W W' : ListBlank (Fin 2)} {cW : ℕ}
    (hW : ∀ l, ReachesIn target_tm cW (cfgA l ([1, 0, 1, 1] +> W))
      (cfgE ([1, 0, 1, 1] +> l) W')) :
    ∀ (ms : List MidItem) (l : ListBlank (Fin 2)),
      ReachesIn target_tm (22 * w3Mid ms + cW)
        (cfgA l ([1, 0, 1, 1] +> encMidR ms W))
        (cfgE ([1, 0, 1, 1] +> l) (encMidR ms W'))
  | [], l => by
    dsimp only [w3Mid, encMidR]
    exact rcast ((hW l)) (by omega)
  | .mid k :: ms, l => by
    dsimp only [w3Mid, w3Item, encMidR, encMidItemR]
    have h1 := step_a_1011_wRM_pow k l (encMidR ms W)
    have h2 := bounce_M_thm hW ms ((wLM ^ k) +> l)
    have h3 := step_e_1011_wLM_pow k l (encMidR ms W')
    exact rcast (((h1.trans h2).trans h3)) (by omega)
  | .t k :: ms, l => by
    dsimp only [w3Mid, w3Item, encMidR, encMidItemR]
    have h1 := step_a_1011_wT_pow k l (encMidR ms W)
    have h2 := bounce_M_thm hW ms ((wZ ^ k) +> l)
    have h3 := step_e_1011_wZ_pow k l (encMidR ms W')
    exact rcast (((h1.trans h2).trans h3)) (by omega)
  | .z k :: ms, l => by
    dsimp only [w3Mid, w3Item, encMidR, encMidItemR]
    have h1 := step_a_1011_wZ_pow k l (encMidR ms W)
    have h2 := bounce_M_thm hW ms ((wT ^ k) +> l)
    have h3 := step_e_1011_wT_pow k l (encMidR ms W')
    exact rcast (((h1.trans h2).trans h3)) (by omega)

private theorem roundtrip_mid_L {T_in T_out : ListBlank (Fin 2)} {cT : ℕ}
    (hT : ∀ r, ReachesIn target_tm cT (cfgE ([1, 0, 1, 1] +> T_in) r)
      (cfgA T_out ([1, 0, 1, 1] +> r))) :
    ∀ (ms : List MidItem) (r : ListBlank (Fin 2)),
      ReachesIn target_tm (22 * w3Mid ms + cT)
        (cfgE ([1, 0, 1, 1] +> encMidL ms T_in) r)
        (cfgA (encMidL ms T_out) ([1, 0, 1, 1] +> r))
  | [], r => by
    dsimp only [w3Mid, encMidL]
    exact rcast ((hT r)) (by omega)
  | .mid k :: ms, r => by
    dsimp only [w3Mid, w3Item, encMidL, encMidItemL]
    have h1 := step_e_1011_wLM_pow k (encMidL ms T_in) r
    have h2 := roundtrip_mid_L hT ms ((wRM ^ k) +> r)
    have h3 := step_a_1011_wRM_pow k (encMidL ms T_out) r
    exact rcast (((h1.trans h2).trans h3)) (by omega)
  | .t k :: ms, r => by
    dsimp only [w3Mid, w3Item, encMidL, encMidItemL]
    have h1 := step_e_1011_wT_pow k (encMidL ms T_in) r
    have h2 := roundtrip_mid_L hT ms ((wZ ^ k) +> r)
    have h3 := step_a_1011_wZ_pow k (encMidL ms T_out) r
    exact rcast (((h1.trans h2).trans h3)) (by omega)
  | .z k :: ms, r => by
    dsimp only [w3Mid, w3Item, encMidL, encMidItemL]
    have h1 := step_e_1011_wZ_pow k (encMidL ms T_in) r
    have h2 := roundtrip_mid_L hT ms ((wT ^ k) +> r)
    have h3 := step_a_1011_wT_pow k (encMidL ms T_out) r
    exact rcast (((h1.trans h2).trans h3)) (by omega)

/-! #### `refl_d0_1` and `refl_d1_1` Building Blocks -/

def d1P0 : List (Fin 2) := [0, 1, 0, 0, 1, 0, 0, 1]
def d1P1 : List (Fin 2) := [0, 0, 0, 1, 0, 1, 1, 0, 0, 1]

private theorem refl_d0_1 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 39
      (cfgA l ([1, 0, 1, 1] +> ([0, 1, 1, 1] +> (wT +> r))))
      (cfgE ([1, 0, 1, 1] +> l) (wT +> ([0, 1, 1, 1] +> r))) := by
  dsimp only [cfgA, cfgE, wT]; bb_steps_in

private theorem d1_entry_8 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 8
      (cfgA l ([1, 0, 1, 1, 0, 1, 0, 1] +> r))
      (cfgA (d1P0 +> l) r) := by
  dsimp only [cfgA, d1P0]; bb_steps_in

private theorem d1_mid_35 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 35
      (cfgE ([1, 0, 1, 1, 0, 1] +> (d1P0 +> l)) ([0] +> r))
      (cfgA (d1P1 +> l) ([1, 0, 1, 1, 0] +> r)) := by
  dsimp only [cfgE, cfgA, d1P0, d1P1]; bb_steps_in

private theorem d1_exit_50 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 50
      (cfgE ([1, 0, 1, 1] +> (d1P1 +> l)) ([0] +> r))
      (cfgE ([1, 0, 1, 1] +> l) (wT +> ([0, 1, 0, 1] +> (wT +> ([0] +> r))))) := by
  dsimp only [cfgE, d1P1, wT]; bb_steps_in

private theorem d1_empty_tf0_57 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 57
      (cfgA l ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] +> (wT +> (wT +> r))))
      (cfgE ([1, 0, 1, 1] +> (d1P1 +> l)) ([0] +> ([1, 1, 1] +> r))) := by
  dsimp only [cfgA, cfgE, wT, d1P1]; bb_steps_in

private theorem d1_empty_tf0_107 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 107
      (cfgA l ([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] +> (wT +> (wT +> r))))
      (cfgE ([1, 0, 1, 1] +> l) (wT +> ([0, 1, 0, 1] +> (wT +> ([0, 1, 1, 1] +> r))))) := by
  exact rcast (((d1_empty_tf0_57 l r).trans (d1_exit_50 l ([1, 1, 1] +> r)))) (by omega)

private theorem d1_empty_turn_14 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 14
      (cfgA (wZ +> l) ([1, 1] +> (wT +> r)))
      (cfgE ([1, 0, 1, 1] +> l) ([0, 1, 1, 1] +> r)) := by
  dsimp only [cfgA, cfgE, wZ, wT]; bb_steps_in

private theorem d1_turn_wZ_12 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 12
      (cfgA (wZ +> l) ([1] +> (wZ +> r)))
      (cfgA (wT +> l) ([1, 0, 1, 1] +> r)) := by
  dsimp only [cfgA, wZ, wT]; bb_steps_in

private theorem wT_pow_succ_0111 : ∀ (k : ℕ) (r : ListBlank (Fin 2)),
    (wT ^ (k + 1)) +> ([0, 1, 1, 1] +> r) =
      [0, 1] +> ([1] +> ((wT ^ (k + 1)) +> ([1] +> r)))
  | 0, r => by rw [pow_one_list]; rfl
  | k + 1, r => by
    rw [ListBlank.append_pow_succ wT (k + 1)]
    rw [wT_pow_succ_0111 k r]
    have heq : wT +> ([0, 1] +> ([1] +> ((wT ^ (k + 1)) +> ([1] +> r)))) =
        [0, 1] +> ([1] +> (wT +> ((wT ^ (k + 1)) +> ([1] +> r)))) := rfl
    rw [heq, ← ListBlank.append_pow_succ wT (k + 1)]

private theorem wT_pow_succ_succ_split : ∀ (u : ℕ) (r : ListBlank (Fin 2)),
    (wT ^ (u + 2)) +> r = [0, 1] +> ([1] +> ((wT ^ (u + 1)) +> r))
  | 0, r => by simp [pow_succ_list, pow_zero_list]; rfl
  | u + 1, r => by
    have hl : (wT ^ (u + 1 + 2)) +> r = wT +> ((wT ^ (u + 2)) +> r) := by
      rw [ListBlank.append_pow_succ wT (u + 2)]
    rw [hl, wT_pow_succ_succ_split u r]
    rfl

private theorem wT_pow_0111_zero_head : ∀ (k : ℕ) (r : ListBlank (Fin 2)),
    ∃ tail, (wT ^ k) +> ([0, 1, 1, 1] +> r) = [0] +> tail ∧
      [1, 0, 1, 1, 0] +> tail = [1, 0, 1, 1] +> ((wT ^ k) +> ([0, 1, 1, 1] +> r)) ∧
      wT +> ([0] +> tail) = (wT ^ (k + 1)) +> ([0, 1, 1, 1] +> r)
  | 0, r => ⟨[1, 1, 1] +> r, rfl, rfl, by rw [pow_one_list]; rfl⟩
  | k + 1, r => by
    refine ⟨[1, 1] +> ((wT ^ k) +> ([0, 1, 1, 1] +> r)), ?_, ?_, ?_⟩
    · rw [ListBlank.append_pow_succ]; rfl
    · rw [ListBlank.append_pow_succ]; rfl
    · rw [ListBlank.append_pow_succ wT (k + 1), ListBlank.append_pow_succ wT k]; rfl

private theorem wT_pow_wZ_zero_head : ∀ (u : ℕ) (r : ListBlank (Fin 2)),
    ∃ tail, (wT ^ u) +> (wZ +> r) = [0] +> tail ∧
      [1, 0, 1, 1, 0] +> tail = [1, 0, 1, 1] +> ((wT ^ u) +> (wZ +> r)) ∧
      wT +> ([0] +> tail) = (wT ^ (u + 1)) +> (wZ +> r)
  | 0, r => ⟨[0, 1] +> r, rfl, rfl, by rw [pow_one_list]; rfl⟩
  | u + 1, r => by
    refine ⟨[1, 1] +> ((wT ^ u) +> (wZ +> r)), ?_, ?_, ?_⟩
    · rw [ListBlank.append_pow_succ]; rfl
    · rw [ListBlank.append_pow_succ]; rfl
    · rw [ListBlank.append_pow_succ wT (u + 1), ListBlank.append_pow_succ wT u]; rfl

private theorem refl_d1_empty_1 (tf b : ℕ) (l rt : ListBlank (Fin 2)) :
    ReachesIn target_tm (44 * tf + 107)
      (cfgA l ([1, 0, 1, 1] +> ([0, 1, 0, 1] +> ((wT ^ tf) +>
        ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> rt))))))
      (cfgE ([1, 0, 1, 1] +> l) (wT +> ([0, 1, 0, 1] +> ((wT ^ (tf + 1)) +>
        ([0, 1, 1, 1] +> ((wT ^ b) +> rt)))))) := by
  cases tf with
  | zero =>
    have hin : [1, 0, 1, 1] +> ([0, 1, 0, 1] +> ((wT ^ 0) +>
        ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> rt)))) =
        [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt))) := by
      have hb : b + 2 = 1 + (1 + b) := by omega
      rw [hb, ListBlank.append_pow_add wT 1 (1 + b), ListBlank.append_pow_add wT 1 b, pow_one_list]
      rfl
    rw [hin, pow_one_list]
    exact rcast ((d1_empty_tf0_107 l ((wT ^ b) +> rt))) (by omega)
  | succ t' =>
    have hin : [1, 0, 1, 1] +> ([0, 1, 0, 1] +> ((wT ^ (t' + 1)) +>
        ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> rt)))) =
        [1, 0, 1, 1, 0, 1, 0, 1] +> ([0, 1] +> ([1] +> ((wT ^ (t' + 1)) +>
          ([1] +> (wT +> (wT +> ((wT ^ b) +> rt))))))) := by
      rw [wT_pow_succ_0111 t' ((wT ^ (b + 2)) +> rt)]
      have hb : b + 2 = 1 + (1 + b) := by omega
      rw [hb, ListBlank.append_pow_add wT 1 (1 + b), ListBlank.append_pow_add wT 1 b, pow_one_list]
      rfl
    rw [hin]
    have h1 := d1_entry_8 l ([0, 1] +> ([1] +> ((wT ^ (t' + 1)) +>
      ([1] +> (wT +> (wT +> ((wT ^ b) +> rt)))))))
    have h2 := step_a_01 (d1P0 +> l) ([1] +> ((wT ^ (t' + 1)) +>
      ([1] +> (wT +> (wT +> ((wT ^ b) +> rt))))))
    have h3 := step_a_101_pow (t' + 1) ([0, 1] +> (d1P0 +> l))
      ([1] +> (wT +> (wT +> ((wT ^ b) +> rt))))
    rw [ListBlank.append_pow_succ wZ t'] at h3
    have h3R : [1] +> ([1] +> (wT +> (wT +> ((wT ^ b) +> rt)))) =
        [1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt))) := rfl
    rw [h3R] at h3
    have h4 := d1_empty_turn_14 ((wZ ^ t') +> ([0, 1] +> (d1P0 +> l)))
      (wT +> ((wT ^ b) +> rt))
    have h5 := step_e_1011_wZ_pow t' ([0, 1] +> (d1P0 +> l))
      ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))
    have h5L : [1, 0, 1, 1] +> ([0, 1] +> (d1P0 +> l)) =
        [1, 0, 1, 1, 0, 1] +> (d1P0 +> l) := rfl
    rw [h5L] at h5
    obtain ⟨tail1, ht1_eq, ht1_mid, _⟩ :=
      wT_pow_0111_zero_head t' (wT +> ((wT ^ b) +> rt))
    rw [ht1_eq] at h5
    have h6 := d1_mid_35 l tail1
    rw [ht1_mid] at h6
    have h7 := bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^ b) +> rt)) [.t t'] (d1P1 +> l)
    dsimp only [encMidR, encMidItemR, w3Mid, w3Item] at h7
    rw [ListBlank.append_pow_comm wT t', ← ListBlank.append_pow_succ wT t'] at h7
    obtain ⟨tail2, ht2_eq, _, ht2_exit⟩ :=
      wT_pow_0111_zero_head (t' + 1) ((wT ^ b) +> rt)
    rw [ht2_eq] at h7
    have h8 := d1_exit_50 l tail2
    rw [ht2_exit] at h8
    exact rcast ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8))
      (by omega)

private theorem refl_d1_mid_1 (u cz b : ℕ) (ms' : List MidItem) (l rt : ListBlank (Fin 2)) :
    ReachesIn target_tm (44 * ((u + 2) + (cz + 1) + w3Mid ms') + 107)
      (cfgA l ([1, 0, 1, 1] +> ([0, 1, 0, 1] +> ((wT ^ (u + 2)) +>
        encMidR (.z (cz + 1) :: ms') ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> rt))))))
      (cfgE ([1, 0, 1, 1] +> l) (wT +> ([0, 1, 0, 1] +> ((wT ^ (u + 1)) +>
        encMidR (.z (cz + 1) :: ms') ((wT ^ 2) +> ([0, 1, 1, 1] +> ((wT ^ b) +> rt))))))) := by
  have hin : [1, 0, 1, 1] +> ([0, 1, 0, 1] +> ((wT ^ (u + 2)) +>
      encMidR (.z (cz + 1) :: ms') ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> rt)))) =
      [1, 0, 1, 1, 0, 1, 0, 1] +> ([0, 1] +> ([1] +> ((wT ^ (u + 1)) +>
        (wZ +> encMidR (.z cz :: ms')
          ([0, 1, 1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt)))))))) := by
    rw [wT_pow_succ_succ_split u]
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wZ cz]
    have hb : b + 2 = 1 + (1 + b) := by omega
    rw [hb, ListBlank.append_pow_add wT 1 (1 + b), ListBlank.append_pow_add wT 1 b, pow_one_list]
    rfl
  rw [hin]
  have h1 := d1_entry_8 l ([0, 1] +> ([1] +> ((wT ^ (u + 1)) +>
    (wZ +> encMidR (.z cz :: ms') ([0, 1, 1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt))))))))
  have h2 := step_a_01 (d1P0 +> l) ([1] +> ((wT ^ (u + 1)) +>
    (wZ +> encMidR (.z cz :: ms') ([0, 1, 1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt)))))))
  have h3 := step_a_101_pow (u + 1) ([0, 1] +> (d1P0 +> l))
    (wZ +> encMidR (.z cz :: ms') ([0, 1, 1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt)))))
  rw [ListBlank.append_pow_succ wZ u] at h3
  have h4 := d1_turn_wZ_12 ((wZ ^ u) +> ([0, 1] +> (d1P0 +> l)))
    (encMidR (.z cz :: ms') ([0, 1, 1, 1] +> (wT +> (wT +> ((wT ^ b) +> rt)))))
  have h5 := bounce_M_thm (fun l' => refl_d0_1 l' (wT +> ((wT ^ b) +> rt)))
    (.z cz :: ms') (wT +> ((wZ ^ u) +> ([0, 1] +> (d1P0 +> l))))
  have h6 := step_e_1011_wT ((wZ ^ u) +> ([0, 1] +> (d1P0 +> l)))
    (encMidR (.z cz :: ms') (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))))
  have h6R : wZ +> encMidR (.z cz :: ms') (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))) =
      encMidR (.z (cz + 1) :: ms') (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))) := by
    dsimp only [encMidR, encMidItemR]
    rw [← ListBlank.append_pow_succ wZ cz]
  rw [h6R] at h6
  have h7 := step_e_1011_wZ_pow u ([0, 1] +> (d1P0 +> l))
    (encMidR (.z (cz + 1) :: ms') (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))))
  have h7L : [1, 0, 1, 1] +> ([0, 1] +> (d1P0 +> l)) = [1, 0, 1, 1, 0, 1] +> (d1P0 +> l) := rfl
  rw [h7L] at h7
  have h7R : (wT ^ u) +> encMidR (.z (cz + 1) :: ms')
      (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))) =
      (wT ^ u) +> (wZ +> encMidR (.z cz :: ms')
        (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt))))) := by
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wZ cz]
  obtain ⟨tail1, ht1_eq, ht1_mid, _⟩ :=
    wT_pow_wZ_zero_head u (encMidR (.z cz :: ms')
      (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt)))))
  rw [h7R, ht1_eq] at h7
  have h8 := d1_mid_35 l tail1
  rw [ht1_mid, ← h7R] at h8
  have h8R : [1, 0, 1, 1] +> ((wT ^ u) +> encMidR (.z (cz + 1) :: ms')
      (wT +> ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt))))) =
      [1, 0, 1, 1] +> encMidR ([.t u] ++ (.z (cz + 1) :: ms') ++ [.t 1])
        ([0, 1, 1, 1] +> (wT +> ((wT ^ b) +> rt))) := by
    rw [encMidR_append, encMidR_append]
    dsimp only [encMidR, encMidItemR]
    rw [pow_one_list]
  rw [h8R] at h8
  have h9 := bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^ b) +> rt))
    ([.t u] ++ (.z (cz + 1) :: ms') ++ [.t 1]) (d1P1 +> l)
  have h9R : encMidR ([.t u] ++ (.z (cz + 1) :: ms') ++ [.t 1])
      (wT +> ([0, 1, 1, 1] +> ((wT ^ b) +> rt))) =
      (wT ^ u) +> (wZ +> encMidR (.z cz :: ms')
        ((wT ^ 2) +> ([0, 1, 1, 1] +> ((wT ^ b) +> rt)))) := by
    rw [encMidR_append, encMidR_append]
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wZ cz]
    rfl
  obtain ⟨tail2, ht2_eq, _, ht2_exit⟩ :=
    wT_pow_wZ_zero_head u (encMidR (.z cz :: ms')
      ((wT ^ 2) +> ([0, 1, 1, 1] +> ((wT ^ b) +> rt))))
  rw [h9R, ht2_eq] at h9
  have h10 := d1_exit_50 l tail2
  rw [ht2_exit] at h10
  have h10R : (wT ^ (u + 1)) +> (wZ +> encMidR (.z cz :: ms')
      ((wT ^ 2) +> ([0, 1, 1, 1] +> ((wT ^ b) +> rt)))) =
      (wT ^ (u + 1)) +> encMidR (.z (cz + 1) :: ms')
        ((wT ^ 2) +> ([0, 1, 1, 1] +> ((wT ^ b) +> rt))) := by
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wZ cz]
  rw [h10R] at h10
  have hw3 : w3Mid ([.t u] ++ (.z (cz + 1) :: ms') ++ [.t 1]) = u + (cz + 1) + w3Mid ms' + 1 := by
    rw [w3Mid_append, w3Mid_append]
    dsimp only [w3Mid, w3Item]
    omega
  exact rcast ((((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
    h8).trans
    h9).trans h10)) (by rw [hw3]; dsimp only [w3Mid, w3Item]; omega)

/-! #### `TowerD01` Parsing, Advancement, Cost, & `tryReflectARD01` -/

inductive TowerD01 : Type
  | d0 (B : ℕ) (rt : List RTok)
  | d1Empty (tf B : ℕ) (rt : List RTok)
  | d1Mid (tf cz : ℕ) (ms' : List MidItem) (w3 B : ℕ) (rt : List RTok)
  deriving DecidableEq, Repr


def TowerWF : TowerD01 → Prop
  | .d0 _ _ => True
  | .d1Empty _ _ _ => True
  | .d1Mid tf cz ms' w3 _ _ => 2 ≤ tf ∧ w3 = tf + (cz + 1) + w3Mid ms'


def maxReflD01 : TowerD01 → ℕ
  | .d0 B _ => B
  | .d1Empty _ B _ => B / 2
  | .d1Mid tf _ _ _ B _ => min (B / 2) (tf - 1)

def towerStepCostD01 : TowerD01 → ℕ → ℕ
  | .d0 _ _, _ => 39
  | .d1Empty tf _ _, j => 44 * (tf + j) + 107
  | .d1Mid _ _ _ w3 _ _, j => 44 * (w3 + j) + 107

def towerCostD01 : TowerD01 → ℕ → ℕ
  | .d0 _ _, N => 39 * N
  | .d1Empty tf _ _, N => N * (44 * tf + 107) + 22 * N * (N - 1)
  | .d1Mid _ _ _ w3 _ _, N => N * (44 * w3 + 107) + 22 * N * (N - 1)

def buildAdvTowerD01 : TowerD01 → ℕ → List RTok
  | .d0 B rt, N =>
    pushRP 1 2 1 (pushRP 1 1 (B - N) rt)
  | .d1Empty tf B rt, N =>
    let inner := pushRP 1 2 1 (pushRP 1 1 (B - 2 * N) rt)
    pushRP 1 0 2 (pushRP 1 1 (tf + N) inner)
  | .d1Mid tf cz ms' _ B rt, N =>
    let inner := pushRP 1 2 1 (pushRP 1 1 (B - 2 * N) rt)
    let afterM := rebuildMR (.z (cz + 1) :: ms') (pushRP 1 1 (2 * N) inner)
    pushRP 1 0 2 (pushRP 1 1 (tf - N) afterM)


private theorem refl_tower_d01_step (tw : TowerD01) (htw : TowerWF tw)
    (j : ℕ) (hj : j < maxReflD01 tw) (l : ListBlank (Fin 2)) :
    ReachesIn target_tm (towerStepCostD01 tw j)
      (cfgA l ([1, 0, 1, 1] +> encR (buildAdvTowerD01 tw j)))
      (cfgE ([1, 0, 1, 1] +> l) (wT +> encR (buildAdvTowerD01 tw (j + 1)))) := by
  cases tw with
  | d0 B rt =>
    dsimp only [maxReflD01] at hj
    dsimp only [towerStepCostD01, buildAdvTowerD01]
    simp only [encR_pushRP, pWord_1_2, pWord_1_1, pow_one_list]
    have hb : B - j = (B - (j + 1)) + 1 := by omega
    rw [hb, ListBlank.append_pow_succ wT (B - (j + 1))]
    exact refl_d0_1 l ((wT ^ (B - (j + 1))) +> encR rt)
  | d1Empty tf B rt =>
    dsimp only [maxReflD01] at hj
    dsimp only [towerStepCostD01, buildAdvTowerD01]
    simp only [encR_pushRP, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list]
    have h0101 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h0101]
    have hb : B - 2 * j = (B - 2 * (j + 1)) + 2 := by omega
    have htf : tf + (j + 1) = (tf + j) + 1 := by omega
    rw [hb, htf]
    exact refl_d1_empty_1 (tf + j) (B - 2 * (j + 1)) l (encR rt)
  | d1Mid tf cz ms' w3 B rt =>
    rcases htw with ⟨htf2, hw3⟩
    dsimp only [maxReflD01] at hj
    dsimp only [towerStepCostD01, buildAdvTowerD01]
    simp only [encR_pushRP, encR_rebuildMR, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list]
    have h0101 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h0101]
    have hu : tf - j = (tf - (j + 1) - 1) + 2 := by omega
    have hu1 : tf - (j + 1) = (tf - (j + 1) - 1) + 1 := by omega
    have hb : B - 2 * j = (B - 2 * (j + 1)) + 2 := by omega
    set u := tf - (j + 1) - 1
    set b := B - 2 * (j + 1)
    rw [hu, hu1, hb]
    have hmid_in : encMidR (.z (cz + 1) :: ms')
        ((wT ^ (2 * j)) +> ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> encR rt))) =
        encMidR (.z (cz + 1) :: (ms' ++ [.t (2 * j)]))
          ([0, 1, 1, 1] +> ((wT ^ (b + 2)) +> encR rt)) := by
      dsimp only [encMidR]
      rw [encMidR_append]
      dsimp only [encMidR, encMidItemR]
    have hmid_out : encMidR (.z (cz + 1) :: (ms' ++ [.t (2 * j)]))
        ((wT ^ 2) +> ([0, 1, 1, 1] +> ((wT ^ b) +> encR rt))) =
        encMidR (.z (cz + 1) :: ms')
          ((wT ^ (2 * (j + 1))) +> ([0, 1, 1, 1] +> ((wT ^ b) +> encR rt))) := by
      dsimp only [encMidR]
      rw [encMidR_append]
      dsimp only [encMidR, encMidItemR]
      rw [pow_append_pow]
      congr 3
    rw [hmid_in]
    have href := refl_d1_mid_1 u cz b (ms' ++ [.t (2 * j)]) l (encR rt)
    rw [hmid_out] at href
    have hcost : 44 * ((u + 2) + (cz + 1) + w3Mid (ms' ++ [.t (2 * j)])) + 107 =
        44 * (w3 + j) + 107 := by
      rw [w3Mid_append]
      dsimp only [w3Mid, w3Item]
      omega
    exact rcast (href) hcost

private theorem quad_step (a m : ℕ) :
    (m + 1 + 1) * a + 22 * (m + 1 + 1) * (m + 1) =
      ((m + 1) * a + 22 * (m + 1) * m) + (a + 44 * (m + 1)) := by
  ring

private theorem towerCostD01_succ (tw : TowerD01) (n : ℕ) :
    towerCostD01 tw (n + 1) = towerCostD01 tw n + towerStepCostD01 tw n := by
  cases tw with
  | d0 _ _ =>
    dsimp only [towerCostD01, towerStepCostD01]; omega
  | d1Empty tf _ _ =>
    dsimp only [towerCostD01, towerStepCostD01]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      have hq := quad_step (44 * tf + 107) m
      omega
  | d1Mid _ _ _ w3 _ _ =>
    dsimp only [towerCostD01, towerStepCostD01]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      have hq := quad_step (44 * w3 + 107) m
      omega


private theorem ec_entry_6 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 6
      (cfgE ([1] +> (wZ +> (wZ +> l))) (wT +> r))
      (cfgA (wT +> (wZ +> l)) ([1, 0, 1, 1] +> r)) := by
  dsimp only [cfgE, cfgA, wZ, wT]; bb_steps_in

private theorem ec_right_6 (l : ListBlank (Fin 2)) :
    ReachesIn target_tm 6
      (cfgA l ([1, 0, 1] +> default))
      (cfgD (wZ +> l) ([0, 1] +> default)) := by
  have h1 := step_a_101 l default
  have h2 : ReachesIn target_tm 3 (cfgA (wZ +> l) default)
      (cfgD (wZ +> l) ([0, 1] +> default)) := by
    have hd : (default : ListBlank (Fin 2)) = [0, 0] +> default := by
      simp [ListBlank.cons_zero_default]
    have hcfg : cfgA (wZ +> l) default = cfgA (wZ +> l) ([0, 0] +> default) := by
      rw [← hd]
    rw [hcfg]
    dsimp only [cfgA, cfgD]
    bb_steps_in
  exact rcast ((h1.trans h2)) (by omega)

private theorem step_d_01 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2
      (cfgD ([0, 1] +> l) r)
      (cfgA ([0] +> l) ([1] +> r)) := by
  dsimp only [cfgD, cfgA]; bb_steps_in

private theorem ec_exit_5 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5
      (cfgD ([0, 0, 0, 1] +> l) r)
      (cfgE ([1] +> l) (wT +> r)) := by
  dsimp only [cfgD, cfgE, wT]; bb_steps_in

private theorem era_conv_one (b' : ℕ) (l : ListBlank (Fin 2)) :
    ReachesIn target_tm (18 * (b' + 2) + 60)
      (cfgE ([1] +> ((wZ ^ 2) +> (wZ +> l))) ((wT ^ (b' + 2)) +> ([0, 1] +> default)))
      (cfgE ([1] +> (wZ +> l)) ((wT ^ (b' + 6)) +> ([0, 1] +> default))) := by
  have hwz2 : (wZ ^ 2) +> (wZ +> l) = wZ +> (wZ +> (wZ +> l)) := rfl
  have hwt_in : (wT ^ (b' + 2)) +> ([0, 1] +> (default : ListBlank (Fin 2))) =
      wT +> ((wT ^ (b' + 1)) +> ([0, 1] +> default)) := by
    rw [ListBlank.append_pow_succ wT (b' + 1)]
  rw [hwz2, hwt_in]
  have h1 := ec_entry_6 (wZ +> l) ((wT ^ (b' + 1)) +> ([0, 1] +> default))
  have h1R : [1, 0, 1, 1] +> ((wT ^ (b' + 1)) +> ([0, 1] +> (default : ListBlank (Fin 2)))) =
      [1] +> ((wT ^ (b' + 2)) +> ([0, 1] +> default)) := by
    rw [ListBlank.append_pow_succ wT (b' + 1)]; rfl
  rw [h1R] at h1
  have h2 := step_a_101_pow (b' + 2) (wT +> (wZ +> (wZ +> l))) ([0, 1] +> default)
  have h3 := ec_right_6 ((wZ ^ (b' + 2)) +> (wT +> (wZ +> (wZ +> l))))
  rw [← ListBlank.append_pow_succ wZ (b' + 2)] at h3
  have h4 := step_d_001_pow (b' + 3) (wT +> (wZ +> (wZ +> l))) ([0, 1] +> default)
  have h5 := step_d_01 ([1] +> (wZ +> (wZ +> l))) ((wT ^ (b' + 3)) +> ([0, 1] +> default))
  have h6 := step_a_101_pow (b' + 3) ([0, 1] +> (wZ +> (wZ +> l))) ([0, 1] +> default)
  have h7 := ec_right_6 ((wZ ^ (b' + 3)) +> ([0, 1] +> (wZ +> (wZ +> l))))
  rw [← ListBlank.append_pow_succ wZ (b' + 3)] at h7
  have h8 := step_d_001_pow (b' + 4) ([0, 1] +> (wZ +> (wZ +> l))) ([0, 1] +> default)
  have h9 := step_d_01 (wZ +> (wZ +> l)) ((wT ^ (b' + 4)) +> ([0, 1] +> default))
  have h9L : [0] +> (wZ +> (wZ +> l)) = [0, 0, 0, 1] +> (wZ +> l) := rfl
  rw [h9L] at h9
  have h10 := step_a_101_pow (b' + 4) ([0, 0, 0, 1] +> (wZ +> l)) ([0, 1] +> default)
  have h11 := ec_right_6 ((wZ ^ (b' + 4)) +> ([0, 0, 0, 1] +> (wZ +> l)))
  rw [← ListBlank.append_pow_succ wZ (b' + 4)] at h11
  have h12 := step_d_001_pow (b' + 5) ([0, 0, 0, 1] +> (wZ +> l)) ([0, 1] +> default)
  have h13 := ec_exit_5 (wZ +> l) ((wT ^ (b' + 5)) +> ([0, 1] +> default))
  rw [← ListBlank.append_pow_succ wT (b' + 5)] at h13
  exact rcast (((((((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
    h8).trans h9).trans h10).trans h11).trans h12).trans h13)) (by omega)

private theorem era_conv_cost_step (b' m : ℕ) :
    (18 * (b' + 2) + 60) + ((m + 1) * (18 * ((b' + 4) + 2) + 60) + 36 * (m + 1) * m) =
      (m + 1 + 1) * (18 * (b' + 2) + 60) + 36 * (m + 1 + 1) * (m + 1) := by
  ring

private theorem era_conv_loop : ∀ (K z_rem b' : ℕ) (l : ListBlank (Fin 2)),
    ReachesIn target_tm (K * (18 * (b' + 2) + 60) + 36 * K * (K - 1))
      (cfgE ([1] +> ((wZ ^ (2 * K + (z_rem + 1))) +> l))
        ((wT ^ (b' + 2)) +> ([0, 1] +> (default : ListBlank (Fin 2)))))
      (cfgE ([1] +> ((wZ ^ (z_rem + 1)) +> l))
        ((wT ^ (b' + 2 + 4 * K)) +> ([0, 1] +> (default : ListBlank (Fin 2)))))
  | 0, z_rem, b', l => by
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    exact ReachesIn.zero target_tm _
  | K + 1, z_rem, b', l => by
    have hexp : 2 * (K + 1) + (z_rem + 1) = 2 + ((2 * K + z_rem) + 1) := by omega
    rw [hexp, ListBlank.append_pow_add wZ 2 ((2 * K + z_rem) + 1),
      ListBlank.append_pow_succ wZ (2 * K + z_rem)]
    have h1 := era_conv_one b' ((wZ ^ (2 * K + z_rem)) +> l)
    rw [← ListBlank.append_pow_succ wZ (2 * K + z_rem)] at h1
    have hexp2 : (2 * K + z_rem) + 1 = 2 * K + (z_rem + 1) := by omega
    have hb2 : b' + 6 = (b' + 4) + 2 := by omega
    rw [hexp2, hb2] at h1
    have h2 := era_conv_loop K z_rem (b' + 4) l
    have hb3 : (b' + 4) + 2 + 4 * K = b' + 2 + 4 * (K + 1) := by omega
    rw [hb3] at h2
    have hcost : (18 * (b' + 2) + 60) + (K * (18 * ((b' + 4) + 2) + 60) + 36 * K * (K - 1)) =
        (K + 1) * (18 * (b' + 2) + 60) + 36 * (K + 1) * ((K + 1) - 1) := by
      cases K with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        exact era_conv_cost_step b' m
    exact rcast ((h1.trans h2)) hcost


private theorem zpad_eq_default : ∀ (k : ℕ),
    (List.replicate k (0 : Fin 2)) +> (default : ListBlank (Fin 2)) = default
  | 0 => rfl
  | k + 1 => by
    dsimp only [List.replicate_succ]
    change (0 : Fin 2) >> ((List.replicate k (0 : Fin 2)) +> default) = default
    rw [zpad_eq_default k, ListBlank.cons_zero_default]


def tailL0 : ListBlank (Fin 2) := wT +> ([0, 1] +> default)
def tailL1 : ListBlank (Fin 2) := wT +> (wZ +> default)
def tailL2 : ListBlank (Fin 2) := wT +> ([0, 1] +> (wZ +> ([0, 1] +> default)))
def tailL3 : ListBlank (Fin 2) := wT +> (wZ +> ([0, 1, 0, 1] +> default))
def tailL4 : ListBlank (Fin 2) := wT +> (wZ +> ([0, 0, 0, 1] +> ([0, 1] +> default)))
def tailL5 : ListBlank (Fin 2) := wT +> ([0, 1, 0, 1, 0, 1] +> (wZ +> ([0, 1] +> default)))
def tailL6 : ListBlank (Fin 2) := wLM +> tailL0


private theorem left_turn_0 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 55
      (cfgE ([1, 0, 1, 1] +> tailL0) r)
      (cfgA tailL1 ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 55
      (cfgE ([1, 0, 1, 1] +> (wT +> ([0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))) r)
      (cfgA (wT +> (wZ +>
        ((List.replicate 15 (0 : Fin 2)) +> default))) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 15] at h
  exact h

private theorem left_turn_1 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 77
      (cfgE ([1, 0, 1, 1] +> tailL1) r)
      (cfgA tailL2 ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 77
      (cfgE ([1, 0, 1, 1] +> (wT +> (wZ +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))) r)
      (cfgA (wT +> ([0, 1] +> (wZ +> ([0, 1] +>
        ((List.replicate 12 (0 : Fin 2)) +> default))))) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 12] at h
  exact h

private theorem left_turn_2 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 55
      (cfgE ([1, 0, 1, 1] +> tailL2) r)
      (cfgA tailL3 ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 55
      (cfgE ([1, 0, 1, 1] +> (wT +> ([0, 1] +> (wZ +> ([0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))))) r)
      (cfgA (wT +> (wZ +> ([0, 1, 0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16] at h
  exact h

private theorem left_turn_3 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 79
      (cfgE ([1, 0, 1, 1] +> tailL3) r)
      (cfgA tailL4 ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 79
      (cfgE ([1, 0, 1, 1] +> (wT +> (wZ +> ([0, 1, 0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default))))) r)
      (cfgA (wT +> (wZ +> ([0, 0, 0, 1] +> ([0, 1] +>
        ((List.replicate 14 (0 : Fin 2)) +> default))))) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 14] at h
  exact h

private theorem left_turn_4 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 93
      (cfgE ([1, 0, 1, 1] +> tailL4) r)
      (cfgA tailL5 ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 93
      (cfgE ([1, 0, 1, 1] +> (wT +> (wZ +> ([0, 0, 0, 1] +> ([0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))))) r)
      (cfgA (wT +> ([0, 1, 0, 1, 0, 1] +> (wZ +> ([0, 1] +>
        ((List.replicate 14 (0 : Fin 2)) +> default))))) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 14] at h
  exact h

private theorem left_turn_5 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 65
      (cfgE ([1, 0, 1, 1] +> tailL5) r)
      (cfgA tailL6 ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 65
      (cfgE ([1, 0, 1, 1] +> (wT +> ([0, 1, 0, 1, 0, 1] +> (wZ +> ([0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))))) r)
      (cfgA (wLM +> (wT +> ([0, 1] +>
        ((List.replicate 16 (0 : Fin 2)) +> default)))) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, wLM, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16] at h
  exact h

/-! #### 6.1 `tryEraED01` (`E_L` Right-Reflection Era for `d ∈ {0, 1}`) -/

def eL1 : List (Fin 2) := [0, 1, 1, 0, 1, 0, 0, 1, 0, 1]
def eL2 : List (Fin 2) := [0, 1, 1, 0, 0, 1, 0, 1, 0, 1]
def eL3 : List (Fin 2) := [0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1]
def eL4 : List (Fin 2) := [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
def eL5 : List (Fin 2) := [0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]

private theorem eraE_turn_0 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 51
      (cfgE ([1, 0, 1, 1] +> default) (wT +> (wZ +> r)))
      (cfgA (eL1 +> default) ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 51
      (cfgE ([1, 0, 1, 1] +> ((List.replicate 16 (0 : Fin 2)) +> default)) (wT +> (wZ +> r)))
      (cfgA (eL1 +> ((List.replicate 12 (0 : Fin 2)) +> default)) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wT, wZ, eL1, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 12] at h
  exact h

private theorem eraE_turn_1 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 55
      (cfgE ([1, 0, 1, 1] +> (eL1 +> default)) r)
      (cfgA (eL2 +> default) ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 55
      (cfgE ([1, 0, 1, 1] +> (eL1 +> ((List.replicate 16 (0 : Fin 2)) +> default))) r)
      (cfgA (eL2 +> ((List.replicate 16 (0 : Fin 2)) +> default)) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, eL1, eL2, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16] at h
  exact h

private theorem eraE_turn_2 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 79
      (cfgE ([1, 0, 1, 1] +> (eL2 +> default)) r)
      (cfgA (eL3 +> default) ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 79
      (cfgE ([1, 0, 1, 1] +> (eL2 +> ((List.replicate 16 (0 : Fin 2)) +> default))) r)
      (cfgA (eL3 +> ((List.replicate 14 (0 : Fin 2)) +> default)) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, eL2, eL3, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 14] at h
  exact h

private theorem eraE_turn_3 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 93
      (cfgE ([1, 0, 1, 1] +> (eL3 +> default)) r)
      (cfgA (eL4 +> default) ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 93
      (cfgE ([1, 0, 1, 1] +> (eL3 +> ((List.replicate 16 (0 : Fin 2)) +> default))) r)
      (cfgA (eL4 +> ((List.replicate 14 (0 : Fin 2)) +> default)) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, eL3, eL4, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 14] at h
  exact h

private theorem eraE_turn_4 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 65
      (cfgE ([1, 0, 1, 1] +> (eL4 +> default)) r)
      (cfgA (eL5 +> default) ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 65
      (cfgE ([1, 0, 1, 1] +> (eL4 +> ((List.replicate 16 (0 : Fin 2)) +> default))) r)
      (cfgA (eL5 +> ((List.replicate 16 (0 : Fin 2)) +> default)) ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, eL4, eL5, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16] at h
  exact h

private theorem eraE_turn_5a (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 66
      (cfgE ([1, 0, 1, 1] +> (eL5 +> default)) r)
      (cfgE default ((wZ ^ 3) +> (wRM +> r))) := by
  have h : ReachesIn target_tm 66
      (cfgE ([1, 0, 1, 1] +> (eL5 +> ((List.replicate 16 (0 : Fin 2)) +> default))) r)
      (cfgE ((List.replicate 16 (0 : Fin 2)) +> default) ((wZ ^ 3) +> (wRM +> r))) := by
    dsimp only [cfgE, eL5, wZ, wRM, pow_succ_list, pow_zero_list, List.replicate]; bb_steps_in
  rw [zpad_eq_default 16] at h
  exact h

private theorem eraE_turn_5b (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 55
      (cfgE default ((wZ ^ 3) +> (wRM +> r)))
      (cfgA (wLM +> (wT +> (wZ +> default))) ([1, 0, 1, 1] +> r)) := by
  have h : ReachesIn target_tm 55
      (cfgE ((List.replicate 16 (0 : Fin 2)) +> default) ((wZ ^ 3) +> (wRM +> r)))
      (cfgA (wLM +> (wT +> (wZ +> ((List.replicate 15 (0 : Fin 2)) +> default))))
        ([1, 0, 1, 1] +> r)) := by
    dsimp only [cfgE, cfgA, wZ, wRM, wLM, wT, pow_succ_list, pow_zero_list, List.replicate]
    bb_steps_in
  rw [zpad_eq_default 16, zpad_eq_default 15] at h
  exact h

private theorem eraE_turn_5 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 121
      (cfgE ([1, 0, 1, 1] +> (eL5 +> default)) r)
      (cfgA (wLM +> (wT +> (wZ +> default))) ([1, 0, 1, 1] +> r)) := by
  exact rcast (((eraE_turn_5a r).trans (eraE_turn_5b r))) (by omega)

def eraECfg (ms : List MidItem) (tw : TowerD01) (j : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wRM ^ j) +>
      encMidR ms ((wT ^ (6 * j)) +> encR (buildAdvTowerD01 tw (6 * j))))))

private theorem eraE_advance_t (ms : List MidItem) (j k : ℕ) (W : ListBlank (Fin 2)) :
    encMidR ([.mid j] ++ ms ++ [.t k]) (wT +> W) =
      encMidR ([.mid j] ++ ms ++ [.t (k + 1)]) W := by
  simp only [encMidR_append, encMidR, encMidItemR]
  rw [ListBlank.append_pow_comm wT k, ← ListBlank.append_pow_succ wT k]

private theorem eraE_w3 (ms : List MidItem) (j k : ℕ) :
    w3Mid ([.mid j] ++ ms ++ [.t k]) = 3 * j + w3Mid ms + k := by
  simp only [w3Mid_append, w3Mid, w3Item]
  omega

private theorem era_E_one_cycle (ms : List MidItem) (tw : TowerD01) (htw : TowerWF tw)
    (j : ℕ) (hj : 6 * (j + 1) ≤ maxReflD01 tw) :
    ReachesIn target_tm
      (865 + 132 * w3Mid ms + 1188 * j +
        (towerStepCostD01 tw (6 * j) + towerStepCostD01 tw (6 * j + 1) +
          towerStepCostD01 tw (6 * j + 2) + towerStepCostD01 tw (6 * j + 3) +
          towerStepCostD01 tw (6 * j + 4) + towerStepCostD01 tw (6 * j + 5)))
      (eraECfg ms tw j) (eraECfg ms tw (j + 1)) := by
  dsimp only [eraECfg]
  have hR0 : (wRM ^ j) +> encMidR ms ((wT ^ (6 * j)) +> encR (buildAdvTowerD01 tw (6 * j))) =
      encMidR ([.mid j] ++ ms ++ [.t (6 * j)]) (encR (buildAdvTowerD01 tw (6 * j))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
  rw [hR0]
  have t0 := eraE_turn_0
    (encMidR ([.mid j] ++ ms ++ [.t (6 * j)]) (encR (buildAdvTowerD01 tw (6 * j))))
  have b0 := bounce_M_thm (refl_tower_d01_step tw htw (6 * j) (by omega))
    ([.mid j] ++ ms ++ [.t (6 * j)]) (eL1 +> default)
  rw [eraE_advance_t] at b0
  have t1 := eraE_turn_1
    (encMidR ([.mid j] ++ ms ++ [.t (6 * j + 1)]) (encR (buildAdvTowerD01 tw (6 * j + 1))))
  have b1 := bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 1) (by omega))
    ([.mid j] ++ ms ++ [.t (6 * j + 1)]) (eL2 +> default)
  rw [eraE_advance_t] at b1
  have t2 := eraE_turn_2
    (encMidR ([.mid j] ++ ms ++ [.t (6 * j + 2)]) (encR (buildAdvTowerD01 tw (6 * j + 2))))
  have b2 := bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 2) (by omega))
    ([.mid j] ++ ms ++ [.t (6 * j + 2)]) (eL3 +> default)
  rw [eraE_advance_t] at b2
  have t3 := eraE_turn_3
    (encMidR ([.mid j] ++ ms ++ [.t (6 * j + 3)]) (encR (buildAdvTowerD01 tw (6 * j + 3))))
  have b3 := bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 3) (by omega))
    ([.mid j] ++ ms ++ [.t (6 * j + 3)]) (eL4 +> default)
  rw [eraE_advance_t] at b3
  have t4 := eraE_turn_4
    (encMidR ([.mid j] ++ ms ++ [.t (6 * j + 4)]) (encR (buildAdvTowerD01 tw (6 * j + 4))))
  have b4 := bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 4) (by omega))
    ([.mid j] ++ ms ++ [.t (6 * j + 4)]) (eL5 +> default)
  rw [eraE_advance_t] at b4
  have t5 := eraE_turn_5
    (encMidR ([.mid j] ++ ms ++ [.t (6 * j + 5)]) (encR (buildAdvTowerD01 tw (6 * j + 5))))
  have b5 := bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 5) (by omega))
    ([.mid j] ++ ms ++ [.t (6 * j + 5)]) (wLM +> (wT +> (wZ +> default)))
  rw [eraE_advance_t] at b5
  have h6j : 6 * j + 5 + 1 = 6 * (j + 1) := by omega
  rw [h6j] at b5
  have hR6 : encMidR ([.mid j] ++ ms ++ [.t (6 * (j + 1))])
      (encR (buildAdvTowerD01 tw (6 * (j + 1)))) =
      (wRM ^ j) +> encMidR ms ((wT ^ (6 * (j + 1))) +>
        encR (buildAdvTowerD01 tw (6 * (j + 1)))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
  rw [hR6] at b5
  have e1 := step_e_1011_wLM (wT +> (wZ +> default))
    ((wRM ^ j) +> encMidR ms ((wT ^ (6 * (j + 1))) +> encR (buildAdvTowerD01 tw (6 * (j + 1)))))
  rw [← ListBlank.append_pow_succ wRM j] at e1
  have e2 := step_e_1011_wT (wZ +> default)
    ((wRM ^ (j + 1)) +> encMidR ms ((wT ^ (6 * (j + 1))) +>
      encR (buildAdvTowerD01 tw (6 * (j + 1)))))
  have e3 := step_e_1011_wZ (default : ListBlank (Fin 2))
    (wZ +> ((wRM ^ (j + 1)) +> encMidR ms ((wT ^ (6 * (j + 1))) +>
      encR (buildAdvTowerD01 tw (6 * (j + 1))))))
  have hw0 := eraE_w3 ms j (6 * j)
  have hw1 := eraE_w3 ms j (6 * j + 1)
  have hw2 := eraE_w3 ms j (6 * j + 2)
  have hw3' := eraE_w3 ms j (6 * j + 3)
  have hw4 := eraE_w3 ms j (6 * j + 4)
  have hw5 := eraE_w3 ms j (6 * j + 5)
  have s01 := (t0.trans b0).trans (t1.trans b1)
  have s23 := (t2.trans b2).trans (t3.trans b3)
  have s45 := (t4.trans b4).trans (t5.trans b5)
  have se := (e1.trans e2).trans e3
  have hchain := ((s01.trans s23).trans s45).trans se
  refine rcast hchain ?_
  rw [hw0, hw1, hw2, hw3', hw4, hw5]
  ring

private theorem era_E_cost_step (w3 m : ℕ) :
    ((m + 1) * (132 * w3 + 865) + 594 * (m + 1) * m) + (865 + 132 * w3 + 1188 * (m + 1)) =
      (m + 1 + 1) * (132 * w3 + 865) + 594 * (m + 1 + 1) * (m + 1) := by
  ring

private theorem era_E_loop (ms : List MidItem) (tw : TowerD01) (htw : TowerWF tw) :
    ∀ (n : ℕ), 6 * n ≤ maxReflD01 tw →
      ReachesIn target_tm
        (n * (132 * w3Mid ms + 865) + 594 * n * (n - 1) + towerCostD01 tw (6 * n))
        (eraECfg ms tw 0) (eraECfg ms tw n)
  | 0, _ => by
    have hz : towerCostD01 tw 0 = 0 := by cases tw <;> simp [towerCostD01]
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, hz]
    exact ReachesIn.zero _ _
  | n + 1, hn => by
    have hprev := era_E_loop ms tw htw n (by omega)
    have hstep := era_E_one_cycle ms tw htw n hn
    have tc0 := towerCostD01_succ tw (6 * n)
    have tc1 := towerCostD01_succ tw (6 * n + 1)
    have tc2 := towerCostD01_succ tw (6 * n + 2)
    have tc3 := towerCostD01_succ tw (6 * n + 3)
    have tc4 := towerCostD01_succ tw (6 * n + 4)
    have tc5 := towerCostD01_succ tw (6 * n + 5)
    have h6n : 6 * n + 5 + 1 = 6 * (n + 1) := by omega
    rw [h6n] at tc5
    have htc : towerCostD01 tw (6 * (n + 1)) = towerCostD01 tw (6 * n) +
        (towerStepCostD01 tw (6 * n) + towerStepCostD01 tw (6 * n + 1) +
          towerStepCostD01 tw (6 * n + 2) + towerStepCostD01 tw (6 * n + 3) +
          towerStepCostD01 tw (6 * n + 4) + towerStepCostD01 tw (6 * n + 5)) := by
      rw [tc5, tc4, tc3, tc2, tc1, tc0]
      ac_rfl
    have hquad : (n * (132 * w3Mid ms + 865) + 594 * n * (n - 1)) +
        (865 + 132 * w3Mid ms + 1188 * n) =
        (n + 1) * (132 * w3Mid ms + 865) + 594 * (n + 1) * ((n + 1) - 1) := by
      cases n with
      | zero =>
        simp only [Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
          Nat.one_mul]
        ring
      | succ m =>
        simp only [Nat.add_sub_cancel]
        exact era_E_cost_step (w3Mid ms) m
    have hchain := hprev.trans hstep
    refine rcast hchain ?_
    rw [htc, ← hquad]
    ac_rfl


private theorem L11_peel_01_13 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 13
      (cfgE ([1, 0, 1, 1, 0, 1] +> (wLM +> l)) ([0] +> r))
      (cfgE ([1, 0, 1, 1] +> (wZ +> (wZ +> l))) ([0, 1] +> (wZ +> ([0] +> r)))) := by
  dsimp only [cfgE, wLM, wZ]; bb_steps_in

private theorem L11_mid_dip_23 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 23
      (cfgA ((wZ ^ 2) +> (wLM +> l)) ([1, 0, 1, 1, 0, 1] +> (wZ +> r)))
      (cfgA ([0, 1] +> ((wZ ^ 2) +> l)) ([1, 0, 1, 1] +> ((wT ^ 4) +> r))) := by
  dsimp only [cfgA, wZ, wLM, wT, pow_succ_list, pow_zero_list]; bb_steps_in

private theorem L11_dip_wZ_30 (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 30
      (cfgE ([1, 0, 1, 1, 0, 1] +> (wZ +> l)) (wT +> r))
      (cfgA ([0, 1] +> l) ([1, 0, 1, 1] +> ((wT ^ 2) +> r))) := by
  dsimp only [cfgE, cfgA, wZ, wT, pow_succ_list, pow_zero_list]; bb_steps_in

private theorem encMidR_zero_head : ∀ (ms : List MidItem) (r : ListBlank (Fin 2)),
    (∃ tail, r = [0] +> tail) → ∃ tail', encMidR ms r = [0] +> tail'
  | [], r, hr => hr
  | .mid 0 :: ms, r, hr => encMidR_zero_head ms r hr
  | .mid (k + 1) :: ms, r, _ => by
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wRM k]
    exact ⟨[1, 1, 0, 1, 1, 0, 0, 1] +> ((wRM ^ k) +> encMidR ms r), rfl⟩
  | .t 0 :: ms, r, hr => encMidR_zero_head ms r hr
  | .t (k + 1) :: ms, r, _ => by
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wT k]
    exact ⟨[1, 1] +> ((wT ^ k) +> encMidR ms r), rfl⟩
  | .z 0 :: ms, r, hr => encMidR_zero_head ms r hr
  | .z (k + 1) :: ms, r, _ => by
    dsimp only [encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wZ k]
    exact ⟨[0, 1] +> ((wZ ^ k) +> encMidR ms r), rfl⟩

private theorem wT_pow_zero_head (q : ℕ) (r : ListBlank (Fin 2))
    (hr : ∃ tail, r = [0] +> tail) :
    ∃ tail', (wT ^ q) +> r = [0] +> tail' := by
  cases q with
  | zero => exact hr
  | succ q' =>
    rw [ListBlank.append_pow_succ wT q']
    exact ⟨[1, 1] +> ((wT ^ q') +> r), rfl⟩

private theorem L11_step3 {T_in T_out : ListBlank (Fin 2)} {cT : ℕ}
    (m_mid m_out q tb b_rem : ℕ) (ms : List MidItem) (rt : ListBlank (Fin 2))
    (hT : ∀ r, ReachesIn target_tm (66 * m_mid + cT)
      (cfgE ([1, 0, 1, 1] +> ((wLM ^ m_mid) +> T_in)) r)
      (cfgA (wLM +> ((wLM ^ m_out) +> T_out)) ([1, 0, 1, 1] +> r))) :
    ReachesIn target_tm (482 + 66 * m_mid + cT + 44 * q + 44 * tb + 44 * w3Mid ms)
      (cfgE ([1, 0, 1, 1] +> ([0, 1] +> (wLM +> ((wLM ^ m_mid) +> T_in))))
        ((wT ^ q) +> encMidR ms ((wT ^ (tb + 1)) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 2)) +> rt)))))
      (cfgA ([0, 1] +> ((wLM ^ m_out) +> T_out))
        ([1, 0, 1, 1] +> ((wT ^ (q + 6)) +>
          encMidR ms ((wT ^ (tb + 3)) +> ([0, 1, 1, 1] +> ((wT ^ b_rem) +> rt)))))) := by
  set R_start := (wT ^ q) +> encMidR ms ((wT ^ (tb + 1)) +>
    ([0, 1, 1, 1] +> ((wT ^ (b_rem + 2)) +> rt)))
  have hR0 : ∃ tail0, R_start = [0] +> tail0 := by
    apply wT_pow_zero_head
    apply encMidR_zero_head
    rw [ListBlank.append_pow_succ wT tb]
    exact ⟨[1, 1] +> ((wT ^ tb) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 2)) +> rt))), rfl⟩
  obtain ⟨tail0, htail0⟩ := hR0
  have hL_in : [1, 0, 1, 1] +> ([0, 1] +> (wLM +> ((wLM ^ m_mid) +> T_in))) =
      [1, 0, 1, 1, 0, 1] +> (wLM +> ((wLM ^ m_mid) +> T_in)) := rfl
  rw [hL_in]
  have s1 := L11_peel_01_13 ((wLM ^ m_mid) +> T_in) tail0
  rw [← htail0] at s1
  have s2a := step_e_1011_wZ (wZ +> ((wLM ^ m_mid) +> T_in)) ([0, 1] +> (wZ +> R_start))
  have s2b := step_e_1011_wZ ((wLM ^ m_mid) +> T_in) (wT +> ([0, 1] +> (wZ +> R_start)))
  have s3 := hT (wT +> (wT +> ([0, 1] +> (wZ +> R_start))))
  have s4a := step_a_1011_wT (wLM +> ((wLM ^ m_out) +> T_out)) (wT +> ([0, 1] +> (wZ +> R_start)))
  have s4b := step_a_1011_wT (wZ +> (wLM +> ((wLM ^ m_out) +> T_out))) ([0, 1] +> (wZ +> R_start))
  have hs4L : wZ +> (wZ +> (wLM +> ((wLM ^ m_out) +> T_out))) =
      (wZ ^ 2) +> (wLM +> ((wLM ^ m_out) +> T_out)) := rfl
  have hs4R : [1, 0, 1, 1] +> ([0, 1] +> (wZ +> R_start)) =
      [1, 0, 1, 1, 0, 1] +> (wZ +> R_start) := rfl
  rw [hs4L, hs4R] at s4b
  have s5 := L11_mid_dip_23 ((wLM ^ m_out) +> T_out) R_start
  have hRA : (wT ^ 4) +> R_start =
      encMidR ([.t (4 + q)] ++ ms ++ [.t (tb + 1)])
        ([0, 1, 1, 1] +> (wT +> ((wT ^ (b_rem + 1)) +> rt))) := by
    dsimp only [R_start]
    simp only [encMidR_append, encMidR, encMidItemR]
    rw [pow_append_pow wT 4 q, ListBlank.append_pow_succ wT (b_rem + 1)]
  rw [hRA] at s5
  have bA := bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^ (b_rem + 1)) +> rt))
    ([.t (4 + q)] ++ ms ++ [.t (tb + 1)]) ([0, 1] +> ((wZ ^ 2) +> ((wLM ^ m_out) +> T_out)))
  have hbAL : [1, 0, 1, 1] +> ([0, 1] +> ((wZ ^ 2) +> ((wLM ^ m_out) +> T_out))) =
      [1, 0, 1, 1, 0, 1] +> (wZ +> (wZ +> ((wLM ^ m_out) +> T_out))) := rfl
  have hbAR : encMidR ([.t (4 + q)] ++ ms ++ [.t (tb + 1)])
      (wT +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 1)) +> rt))) =
      wT +> ((wT ^ (3 + q)) +> encMidR ms
        ((wT ^ (tb + 2)) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 1)) +> rt)))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
    have h4q : 4 + q = (3 + q) + 1 := by omega
    rw [h4q, ListBlank.append_pow_succ wT (3 + q)]
    rw [ListBlank.append_pow_comm wT (tb + 1), ← ListBlank.append_pow_succ wT (tb + 1)]
  rw [hbAL, hbAR] at bA
  have s6 := L11_dip_wZ_30 (wZ +> ((wLM ^ m_out) +> T_out))
    ((wT ^ (3 + q)) +> encMidR ms ((wT ^ (tb + 2)) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 1)) +> rt))))
  have hs6R : (wT ^ 2) +> ((wT ^ (3 + q)) +> encMidR ms
      ((wT ^ (tb + 2)) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 1)) +> rt)))) =
      encMidR ([.t (5 + q)] ++ ms ++ [.t (tb + 2)])
        ([0, 1, 1, 1] +> (wT +> ((wT ^ b_rem) +> rt))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
    rw [pow_append_pow wT 2 (3 + q), ListBlank.append_pow_succ wT b_rem]
    have h23 : 2 + (3 + q) = 5 + q := by omega
    rw [h23]
  rw [hs6R] at s6
  have bB := bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^ b_rem) +> rt))
    ([.t (5 + q)] ++ ms ++ [.t (tb + 2)]) ([0, 1] +> (wZ +> ((wLM ^ m_out) +> T_out)))
  have hbBL : [1, 0, 1, 1] +> ([0, 1] +> (wZ +> ((wLM ^ m_out) +> T_out))) =
      [1, 0, 1, 1, 0, 1] +> (wZ +> ((wLM ^ m_out) +> T_out)) := rfl
  have hbBR : encMidR ([.t (5 + q)] ++ ms ++ [.t (tb + 2)])
      (wT +> ([0, 1, 1, 1] +> ((wT ^ b_rem) +> rt))) =
      wT +> ((wT ^ (4 + q)) +> encMidR ms
        ((wT ^ (tb + 3)) +> ([0, 1, 1, 1] +> ((wT ^ b_rem) +> rt)))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
    have h5q : 5 + q = (4 + q) + 1 := by omega
    rw [h5q, ListBlank.append_pow_succ wT (4 + q)]
    rw [ListBlank.append_pow_comm wT (tb + 2), ← ListBlank.append_pow_succ wT (tb + 2)]
  rw [hbBL, hbBR] at bB
  have s7 := L11_dip_wZ_30 ((wLM ^ m_out) +> T_out)
    ((wT ^ (4 + q)) +> encMidR ms ((wT ^ (tb + 3)) +> ([0, 1, 1, 1] +> ((wT ^ b_rem) +> rt))))
  rw [pow_append_pow wT 2 (4 + q)] at s7
  have h24 : 2 + (4 + q) = q + 6 := by omega
  rw [h24] at s7
  have hwA : w3Mid ([.t (4 + q)] ++ ms ++ [.t (tb + 1)]) = 4 + q + w3Mid ms + (tb + 1) := by
    simp only [w3Mid_append, w3Mid, w3Item]; omega
  have hwB : w3Mid ([.t (5 + q)] ++ ms ++ [.t (tb + 2)]) = 5 + q + w3Mid ms + (tb + 2) := by
    simp only [w3Mid_append, w3Mid, w3Item]; omega
  exact (((((((((s1.trans s2a).trans s2b).trans s3).trans s4a).trans s4b).trans s5).trans
    bA).trans s6).trans bB).trans s7 |> (rcast · (by omega))

private theorem L11_bounce_step {T_cur : ListBlank (Fin 2)}
    (m_out q tb b_rem : ℕ) (ms : List MidItem) (rt : ListBlank (Fin 2)) :
    ReachesIn target_tm (22 * (q + w3Mid ms + tb) + 39)
      (cfgA ([0, 1] +> ((wLM ^ (m_out + 1)) +> T_cur))
        ([1, 0, 1, 1] +> ((wT ^ q) +>
          encMidR ms ((wT ^ tb) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 3)) +> rt))))))
      (cfgE ([1, 0, 1, 1] +> ([0, 1] +> (wLM +> ((wLM ^ m_out) +> T_cur))))
        ((wT ^ q) +> encMidR ms
          ((wT ^ (tb + 1)) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 2)) +> rt))))) := by
  rw [ListBlank.append_pow_succ wLM m_out]
  have hR_in : (wT ^ q) +> encMidR ms ((wT ^ tb) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 3)) +> rt))) =
      encMidR ([.t q] ++ ms ++ [.t tb]) ([0, 1, 1, 1] +> (wT +> ((wT ^ (b_rem + 2)) +> rt))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
    rw [ListBlank.append_pow_succ wT (b_rem + 2)]
  rw [hR_in]
  have hb := bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^ (b_rem + 2)) +> rt))
    ([.t q] ++ ms ++ [.t tb]) ([0, 1] +> (wLM +> ((wLM ^ m_out) +> T_cur)))
  have hR_out : encMidR ([.t q] ++ ms ++ [.t tb])
      (wT +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 2)) +> rt))) =
      (wT ^ q) +> encMidR ms ((wT ^ (tb + 1)) +> ([0, 1, 1, 1] +> ((wT ^ (b_rem + 2)) +> rt))) := by
    simp only [encMidR_append, encMidR, encMidItemR]
    rw [ListBlank.append_pow_comm wT tb, ← ListBlank.append_pow_succ wT tb]
  rw [hR_out] at hb
  have hw : w3Mid ([.t q] ++ ms ++ [.t tb]) = q + w3Mid ms + tb := by
    simp only [w3Mid_append, w3Mid, w3Item]; omega
  exact rcast (hb) (by omega)

private theorem L11_turn_succ {T_in T_out : ListBlank (Fin 2)} {cT : ℕ}
    (hT : ∀ r, ReachesIn target_tm cT (cfgE ([1, 0, 1, 1] +> T_in) r)
      (cfgA T_out ([1, 0, 1, 1] +> r)))
    (m_out : ℕ) (r : ListBlank (Fin 2)) :
    ReachesIn target_tm (66 * (m_out + 1) + cT)
      (cfgE ([1, 0, 1, 1] +> ((wLM ^ (m_out + 1)) +> T_in)) r)
      (cfgA (wLM +> ((wLM ^ m_out) +> T_out)) ([1, 0, 1, 1] +> r)) := by
  have h := roundtrip_mid_L hT [.mid (m_out + 1)] r
  dsimp only [encMidL, encMidItemL, w3Mid, w3Item] at h
  have hout : (wLM ^ (m_out + 1)) +> T_out = wLM +> ((wLM ^ m_out) +> T_out) := by
    rw [ListBlank.append_pow_succ wLM m_out]
  rw [hout] at h
  exact rcast (h) (by omega)

private theorem L11_turn_last (m_out : ℕ) (r : ListBlank (Fin 2)) :
    ReachesIn target_tm (66 * m_out + 65)
      (cfgE ([1, 0, 1, 1] +> ((wLM ^ m_out) +> tailL5)) r)
      (cfgA (wLM +> ((wLM ^ m_out) +> tailL0)) ([1, 0, 1, 1] +> r)) := by
  have h := roundtrip_mid_L left_turn_5 [.mid m_out] r
  dsimp only [encMidL, encMidItemL, w3Mid, w3Item, tailL6] at h
  rw [ListBlank.append_pow_comm wLM m_out] at h
  exact rcast (h) (by omega)

def eraL11Cfg (remMidL : ℕ) (ms : List MidItem) (B : ℕ) (rt : ListBlank (Fin 2))
    (K n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgA ([0, 1] +> ((wLM ^ (remMidL + 11 * (K - n))) +> tailL0))
    ([1, 0, 1, 1] +> ((wT ^ (36 * n)) +>
      encMidR ms ((wT ^ (18 * n)) +> ([0, 1, 1, 1] +> ((wT ^ (B - 18 * n)) +> rt)))))

private theorem era_L11_d0_one (remMidL : ℕ) (ms : List MidItem) (B : ℕ) (rt : ListBlank (Fin 2))
    (K n : ℕ) (hn : n < K) (hB : 18 * K ≤ B) :
    ReachesIn target_tm
      (14440 + 396 * (remMidL + 11 * (K - 1 - n)) + 396 * w3Mid ms + 396 * (54 * n))
      (eraL11Cfg remMidL ms B rt K n) (eraL11Cfg remMidL ms B rt K (n + 1)) := by
  dsimp only [eraL11Cfg]
  set m' := remMidL + 11 * (K - 1 - n)
  set q0 := 36 * n
  set tb0 := 18 * n
  set b0 := B - 18 * (n + 1)
  have hm_in : remMidL + 11 * (K - n) = (m' + 10) + 1 := by omega
  have hb_in : B - 18 * n = (b0 + 15) + 3 := by omega
  have hm_out : remMidL + 11 * (K - (n + 1)) = m' := by omega
  have hq_out : 36 * (n + 1) = (q0 + 30) + 6 := by omega
  have htb_out : 18 * (n + 1) = (tb0 + 15) + 3 := by omega
  rw [hm_in, hb_in, hm_out, hq_out, htb_out]
  have p0a := L11_bounce_step (T_cur := tailL0) (m' + 10) q0 tb0 (b0 + 15) ms rt
  have p0b := L11_step3 (m' + 10) (m' + 9) q0 tb0 (b0 + 15) ms rt
    (L11_turn_succ left_turn_0 (m' + 9))
  have hm1 : m' + 9 = (m' + 8) + 1 := by omega
  have hb1 : b0 + 15 = (b0 + 12) + 3 := by omega
  rw [hm1, hb1] at p0b
  have s0 := p0a.trans p0b
  have p1a := L11_bounce_step (T_cur := tailL1) (m' + 8) (q0 + 6) (tb0 + 3) (b0 + 12) ms rt
  have p1b := L11_step3 (m' + 8) (m' + 7) (q0 + 6) (tb0 + 3) (b0 + 12) ms rt
    (L11_turn_succ left_turn_1 (m' + 7))
  have hm2 : m' + 7 = (m' + 6) + 1 := by omega
  have hb2 : b0 + 12 = (b0 + 9) + 3 := by omega
  have hq2 : (q0 + 6) + 6 = q0 + 12 := by omega
  have htb2 : (tb0 + 3) + 3 = tb0 + 6 := by omega
  rw [hm2, hb2, hq2, htb2] at p1b
  have s1 := p1a.trans p1b
  have p2a := L11_bounce_step (T_cur := tailL2) (m' + 6) (q0 + 12) (tb0 + 6) (b0 + 9) ms rt
  have p2b := L11_step3 (m' + 6) (m' + 5) (q0 + 12) (tb0 + 6) (b0 + 9) ms rt
    (L11_turn_succ left_turn_2 (m' + 5))
  have hm3 : m' + 5 = (m' + 4) + 1 := by omega
  have hb3 : b0 + 9 = (b0 + 6) + 3 := by omega
  have hq3 : (q0 + 12) + 6 = q0 + 18 := by omega
  have htb3 : (tb0 + 6) + 3 = tb0 + 9 := by omega
  rw [hm3, hb3, hq3, htb3] at p2b
  have s2 := p2a.trans p2b
  have p3a := L11_bounce_step (T_cur := tailL3) (m' + 4) (q0 + 18) (tb0 + 9) (b0 + 6) ms rt
  have p3b := L11_step3 (m' + 4) (m' + 3) (q0 + 18) (tb0 + 9) (b0 + 6) ms rt
    (L11_turn_succ left_turn_3 (m' + 3))
  have hm4 : m' + 3 = (m' + 2) + 1 := by omega
  have hb4 : b0 + 6 = (b0 + 3) + 3 := by omega
  have hq4 : (q0 + 18) + 6 = q0 + 24 := by omega
  have htb4 : (tb0 + 9) + 3 = tb0 + 12 := by omega
  rw [hm4, hb4, hq4, htb4] at p3b
  have s3 := p3a.trans p3b
  have p4a := L11_bounce_step (T_cur := tailL4) (m' + 2) (q0 + 24) (tb0 + 12) (b0 + 3) ms rt
  have p4b := L11_step3 (m' + 2) (m' + 1) (q0 + 24) (tb0 + 12) (b0 + 3) ms rt
    (L11_turn_succ left_turn_4 (m' + 1))
  have hq5 : (q0 + 24) + 6 = q0 + 30 := by omega
  have htb5 : (tb0 + 12) + 3 = tb0 + 15 := by omega
  rw [hq5, htb5] at p4b
  have s4 := p4a.trans p4b
  have p5a := L11_bounce_step (T_cur := tailL5) m' (q0 + 30) (tb0 + 15) b0 ms rt
  have p5b := L11_step3 m' m' (q0 + 30) (tb0 + 15) b0 ms rt (L11_turn_last m')
  have s5 := p5a.trans p5b
  have hchain := ((s0.trans s1).trans (s2.trans s3)).trans (s4.trans s5)
  refine rcast hchain ?_
  ring

private theorem era_L11_loop_cost_step (rem w3 K_rem m : ℕ) :
    ((m + 1) * (14440 + 396 * rem + 396 * w3 + 4356 * (K_rem + (m + 1))) + 8514 * (m + 1) * m) +
        (14440 + 396 * (rem + 11 * K_rem) + 396 * w3 + 396 * (54 * (m + 1))) =
      (m + 1 + 1) * (14440 + 396 * rem + 396 * w3 + 4356 * (K_rem + (m + 1))) +
        8514 * (m + 1 + 1) * (m + 1) := by
  ring

private theorem era_L11_cost_at_K (rem w3 m : ℕ) :
    (m + 1) * (14440 + 396 * rem + 396 * w3 + 4356 * m) + 8514 * (m + 1) * m =
      (m + 1) * (13738 + 396 * rem + 396 * w3) + 12870 * (m + 1) * m + 39 * (18 * (m + 1)) := by
  ring

private theorem era_L11_d0_loop (remMidL : ℕ) (ms : List MidItem) (B : ℕ) (rt : ListBlank (Fin 2))
    (K : ℕ) (hB : 18 * K ≤ B) :
    ∀ (n : ℕ), n ≤ K →
      ReachesIn target_tm
        (n * (14440 + 396 * remMidL + 396 * w3Mid ms + 4356 * (K - 1)) + 8514 * n * (n - 1))
        (eraL11Cfg remMidL ms B rt K 0) (eraL11Cfg remMidL ms B rt K n)
  | 0, _ => by
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    exact ReachesIn.zero _ _
  | n + 1, hn => by
    have hprev := era_L11_d0_loop remMidL ms B rt K hB n (by omega)
    have hstep := era_L11_d0_one remMidL ms B rt K n (by omega) hB
    have hcost : (n * (14440 + 396 * remMidL + 396 * w3Mid ms + 4356 * (K - 1)) +
          8514 * n * (n - 1)) +
        (14440 + 396 * (remMidL + 11 * (K - 1 - n)) + 396 * w3Mid ms + 396 * (54 * n)) =
        (n + 1) * (14440 + 396 * remMidL + 396 * w3Mid ms + 4356 * (K - 1)) +
          8514 * (n + 1) * ((n + 1) - 1) := by
      cases n with
      | zero =>
        simp only [Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
          Nat.one_mul, Nat.sub_zero]
        ring
      | succ m =>
        simp only [Nat.add_sub_cancel]
        set K_rem := K - 1 - (m + 1)
        have hK1 : K - 1 = K_rem + (m + 1) := by omega
        rw [hK1]
        exact era_L11_loop_cost_step remMidL (w3Mid ms) K_rem m
    exact rcast ((hprev.trans hstep)) hcost

/-! ### Symbolic Linear-Form (`SymN`) Engine & Soundness -/

structure SymN where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  k  : ℕ
  deriving DecidableEq, Repr

def evalSymN (v : Fin 5 → ℕ) (x : SymN) : ℕ :=
  x.c0 * v 0 + x.c1 * v 1 + x.c2 * v 2 + x.c3 * v 3 + x.c4 * v 4 + x.k

def symConst (k : ℕ) : SymN := ⟨0, 0, 0, 0, 0, k⟩
def symZero : SymN := ⟨0, 0, 0, 0, 0, 0⟩
def symOne : SymN := ⟨0, 0, 0, 0, 0, 1⟩

def symIsZero (x : SymN) : Bool :=
  x.c0 == 0 && x.c1 == 0 && x.c2 == 0 && x.c3 == 0 && x.c4 == 0 && x.k == 0

def symIsConst (x : SymN) : Bool :=
  x.c0 == 0 && x.c1 == 0 && x.c2 == 0 && x.c3 == 0 && x.c4 == 0

def symIsConst1 (x : SymN) : Bool :=
  x.c0 == 0 && x.c1 == 0 && x.c2 == 0 && x.c3 == 0 && x.c4 == 0 && x.k == 1

def symAdd (x y : SymN) : SymN :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3, x.c4 + y.c4, x.k + y.k⟩

def symAdd1 (x y : SymN) : SymN :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3, x.c4 + y.c4, x.k + y.k + 1⟩

def symAddConst (x : SymN) (n : ℕ) : SymN :=
  ⟨x.c0, x.c1, x.c2, x.c3, x.c4, x.k + n⟩

def symScale (m : ℕ) (x : SymN) : SymN :=
  ⟨m * x.c0, m * x.c1, m * x.c2, m * x.c3, m * x.c4, m * x.k⟩

def symSub (x y : SymN) : Option SymN :=
  if y.c0 ≤ x.c0 && y.c1 ≤ x.c1 && y.c2 ≤ x.c2 && y.c3 ≤ x.c3 && y.c4 ≤ x.c4 && y.k ≤ x.k then
    some ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2, x.c3 - y.c3, x.c4 - y.c4, x.k - y.k⟩
  else none

def symLe (x y : SymN) : Bool :=
  decide (x.c0 ≤ y.c0) && decide (x.c1 ≤ y.c1) && decide (x.c2 ≤ y.c2) &&
    decide (x.c3 ≤ y.c3) && decide (x.c4 ≤ y.c4) && decide (x.k ≤ y.k)

def symDivMod (x : SymN) (d : ℕ) : Option (SymN × ℕ) :=
  if decide (0 < d) && x.c0 % d == 0 && x.c1 % d == 0 && x.c2 % d == 0 &&
      x.c3 % d == 0 && x.c4 % d == 0 then
    some (⟨x.c0 / d, x.c1 / d, x.c2 / d, x.c3 / d, x.c4 / d, x.k / d⟩, x.k % d)
  else none

inductive SymDec : Type
  | isZero
  | isSucc (x' : SymN)
  | stuck
  deriving DecidableEq, Repr

def symDec (x : SymN) : SymDec :=
  match x.k with
  | k' + 1 => .isSucc ⟨x.c0, x.c1, x.c2, x.c3, x.c4, k'⟩
  | 0 =>
    if x.c0 == 0 && x.c1 == 0 && x.c2 == 0 && x.c3 == 0 && x.c4 == 0 then .isZero
    else .stuck

private theorem evalSymN_const (v : Fin 5 → ℕ) (k : ℕ) :
    evalSymN v (symConst k) = k := by
  simp [evalSymN, symConst]

private theorem evalSymN_zero (v : Fin 5 → ℕ) : evalSymN v symZero = 0 := by
  simp [evalSymN, symZero]

private theorem evalSymN_one (v : Fin 5 → ℕ) : evalSymN v symOne = 1 := by
  simp [evalSymN, symOne]

private theorem evalSymN_isZero {v : Fin 5 → ℕ} {x : SymN} (h : symIsZero x = true) :
    evalSymN v x = 0 := by
  unfold symIsZero at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hk⟩
  simp [evalSymN, h0, h1, h2, h3, h4, hk]

private theorem evalSymN_isConst {v : Fin 5 → ℕ} {x : SymN} (h : symIsConst x = true) :
    evalSymN v x = x.k := by
  unfold symIsConst at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
  simp [evalSymN, h0, h1, h2, h3, h4]

private theorem evalSymN_isConst1 {v : Fin 5 → ℕ} {x : SymN} (h : symIsConst1 x = true) :
    evalSymN v x = 1 := by
  unfold symIsConst1 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hk⟩
  simp [evalSymN, h0, h1, h2, h3, h4, hk]

private theorem evalSymN_add (v : Fin 5 → ℕ) (x y : SymN) :
    evalSymN v (symAdd x y) = evalSymN v x + evalSymN v y := by
  dsimp only [evalSymN, symAdd]; ring

private theorem evalSymN_add1 (v : Fin 5 → ℕ) (x y : SymN) :
    evalSymN v (symAdd1 x y) = evalSymN v x + evalSymN v y + 1 := by
  dsimp only [evalSymN, symAdd1]; ring

private theorem evalSymN_addConst (v : Fin 5 → ℕ) (x : SymN) (n : ℕ) :
    evalSymN v (symAddConst x n) = evalSymN v x + n := by
  dsimp only [evalSymN, symAddConst]; omega

private theorem evalSymN_scale (v : Fin 5 → ℕ) (m : ℕ) (x : SymN) :
    evalSymN v (symScale m x) = m * evalSymN v x := by
  dsimp only [evalSymN, symScale]; ring

private theorem evalSymN_le {v : Fin 5 → ℕ} {x y : SymN} (h : symLe x y = true) :
    evalSymN v x ≤ evalSymN v y := by
  unfold symLe at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hk⟩
  have m0 := Nat.mul_le_mul_right (v 0) h0
  have m1 := Nat.mul_le_mul_right (v 1) h1
  have m2 := Nat.mul_le_mul_right (v 2) h2
  have m3 := Nat.mul_le_mul_right (v 3) h3
  have m4 := Nat.mul_le_mul_right (v 4) h4
  dsimp only [evalSymN]; omega

private theorem evalSymN_sub {v : Fin 5 → ℕ} {x y d : SymN} (h : symSub x y = some d) :
    evalSymN v y ≤ evalSymN v x ∧ evalSymN v d = evalSymN v x - evalSymN v y := by
  unfold symSub at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hk⟩
    have m0 := Nat.mul_le_mul_right (v 0) h0
    have m1 := Nat.mul_le_mul_right (v 1) h1
    have m2 := Nat.mul_le_mul_right (v 2) h2
    have m3 := Nat.mul_le_mul_right (v 3) h3
    have m4 := Nat.mul_le_mul_right (v 4) h4
    have s0 : (x.c0 - y.c0) * v 0 + y.c0 * v 0 = x.c0 * v 0 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h0]
    have s1 : (x.c1 - y.c1) * v 1 + y.c1 * v 1 = x.c1 * v 1 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h1]
    have s2 : (x.c2 - y.c2) * v 2 + y.c2 * v 2 = x.c2 * v 2 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h2]
    have s3 : (x.c3 - y.c3) * v 3 + y.c3 * v 3 = x.c3 * v 3 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h3]
    have s4 : (x.c4 - y.c4) * v 4 + y.c4 * v 4 = x.c4 * v 4 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h4]
    dsimp only [evalSymN]; omega

private theorem evalSymN_divMod {v : Fin 5 → ℕ} {x q : SymN} {d r : ℕ}
    (h : symDivMod x d = some (q, r)) :
    0 < d ∧ r < d ∧ evalSymN v x = d * evalSymN v q + r := by
  unfold symDivMod at h
  split_ifs at h with hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    rcases hc with ⟨⟨⟨⟨⟨hd, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩
    have q0 : d * (x.c0 / d) = x.c0 := by have := Nat.div_add_mod x.c0 d; omega
    have q1 : d * (x.c1 / d) = x.c1 := by have := Nat.div_add_mod x.c1 d; omega
    have q2 : d * (x.c2 / d) = x.c2 := by have := Nat.div_add_mod x.c2 d; omega
    have q3 : d * (x.c3 / d) = x.c3 := by have := Nat.div_add_mod x.c3 d; omega
    have q4 : d * (x.c4 / d) = x.c4 := by have := Nat.div_add_mod x.c4 d; omega
    have qk : d * (x.k / d) + x.k % d = x.k := Nat.div_add_mod x.k d
    refine ⟨hd, Nat.mod_lt x.k hd, ?_⟩
    dsimp only [evalSymN]
    calc x.c0 * v 0 + x.c1 * v 1 + x.c2 * v 2 + x.c3 * v 3 + x.c4 * v 4 + x.k
        = (d * (x.c0 / d)) * v 0 + (d * (x.c1 / d)) * v 1 + (d * (x.c2 / d)) * v 2 +
            (d * (x.c3 / d)) * v 3 + (d * (x.c4 / d)) * v 4 + (d * (x.k / d) + x.k % d) := by
          rw [q0, q1, q2, q3, q4, qk]
      _ = d * (x.c0 / d * v 0 + x.c1 / d * v 1 + x.c2 / d * v 2 + x.c3 / d * v 3 +
            x.c4 / d * v 4 + x.k / d) + x.k % d := by ring

private theorem symDec_isZero {v : Fin 5 → ℕ} {x : SymN} (h : symDec x = .isZero) :
    evalSymN v x = 0 := by
  rcases x with ⟨c0, c1, c2, c3, c4, k⟩
  cases k with
  | succ _ => simp [symDec] at h
  | zero =>
    dsimp only [symDec] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rcases hc with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
      simp [evalSymN, h0, h1, h2, h3, h4]

private theorem symDec_isSucc {v : Fin 5 → ℕ} {x x' : SymN} (h : symDec x = .isSucc x') :
    evalSymN v x = evalSymN v x' + 1 := by
  rcases x with ⟨c0, c1, c2, c3, c4, k⟩
  cases k with
  | zero =>
    dsimp only [symDec] at h
    split_ifs at h
  | succ k' =>
    dsimp only [symDec] at h
    injection h with hx; subst hx
    dsimp only [evalSymN]; omega

private theorem evalSymN_ge_k (v : Fin 5 → ℕ) (x : SymN) : x.k ≤ evalSymN v x := by
  dsimp only [evalSymN]; omega

/-! #### Symbolic Stack Types & Encoding -/

inductive SymLTok : Type
  | pair (z o : ℕ) (c : SymN)
  | mid (c : SymN)
  deriving DecidableEq, Repr

inductive SymRTok : Type
  | pair (z o : ℕ) (c : SymN)
  | mid (c : SymN)
  deriving DecidableEq, Repr

abbrev SymState : Type := Mode × List SymLTok × List SymRTok

def encSL (v : Fin 5 → ℕ) : List SymLTok → ListBlank (Fin 2)
  | [] => default
  | .pair z o c :: ts => ((pWord z o) ^ (evalSymN v c + 1)) +> encSL v ts
  | .mid c :: ts => (wLM ^ (evalSymN v c + 1)) +> encSL v ts

def encSR (v : Fin 5 → ℕ) : List SymRTok → ListBlank (Fin 2)
  | [] => default
  | .pair z o c :: ts => ((pWord z o) ^ (evalSymN v c + 1)) +> encSR v ts
  | .mid c :: ts => (wRM ^ (evalSymN v c + 1)) +> encSR v ts

def evalSym (v : Fin 5 → ℕ) : SymState → Cfg (Fin 2) (Fin 6)
  | (.mA, L, R) => cfgA (encSL v L) (encSR v R)
  | (.mD, L, R) => cfgD (encSL v L) (encSR v R)
  | (.mE, L, R) => cfgE (encSL v L) (encSR v R)
  | (.mHalt, L, R) => cfgHalt (encSL v L) (encSR v R)

def evalRTok (v : Fin 5 → ℕ) : SymRTok → RTok
  | .pair z o c => .pair z o (evalSymN v c)
  | .mid c => .mid (evalSymN v c)

private theorem encSR_eq_encR_map (v : Fin 5 → ℕ) : ∀ (R : List SymRTok),
    encSR v R = encR (R.map (evalRTok v))
  | [] => rfl
  | .pair z o c :: ts => by simp [encSR, encR, evalRTok, encSR_eq_encR_map v ts]
  | .mid c :: ts => by simp [encSR, encR, evalRTok, encSR_eq_encR_map v ts]

/-! #### Symbolic Stack Constructors & Soundness -/

def symDecPairL (z o : ℕ) (c : SymN) (ts : List SymLTok) : Option (List SymLTok) :=
  match symDec c with
  | .isZero => some ts
  | .isSucc c' => some (.pair z o c' :: ts)
  | .stuck => none

def symDecMidL (c : SymN) (ts : List SymLTok) : Option (List SymLTok) :=
  match symDec c with
  | .isZero => some ts
  | .isSucc c' => some (.mid c' :: ts)
  | .stuck => none

def symDecPairR (z o : ℕ) (c : SymN) (ts : List SymRTok) : Option (List SymRTok) :=
  match symDec c with
  | .isZero => some ts
  | .isSucc c' => some (.pair z o c' :: ts)
  | .stuck => none

def symDecMidR (c : SymN) (ts : List SymRTok) : Option (List SymRTok) :=
  match symDec c with
  | .isZero => some ts
  | .isSucc c' => some (.mid c' :: ts)
  | .stuck => none

def symPushLM (k : SymN) (L : List SymLTok) : Option (List SymLTok) :=
  match symDec k with
  | .isZero => some L
  | .isSucc k' =>
    match L with
    | .mid c :: ts => some (.mid (symAdd1 c k') :: ts)
    | ts => some (.mid k' :: ts)
  | .stuck => none

def symCoalesceL : List SymLTok → Option (List SymLTok)
  | .pair 1 1 c0 :: .pair 2 0 c2 :: rest =>
    if symIsZero c0 then
      if symIsConst1 c2 then
        symPushLM symOne rest
      else if 2 ≤ c2.k then
        symPushLM symOne (.pair 2 0 ⟨c2.c0, c2.c1, c2.c2, c2.c3, c2.c4, c2.k - 2⟩ :: rest)
      else if symIsZero c2 then
        some (.pair 1 1 c0 :: .pair 2 0 c2 :: rest)
      else none
    else some (.pair 1 1 c0 :: .pair 2 0 c2 :: rest)
  | L => some L

def symPushLPPre (z o : ℕ) (k' : SymN) : List SymLTok → List SymLTok
  | .pair z' o' c :: ts =>
    if z == z' && o == o' then .pair z o (symAdd1 c k') :: ts
    else .pair z o k' :: .pair z' o' c :: ts
  | ts => .pair z o k' :: ts

def symPushLP (z o : ℕ) (k : SymN) (L : List SymLTok) : Option (List SymLTok) :=
  match symDec k with
  | .isZero => some L
  | .isSucc k' => symCoalesceL (symPushLPPre z o k' L)
  | .stuck => none

def symNormL : List SymLTok → Option (List SymLTok)
  | .mid c :: ts =>
    match symDecMidL c ts with
    | none => none
    | some ts' => some (.pair 1 1 symZero :: .pair 2 0 symOne :: ts')
  | L => some L

def symPushZerosL (k : ℕ) (L : List SymLTok) : Option (List SymLTok) :=
  if k == 0 then some L
  else
    match symNormL L with
    | none => none
    | some [] => some []
    | some (.pair z o c :: ts) =>
      match symDecPairL z o c ts with
      | none => none
      | some ts' => symPushLP (z + k) o symOne ts'
    | some (.mid _ :: _) => none

def symPushOnesL (k : ℕ) (L : List SymLTok) : Option (List SymLTok) :=
  match k with
  | 0 => some L
  | k' + 1 =>
    match L with
    | [] => some [.pair 0 k' symZero]
    | .pair 0 o c :: ts =>
      match symDecPairL 0 o c ts with
      | none => none
      | some ts' => symPushLP 0 (o + k' + 1) symOne ts'
    | .pair (z' + 1) o c :: ts => symPushLP 0 k' symOne (.pair (z' + 1) o c :: ts)
    | .mid c :: ts => symPushLP 0 k' symOne (.mid c :: ts)

def symPushWLMSem (k : SymN) (L : List SymLTok) : Option (List SymLTok) :=
  match symDec k with
  | .isZero => some L
  | .isSucc k' =>
    match symPushLP 2 0 (symConst 2) L with
    | none => none
    | some L1 =>
      match symPushLP 1 1 symOne L1 with
      | none => none
      | some L2 => symPushLM k' L2
  | .stuck => none

def symPopBitL (L : List SymLTok) : Option (Fin 2 × List SymLTok) :=
  match symNormL L with
  | none => none
  | some [] => some (0, [])
  | some (.pair 0 0 c :: ts) =>
    match symDecPairL 0 0 c ts with
    | none => none
    | some ts' => some (1, ts')
  | some (.pair 0 (o' + 1) c :: ts) =>
    match symDecPairL 0 (o' + 1) c ts with
    | none => none
    | some ts' =>
      match symPushLP 0 o' symOne ts' with
      | none => none
      | some L' => some (1, L')
  | some (.pair (z' + 1) o c :: ts) =>
    match symDecPairL (z' + 1) o c ts with
    | none => none
    | some ts' =>
      match symPushLP z' o symOne ts' with
      | none => none
      | some L' => some (0, L')
  | some (.mid _ :: _) => none

def symPushRM (k : SymN) (R : List SymRTok) : Option (List SymRTok) :=
  match symDec k with
  | .isZero => some R
  | .isSucc k' =>
    match R with
    | .mid c :: ts => some (.mid (symAdd1 c k') :: ts)
    | ts => some (.mid k' :: ts)
  | .stuck => none

def symCoalesceR : List SymRTok → Option (List SymRTok)
  | .pair 1 1 c0 :: .pair 2 0 c1 :: rest =>
    if symIsConst1 c0 then
      match symDecPairR 2 0 c1 rest with
      | none => none
      | some rest' => symPushRM symOne rest'
    else some (.pair 1 1 c0 :: .pair 2 0 c1 :: rest)
  | R => some R

def symPushRPPre (z o : ℕ) (k' : SymN) : List SymRTok → List SymRTok
  | .pair z' o' c :: ts =>
    if z == z' && o == o' then .pair z o (symAdd1 c k') :: ts
    else .pair z o k' :: .pair z' o' c :: ts
  | ts => .pair z o k' :: ts

def symPushRP (z o : ℕ) (k : SymN) (R : List SymRTok) : Option (List SymRTok) :=
  match symDec k with
  | .isZero => some R
  | .isSucc k' => symCoalesceR (symPushRPPre z o k' R)
  | .stuck => none

def symNormR : List SymRTok → Option (List SymRTok)
  | .mid c :: ts =>
    match symDecMidR c ts with
    | none => none
    | some ts' => some (.pair 1 1 symOne :: .pair 2 0 symZero :: ts')
  | R => some R

def symPushZerosR (k : ℕ) (R : List SymRTok) : Option (List SymRTok) :=
  if k == 0 then some R
  else
    match symNormR R with
    | none => none
    | some [] => some []
    | some (.pair z o c :: ts) =>
      match symDecPairR z o c ts with
      | none => none
      | some ts' => symPushRP (z + k) o symOne ts'
    | some (.mid _ :: _) => none

def symPushOnesR (k : ℕ) (R : List SymRTok) : Option (List SymRTok) :=
  match k with
  | 0 => some R
  | k' + 1 =>
    match R with
    | [] => some [.pair 0 k' symZero]
    | .pair 0 o c :: ts =>
      match symDecPairR 0 o c ts with
      | none => none
      | some ts' => symPushRP 0 (o + k' + 1) symOne ts'
    | .pair (z' + 1) o c :: ts => symPushRP 0 k' symOne (.pair (z' + 1) o c :: ts)
    | .mid c :: ts => symPushRP 0 k' symOne (.mid c :: ts)

def symPushWRMSem (k : SymN) (R : List SymRTok) : Option (List SymRTok) :=
  match symDec k with
  | .isZero => some R
  | .isSucc k' =>
    match symPushRP 2 0 symOne R with
    | none => none
    | some R1 =>
      match symPushRP 1 1 (symConst 2) R1 with
      | none => none
      | some R2 => symPushRM k' R2
  | .stuck => none

def symPopBitR (R : List SymRTok) : Option (Fin 2 × List SymRTok) :=
  match symNormR R with
  | none => none
  | some [] => some (0, [])
  | some (.pair 0 0 c :: ts) =>
    match symDecPairR 0 0 c ts with
    | none => none
    | some ts' => some (1, ts')
  | some (.pair 0 (o' + 1) c :: ts) =>
    match symDecPairR 0 (o' + 1) c ts with
    | none => none
    | some ts' =>
      match symPushRP 0 o' symOne ts' with
      | none => none
      | some R' => some (1, R')
  | some (.pair (z' + 1) o c :: ts) =>
    match symDecPairR (z' + 1) o c ts with
    | none => none
    | some ts' =>
      match symPushRP z' o symOne ts' with
      | none => none
      | some R' => some (0, R')
  | some (.mid _ :: _) => none

/-! #### Symbolic Stack Encoding Proofs -/

private theorem encSL_decPairL {v : Fin 5 → ℕ} {z o : ℕ} {c : SymN} {ts out : List SymLTok}
    (h : symDecPairL z o c ts = some out) :
    (pWord z o) +> encSL v out = encSL v (.pair z o c :: ts) := by
  unfold symDecPairL at h
  rcases hd : symDec c with _ | c' | _
  · rw [hd] at h; injection h with h; subst h
    simp [encSL, symDec_isZero hd, pow_one_list]
  · rw [hd] at h; injection h with h; subst h
    simp only [encSL, symDec_isSucc hd]
    rw [← ListBlank.append_pow_succ]
  · rw [hd] at h; cases h

private theorem encSL_decMidL {v : Fin 5 → ℕ} {c : SymN} {ts out : List SymLTok}
    (h : symDecMidL c ts = some out) :
    wLM +> encSL v out = encSL v (.mid c :: ts) := by
  unfold symDecMidL at h
  rcases hd : symDec c with _ | c' | _
  · rw [hd] at h; injection h with h; subst h
    simp [encSL, symDec_isZero hd, pow_one_list]
  · rw [hd] at h; injection h with h; subst h
    simp only [encSL, symDec_isSucc hd]
    rw [← ListBlank.append_pow_succ]
  · rw [hd] at h; cases h

private theorem encSR_decPairR {v : Fin 5 → ℕ} {z o : ℕ} {c : SymN} {ts out : List SymRTok}
    (h : symDecPairR z o c ts = some out) :
    (pWord z o) +> encSR v out = encSR v (.pair z o c :: ts) := by
  unfold symDecPairR at h
  rcases hd : symDec c with _ | c' | _
  · rw [hd] at h; injection h with h; subst h
    simp [encSR, symDec_isZero hd, pow_one_list]
  · rw [hd] at h; injection h with h; subst h
    simp only [encSR, symDec_isSucc hd]
    rw [← ListBlank.append_pow_succ]
  · rw [hd] at h; cases h

private theorem encSR_decMidR {v : Fin 5 → ℕ} {c : SymN} {ts out : List SymRTok}
    (h : symDecMidR c ts = some out) :
    wRM +> encSR v out = encSR v (.mid c :: ts) := by
  unfold symDecMidR at h
  rcases hd : symDec c with _ | c' | _
  · rw [hd] at h; injection h with h; subst h
    simp [encSR, symDec_isZero hd, pow_one_list]
  · rw [hd] at h; injection h with h; subst h
    simp only [encSR, symDec_isSucc hd]
    rw [← ListBlank.append_pow_succ]
  · rw [hd] at h; cases h

private theorem encSL_pushLM {v : Fin 5 → ℕ} {k : SymN} {L out : List SymLTok}
    (h : symPushLM k L = some out) :
    encSL v out = (wLM ^ evalSymN v k) +> encSL v L := by
  unfold symPushLM at h
  rcases hd : symDec k with _ | k' | _
  · rw [hd] at h; injection h with h; subst h
    rw [symDec_isZero hd]; rfl
  · rw [hd] at h; rw [symDec_isSucc hd]
    cases L with
    | nil => injection h with h; subst h; rfl
    | cons t ts =>
      cases t with
      | pair _ _ _ => injection h with h; subst h; rfl
      | mid c =>
        injection h with h; subst h
        simp only [encSL, evalSymN_add1, pow_append_pow]
        congr 2; omega
  · rw [hd] at h; cases h

private theorem encSL_coalesceL {v : Fin 5 → ℕ} {L out : List SymLTok}
    (h : symCoalesceL L = some out) :
    encSL v out = encSL v L := by
  unfold symCoalesceL at h
  split at h
  · rename_i c0 c2 rest
    split_ifs at h with h0 h1 h2 hz
    · rw [encSL_pushLM h, evalSymN_one, pow_one_list]
      simp only [encSL, evalSymN_isZero h0, evalSymN_isConst1 h1, pWord_1_1, pWord_2_0]
      rfl
    · rw [encSL_pushLM h, evalSymN_one, pow_one_list]
      simp only [encSL, evalSymN_isZero h0, pWord_1_1, pWord_2_0]
      have hsub : evalSymN v c2 + 1 = 2 + (evalSymN v ⟨c2.c0, c2.c1, c2.c2, c2.c3, c2.c4,
        c2.k - 2⟩ + 1) := by
        dsimp only [evalSymN]; omega
      rw [hsub, ListBlank.append_pow_add wZ 2]
      rfl
    · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl
  · injection h with h; subst h; rfl

private theorem encSL_pushLP {v : Fin 5 → ℕ} {z o : ℕ} {k : SymN} {L out : List SymLTok}
    (h : symPushLP z o k L = some out) :
    encSL v out = ((pWord z o) ^ evalSymN v k) +> encSL v L := by
  unfold symPushLP at h
  rcases hd : symDec k with _ | k' | _
  · rw [hd] at h; injection h with h; subst h
    rw [symDec_isZero hd]; rfl
  · rw [hd] at h; rw [symDec_isSucc hd, encSL_coalesceL h]
    cases L with
    | nil => simp [symPushLPPre, encSL]
    | cons t ts =>
      cases t with
      | mid _ => simp [symPushLPPre, encSL]
      | pair z' o' c =>
        simp only [symPushLPPre]
        by_cases heq : ((z == z') && (o == o')) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true heq))]
          simp only [Bool.and_eq_true, beq_iff_eq] at heq
          rcases heq with ⟨rfl, rfl⟩
          simp only [encSL, evalSymN_add1, pow_append_pow]
          congr 2; omega
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false heq))]; simp [encSL]
  · rw [hd] at h; cases h

private theorem encSL_normL {v : Fin 5 → ℕ} {L out : List SymLTok}
    (h : symNormL L = some out) :
    encSL v out = encSL v L := by
  cases L with
  | nil => simp [symNormL] at h; subst h; rfl
  | cons t ts =>
    cases t with
    | pair _ _ _ => simp [symNormL] at h; subst h; rfl
    | mid c =>
      dsimp only [symNormL] at h
      rcases hd : symDecMidL c ts with _ | ts'
      · rw [hd] at h; cases h
      · rw [hd] at h; injection h with h; subst h
        rw [← encSL_decMidL hd]
        simp only [encSL, evalSymN_zero, evalSymN_one, pWord_1_1, pWord_2_0]
        rfl

private theorem encSL_pushZerosL {v : Fin 5 → ℕ} {k : ℕ} {L out : List SymLTok}
    (h : symPushZerosL k L = some out) :
    encSL v out = (([0] : List (Fin 2)) ^ k) +> encSL v L := by
  unfold symPushZerosL at h
  by_cases hk : (k == 0) = Bool.true
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hk))] at h; injection h with h; subst h
    have hk0 : k = 0 := eq_of_beq hk; subst hk0; rfl
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hk))] at h; try dsimp only at h
    rcases hn : symNormL L with _ | nL
    · rw [hn] at h; cases h
    · rw [hn] at h; rw [← encSL_normL hn]
      rcases nL with _ | ⟨t, ts⟩
      · injection h with h; subst h
        simp only [encSL]; exact (zeros_append_default k).symm
      · cases t with
        | mid _ => cases h
        | pair z o c =>
          try dsimp only at h
          rcases hd : symDecPairL z o c ts with _ | ts'
          · rw [hd] at h; cases h
          · rw [hd] at h; try dsimp only at h
            rw [encSL_pushLP h, evalSymN_one, pow_one_list, ← encSL_decPairL hd]
            simp only [pWord, replicate_eq_pow]
            rw [Nat.add_comm z k, list_pow_add]
            simp only [listblank_append_right_assoc]

private theorem encSL_pushOnesL {v : Fin 5 → ℕ} {k : ℕ} {L out : List SymLTok}
    (h : symPushOnesL k L = some out) :
    encSL v out = (([1] : List (Fin 2)) ^ k) +> encSL v L := by
  cases k with
  | zero => simp [symPushOnesL] at h; subst h; rfl
  | succ k' =>
    cases L with
    | nil =>
      simp only [symPushOnesL, Option.some.injEq] at h; subst h
      simp only [encSL, evalSymN_zero, Nat.zero_add, pow_one_list, pWord_zero_eq]
    | cons t ts =>
      cases t with
      | mid c =>
        dsimp only [symPushOnesL] at h
        rw [encSL_pushLP h, evalSymN_one, pow_one_list, pWord_zero_eq]
      | pair z o c =>
        cases z with
        | zero =>
          dsimp only [symPushOnesL] at h
          rcases hd : symDecPairL 0 o c ts with _ | ts'
          · rw [hd] at h; cases h
          · rw [hd] at h; try dsimp only at h
            rw [encSL_pushLP h, evalSymN_one, pow_one_list, ← encSL_decPairL hd,
              pWord_zero_eq, pWord_zero_eq, pow_append_pow]
            congr 2; omega
        | succ z' =>
          dsimp only [symPushOnesL] at h
          rw [encSL_pushLP h, evalSymN_one, pow_one_list, pWord_zero_eq]

private theorem encSL_pushWLMSem {v : Fin 5 → ℕ} {k : SymN} {L out : List SymLTok}
    (h : symPushWLMSem k L = some out) :
    encSL v out = (wLM ^ evalSymN v k) +> encSL v L := by
  unfold symPushWLMSem at h
  rcases hd : symDec k with _ | k' | _
  · rw [hd] at h; injection h with h; subst h
    rw [symDec_isZero hd]; rfl
  · rw [hd] at h; rw [symDec_isSucc hd]
    rcases h1 : symPushLP 2 0 (symConst 2) L with _ | L1
    · rw [h1] at h; cases h
    · rw [h1] at h; try dsimp only at h
      rcases h2 : symPushLP 1 1 symOne L1 with _ | L2
      · rw [h2] at h; cases h
      · rw [h2] at h; try dsimp only at h
        rw [encSL_pushLM h, encSL_pushLP h2, encSL_pushLP h1,
          evalSymN_one, evalSymN_const, pWord_1_1, pWord_2_0]
        have heq : (wT ^ 1) +> ((wZ ^ 2) +> encSL v L) = (wLM ^ 1) +> encSL v L := rfl
        rw [heq, pow_append_pow]
  · rw [hd] at h; cases h

private theorem encSL_popBitL {v : Fin 5 → ℕ} {L out : List SymLTok} {b : Fin 2}
    (h : symPopBitL L = some (b, out)) :
    encSL v L = b >> encSL v out := by
  unfold symPopBitL at h
  rcases hn : symNormL L with _ | nL
  · rw [hn] at h; cases h
  · rw [hn] at h; rw [← encSL_normL hn]
    rcases nL with _ | ⟨t, ts⟩
    · injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      simp [encSL, ListBlank.cons_zero_default]
    · cases t with
      | mid _ => cases h
      | pair z o c =>
        cases z with
        | zero =>
          cases o with
          | zero =>
            try dsimp only at h
            rcases hd : symDecPairL 0 0 c ts with _ | ts'
            · rw [hd] at h; cases h
            · rw [hd] at h; injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
              rw [← encSL_decPairL hd]; rfl
          | succ o' =>
            try dsimp only at h
            rcases hd : symDecPairL 0 (o' + 1) c ts with _ | ts'
            · rw [hd] at h; cases h
            · rw [hd] at h; try dsimp only at h
              rcases hp : symPushLP 0 o' symOne ts' with _ | L'
              · rw [hp] at h; cases h
              · rw [hp] at h; injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
                rw [encSL_pushLP hp, evalSymN_one, pow_one_list, ← encSL_decPairL hd]
                simp [pWord, List.replicate_succ]
        | succ z' =>
          try dsimp only at h
          rcases hd : symDecPairL (z' + 1) o c ts with _ | ts'
          · rw [hd] at h; cases h
          · rw [hd] at h; try dsimp only at h
            rcases hp : symPushLP z' o symOne ts' with _ | L'
            · rw [hp] at h; cases h
            · rw [hp] at h; injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
              rw [encSL_pushLP hp, evalSymN_one, pow_one_list, ← encSL_decPairL hd]
              simp [pWord, List.replicate_succ, listblank_append_right_assoc]

private theorem encSR_pushRM {v : Fin 5 → ℕ} {k : SymN} {R out : List SymRTok}
    (h : symPushRM k R = some out) :
    encSR v out = (wRM ^ evalSymN v k) +> encSR v R := by
  unfold symPushRM at h
  rcases hd : symDec k with _ | k' | _
  · rw [hd] at h; injection h with h; subst h
    rw [symDec_isZero hd]; rfl
  · rw [hd] at h; rw [symDec_isSucc hd]
    cases R with
    | nil => injection h with h; subst h; rfl
    | cons t ts =>
      cases t with
      | pair _ _ _ => injection h with h; subst h; rfl
      | mid c =>
        injection h with h; subst h
        simp only [encSR, evalSymN_add1, pow_append_pow]
        congr 2; omega
  · rw [hd] at h; cases h

private theorem encSR_coalesceR {v : Fin 5 → ℕ} {R out : List SymRTok}
    (h : symCoalesceR R = some out) :
    encSR v out = encSR v R := by
  unfold symCoalesceR at h
  split at h
  · rename_i c0 c1 rest
    split_ifs at h with h1
    · rcases hd : symDecPairR 2 0 c1 rest with _ | rest'
      · rw [hd] at h; cases h
      · rw [hd] at h; try dsimp only at h
        rw [encSR_pushRM h, evalSymN_one, pow_one_list]
        have htail := encSR_decPairR (v := v) hd
        rw [pWord_2_0] at htail
        have hrhs : encSR v (.pair 1 1 c0 :: .pair 2 0 c1 :: rest) =
            (wT ^ 2) +> (wZ +> encSR v rest') := by
          rw [encSR, htail, evalSymN_isConst1 h1, pWord_1_1]
        rw [hrhs]; rfl
    · injection h with h; subst h; rfl
  · injection h with h; subst h; rfl

private theorem encSR_pushRP {v : Fin 5 → ℕ} {z o : ℕ} {k : SymN} {R out : List SymRTok}
    (h : symPushRP z o k R = some out) :
    encSR v out = ((pWord z o) ^ evalSymN v k) +> encSR v R := by
  unfold symPushRP at h
  rcases hd : symDec k with _ | k' | _
  · rw [hd] at h; injection h with h; subst h
    rw [symDec_isZero hd]; rfl
  · rw [hd] at h; rw [symDec_isSucc hd, encSR_coalesceR h]
    cases R with
    | nil => simp [symPushRPPre, encSR]
    | cons t ts =>
      cases t with
      | mid _ => simp [symPushRPPre, encSR]
      | pair z' o' c =>
        simp only [symPushRPPre]
        by_cases heq : ((z == z') && (o == o')) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true heq))]
          simp only [Bool.and_eq_true, beq_iff_eq] at heq
          rcases heq with ⟨rfl, rfl⟩
          simp only [encSR, evalSymN_add1, pow_append_pow]
          congr 2; omega
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false heq))]; simp [encSR]
  · rw [hd] at h; cases h

private theorem encSR_normR {v : Fin 5 → ℕ} {R out : List SymRTok}
    (h : symNormR R = some out) :
    encSR v out = encSR v R := by
  cases R with
  | nil => simp [symNormR] at h; subst h; rfl
  | cons t ts =>
    cases t with
    | pair _ _ _ => simp [symNormR] at h; subst h; rfl
    | mid c =>
      dsimp only [symNormR] at h
      rcases hd : symDecMidR c ts with _ | ts'
      · rw [hd] at h; cases h
      · rw [hd] at h; injection h with h; subst h
        rw [← encSR_decMidR hd]
        simp only [encSR, evalSymN_zero, evalSymN_one, pWord_1_1, pWord_2_0]
        rfl

private theorem encSR_pushZerosR {v : Fin 5 → ℕ} {k : ℕ} {R out : List SymRTok}
    (h : symPushZerosR k R = some out) :
    encSR v out = (([0] : List (Fin 2)) ^ k) +> encSR v R := by
  unfold symPushZerosR at h
  by_cases hk : (k == 0) = Bool.true
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hk))] at h; injection h with h; subst h
    have hk0 : k = 0 := eq_of_beq hk; subst hk0; rfl
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hk))] at h; try dsimp only at h
    rcases hn : symNormR R with _ | nR
    · rw [hn] at h; cases h
    · rw [hn] at h; rw [← encSR_normR hn]
      rcases nR with _ | ⟨t, ts⟩
      · injection h with h; subst h
        simp only [encSR]; exact (zeros_append_default k).symm
      · cases t with
        | mid _ => cases h
        | pair z o c =>
          try dsimp only at h
          rcases hd : symDecPairR z o c ts with _ | ts'
          · rw [hd] at h; cases h
          · rw [hd] at h; try dsimp only at h
            rw [encSR_pushRP h, evalSymN_one, pow_one_list, ← encSR_decPairR hd]
            simp only [pWord, replicate_eq_pow]
            rw [Nat.add_comm z k, list_pow_add]
            simp only [listblank_append_right_assoc]

private theorem encSR_pushOnesR {v : Fin 5 → ℕ} {k : ℕ} {R out : List SymRTok}
    (h : symPushOnesR k R = some out) :
    encSR v out = (([1] : List (Fin 2)) ^ k) +> encSR v R := by
  cases k with
  | zero => simp [symPushOnesR] at h; subst h; rfl
  | succ k' =>
    cases R with
    | nil =>
      simp only [symPushOnesR, Option.some.injEq] at h; subst h
      simp only [encSR, evalSymN_zero, Nat.zero_add, pow_one_list, pWord_zero_eq]
    | cons t ts =>
      cases t with
      | mid c =>
        dsimp only [symPushOnesR] at h
        rw [encSR_pushRP h, evalSymN_one, pow_one_list, pWord_zero_eq]
      | pair z o c =>
        cases z with
        | zero =>
          dsimp only [symPushOnesR] at h
          rcases hd : symDecPairR 0 o c ts with _ | ts'
          · rw [hd] at h; cases h
          · rw [hd] at h; try dsimp only at h
            rw [encSR_pushRP h, evalSymN_one, pow_one_list, ← encSR_decPairR hd,
              pWord_zero_eq, pWord_zero_eq, pow_append_pow]
            congr 2; omega
        | succ z' =>
          dsimp only [symPushOnesR] at h
          rw [encSR_pushRP h, evalSymN_one, pow_one_list, pWord_zero_eq]

private theorem encSR_pushWRMSem {v : Fin 5 → ℕ} {k : SymN} {R out : List SymRTok}
    (h : symPushWRMSem k R = some out) :
    encSR v out = (wRM ^ evalSymN v k) +> encSR v R := by
  unfold symPushWRMSem at h
  rcases hd : symDec k with _ | k' | _
  · rw [hd] at h; injection h with h; subst h
    rw [symDec_isZero hd]; rfl
  · rw [hd] at h; rw [symDec_isSucc hd]
    rcases h1 : symPushRP 2 0 symOne R with _ | R1
    · rw [h1] at h; cases h
    · rw [h1] at h; try dsimp only at h
      rcases h2 : symPushRP 1 1 (symConst 2) R1 with _ | R2
      · rw [h2] at h; cases h
      · rw [h2] at h; try dsimp only at h
        rw [encSR_pushRM h, encSR_pushRP h2, encSR_pushRP h1,
          evalSymN_one, evalSymN_const, pWord_1_1, pWord_2_0]
        have heq : (wT ^ 2) +> ((wZ ^ 1) +> encSR v R) = (wRM ^ 1) +> encSR v R := rfl
        rw [heq, pow_append_pow]
  · rw [hd] at h; cases h

private theorem encSR_popBitR {v : Fin 5 → ℕ} {R out : List SymRTok} {b : Fin 2}
    (h : symPopBitR R = some (b, out)) :
    encSR v R = b >> encSR v out := by
  unfold symPopBitR at h
  rcases hn : symNormR R with _ | nR
  · rw [hn] at h; cases h
  · rw [hn] at h; rw [← encSR_normR hn]
    rcases nR with _ | ⟨t, ts⟩
    · injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      simp [encSR, ListBlank.cons_zero_default]
    · cases t with
      | mid _ => cases h
      | pair z o c =>
        cases z with
        | zero =>
          cases o with
          | zero =>
            try dsimp only at h
            rcases hd : symDecPairR 0 0 c ts with _ | ts'
            · rw [hd] at h; cases h
            · rw [hd] at h; injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
              rw [← encSR_decPairR hd]; rfl
          | succ o' =>
            try dsimp only at h
            rcases hd : symDecPairR 0 (o' + 1) c ts with _ | ts'
            · rw [hd] at h; cases h
            · rw [hd] at h; try dsimp only at h
              rcases hp : symPushRP 0 o' symOne ts' with _ | R'
              · rw [hp] at h; cases h
              · rw [hp] at h; injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
                rw [encSR_pushRP hp, evalSymN_one, pow_one_list, ← encSR_decPairR hd]
                simp [pWord, List.replicate_succ]
        | succ z' =>
          try dsimp only at h
          rcases hd : symDecPairR (z' + 1) o c ts with _ | ts'
          · rw [hd] at h; cases h
          · rw [hd] at h; try dsimp only at h
            rcases hp : symPushRP z' o symOne ts' with _ | R'
            · rw [hp] at h; cases h
            · rw [hp] at h; injection h with h; rcases Prod.mk.inj h with ⟨rfl, rfl⟩
              rw [encSR_pushRP hp, evalSymN_one, pow_one_list, ← encSR_decPairR hd]
              simp [pWord, List.replicate_succ, listblank_append_right_assoc]

/-! #### Symbolic Sweeps & Base Step (`symStepBase`) -/

def symSweepARAux : List SymRTok → Bool → List SymLTok → Option (List SymLTok × List SymRTok)
  | [], false, L => some (L, [])
  | [], true, L => some (L, [.pair 0 0 symZero])
  | .mid c :: rest, false, L =>
    match symPushLP 1 0 symOne L with
    | none => none
    | some L1 =>
      match symPushLP 2 0 symOne L1 with
      | none => none
      | some L2 =>
        match symDecMidR c rest with
        | none => none
        | some rest' => some (L2, .pair 0 0 symZero :: .pair 2 0 symZero :: rest')
  | .mid c :: rest, true, L =>
    match symPushLP 2 0 (symConst 2) L with
    | none => none
    | some L1 =>
      match symDecMidR c rest with
      | none => none
      | some rest' => some (L1, .pair 0 0 symZero :: .pair 2 0 symZero :: rest')
  | .pair 0 0 c :: rest, false, L =>
    if symIsZero c then symSweepARAux rest true L
    else some (L, .pair 0 0 c :: rest)
  | .pair 0 (o' + 1) c :: rest, false, L => some (L, .pair 0 (o' + 1) c :: rest)
  | .pair 0 o c :: rest, true, L =>
    match symPushOnesR 1 (.pair 0 o c :: rest) with
    | none => none
    | some R' => some (L, R')
  | .pair 1 0 c :: rest, false, L =>
    match symPushLP 1 0 (symAddConst c 1) L with
    | none => none
    | some L1 => symSweepARAux rest false L1
  | .pair 1 1 c :: rest, false, L =>
    match symDec c with
    | .isZero =>
      match symPushLP 1 0 symOne L with
      | none => none
      | some L1 => symSweepARAux rest true L1
    | .isSucc _ =>
      match symPushLP 1 0 symOne L with
      | none => none
      | some L1 =>
        match symPushLP 2 0 c L1 with
        | none => none
        | some L2 => symSweepARAux rest true L2
    | .stuck => none
  | .pair 1 (o'' + 2) c :: rest, false, L =>
    match symPushLP 1 0 symOne L with
    | none => none
    | some L1 =>
      match symDecPairR 1 (o'' + 2) c rest with
      | none => none
      | some r1 =>
        match symPushOnesR (o'' + 2) r1 with
        | none => none
        | some R' => some (L1, R')
  | .pair 1 0 c :: rest, true, L =>
    match symDec c with
    | .isZero =>
      match symPushLP 2 0 symOne L with
      | none => none
      | some L1 => symSweepARAux rest false L1
    | .isSucc _ =>
      match symPushLP 2 0 symOne L with
      | none => none
      | some L1 =>
        match symPushLP 1 0 c L1 with
        | none => none
        | some L2 => symSweepARAux rest false L2
    | .stuck => none
  | .pair 1 1 c :: rest, true, L =>
    match symPushLP 2 0 (symAddConst c 1) L with
    | none => none
    | some L1 => symSweepARAux rest true L1
  | .pair 1 (o'' + 2) c :: rest, true, L =>
    match symPushLP 2 0 symOne L with
    | none => none
    | some L1 =>
      match symDecPairR 1 (o'' + 2) c rest with
      | none => none
      | some r1 =>
        match symPushOnesR (o'' + 2) r1 with
        | none => none
        | some R' => some (L1, R')
  | .pair (z'' + 2) o c :: rest, false, L => some (L, .pair (z'' + 2) o c :: rest)
  | .pair (z'' + 2) o c :: rest, true, L =>
    match symPushOnesR 1 (.pair (z'' + 2) o c :: rest) with
    | none => none
    | some R' => some (L, R')

private theorem symSweepARAux_sound (v : Fin 5 → ℕ) :
    ∀ (ts : List SymRTok) (after1 : Bool) (L L' : List SymLTok) (R' : List SymRTok),
    symSweepARAux ts after1 L = some (L', R') →
      ReachesStar target_tm
        (cfgA (encSL v L) (if after1 then [1] +> encSR v ts else encSR v ts))
        (cfgA (encSL v L') (encSR v R'))
  | [], false, L, L', R', h => by
    simp only [symSweepARAux, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | [], true, L, L', R', h => by
    simp only [symSweepARAux, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have heq : encSR v [.pair 0 0 symZero] = [1] +> encSR v [] := by
      simp [encSR, evalSymN_zero, pWord_0_0, pow_one_list]
    rw [heq]; exact ReachesStar.refl _ _
  | .mid c :: rest, false, L, L', R', h => by
    dsimp only [symSweepARAux] at h
    rcases h1 : symPushLP 1 0 symOne L with _ | L1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    rcases h2 : symPushLP 2 0 symOne L1 with _ | L2; · rw [h2] at h; cases h
    rw [h2] at h; try dsimp only at h
    rcases hd : symDecMidR c rest with _ | rest'; · rw [hd] at h; cases h
    rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [← encSR_decMidR hd, encSL_pushLP h2, encSL_pushLP h1, evalSymN_one,
      pWord_2_0, pWord_1_0, pow_one_list, pow_one_list]
    have hr : encSR v (.pair 0 0 symZero :: .pair 2 0 symZero :: rest') =
        [1, 0, 0, 1] +> encSR v rest' := by
      simp [encSR, evalSymN_zero, pWord_0_0, pWord_2_0, pow_one_list]; rfl
    rw [hr]
    have hl : wRM +> encSR v rest' =
        [0, 1] +> ([1, 0, 1] +> ([1, 0, 0, 1] +> encSR v rest')) := rfl
    rw [hl]
    exact ((step_a_01 (encSL v L) _).trans (step_a_101 ([0, 1] +> encSL v L) _)).to_star
  | .mid c :: rest, true, L, L', R', h => by
    dsimp only [symSweepARAux] at h
    rcases h1 : symPushLP 2 0 (symConst 2) L with _ | L1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    rcases hd : symDecMidR c rest with _ | rest'; · rw [hd] at h; cases h
    rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [ite_true]
    rw [← encSR_decMidR hd, encSL_pushLP h1, evalSymN_const, pWord_2_0]
    have hr : encSR v (.pair 0 0 symZero :: .pair 2 0 symZero :: rest') =
        [1] +> (wZ +> encSR v rest') := by
      simp [encSR, evalSymN_zero, pWord_0_0, pWord_2_0, pow_one_list]
    rw [hr]
    have hl : [1] +> (wRM +> encSR v rest') =
        [1] +> ((wT ^ 2) +> (wZ +> encSR v rest')) := rfl
    rw [hl]
    exact (step_a_101_pow 2 (encSL v L) (wZ +> encSR v rest')).to_star
  | .pair z o c :: rest, after1, L, L', R', h => by
    cases z with
    | zero =>
      cases after1
      · cases o with
        | zero =>
          dsimp only [symSweepARAux] at h
          by_cases hz : symIsZero c = true
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz))] at h; try dsimp only at h
            have ih := symSweepARAux_sound v rest true L L' R' h
            simp only [Bool.false_eq_true, ite_false]
            simp only [ite_true] at ih
            have heq : encSR v (.pair 0 0 c :: rest) = [1] +> encSR v rest := by
              simp [encSR, evalSymN_isZero hz, pWord_0_0, pow_one_list]
            rw [heq]; exact ih
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz))] at h; try dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
        | succ o' =>
          simp only [symSweepARAux, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
      · simp only [symSweepARAux] at h
        rcases hp : symPushOnesR 1 (.pair 0 o c :: rest) with _ | R1; · rw [hp] at h; cases h
        rw [hp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [ite_true]
        rw [encSR_pushOnesR hp, pow_one_list]
    | succ z' =>
      cases z' with
      | zero =>
        cases after1
        · cases o with
          | zero =>
            dsimp only [symSweepARAux] at h
            rcases h1 : symPushLP 1 0 (symAddConst c 1) L with _ | L1; · rw [h1] at h; cases h
            rw [h1] at h; try dsimp only at h
            have ih := symSweepARAux_sound v rest false L1 L' R' h
            simp only [Bool.false_eq_true, ite_false] at ih ⊢
            dsimp only [encSR]; rw [pWord_1_0]
            have hs := step_a_01_pow (evalSymN v c + 1) (encSL v L) (encSR v rest)
            rw [← evalSymN_addConst v c 1, ← pWord_1_0, ← encSL_pushLP h1] at hs
            exact hs.to_star.trans ih
          | succ o' =>
            cases o' with
            | zero =>
              dsimp only [symSweepARAux] at h
              rcases hd : symDec c with _ | c' | _
              · rw [hd] at h; try dsimp only at h
                rcases h1 : symPushLP 1 0 symOne L with _ | L1; · rw [h1] at h; cases h
                rw [h1] at h; try dsimp only at h
                have ih := symSweepARAux_sound v rest true L1 L' R' h
                simp only [Bool.false_eq_true, ite_false]
                simp only [ite_true] at ih
                dsimp only [encSR]; rw [symDec_isZero hd, pWord_1_1, pow_one_list]
                have heq : wT +> encSR v rest = [0, 1] +> ([1] +> encSR v rest) := rfl
                rw [heq]
                have hL1 : encSL v L1 = [0, 1] +> encSL v L := by
                  rw [encSL_pushLP h1, evalSymN_one, pWord_1_0, pow_one_list]
                have hs := step_a_01 (encSL v L) ([1] +> encSR v rest)
                rw [← hL1] at hs
                exact hs.to_star.trans ih
              · rw [hd] at h; try dsimp only at h
                rcases h1 : symPushLP 1 0 symOne L with _ | L1; · rw [h1] at h; cases h
                rw [h1] at h; try dsimp only at h
                rcases h2 : symPushLP 2 0 c L1 with _ | L2; · rw [h2] at h; cases h
                rw [h2] at h; try dsimp only at h
                have ih := symSweepARAux_sound v rest true L2 L' R' h
                simp only [Bool.false_eq_true, ite_false]
                simp only [ite_true] at ih
                dsimp only [encSR]; rw [pWord_1_1, ListBlank.append_pow_succ]
                have heq : wT +> ((wT ^ evalSymN v c) +> encSR v rest) =
                    [0, 1] +> ([1] +> ((wT ^ evalSymN v c) +> encSR v rest)) := rfl
                rw [heq]
                have hL1 : encSL v L1 = [0, 1] +> encSL v L := by
                  rw [encSL_pushLP h1, evalSymN_one, pWord_1_0, pow_one_list]
                have s1 := step_a_01 (encSL v L) ([1] +> ((wT ^ evalSymN v c) +> encSR v rest))
                rw [← hL1] at s1
                have s2 := step_a_101_pow (evalSymN v c) (encSL v L1) (encSR v rest)
                rw [← pWord_2_0, ← encSL_pushLP h2] at s2
                exact (s1.trans s2).to_star.trans ih
              · rw [hd] at h; cases h
            | succ o'' =>
              dsimp only [symSweepARAux] at h
              rcases h1 : symPushLP 1 0 symOne L with _ | L1; · rw [h1] at h; cases h
              rw [h1] at h; try dsimp only at h
              rcases hd : symDecPairR 1 (o'' + 2) c rest with _ | r1; · rw [hd] at h; cases h
              rw [hd] at h; try dsimp only at h
              rcases h2 : symPushOnesR (o'' + 2) r1 with _ | R1; · rw [h2] at h; cases h
              rw [h2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simp only [Bool.false_eq_true, ite_false]
              rw [← encSR_decPairR hd, encSL_pushLP h1, encSR_pushOnesR h2,
                evalSymN_one, pWord_1_0, pow_one_list]
              have hpw : pWord 1 (o'' + 2) = [0, 1] ++ ([1] : List (Fin 2)) ^ (o'' + 2) := by
                rw [pWord]
                simp only [List.replicate_succ (n := o'' + 2), replicate_eq_pow, pow_one_list]
                rfl
              have hpw2 : (pWord 1 (o'' + 2)) +> encSR v r1 =
                  [0, 1] +> ((([1] : List (Fin 2)) ^ (o'' + 2)) +> encSR v r1) := by
                rw [hpw]; simp only [listblank_append_right_assoc]
              rw [hpw2]
              exact (step_a_01 (encSL v L) _).to_star
        · cases o with
          | zero =>
            dsimp only [symSweepARAux] at h
            rcases hd : symDec c with _ | c' | _
            · rw [hd] at h; try dsimp only at h
              rcases h1 : symPushLP 2 0 symOne L with _ | L1; · rw [h1] at h; cases h
              rw [h1] at h; try dsimp only at h
              have ih := symSweepARAux_sound v rest false L1 L' R' h
              simp only [ite_true]
              simp only [Bool.false_eq_true, ite_false] at ih
              dsimp only [encSR]; rw [symDec_isZero hd, pWord_1_0, pow_one_list]
              have heq : [1] +> ([0, 1] +> encSR v rest) = [1, 0, 1] +> encSR v rest := rfl
              rw [heq]
              have hL1 : encSL v L1 = wZ +> encSL v L := by
                rw [encSL_pushLP h1, evalSymN_one, pWord_2_0, pow_one_list]
              have s1 := step_a_101 (encSL v L) (encSR v rest)
              rw [← hL1] at s1
              exact s1.to_star.trans ih
            · rw [hd] at h; try dsimp only at h
              rcases h1 : symPushLP 2 0 symOne L with _ | L1; · rw [h1] at h; cases h
              rw [h1] at h; try dsimp only at h
              rcases h2 : symPushLP 1 0 c L1 with _ | L2; · rw [h2] at h; cases h
              rw [h2] at h; try dsimp only at h
              have ih := symSweepARAux_sound v rest false L2 L' R' h
              simp only [ite_true]
              simp only [Bool.false_eq_true, ite_false] at ih
              dsimp only [encSR]; rw [pWord_1_0, ListBlank.append_pow_succ]
              have heq : [1] +> ([0, 1] +> ((([0,
                1] : List (Fin 2)) ^ evalSymN v c) +> encSR v rest)) =
                  [1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ evalSymN v c) +> encSR v rest) := rfl
              rw [heq]
              have hL1 : encSL v L1 = wZ +> encSL v L := by
                rw [encSL_pushLP h1, evalSymN_one, pWord_2_0, pow_one_list]
              have s1 := step_a_101 (encSL v L) ((([0,
                1] : List (Fin 2)) ^ evalSymN v c) +> encSR v rest)
              rw [← hL1] at s1
              have s2 := step_a_01_pow (evalSymN v c) (encSL v L1) (encSR v rest)
              rw [← pWord_1_0, ← encSL_pushLP h2] at s2
              exact (s1.trans s2).to_star.trans ih
            · rw [hd] at h; cases h
          | succ o' =>
            cases o' with
            | zero =>
              dsimp only [symSweepARAux] at h
              rcases h1 : symPushLP 2 0 (symAddConst c 1) L with _ | L1; · rw [h1] at h; cases h
              rw [h1] at h; try dsimp only at h
              have ih := symSweepARAux_sound v rest true L1 L' R' h
              simp only [ite_true] at ih ⊢
              dsimp only [encSR]; rw [pWord_1_1]
              have hs := step_a_101_pow (evalSymN v c + 1) (encSL v L) (encSR v rest)
              rw [← evalSymN_addConst v c 1, ← pWord_2_0, ← encSL_pushLP h1] at hs
              exact hs.to_star.trans ih
            | succ o'' =>
              dsimp only [symSweepARAux] at h
              rcases h1 : symPushLP 2 0 symOne L with _ | L1; · rw [h1] at h; cases h
              rw [h1] at h; try dsimp only at h
              rcases hd : symDecPairR 1 (o'' + 2) c rest with _ | r1; · rw [hd] at h; cases h
              rw [hd] at h; try dsimp only at h
              rcases h2 : symPushOnesR (o'' + 2) r1 with _ | R1; · rw [h2] at h; cases h
              rw [h2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simp only [ite_true]
              rw [← encSR_decPairR hd, encSL_pushLP h1, encSR_pushOnesR h2,
                evalSymN_one, pWord_2_0, pow_one_list]
              have hpw : pWord 1 (o'' + 2) = [0, 1] ++ ([1] : List (Fin 2)) ^ (o'' + 2) := by
                rw [pWord]
                simp only [List.replicate_succ (n := o'' + 2), replicate_eq_pow, pow_one_list]
                rfl
              have hpw2 : [1] +> ((pWord 1 (o'' + 2)) +> encSR v r1) =
                  [1, 0, 1] +> ((([1] : List (Fin 2)) ^ (o'' + 2)) +> encSR v r1) := by
                rw [hpw]; simp only [listblank_append_right_assoc]; rfl
              rw [hpw2]
              exact (step_a_101 (encSL v L) _).to_star
      | succ z'' =>
        cases after1
        · simp only [symSweepARAux, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
        · dsimp only [symSweepARAux] at h
          rcases hp : symPushOnesR 1 (.pair (z'' + 2) o c :: rest) with _ | R1
          · rw [hp] at h; cases h
          rw [hp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [ite_true]
          rw [encSR_pushOnesR hp, pow_one_list]

def symSweepDL : List SymLTok → List SymRTok → Option (List SymLTok × List SymRTok)
  | [], R => some ([], R)
  | .mid c :: rest, R => some (.mid c :: rest, R)
  | .pair 0 o c :: rest, R => some (.pair 0 o c :: rest, R)
  | .pair 1 o c :: rest, R => some (.pair 1 o c :: rest, R)
  | .pair 2 0 c :: rest, R =>
    match symPushRP 1 1 (symAddConst c 1) R with
    | none => none
    | some R1 => symSweepDL rest R1
  | .pair 2 (o' + 1) c :: rest, R =>
    match symDecPairL 2 (o' + 1) c rest with
    | none => none
    | some l1 =>
      match symPushOnesL (o' + 1) l1 with
      | none => none
      | some L' =>
        match symPushRP 1 1 symOne R with
        | none => none
        | some R' => some (L', R')
  | .pair (z''' + 3) o c :: rest, R => some (.pair (z''' + 3) o c :: rest, R)

private theorem symSweepDL_sound (v : Fin 5 → ℕ) :
    ∀ (ts : List SymLTok) (R : List SymRTok) (L' : List SymLTok) (R' : List SymRTok),
    symSweepDL ts R = some (L', R') →
      ReachesStar target_tm (cfgD (encSL v ts) (encSR v R)) (cfgD (encSL v L') (encSR v R'))
  | [], R, L', R', h => by
    simp only [symSweepDL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | .mid c :: rest, R, L', R', h => by
    simp only [symSweepDL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | .pair 0 o c :: rest, R, L', R', h => by
    simp only [symSweepDL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | .pair 1 o c :: rest, R, L', R', h => by
    simp only [symSweepDL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | .pair 2 0 c :: rest, R, L', R', h => by
    dsimp only [symSweepDL] at h
    rcases h1 : symPushRP 1 1 (symAddConst c 1) R with _ | R1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    have ih := symSweepDL_sound v rest R1 L' R' h
    dsimp only [encSL]; rw [pWord_2_0]
    have hs := step_d_001_pow (evalSymN v c + 1) (encSL v rest) (encSR v R)
    rw [← evalSymN_addConst v c 1, ← pWord_1_1, ← encSR_pushRP h1] at hs
    exact hs.to_star.trans ih
  | .pair 2 (o' + 1) c :: rest, R, L', R', h => by
    dsimp only [symSweepDL] at h
    rcases hd : symDecPairL 2 (o' + 1) c rest with _ | l1; · rw [hd] at h; cases h
    rw [hd] at h; try dsimp only at h
    rcases h1 : symPushOnesL (o' + 1) l1 with _ | L1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    rcases h2 : symPushRP 1 1 symOne R with _ | R1; · rw [h2] at h; cases h
    rw [h2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [← encSL_decPairL hd, encSL_pushOnesL h1, encSR_pushRP h2,
      evalSymN_one, pWord_1_1, pow_one_list]
    have hpw : pWord 2 (o' + 1) = wZ ++ ([1] : List (Fin 2)) ^ (o' + 1) := by
      rw [pWord]; simp only [List.replicate_succ (n := o' + 1), replicate_eq_pow]; rfl
    have hpw2 : (pWord 2 (o' + 1)) +> encSL v l1 =
        wZ +> ((([1] : List (Fin 2)) ^ (o' + 1)) +> encSL v l1) := by
      rw [hpw]; simp only [listblank_append_right_assoc]
    rw [hpw2]
    exact (step_d_001 _ (encSR v R)).to_star
  | .pair (z''' + 3) o c :: rest, R, L', R', h => by
    simp only [symSweepDL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _

def symSweepEL : List SymLTok → List SymRTok → Option (List SymLTok × List SymRTok)
  | [], R => some ([], R)
  | .mid c :: rest, R => some (.mid c :: rest, R)
  | .pair 0 o c :: rest, R =>
    if symIsConst c then
      let k := (o + 1) * (c.k + 1)
      match symPushZerosR k R with
      | none => none
      | some R1 => symSweepEL rest R1
    else none
  | .pair (z' + 1) o c :: rest, R => some (.pair (z' + 1) o c :: rest, R)

private theorem symSweepEL_sound (v : Fin 5 → ℕ) :
    ∀ (ts : List SymLTok) (R : List SymRTok) (L' : List SymLTok) (R' : List SymRTok),
    symSweepEL ts R = some (L', R') →
      ReachesStar target_tm (cfgE (encSL v ts) (encSR v R)) (cfgE (encSL v L') (encSR v R'))
  | [], R, L', R', h => by
    simp only [symSweepEL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | .mid c :: rest, R, L', R', h => by
    simp only [symSweepEL, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _
  | .pair z o c :: rest, R, L', R', h => by
    cases z with
    | zero =>
      dsimp only [symSweepEL] at h
      by_cases hc : symIsConst c = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc))] at h; try dsimp only at h
        rcases h1 : symPushZerosR ((o + 1) * (c.k + 1)) R with _ | R1; · rw [h1] at h; cases h
        rw [h1] at h; try dsimp only at h
        have ih := symSweepEL_sound v rest R1 L' R' h
        dsimp only [encSL]; rw [evalSymN_isConst hc]
        have hones : (pWord 0 o) ^ (c.k + 1) = ([1] : List (Fin 2)) ^ ((o + 1) * (c.k + 1)) := by
          simp only [pWord_zero_eq, ← list_pow_mul]
        rw [hones]
        have hs := step_e_ones ((o + 1) * (c.k + 1)) (encSL v rest) (encSR v R)
        rw [← encSR_pushZerosR h1] at hs
        exact hs.to_star.trans ih
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc))] at h; cases h
    | succ z' =>
      simp only [symSweepEL, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; exact ReachesStar.refl _ _

private theorem fin2_eq_one_of_ne_zero {b : Fin 2} (h : ¬((b == 0) = Bool.true)) : b = 1 := by
  rcases b with ⟨_ | _ | b, hb⟩
  · exact absurd rfl h
  · rfl
  · omega

private theorem fin2_eq_zero_of_ne_one {b : Fin 2} (h : ¬((b == 1) = Bool.true)) : b = 0 := by
  rcases b with ⟨_ | _ | b, hb⟩
  · rfl
  · exact absurd rfl h
  · omega

def symStepBase (s : SymState) : Option SymState :=
  match s with
  | (.mHalt, _, _) => none
  | (.mA, L0, R0) =>
    match symSweepARAux R0 false L0 with
    | none => none
    | some (L, R) =>
      match symPopBitR R with
      | none => none
      | some (r1, R1) =>
        if r1 == 0 then
          match symPopBitR R1 with
          | none => none
          | some (r2, R2) =>
            if r2 == 0 then
              match symPushOnesR 1 R2 with
              | none => none
              | some Ra =>
                match symPushZerosR 1 Ra with
                | none => none
                | some Rb => some (.mD, L, Rb)
            else
              match symPushOnesL 1 L with
              | none => none
              | some La =>
                match symPushZerosL 1 La with
                | none => none
                | some Lb => some (.mA, Lb, R2)
        else
          match symPopBitR R1 with
          | none => none
          | some (r2, R2) =>
            if r2 == 1 then
              match symPushOnesL 1 L with
              | none => none
              | some La =>
                match symPushZerosR 1 R2 with
                | none => none
                | some Ra => some (.mE, La, Ra)
            else
              match symPopBitR R2 with
              | none => none
              | some (r3, R3) =>
                if r3 == 0 then
                  match symPushOnesL 1 L with
                  | none => none
                  | some La =>
                    match symPushOnesR 1 R3 with
                    | none => none
                    | some Ra =>
                      match symPushZerosR 1 Ra with
                      | none => none
                      | some Rb => some (.mE, La, Rb)
                else
                  match symPushLP 2 0 symOne L with
                  | none => none
                  | some La => some (.mA, La, R3)
  | (.mD, L0, R0) =>
    match symSweepDL L0 R0 with
    | none => none
    | some (L, R) =>
      match symPopBitL L with
      | none => none
      | some (l1, L1) =>
        if l1 == 1 then
          match symPopBitL L1 with
          | none => none
          | some (l2, L2) =>
            if l2 == 1 then
              match symPushZerosR 1 R with
              | none => none
              | some Ra => some (.mHalt, L2, Ra)
            else
              match symPopBitL L2 with
              | none => none
              | some (l3, L3) =>
                if l3 == 0 then
                  match symPushZerosR 1 R with
                  | none => none
                  | some Ra =>
                    match symPushOnesR 1 Ra with
                    | none => none
                    | some Rb =>
                      match symPushZerosR 1 Rb with
                      | none => none
                      | some Rc => some (.mD, L3, Rc)
                else
                  match symPushOnesL 1 L3 with
                  | none => none
                  | some La =>
                    match symPushOnesR 1 R with
                    | none => none
                    | some Ra =>
                      match symPushZerosR 1 Ra with
                      | none => none
                      | some Rb => some (.mE, La, Rb)
        else
          match symPopBitL L1 with
          | none => none
          | some (l2, L2) =>
            if l2 == 1 then
              match symPushZerosL 1 L2 with
              | none => none
              | some La =>
                match symPushOnesR 1 R with
                | none => none
                | some Ra => some (.mA, La, Ra)
            else
              match symPopBitL L2 with
              | none => none
              | some (l3, L3) =>
                if l3 == 1 then
                  match symPushRP 1 1 symOne R with
                  | none => none
                  | some Ra => some (.mD, L3, Ra)
                else
                  match symPopBitL L3 with
                  | none => none
                  | some (l4, L4) =>
                    if l4 == 0 then
                      match symPushOnesL 1 L4 with
                      | none => none
                      | some La =>
                        match symPushZerosL 1 La with
                        | none => none
                        | some Lb =>
                          match symPushOnesR 2 R with
                          | none => none
                          | some Ra => some (.mA, Lb, Ra)
                    else
                      match symPushOnesL 1 L4 with
                      | none => none
                      | some La =>
                        match symPushOnesR 2 R with
                        | none => none
                        | some Ra =>
                          match symPushZerosR 1 Ra with
                          | none => none
                          | some Rb => some (.mE, La, Rb)
  | (.mE, L0, R0) =>
    match symSweepEL L0 R0 with
    | none => none
    | some (L, R) =>
      match symPopBitL L with
      | none => none
      | some (l1, L1) =>
        if l1 == 1 then
          match symPushZerosR 1 R with
          | none => none
          | some Ra => some (.mE, L1, Ra)
        else
          match symPopBitR R with
          | none => none
          | some (r1, R1) =>
            if r1 == 1 then
              match symPushZerosL 2 L1 with
              | none => none
              | some La => some (.mA, La, R1)
            else
              match symPopBitL L1 with
              | none => none
              | some (l2, L2) =>
                if l2 == 0 then
                  match symPushOnesL 1 L2 with
                  | none => none
                  | some La =>
                    match symPushZerosL 1 La with
                    | none => none
                    | some Lb =>
                      match symPushOnesR 1 R1 with
                      | none => none
                      | some Ra => some (.mA, Lb, Ra)
                else
                  match symPushOnesL 1 L2 with
                  | none => none
                  | some La =>
                    match symPushOnesR 1 R1 with
                    | none => none
                    | some Ra =>
                      match symPushZerosR 1 Ra with
                      | none => none
                      | some Rb => some (.mE, La, Rb)

private theorem symStepBase_sound (v : Fin 5 → ℕ) {s s' : SymState}
    (h : symStepBase s = some s') :
    ReachesPlus target_tm (evalSym v s) (evalSym v s') := by
  rcases s with ⟨m, L0, R0⟩
  cases m with
  | mHalt => simp [symStepBase] at h
  | mA =>
    dsimp only [symStepBase, evalSym] at h ⊢
    rcases hsw : symSweepARAux R0 false L0 with _ | ⟨L, R⟩; · rw [hsw] at h; cases h
    rw [hsw] at h; try dsimp only at h
    have hsw' := symSweepARAux_sound v R0 false L0 L R hsw
    simp only [Bool.false_eq_true, ite_false] at hsw'
    rcases hp1 : symPopBitR R with _ | ⟨r1, R1⟩; · rw [hp1] at h; cases h
    rw [hp1] at h; dsimp only at h; have hr1 := encSR_popBitR (v := v) hp1
    by_cases hb1 : (r1 == 0) = Bool.true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb1))] at h; have heq1 : r1 = 0 := eq_of_beq hb1
      rcases hp2 : symPopBitR R1 with _ | ⟨r2, R2⟩; · rw [hp2] at h; cases h
      rw [hp2] at h; dsimp only at h; have hr2 := encSR_popBitR (v := v) hp2
      by_cases hb2 : (r2 == 0) = Bool.true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb2))] at h; have heq2 : r2 = 0 := eq_of_beq hb2
        rcases h1 : symPushOnesR 1 R2 with _ | Ra; · rw [h1] at h; cases h
        rw [h1] at h; try dsimp only at h
        rcases h2 : symPushZerosR 1 Ra with _ | Rb; · rw [h2] at h; cases h
        rw [h2] at h; injection h with h; subst h
        rw [heq1, hr2, heq2] at hr1; rw [hr1] at hsw'
        dsimp only [evalSym]; rw [encSR_pushZerosR h2, encSR_pushOnesR h1]
        exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_a_00 (encSL v L) (encSR v R2)))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at h
        have heq2 : r2 = 1 := fin2_eq_one_of_ne_zero hb2
        rcases h1 : symPushOnesL 1 L with _ | La; · rw [h1] at h; cases h
        rw [h1] at h; try dsimp only at h
        rcases h2 : symPushZerosL 1 La with _ | Lb; · rw [h2] at h; cases h
        rw [h2] at h; injection h with h; subst h
        rw [heq1, hr2, heq2] at hr1; rw [hr1] at hsw'
        dsimp only [evalSym]; rw [encSL_pushZerosL h2, encSL_pushOnesL h1]
        exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (step_a_01 (encSL v L) (encSR v R2)))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb1))] at h
      have heq1 : r1 = 1 := fin2_eq_one_of_ne_zero hb1
      rcases hp2 : symPopBitR R1 with _ | ⟨r2, R2⟩; · rw [hp2] at h; cases h
      rw [hp2] at h; dsimp only at h; have hr2 := encSR_popBitR (v := v) hp2
      by_cases hb2 : (r2 == 1) = Bool.true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb2))] at h; have heq2 : r2 = 1 := eq_of_beq hb2
        rcases h1 : symPushOnesL 1 L with _ | La; · rw [h1] at h; cases h
        rw [h1] at h; try dsimp only at h
        rcases h2 : symPushZerosR 1 R2 with _ | Ra; · rw [h2] at h; cases h
        rw [h2] at h; injection h with h; subst h
        rw [heq1, hr2, heq2] at hr1; rw [hr1] at hsw'
        dsimp only [evalSym]; rw [encSL_pushOnesL h1, encSR_pushZerosR h2]
        exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_a_11 (encSL v L) (encSR v R2)))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at h
        have heq2 : r2 = 0 := fin2_eq_zero_of_ne_one hb2
        rcases hp3 : symPopBitR R2 with _ | ⟨r3, R3⟩; · rw [hp3] at h; cases h
        rw [hp3] at h; dsimp only at h; have hr3 := encSR_popBitR (v := v) hp3
        by_cases hb3 : (r3 == 0) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb3))] at h; have heq3 : r3 = 0 := eq_of_beq hb3
          rcases h1 : symPushOnesL 1 L with _ | La; · rw [h1] at h; cases h
          rw [h1] at h; try dsimp only at h
          rcases h2 : symPushOnesR 1 R3 with _ | Ra; · rw [h2] at h; cases h
          rw [h2] at h; try dsimp only at h
          rcases h3 : symPushZerosR 1 Ra with _ | Rb; · rw [h3] at h; cases h
          rw [h3] at h; injection h with h; subst h
          rw [heq1, hr2, heq2, hr3, heq3] at hr1; rw [hr1] at hsw'
          dsimp only [evalSym]; rw [encSL_pushOnesL h1, encSR_pushZerosR h3, encSR_pushOnesR h2]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_a_100 (encSL v L) (encSR v R3)))
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb3))] at h
          have heq3 : r3 = 1 := fin2_eq_one_of_ne_zero hb3
          rcases h1 : symPushLP 2 0 symOne L with _ | La; · rw [h1] at h; cases h
          rw [h1] at h; injection h with h; subst h
          rw [heq1, hr2, heq2, hr3, heq3] at hr1; rw [hr1] at hsw'
          dsimp only [evalSym]; rw [encSL_pushLP h1, evalSymN_one, pWord_2_0, pow_one_list]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (step_a_101 (encSL v L) (encSR v R3)))
  | mD =>
    dsimp only [symStepBase, evalSym] at h ⊢
    rcases hsw : symSweepDL L0 R0 with _ | ⟨L, R⟩; · rw [hsw] at h; cases h
    rw [hsw] at h; try dsimp only at h
    have hsw' := symSweepDL_sound v L0 R0 L R hsw
    rcases hp1 : symPopBitL L with _ | ⟨l1, L1⟩; · rw [hp1] at h; cases h
    rw [hp1] at h; dsimp only at h; have hl1 := encSL_popBitL (v := v) hp1
    by_cases hb1 : (l1 == 1) = Bool.true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb1))] at h; have heq1 : l1 = 1 := eq_of_beq hb1
      rcases hp2 : symPopBitL L1 with _ | ⟨l2, L2⟩; · rw [hp2] at h; cases h
      rw [hp2] at h; dsimp only at h; have hl2 := encSL_popBitL (v := v) hp2
      by_cases hb2 : (l2 == 1) = Bool.true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb2))] at h; have heq2 : l2 = 1 := eq_of_beq hb2
        rcases h1 : symPushZerosR 1 R with _ | Ra; · rw [h1] at h; cases h
        rw [h1] at h; injection h with h; subst h
        rw [heq1, hl2, heq2] at hl1; rw [hl1] at hsw'
        dsimp only [evalSym]; rw [encSR_pushZerosR h1]
        exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_d_11_halt (encSL v L2) (encSR v
          R)))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at h
        have heq2 : l2 = 0 := fin2_eq_zero_of_ne_one hb2
        rcases hp3 : symPopBitL L2 with _ | ⟨l3, L3⟩; · rw [hp3] at h; cases h
        rw [hp3] at h; dsimp only at h; have hl3 := encSL_popBitL (v := v) hp3
        by_cases hb3 : (l3 == 0) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb3))] at h; have heq3 : l3 = 0 := eq_of_beq hb3
          rcases h1 : symPushZerosR 1 R with _ | Ra; · rw [h1] at h; cases h
          rw [h1] at h; try dsimp only at h
          rcases h2 : symPushOnesR 1 Ra with _ | Rb; · rw [h2] at h; cases h
          rw [h2] at h; try dsimp only at h
          rcases h3 : symPushZerosR 1 Rb with _ | Rc; · rw [h3] at h; cases h
          rw [h3] at h; injection h with h; subst h
          rw [heq1, hl2, heq2, hl3, heq3] at hl1; rw [hl1] at hsw'
          dsimp only [evalSym]; rw [encSR_pushZerosR h3, encSR_pushOnesR h2, encSR_pushZerosR h1]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_d_100 (encSL v L3) (encSR v R)))
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb3))] at h
          have heq3 : l3 = 1 := fin2_eq_one_of_ne_zero hb3
          rcases h1 : symPushOnesL 1 L3 with _ | La; · rw [h1] at h; cases h
          rw [h1] at h; try dsimp only at h
          rcases h2 : symPushOnesR 1 R with _ | Ra; · rw [h2] at h; cases h
          rw [h2] at h; try dsimp only at h
          rcases h3 : symPushZerosR 1 Ra with _ | Rb; · rw [h3] at h; cases h
          rw [h3] at h; injection h with h; subst h
          rw [heq1, hl2, heq2, hl3, heq3] at hl1; rw [hl1] at hsw'
          dsimp only [evalSym]; rw [encSL_pushOnesL h1, encSR_pushZerosR h3, encSR_pushOnesR h2]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_d_101 (encSL v L3) (encSR v R)))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb1))] at h
      have heq1 : l1 = 0 := fin2_eq_zero_of_ne_one hb1
      rcases hp2 : symPopBitL L1 with _ | ⟨l2, L2⟩; · rw [hp2] at h; cases h
      rw [hp2] at h; dsimp only at h; have hl2 := encSL_popBitL (v := v) hp2
      by_cases hb2 : (l2 == 1) = Bool.true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb2))] at h; have heq2 : l2 = 1 := eq_of_beq hb2
        rcases h1 : symPushZerosL 1 L2 with _ | La; · rw [h1] at h; cases h
        rw [h1] at h; try dsimp only at h
        rcases h2 : symPushOnesR 1 R with _ | Ra; · rw [h2] at h; cases h
        rw [h2] at h; injection h with h; subst h
        rw [heq1, hl2, heq2] at hl1; rw [hl1] at hsw'
        dsimp only [evalSym]; rw [encSL_pushZerosL h1, encSR_pushOnesR h2]
        exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_d_01 (encSL v L2) (encSR v R)))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at h
        have heq2 : l2 = 0 := fin2_eq_zero_of_ne_one hb2
        rcases hp3 : symPopBitL L2 with _ | ⟨l3, L3⟩; · rw [hp3] at h; cases h
        rw [hp3] at h; dsimp only at h; have hl3 := encSL_popBitL (v := v) hp3
        by_cases hb3 : (l3 == 1) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb3))] at h; have heq3 : l3 = 1 := eq_of_beq hb3
          rcases h1 : symPushRP 1 1 symOne R with _ | Ra; · rw [h1] at h; cases h
          rw [h1] at h; injection h with h; subst h
          rw [heq1, hl2, heq2, hl3, heq3] at hl1; rw [hl1] at hsw'
          dsimp only [evalSym]; rw [encSR_pushRP h1, evalSymN_one, pWord_1_1, pow_one_list]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (step_d_001 (encSL v L3) (encSR v R)))
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb3))] at h
          have heq3 : l3 = 0 := fin2_eq_zero_of_ne_one hb3
          rcases hp4 : symPopBitL L3 with _ | ⟨l4, L4⟩; · rw [hp4] at h; cases h
          rw [hp4] at h; dsimp only at h; have hl4 := encSL_popBitL (v := v) hp4
          by_cases hb4 : (l4 == 0) = Bool.true
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb4))] at h
            have heq4 : l4 = 0 := eq_of_beq hb4
            rcases h1 : symPushOnesL 1 L4 with _ | La; · rw [h1] at h; cases h
            rw [h1] at h; try dsimp only at h
            rcases h2 : symPushZerosL 1 La with _ | Lb; · rw [h2] at h; cases h
            rw [h2] at h; try dsimp only at h
            rcases h3 : symPushOnesR 2 R with _ | Ra; · rw [h3] at h; cases h
            rw [h3] at h; injection h with h; subst h
            rw [heq1, hl2, heq2, hl3, heq3, hl4, heq4] at hl1; rw [hl1] at hsw'
            dsimp only [evalSym]; rw [encSL_pushZerosL h2, encSL_pushOnesL h1, encSR_pushOnesR h3]
            exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_d_0000 (encSL v L4) (encSR v
              R)))
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb4))] at h
            have heq4 : l4 = 1 := fin2_eq_one_of_ne_zero hb4
            rcases h1 : symPushOnesL 1 L4 with _ | La; · rw [h1] at h; cases h
            rw [h1] at h; try dsimp only at h
            rcases h2 : symPushOnesR 2 R with _ | Ra; · rw [h2] at h; cases h
            rw [h2] at h; try dsimp only at h
            rcases h3 : symPushZerosR 1 Ra with _ | Rb; · rw [h3] at h; cases h
            rw [h3] at h; injection h with h; subst h
            rw [heq1, hl2, heq2, hl3, heq3, hl4, heq4] at hl1; rw [hl1] at hsw'
            dsimp only [evalSym]; rw [encSL_pushOnesL h1, encSR_pushZerosR h3, encSR_pushOnesR h2]
            exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_d_0001 (encSL v L4) (encSR v
              R)))
  | mE =>
    dsimp only [symStepBase, evalSym] at h ⊢
    rcases hsw : symSweepEL L0 R0 with _ | ⟨L, R⟩; · rw [hsw] at h; cases h
    rw [hsw] at h; try dsimp only at h
    have hsw' := symSweepEL_sound v L0 R0 L R hsw
    rcases hp1 : symPopBitL L with _ | ⟨l1, L1⟩; · rw [hp1] at h; cases h
    rw [hp1] at h; dsimp only at h; have hl1 := encSL_popBitL (v := v) hp1
    by_cases hb1 : (l1 == 1) = Bool.true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb1))] at h; have heq1 : l1 = 1 := eq_of_beq hb1
      rcases h1 : symPushZerosR 1 R with _ | Ra; · rw [h1] at h; cases h
      rw [h1] at h; injection h with h; subst h
      rw [heq1] at hl1; rw [hl1] at hsw'
      dsimp only [evalSym]; rw [encSR_pushZerosR h1]
      exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (step_e_one (encSL v L1) (encSR v R)))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb1))] at h
      have heq1 : l1 = 0 := fin2_eq_zero_of_ne_one hb1
      rcases hq1 : symPopBitR R with _ | ⟨r1, R1⟩; · rw [hq1] at h; cases h
      rw [hq1] at h; dsimp only at h; have hr1 := encSR_popBitR (v := v) hq1
      by_cases hr1b : (r1 == 1) = Bool.true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hr1b))] at h; have hreq1 : r1 = 1 := eq_of_beq hr1b
        rcases h1 : symPushZerosL 2 L1 with _ | La; · rw [h1] at h; cases h
        rw [h1] at h; injection h with h; subst h
        rw [heq1] at hl1; rw [hreq1] at hr1; rw [hl1, hr1] at hsw'
        dsimp only [evalSym]; rw [encSL_pushZerosL h1]
        exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_e_0_r1 (encSL v L1) (encSR v R1)))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hr1b))] at h
        have hreq1 : r1 = 0 := fin2_eq_zero_of_ne_one hr1b
        rcases hp2 : symPopBitL L1 with _ | ⟨l2, L2⟩; · rw [hp2] at h; cases h
        rw [hp2] at h; dsimp only at h; have hl2 := encSL_popBitL (v := v) hp2
        by_cases hb2 : (l2 == 0) = Bool.true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb2))] at h; have heq2 : l2 = 0 := eq_of_beq hb2
          rcases h1 : symPushOnesL 1 L2 with _ | La; · rw [h1] at h; cases h
          rw [h1] at h; try dsimp only at h
          rcases h2 : symPushZerosL 1 La with _ | Lb; · rw [h2] at h; cases h
          rw [h2] at h; try dsimp only at h
          rcases h3 : symPushOnesR 1 R1 with _ | Ra; · rw [h3] at h; cases h
          rw [h3] at h; injection h with h; subst h
          rw [heq1, hl2, heq2] at hl1; rw [hreq1] at hr1; rw [hl1, hr1] at hsw'
          dsimp only [evalSym]; rw [encSL_pushZerosL h2, encSL_pushOnesL h1, encSR_pushOnesR h3]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_e_00_r0 (encSL v L2) (encSR v
            R1)))
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at h
          have heq2 : l2 = 1 := fin2_eq_one_of_ne_zero hb2
          rcases h1 : symPushOnesL 1 L2 with _ | La; · rw [h1] at h; cases h
          rw [h1] at h; try dsimp only at h
          rcases h2 : symPushOnesR 1 R1 with _ | Ra; · rw [h2] at h; cases h
          rw [h2] at h; try dsimp only at h
          rcases h3 : symPushZerosR 1 Ra with _ | Rb; · rw [h3] at h; cases h
          rw [h3] at h; injection h with h; subst h
          rw [heq1, hl2, heq2] at hl1; rw [hreq1] at hr1; rw [hl1, hr1] at hsw'
          dsimp only [evalSym]; rw [encSL_pushOnesL h1, encSR_pushZerosR h3, encSR_pushOnesR h2]
          exact hsw'.trans_plus (ReachesIn.to_plus (by omega) (exit_e_01_r0 (encSL v L2) (encSR v
            R1)))

/-! #### Symbolic `[1,0,1,1]` Transducers (`symStepTrans`) & Linear Sweeps -/

def symPush1011L (L : List SymLTok) : Option (List SymLTok) :=
  match symPushOnesL 2 L with
  | none => none
  | some L1 =>
    match symPushZerosL 1 L1 with
    | none => none
    | some L2 => symPushOnesL 1 L2

def symPush1011R (R : List SymRTok) : Option (List SymRTok) :=
  match symPushOnesR 2 R with
  | none => none
  | some R1 =>
    match symPushZerosR 1 R1 with
    | none => none
    | some R2 => symPushOnesR 1 R2

private theorem encSL_push1011L {v : Fin 5 → ℕ} {L out : List SymLTok}
    (h : symPush1011L L = some out) :
    encSL v out = [1, 0, 1, 1] +> encSL v L := by
  unfold symPush1011L at h
  rcases h1 : symPushOnesL 2 L with _ | L1; · rw [h1] at h; cases h
  rw [h1] at h; try dsimp only at h
  rcases h2 : symPushZerosL 1 L1 with _ | L2; · rw [h2] at h; cases h
  rw [h2] at h; try dsimp only at h
  rw [encSL_pushOnesL h, encSL_pushZerosL h2, encSL_pushOnesL h1]; rfl

private theorem encSR_push1011R {v : Fin 5 → ℕ} {R out : List SymRTok}
    (h : symPush1011R R = some out) :
    encSR v out = [1, 0, 1, 1] +> encSR v R := by
  unfold symPush1011R at h
  rcases h1 : symPushOnesR 2 R with _ | R1; · rw [h1] at h; cases h
  rw [h1] at h; try dsimp only at h
  rcases h2 : symPushZerosR 1 R1 with _ | R2; · rw [h2] at h; cases h
  rw [h2] at h; try dsimp only at h
  rw [encSR_pushOnesR h, encSR_pushZerosR h2, encSR_pushOnesR h1]; rfl

def symPeel1011L (L : List SymLTok) : Option (List SymLTok) :=
  match symNormL L with
  | some (.pair 0 0 c0 :: rest0) =>
    if symIsZero c0 then
      match symNormL rest0 with
      | some (.pair 1 (o' + 1) c :: rest1) =>
        match symDecPairL 1 (o' + 1) c rest1 with
        | none => none
        | some l1 => symPushOnesL o' l1
      | _ => none
    else none
  | _ => none

def symPeel1011R (R : List SymRTok) : Option (List SymRTok) :=
  match symNormR R with
  | some (.pair 0 0 c0 :: rest0) =>
    if symIsZero c0 then
      match symNormR rest0 with
      | some (.pair 1 (o' + 1) c :: rest1) =>
        match symDecPairR 1 (o' + 1) c rest1 with
        | none => none
        | some r1 => symPushOnesR o' r1
      | _ => none
    else none
  | _ => none

private theorem symPeel1011L_spec {v : Fin 5 → ℕ} {L lt : List SymLTok}
    (h : symPeel1011L L = some lt) :
    encSL v L = [1, 0, 1, 1] +> encSL v lt := by
  unfold symPeel1011L at h
  rcases hn0 : symNormL L with _ | n0; · rw [hn0] at h; cases h
  rw [hn0] at h; rw [← encSL_normL hn0]
  rcases n0 with _ | ⟨t0, rest0⟩; · cases h
  rcases t0 with ⟨z0, o0, c0⟩ | _; swap; · cases h
  rcases z0 with _ | _; swap; · cases h
  rcases o0 with _ | _; swap; · cases h
  simp only at h
  split_ifs at h with hz0
  dsimp only [encSL]; rw [evalSymN_isZero hz0, pWord_0_0, pow_one_list]
  rcases hn1 : symNormL rest0 with _ | n1; · rw [hn1] at h; cases h
  rw [hn1] at h; rw [← encSL_normL hn1]
  rcases n1 with _ | ⟨t1, rest1⟩; · cases h
  rcases t1 with ⟨z1, o1, c1⟩ | _; swap; · cases h
  rcases z1 with _ | z1'; · cases h
  rcases z1' with _ | _; swap; · cases h
  rcases o1 with _ | o'; · cases h
  change (match symDecPairL 1 (o' + 1) c1 rest1 with
    | none => none | some l1 => symPushOnesL o' l1) = some lt at h
  rcases hd : symDecPairL 1 (o' + 1) c1 rest1 with _ | l1; · rw [hd] at h; cases h
  rw [hd] at h; dsimp only at h
  rw [encSL_pushOnesL h, ← encSL_decPairL hd]
  have hpw : pWord 1 (o' + 1) = [0, 1, 1] ++ ([1] : List (Fin 2)) ^ o' := by
    rw [pWord]
    simp only [List.replicate_succ (n := o' + 1), List.replicate_succ (n := o'),
      replicate_eq_pow, pow_one_list]
    rfl
  rw [hpw]; simp only [listblank_append_right_assoc]; rfl

private theorem symPeel1011R_spec {v : Fin 5 → ℕ} {R rt : List SymRTok}
    (h : symPeel1011R R = some rt) :
    encSR v R = [1, 0, 1, 1] +> encSR v rt := by
  unfold symPeel1011R at h
  rcases hn0 : symNormR R with _ | n0; · rw [hn0] at h; cases h
  rw [hn0] at h; rw [← encSR_normR hn0]
  rcases n0 with _ | ⟨t0, rest0⟩; · cases h
  rcases t0 with ⟨z0, o0, c0⟩ | _; swap; · cases h
  rcases z0 with _ | _; swap; · cases h
  rcases o0 with _ | _; swap; · cases h
  simp only at h
  split_ifs at h with hz0
  dsimp only [encSR]; rw [evalSymN_isZero hz0, pWord_0_0, pow_one_list]
  rcases hn1 : symNormR rest0 with _ | n1; · rw [hn1] at h; cases h
  rw [hn1] at h; rw [← encSR_normR hn1]
  rcases n1 with _ | ⟨t1, rest1⟩; · cases h
  rcases t1 with ⟨z1, o1, c1⟩ | _; swap; · cases h
  rcases z1 with _ | z1'; · cases h
  rcases z1' with _ | _; swap; · cases h
  rcases o1 with _ | o'; · cases h
  change (match symDecPairR 1 (o' + 1) c1 rest1 with
    | none => none | some r1 => symPushOnesR o' r1) = some rt at h
  rcases hd : symDecPairR 1 (o' + 1) c1 rest1 with _ | r1; · rw [hd] at h; cases h
  rw [hd] at h; dsimp only at h
  rw [encSR_pushOnesR h, ← encSR_decPairR hd]
  have hpw : pWord 1 (o' + 1) = [0, 1, 1] ++ ([1] : List (Fin 2)) ^ o' := by
    rw [pWord]
    simp only [List.replicate_succ (n := o' + 1), List.replicate_succ (n := o'),
      replicate_eq_pow, pow_one_list]
    rfl
  rw [hpw]; simp only [listblank_append_right_assoc]; rfl

def symConsumeAR1011 : List SymRTok → List SymLTok → Bool →
    Option (List SymRTok × List SymLTok × Bool)
  | [], L, did => some ([], L, did)
  | .mid c :: rt, L, _ =>
    match symPushWLMSem (symAddConst c 1) L with
    | none => none
    | some L1 => symConsumeAR1011 rt L1 true
  | .pair 0 o c :: rt, L, did => some (.pair 0 o c :: rt, L, did)
  | .pair 1 0 c :: rt, L, did => some (.pair 1 0 c :: rt, L, did)
  | .pair 1 1 c :: rt, L, _ =>
    match symPushLP 2 0 (symAddConst c 1) L with
    | none => none
    | some L1 => symConsumeAR1011 rt L1 true
  | .pair 1 (o'' + 2) c :: rt, L, did => some (.pair 1 (o'' + 2) c :: rt, L, did)
  | .pair 2 0 c :: rt, L, _ =>
    match symPushLP 1 1 (symAddConst c 1) L with
    | none => none
    | some L1 => symConsumeAR1011 rt L1 true
  | .pair 2 (o' + 1) c :: rt, L, did => some (.pair 2 (o' + 1) c :: rt, L, did)
  | .pair (z''' + 3) o c :: rt, L, did => some (.pair (z''' + 3) o c :: rt, L, did)

private theorem symConsumeAR1011_sound (v : Fin 5 → ℕ) :
    ∀ (rt : List SymRTok) (L : List SymLTok) (did : Bool)
      (rt' : List SymRTok) (L' : List SymLTok) (did' : Bool),
    symConsumeAR1011 rt L did = some (rt', L', did') →
      ∃ n, (did = false → did' = true → 0 < n) ∧
        ReachesIn target_tm n
          (cfgA (encSL v L) ([1, 0, 1, 1] +> encSR v rt))
          (cfgA (encSL v L') ([1, 0, 1, 1] +> encSR v rt'))
  | [], L, did, rt', L', did', h => by
    simp only [symConsumeAR1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .mid c :: rest, L, did, rt', L', did', h => by
    dsimp only [symConsumeAR1011] at h
    rcases hp : symPushWLMSem (symAddConst c 1) L with _ | L1; · rw [hp] at h; cases h
    rw [hp] at h; try dsimp only at h
    obtain ⟨n2, _, hr2⟩ := symConsumeAR1011_sound v rest L1 true rt' L' did' h
    dsimp only [encSR]
    have hs := step_a_1011_wRM_pow (evalSymN v c + 1) (encSL v L) (encSR v rest)
    rw [← evalSymN_addConst v c 1, ← encSL_pushWLMSem hp] at hs
    exact ⟨21 * (evalSymN v c + 1) + n2, fun _ _ => by omega, hs.trans hr2⟩
  | .pair 0 o c :: rest, L, did, rt', L', did', h => by
    simp only [symConsumeAR1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair 1 0 c :: rest, L, did, rt', L', did', h => by
    simp only [symConsumeAR1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair 1 1 c :: rest, L, did, rt', L', did', h => by
    dsimp only [symConsumeAR1011] at h
    rcases hp : symPushLP 2 0 (symAddConst c 1) L with _ | L1; · rw [hp] at h; cases h
    rw [hp] at h; try dsimp only at h
    obtain ⟨n2, _, hr2⟩ := symConsumeAR1011_sound v rest L1 true rt' L' did' h
    dsimp only [encSR]; rw [pWord_1_1]
    have hs := step_a_1011_wT_pow (evalSymN v c + 1) (encSL v L) (encSR v rest)
    rw [← evalSymN_addConst v c 1, ← pWord_2_0, ← encSL_pushLP hp] at hs
    exact ⟨3 * (evalSymN v c + 1) + n2, fun _ _ => by omega, hs.trans hr2⟩
  | .pair 1 (o'' + 2) c :: rest, L, did, rt', L', did', h => by
    simp only [symConsumeAR1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair 2 0 c :: rest, L, did, rt', L', did', h => by
    dsimp only [symConsumeAR1011] at h
    rcases hp : symPushLP 1 1 (symAddConst c 1) L with _ | L1; · rw [hp] at h; cases h
    rw [hp] at h; try dsimp only at h
    obtain ⟨n2, _, hr2⟩ := symConsumeAR1011_sound v rest L1 true rt' L' did' h
    dsimp only [encSR]; rw [pWord_2_0]
    have hs := step_a_1011_wZ_pow (evalSymN v c + 1) (encSL v L) (encSR v rest)
    rw [← evalSymN_addConst v c 1, ← pWord_1_1, ← encSL_pushLP hp] at hs
    exact ⟨15 * (evalSymN v c + 1) + n2, fun _ _ => by omega, hs.trans hr2⟩
  | .pair 2 (o' + 1) c :: rest, L, did, rt', L', did', h => by
    simp only [symConsumeAR1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair (z''' + 3) o c :: rest, L, did, rt', L', did', h => by
    simp only [symConsumeAR1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩

def symConsumeEL1011 : List SymLTok → List SymRTok → Bool →
    Option (List SymLTok × List SymRTok × Bool)
  | [], R, did => some ([], R, did)
  | .mid c :: lt, R, _ =>
    match symPushWRMSem (symAddConst c 1) R with
    | none => none
    | some R1 => symConsumeEL1011 lt R1 true
  | .pair 0 o c :: lt, R, did => some (.pair 0 o c :: lt, R, did)
  | .pair 1 0 c :: lt, R, did => some (.pair 1 0 c :: lt, R, did)
  | .pair 1 1 c :: lt, R, _ =>
    match symPushRP 2 0 (symAddConst c 1) R with
    | none => none
    | some R1 => symConsumeEL1011 lt R1 true
  | .pair 1 (o'' + 2) c :: lt, R, did => some (.pair 1 (o'' + 2) c :: lt, R, did)
  | .pair 2 0 c :: lt, R, _ =>
    match symPushRP 1 1 (symAddConst c 1) R with
    | none => none
    | some R1 => symConsumeEL1011 lt R1 true
  | .pair 2 (o' + 1) c :: lt, R, did => some (.pair 2 (o' + 1) c :: lt, R, did)
  | .pair (z''' + 3) o c :: lt, R, did => some (.pair (z''' + 3) o c :: lt, R, did)

private theorem symConsumeEL1011_sound (v : Fin 5 → ℕ) :
    ∀ (lt : List SymLTok) (R : List SymRTok) (did : Bool)
      (lt' : List SymLTok) (R' : List SymRTok) (did' : Bool),
    symConsumeEL1011 lt R did = some (lt', R', did') →
      ∃ n, (did = false → did' = true → 0 < n) ∧
        ReachesIn target_tm n
          (cfgE ([1, 0, 1, 1] +> encSL v lt) (encSR v R))
          (cfgE ([1, 0, 1, 1] +> encSL v lt') (encSR v R'))
  | [], R, did, lt', R', did', h => by
    simp only [symConsumeEL1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .mid c :: rest, R, did, lt', R', did', h => by
    dsimp only [symConsumeEL1011] at h
    rcases hp : symPushWRMSem (symAddConst c 1) R with _ | R1; · rw [hp] at h; cases h
    rw [hp] at h; try dsimp only at h
    obtain ⟨n2, _, hr2⟩ := symConsumeEL1011_sound v rest R1 true lt' R' did' h
    dsimp only [encSL]
    have hs := step_e_1011_wLM_pow (evalSymN v c + 1) (encSL v rest) (encSR v R)
    rw [← evalSymN_addConst v c 1, ← encSR_pushWRMSem hp] at hs
    exact ⟨45 * (evalSymN v c + 1) + n2, fun _ _ => by omega, hs.trans hr2⟩
  | .pair 0 o c :: rest, R, did, lt', R', did', h => by
    simp only [symConsumeEL1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair 1 0 c :: rest, R, did, lt', R', did', h => by
    simp only [symConsumeEL1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair 1 1 c :: rest, R, did, lt', R', did', h => by
    dsimp only [symConsumeEL1011] at h
    rcases hp : symPushRP 2 0 (symAddConst c 1) R with _ | R1; · rw [hp] at h; cases h
    rw [hp] at h; try dsimp only at h
    obtain ⟨n2, _, hr2⟩ := symConsumeEL1011_sound v rest R1 true lt' R' did' h
    dsimp only [encSL]; rw [pWord_1_1]
    have hs := step_e_1011_wT_pow (evalSymN v c + 1) (encSL v rest) (encSR v R)
    rw [← evalSymN_addConst v c 1, ← pWord_2_0, ← encSR_pushRP hp] at hs
    exact ⟨7 * (evalSymN v c + 1) + n2, fun _ _ => by omega, hs.trans hr2⟩
  | .pair 1 (o'' + 2) c :: rest, R, did, lt', R', did', h => by
    simp only [symConsumeEL1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair 2 0 c :: rest, R, did, lt', R', did', h => by
    dsimp only [symConsumeEL1011] at h
    rcases hp : symPushRP 1 1 (symAddConst c 1) R with _ | R1; · rw [hp] at h; cases h
    rw [hp] at h; try dsimp only at h
    obtain ⟨n2, _, hr2⟩ := symConsumeEL1011_sound v rest R1 true lt' R' did' h
    dsimp only [encSL]; rw [pWord_2_0]
    have hs := step_e_1011_wZ_pow (evalSymN v c + 1) (encSL v rest) (encSR v R)
    rw [← evalSymN_addConst v c 1, ← pWord_1_1, ← encSR_pushRP hp] at hs
    exact ⟨19 * (evalSymN v c + 1) + n2, fun _ _ => by omega, hs.trans hr2⟩
  | .pair 2 (o' + 1) c :: rest, R, did, lt', R', did', h => by
    simp only [symConsumeEL1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩
  | .pair (z''' + 3) o c :: rest, R, did, lt', R', did', h => by
    simp only [symConsumeEL1011, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨0, (fun h1 h2 => by rw [h1] at h2; cases h2), ReachesIn.zero _ _⟩

def symStepTrans (s : SymState) : Option SymState :=
  match s with
  | (.mA, L, R) =>
    match symPeel1011R R with
    | some rt0 =>
      match symConsumeAR1011 rt0 L false with
      | some (rt, L2, true) =>
        match symPush1011R rt with
        | none => none
        | some R' => some (.mA, L2, R')
      | some (_, _, false) => symStepBase (.mA, L, R)
      | none => none
    | none => symStepBase (.mA, L, R)
  | (.mE, L, R) =>
    match symPeel1011L L with
    | some lt0 =>
      match symConsumeEL1011 lt0 R false with
      | some (lt, R2, true) =>
        match symPush1011L lt with
        | none => none
        | some L' => some (.mE, L', R2)
      | some (_, _, false) => symStepBase (.mE, L, R)
      | none => none
    | none => symStepBase (.mE, L, R)
  | s => symStepBase s

private theorem symStepTrans_sound (v : Fin 5 → ℕ) {s s' : SymState}
    (h : symStepTrans s = some s') :
    ReachesPlus target_tm (evalSym v s) (evalSym v s') := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | mHalt => exact symStepBase_sound v h
  | mD => exact symStepBase_sound v h
  | mA =>
    dsimp only [symStepTrans] at h
    rcases hp : symPeel1011R R with _ | rt0
    · rw [hp] at h; exact symStepBase_sound v h
    · rw [hp] at h; try dsimp only at h
      rcases hc : symConsumeAR1011 rt0 L false with _ | ⟨rt, L2, did⟩
      · rw [hc] at h; cases h
      · rw [hc] at h; try dsimp only at h
        cases did <;> dsimp only at h
        · exact symStepBase_sound v h
        · rcases hpu : symPush1011R rt with _ | R'
          · rw [hpu] at h; cases h
          · rw [hpu] at h; injection h with h; subst h
            obtain ⟨n, hpos, hreach⟩ := symConsumeAR1011_sound v rt0 L false rt L2 true hc
            dsimp only [evalSym]
            rw [symPeel1011R_spec hp, encSR_push1011R hpu]
            exact ReachesIn.to_plus (hpos rfl rfl) hreach
  | mE =>
    dsimp only [symStepTrans] at h
    rcases hp : symPeel1011L L with _ | lt0
    · rw [hp] at h; exact symStepBase_sound v h
    · rw [hp] at h; try dsimp only at h
      rcases hc : symConsumeEL1011 lt0 R false with _ | ⟨lt, R2, did⟩
      · rw [hc] at h; cases h
      · rw [hc] at h; try dsimp only at h
        cases did <;> dsimp only at h
        · exact symStepBase_sound v h
        · rcases hpu : symPush1011L lt with _ | L'
          · rw [hpu] at h; cases h
          · rw [hpu] at h; injection h with h; subst h
            obtain ⟨n, hpos, hreach⟩ := symConsumeEL1011_sound v lt0 R false lt R2 true hc
            dsimp only [evalSym]
            rw [symPeel1011L_spec hp, encSL_push1011L hpu]
            exact ReachesIn.to_plus (hpos rfl rfl) hreach

def symTryDL1WZ (L : List SymLTok) (R : List SymRTok) : Option SymState :=
  match L, R with
  | .pair 0 0 c0 :: L1, .pair 1 0 cr :: R1 =>
    if symIsZero c0 then
      match symNormL L1 with
      | some (.pair 2 0 cz :: lRest) =>
        match symDecPairR 1 0 cr R1 with
        | none => none
        | some rAfter =>
          match symPushRP 2 0 (symAddConst cz 1) rAfter with
          | none => none
          | some r1 =>
            match symPushRP 1 0 symOne r1 with
            | none => none
            | some r2 => some (.mD, .pair 0 0 symZero :: lRest, r2)
      | _ => none
    else none
  | _, _ => none

private theorem symTryDL1WZ_sound (v : Fin 5 →
  ℕ) {L : List SymLTok} {R : List SymRTok} {s' : SymState}
    (h : symTryDL1WZ L R = some s') :
    ReachesPlus target_tm (evalSym v (.mD, L, R)) (evalSym v s') := by
  unfold symTryDL1WZ at h
  split at h
  · rename_i c0 L1 cr R1
    split_ifs at h with hz0
    rcases hn : symNormL L1 with _ | n1; · rw [hn] at h; cases h
    rw [hn] at h
    match n1, hn, h with
    | .pair 2 0 cz :: lRest, hn, h =>
      simp only at h
      rcases hd : symDecPairR 1 0 cr R1 with _ | rAfter; · rw [hd] at h; cases h
      rw [hd] at h; try dsimp only at h
      rcases h1 : symPushRP 2 0 (symAddConst cz 1) rAfter with _ | r1; · rw [h1] at h; cases h
      rw [h1] at h; try dsimp only at h
      rcases h2 : symPushRP 1 0 symOne r1 with _ | r2; · rw [h2] at h; cases h
      rw [h2] at h; injection h with h; subst h
      dsimp only [evalSym]
      have hl : encSL v (.pair 0 0 c0 :: L1) =
          [1] +> ((wZ ^ (evalSymN v cz + 1)) +> encSL v lRest) := by
        dsimp only [encSL]; rw [evalSymN_isZero hz0, pWord_0_0, pow_one_list, ← encSL_normL hn]
        simp [encSL, pWord_2_0]
      have hr : encSR v (.pair 1 0 cr :: R1) = [0, 1] +> encSR v rAfter := by
        rw [← encSR_decPairR hd, pWord_1_0]
      have houtL : encSL v (.pair 0 0 symZero :: lRest) = [1] +> encSL v lRest := by
        simp [encSL, evalSymN_zero, pWord_0_0, pow_one_list]
      rw [hl, hr, houtL, encSR_pushRP h2, encSR_pushRP h1, evalSymN_one, evalSymN_addConst,
        pWord_1_0, pWord_2_0, pow_one_list]
      exact ReachesIn.to_plus (by omega)
        (step_dl_1_wZ_pow (evalSymN v cz + 1) (encSL v lRest) (encSR v rAfter))
    | [], _, h | .mid _ :: _, _, h | .pair 0 _ _ :: _, _, h | .pair 1 _ _ :: _, _, h
    | .pair 2 (_ + 1) _ :: _, _, h | .pair (_ + 3) _ _ :: _, _, h => cases h
  · cases h

def symTryEL1101 (L : List SymLTok) (R : List SymRTok) : Option SymState :=
  match L, R with
  | .pair 0 1 c0 :: L1, .pair 1 0 cr :: R1 =>
    if symIsZero c0 then
      match symNormL L1 with
      | some (.pair 1 1 ct :: lRest) =>
        match symDecPairR 1 0 cr R1 with
        | none => none
        | some rAfter =>
          match symPushRP 2 0 (symAddConst ct 1) rAfter with
          | none => none
          | some r1 =>
            match symPushRP 1 0 symOne r1 with
            | none => none
            | some r2 => some (.mE, .pair 0 1 symZero :: lRest, r2)
      | _ => none
    else none
  | _, _ => none

private theorem symTryEL1101_sound (v : Fin 5 →
  ℕ) {L : List SymLTok} {R : List SymRTok} {s' : SymState}
    (h : symTryEL1101 L R = some s') :
    ReachesPlus target_tm (evalSym v (.mE, L, R)) (evalSym v s') := by
  unfold symTryEL1101 at h
  split at h
  · rename_i c0 L1 cr R1
    split_ifs at h with hz0
    rcases hn : symNormL L1 with _ | n1; · rw [hn] at h; cases h
    rw [hn] at h
    match n1, hn, h with
    | .pair 1 1 ct :: lRest, hn, h =>
      simp only at h
      rcases hd : symDecPairR 1 0 cr R1 with _ | rAfter; · rw [hd] at h; cases h
      rw [hd] at h; try dsimp only at h
      rcases h1 : symPushRP 2 0 (symAddConst ct 1) rAfter with _ | r1; · rw [h1] at h; cases h
      rw [h1] at h; try dsimp only at h
      rcases h2 : symPushRP 1 0 symOne r1 with _ | r2; · rw [h2] at h; cases h
      rw [h2] at h; injection h with h; subst h
      dsimp only [evalSym]
      have hl : encSL v (.pair 0 1 c0 :: L1) =
          [1, 1] +> ((wT ^ (evalSymN v ct + 1)) +> encSL v lRest) := by
        dsimp only [encSL]; rw [evalSymN_isZero hz0, pWord_0_1, pow_one_list, ← encSL_normL hn]
        simp [encSL, pWord_1_1]
      have hr : encSR v (.pair 1 0 cr :: R1) = [0, 1] +> encSR v rAfter := by
        rw [← encSR_decPairR hd, pWord_1_0]
      have houtL : encSL v (.pair 0 1 symZero :: lRest) = [1, 1] +> encSL v lRest := by
        simp [encSL, evalSymN_zero, pWord_0_1, pow_one_list]
      rw [hl, hr, houtL, encSR_pushRP h2, encSR_pushRP h1, evalSymN_one, evalSymN_addConst,
        pWord_1_0, pWord_2_0, pow_one_list]
      exact ReachesIn.to_plus (by omega)
        (step_el_11_01_pow (evalSymN v ct + 1) (encSL v lRest) (encSR v rAfter))
    | [], _, h | .mid _ :: _, _, h | .pair 0 _ _ :: _, _, h | .pair 1 0 _ :: _, _, h
    | .pair 1 (_ + 2) _ :: _, _, h | .pair (_ + 2) _ _ :: _, _, h => cases h
  · cases h

/-! #### Symbolic Era Accelerators (`symTryEraConv`, `symTryEraED01`, `symTryEraL11D0`) -/

def symPeelLeadingWZL : List SymLTok → SymN → SymN × List SymLTok
  | [], z => (z, [])
  | .pair 2 0 c :: rest, z => symPeelLeadingWZL rest (symAdd z (symAddConst c 1))
  | ts, z => (z, ts)

private theorem symPeelLeadingWZL_spec (v : Fin 5 → ℕ) :
    ∀ (cur : List SymLTok) (z0 : SymN),
    let res := symPeelLeadingWZL cur z0
    evalSymN v z0 ≤ evalSymN v res.1 ∧
      encSL v cur = (wZ ^ (evalSymN v res.1 - evalSymN v z0)) +> encSL v res.2
  | [], z0 => ⟨Nat.le_refl _, by simp [symPeelLeadingWZL, pow_zero_list, ListBlank.append]⟩
  | .mid c :: rest, z0 => ⟨Nat.le_refl _, by simp [symPeelLeadingWZL, pow_zero_list,
    ListBlank.append]⟩
  | .pair 0 o c :: rest, z0 => ⟨Nat.le_refl _, by simp [symPeelLeadingWZL, pow_zero_list,
    ListBlank.append]⟩
  | .pair 1 o c :: rest, z0 => ⟨Nat.le_refl _, by simp [symPeelLeadingWZL, pow_zero_list,
    ListBlank.append]⟩
  | .pair 2 0 c :: rest, z0 => by
    simp only [symPeelLeadingWZL]; dsimp only [encSL]
    obtain ⟨hle, henc⟩ := symPeelLeadingWZL_spec v rest (symAdd z0 (symAddConst c 1))
    rw [evalSymN_add, evalSymN_addConst] at hle henc
    refine ⟨by omega, ?_⟩
    rw [pWord_2_0, henc, pow_append_pow]
    congr 2; omega
  | .pair 2 (o' + 1) c :: rest, z0 => ⟨Nat.le_refl _, by simp [symPeelLeadingWZL, pow_zero_list,
    ListBlank.append]⟩
  | .pair (z''' + 3) o c :: rest, z0 => ⟨Nat.le_refl _, by simp [symPeelLeadingWZL, pow_zero_list,
    ListBlank.append]⟩

def symTryEraConv (L : List SymLTok) (R : List SymRTok) : Option SymState :=
  match L, R with
  | .pair 0 0 c0 :: lRest0, [.pair 1 1 cb, .pair 1 0 c1] =>
    if symIsZero c0 && symIsZero c1 then
      let B := symAddConst cb 1
      if 2 ≤ B.k then
        let (zTot, lTail) := symPeelLeadingWZL lRest0 symZero
        if 3 ≤ zTot.k then
          match symDivMod ⟨zTot.c0, zTot.c1, zTot.c2, zTot.c3, zTot.c4, zTot.k - 1⟩ 2 with
          | some (K, rem) =>
            if 1 ≤ K.k then
              match symPushLP 2 0 (symConst (1 + rem)) lTail with
              | none => none
              | some l1 =>
                let b4k := symAdd B (symScale 4 K)
                some (.mE, .pair 0 0 symZero :: l1,
                  [.pair 1 1 ⟨b4k.c0, b4k.c1, b4k.c2, b4k.c3, b4k.c4, b4k.k - 1⟩,
                    .pair 1 0 symZero])
            else none
          | none => none
        else none
      else none
    else none
  | _, _ => none

private theorem symTryEraConv_sound (v : Fin 5 →
  ℕ) {L : List SymLTok} {R : List SymRTok} {s' : SymState}
    (h : symTryEraConv L R = some s') :
    ReachesPlus target_tm (evalSym v (.mE, L, R)) (evalSym v s') := by
  unfold symTryEraConv at h
  split at h
  · rename_i c0 lRest0 cb c1
    by_cases hz01 : (symIsZero c0 && symIsZero c1) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz01))] at h; try dsimp only at h
      simp only [Bool.and_eq_true] at hz01
      rcases hz01 with ⟨hz0, hz1⟩
      try dsimp only at h
      by_cases hB : 2 ≤ (symAddConst cb 1).k
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hB))] at h; try dsimp only at h
        have hp := symPeelLeadingWZL_spec v lRest0 symZero
        set pz := symPeelLeadingWZL lRest0 symZero
        by_cases hz : 3 ≤ pz.1.k
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz))] at h; try dsimp only at h
          rcases hdm : symDivMod ⟨pz.1.c0, pz.1.c1, pz.1.c2, pz.1.c3, pz.1.c4, pz.1.k - 1⟩ 2 with
            _ | ⟨K, rem⟩
          · rw [hdm] at h; cases h
          · rw [hdm] at h; try dsimp only at h
            by_cases hK : 1 ≤ K.k
            · rw [(ite_eq_left_of_eq_true _ _ (eq_true hK))] at h; try dsimp only at h
              rcases hpl : symPushLP 2 0 (symConst (1 + rem)) pz.2 with _ | l1
              · rw [hpl] at h; cases h
              · rw [hpl] at h; injection h with h; subst h
                obtain ⟨_, hrem2, hdiv⟩ := evalSymN_divMod (v := v) hdm
                have hKz : 1 ≤ evalSymN v K := le_trans hK (evalSymN_ge_k v K)
                have hBz : 2 ≤ evalSymN v cb + 1 := by
                  have := evalSymN_ge_k v cb; dsimp only [symAddConst] at hB; omega
                have hsub1 : evalSymN v ⟨pz.1.c0, pz.1.c1, pz.1.c2, pz.1.c3, pz.1.c4, pz.1.k - 1⟩ =
                    evalSymN v pz.1 - 1 := by
                  dsimp only [evalSymN]; omega
                rw [hsub1] at hdiv
                have hpz_ge : 3 ≤ evalSymN v pz.1 := le_trans hz (evalSymN_ge_k v pz.1)
                dsimp only [evalSym, encSL, encSR]
                rw [evalSymN_isZero hz0, evalSymN_isZero hz1, evalSymN_zero,
                  pWord_0_0, pWord_1_1, pWord_1_0, pow_one_list,
                  encSL_pushLP hpl, evalSymN_const, pWord_2_0]
                rw [hp.2, evalSymN_zero, Nat.sub_zero]
                set b4k := symAdd (symAddConst cb 1) (symScale 4 K)
                have hb4k_k : 1 ≤ b4k.k := by dsimp only [b4k, symAdd, symAddConst, symScale]; omega
                have hb4k_ev : evalSymN v ⟨b4k.c0, b4k.c1, b4k.c2, b4k.c3, b4k.c4, b4k.k - 1⟩ + 1 =
                    (evalSymN v cb - 1) + 2 + 4 * evalSymN v K := by
                  have he1 : evalSymN v ⟨b4k.c0, b4k.c1, b4k.c2, b4k.c3, b4k.c4, b4k.k - 1⟩ + 1 =
                      evalSymN v b4k := by dsimp only [evalSymN]; omega
                  rw [he1]
                  dsimp only [b4k]
                  rw [evalSymN_add, evalSymN_addConst, evalSymN_scale]; omega
                have hb' : evalSymN v cb + 1 = (evalSymN v cb - 1) + 2 := by omega
                have hzSplit : evalSymN v pz.1 = 2 * evalSymN v K + (rem + 1) := by omega
                have h1r : 1 + rem = rem + 1 := by omega
                rw [hb4k_ev, hb', hzSplit, h1r]
                have hpos : 0 < evalSymN v K * (18 * (evalSymN v cb - 1 + 2) + 60) +
                    36 * evalSymN v K * (evalSymN v K - 1) := by
                  have : 1 * (18 * (evalSymN v cb - 1 + 2) + 60) ≤
                      evalSymN v K * (18 * (evalSymN v cb - 1 + 2) + 60) :=
                    Nat.mul_le_mul_right _ hKz
                  omega
                exact ReachesIn.to_plus hpos
                  (era_conv_loop (evalSymN v K) rem (evalSymN v cb - 1) (encSL v pz.2))
            · rw [(ite_eq_right_of_eq_false _ _ (eq_false hK))] at h; cases h
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz))] at h; cases h
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hB))] at h; cases h
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz01))] at h; cases h
  · cases h

inductive SymMidItem : Type
  | mid (cnt : SymN)
  | t (cnt : SymN)
  | z (cnt : SymN)
  deriving DecidableEq, Repr

def evalMidItem (v : Fin 5 → ℕ) : SymMidItem → MidItem
  | .mid c => .mid (evalSymN v c)
  | .t c => .t (evalSymN v c)
  | .z c => .z (evalSymN v c)

def symRebuildMR : List SymMidItem → List SymRTok → Option (List SymRTok)
  | [], tail => some tail
  | .mid k :: ms, tail =>
    match symRebuildMR ms tail with
    | none => none
    | some t1 => symPushWRMSem k t1
  | .t k :: ms, tail =>
    match symRebuildMR ms tail with
    | none => none
    | some t1 => symPushRP 1 1 k t1
  | .z k :: ms, tail =>
    match symRebuildMR ms tail with
    | none => none
    | some t1 => symPushRP 2 0 k t1

private theorem encSR_symRebuildMR (v : Fin 5 → ℕ) :
    ∀ (ms : List SymMidItem) (tail out : List SymRTok),
    symRebuildMR ms tail = some out →
      encSR v out = encMidR (ms.map (evalMidItem v)) (encSR v tail)
  | [], tail, out, h => by simp [symRebuildMR] at h; subst h; rfl
  | .mid k :: ms, tail, out, h => by
    dsimp only [symRebuildMR] at h
    rcases hr : symRebuildMR ms tail with _ | t1; · rw [hr] at h; cases h
    rw [hr] at h; try dsimp only at h
    rw [encSR_pushWRMSem h, encSR_symRebuildMR v ms tail t1 hr]; rfl
  | .t k :: ms, tail, out, h => by
    dsimp only [symRebuildMR] at h
    rcases hr : symRebuildMR ms tail with _ | t1; · rw [hr] at h; cases h
    rw [hr] at h; try dsimp only at h
    rw [encSR_pushRP h, pWord_1_1, encSR_symRebuildMR v ms tail t1 hr]; rfl
  | .z k :: ms, tail, out, h => by
    dsimp only [symRebuildMR] at h
    rcases hr : symRebuildMR ms tail with _ | t1; · rw [hr] at h; cases h
    rw [hr] at h; try dsimp only at h
    rw [encSR_pushRP h, pWord_2_0, encSR_symRebuildMR v ms tail t1 hr]; rfl

def symPeelLeadingWTR : List SymRTok → SymN → Option (SymN × List SymRTok)
  | [], tf => some (tf, [])
  | .mid c :: rest, tf =>
    match symDecMidR c rest with
    | none => none
    | some rest' => some (symAddConst tf 2, .pair 2 0 symZero :: rest')
  | .pair 1 1 c :: rest, tf => symPeelLeadingWTR rest (symAdd tf (symAddConst c 1))
  | cur, tf => some (tf, cur)

private theorem symPeelLeadingWTR_spec (v : Fin 5 → ℕ) :
    ∀ (cur : List SymRTok) (tf0 tf1 : SymN) (rem : List SymRTok),
    symPeelLeadingWTR cur tf0 = some (tf1, rem) →
      evalSymN v tf0 ≤ evalSymN v tf1 ∧
        encSR v cur = (wT ^ (evalSymN v tf1 - evalSymN v tf0)) +> encSR v rem
  | [], tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩
  | .mid c :: rest, tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR] at h
    rcases hd : symDecMidR c rest with _ | rest'; · rw [hd] at h; cases h
    rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [evalSymN_addConst]
    refine ⟨by omega, ?_⟩
    have hsub : evalSymN v tf0 + 2 - evalSymN v tf0 = 2 := by omega
    rw [hsub, ← encSR_decMidR hd]
    simp only [encSR, evalSymN_zero, pWord_2_0]; rfl
  | .pair 0 o c :: rest, tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩
  | .pair 1 0 c :: rest, tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩
  | .pair 1 1 c :: rest, tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR] at h
    obtain ⟨hle, henc⟩ := symPeelLeadingWTR_spec v rest (symAdd tf0 (symAddConst c 1)) tf1 rem h
    rw [evalSymN_add, evalSymN_addConst] at hle henc
    refine ⟨by omega, ?_⟩
    dsimp only [encSR]; rw [pWord_1_1, henc, pow_append_pow]
    congr 2; omega
  | .pair 1 (o'' + 2) c :: rest, tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩
  | .pair (z'' + 2) o c :: rest, tf0, tf1, rem, h => by
    simp only [symPeelLeadingWTR, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩

inductive SymTowerD01 : Type
  | d0 (B : SymN) (rt : List SymRTok)
  | d1Empty (tf B : SymN) (rt : List SymRTok)
  | d1Mid (tf cz : SymN) (ms' : List SymMidItem) (B : SymN) (rt : List SymRTok)
  deriving DecidableEq, Repr

def evalTower (v : Fin 5 → ℕ) : SymTowerD01 → TowerD01
  | .d0 B rt => .d0 (evalSymN v B) (rt.map (evalRTok v))
  | .d1Empty tf B rt => .d1Empty (evalSymN v tf) (evalSymN v B) (rt.map (evalRTok v))
  | .d1Mid tf cz ms' B rt =>
    let msE := ms'.map (evalMidItem v)
    .d1Mid (evalSymN v tf) (evalSymN v cz) msE
      (evalSymN v tf + (evalSymN v cz + 1) + w3Mid msE) (evalSymN v B) (rt.map (evalRTok v))

def symScanStageMidR : List SymRTok → Option (List SymMidItem × List SymRTok)
  | [] => none
  | .mid c :: rest =>
    match symScanStageMidR rest with
    | some (ms, tail) => some (.mid (symAddConst c 1) :: ms, tail)
    | none => none
  | .pair 1 1 c :: rest =>
    match symScanStageMidR rest with
    | some (ms, tail) => some (.t (symAddConst c 1) :: ms, tail)
    | none => none
  | .pair 1 2 c :: rest =>
    if symIsZero c then some ([], rest) else none
  | .pair 2 0 c :: rest =>
    match symScanStageMidR rest with
    | some (ms, tail) => some (.z (symAddConst c 1) :: ms, tail)
    | none => none
  | _ :: _ => none

private theorem symScanStageMidR_spec (v : Fin 5 → ℕ) :
    ∀ (cur : List SymRTok) {ms : List SymMidItem} {tail : List SymRTok},
    symScanStageMidR cur = some (ms, tail) →
      encSR v cur = encMidR (ms.map (evalMidItem v)) ([0, 1, 1, 1] +> encSR v tail)
  | [], _, _, h => by cases h
  | .mid c :: rest, _, _, h => by
    simp only [symScanStageMidR] at h
    rcases hs : symScanStageMidR rest with _ | ⟨ms0, tail0⟩; · rw [hs] at h; cases h
    rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    dsimp only [encSR, List.map, encMidR, evalMidItem, encMidItemR]
    rw [evalSymN_addConst, symScanStageMidR_spec v rest hs]
  | .pair 1 1 c :: rest, _, _, h => by
    simp only [symScanStageMidR] at h
    rcases hs : symScanStageMidR rest with _ | ⟨ms0, tail0⟩; · rw [hs] at h; cases h
    rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    dsimp only [encSR, List.map, encMidR, evalMidItem, encMidItemR]
    rw [pWord_1_1, evalSymN_addConst, symScanStageMidR_spec v rest hs]
  | .pair 1 2 c :: rest, _, _, h => by
    simp only [symScanStageMidR] at h
    split_ifs at h with hz
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [encSR, evalSymN_isZero hz, pWord_1_2, pow_one_list, encMidR]
  | .pair 2 0 c :: rest, _, _, h => by
    simp only [symScanStageMidR] at h
    rcases hs : symScanStageMidR rest with _ | ⟨ms0, tail0⟩; · rw [hs] at h; cases h
    rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    dsimp only [encSR, List.map, encMidR, evalMidItem, encMidItemR]
    rw [pWord_2_0, evalSymN_addConst, symScanStageMidR_spec v rest hs]
  | .pair 0 _ _ :: _, _, _, h => by cases h
  | .pair 1 0 _ :: _, _, _, h => by cases h
  | .pair 1 (_ + 3) _ :: _, _, _, h => by cases h
  | .pair 2 (_ + 1) _ :: _, _, _, h => by cases h
  | .pair (_ + 3) _ _ :: _, _, _, h => by cases h

def symParseTowerD01 : List SymRTok → Option SymTowerD01
  | .pair 1 0 c0 :: rest0 =>
    if symIsConst1 c0 then
      match symPeelLeadingWTR rest0 symZero with
      | some (tf, .pair 1 2 c1 :: rest2) =>
        if symIsZero c1 then
          match symPeelLeadingWTR rest2 symZero with
          | some (B, rt) => if 1 ≤ B.k then some (.d1Empty tf B rt) else none
          | none => none
        else none
      | some (tf, .pair 2 0 cz :: rest1') =>
        if 2 ≤ tf.k then
          match symScanStageMidR rest1' with
          | some (ms', rest2) =>
            match symPeelLeadingWTR rest2 symZero with
            | some (B, rt) => if 1 ≤ B.k then some (.d1Mid tf cz ms' B rt) else none
            | none => none
          | none => none
        else none
      | _ => none
    else none
  | .pair 1 2 c0 :: rest0 =>
    if symIsZero c0 then
      match symPeelLeadingWTR rest0 symZero with
      | some (B, rt) => if 1 ≤ B.k then some (.d0 B rt) else none
      | none => none
    else none
  | _ => none

def symScanMAndTowerD01 : List SymRTok → Option (List SymMidItem × SymTowerD01)
  | [] => none
  | .mid c :: rest =>
    match symScanMAndTowerD01 rest with
    | some (ms, tw) => some (.mid (symAddConst c 1) :: ms, tw)
    | none => none
  | .pair 1 0 c :: rest =>
    if symIsConst1 c then
      match symParseTowerD01 (.pair 1 0 c :: rest) with
      | some tw => some ([], tw)
      | none => none
    else none
  | .pair 1 1 c :: rest =>
    match symScanMAndTowerD01 rest with
    | some (ms, tw) => some (.t (symAddConst c 1) :: ms, tw)
    | none => none
  | .pair 1 2 c :: rest =>
    if symIsZero c then
      match symParseTowerD01 (.pair 1 2 c :: rest) with
      | some tw => some ([], tw)
      | none => none
    else none
  | .pair 2 0 c :: rest =>
    match symScanMAndTowerD01 rest with
    | some (ms, tw) => some (.z (symAddConst c 1) :: ms, tw)
    | none => none
  | _ :: _ => none

private theorem symParseTowerD01_spec (v : Fin 5 → ℕ) :
    ∀ {cur : List SymRTok} {tw : SymTowerD01},
    symParseTowerD01 cur = some tw →
      TowerWF (evalTower v tw) ∧ encSR v cur = encR (buildAdvTowerD01 (evalTower v tw) 0)
  | .pair 1 0 c0 :: rest0, tw, h => by
    simp only [symParseTowerD01] at h
    split_ifs at h with hc1
    rcases hp1 : symPeelLeadingWTR rest0 symZero with _ | ⟨tf, rest1⟩; · rw [hp1] at h; cases h
    rw [hp1] at h; try dsimp only at h
    obtain ⟨_, he1⟩ := symPeelLeadingWTR_spec v rest0 symZero tf rest1 hp1
    rw [evalSymN_zero, Nat.sub_zero] at he1
    match rest1, h with
    | .pair 1 2 c1 :: rest1', h =>
      simp only at h
      split_ifs at h with hz1
      rcases hp2 : symPeelLeadingWTR rest1' symZero with _ | ⟨B, rt⟩; · rw [hp2] at h; cases h
      rw [hp2] at h; try dsimp only at h
      split_ifs at h with hB
      injection h with h; subst h
      obtain ⟨_, he2⟩ := symPeelLeadingWTR_spec v rest1' symZero B rt hp2
      rw [evalSymN_zero, Nat.sub_zero] at he2
      refine ⟨trivial, ?_⟩
      dsimp only [encSR, evalTower, buildAdvTowerD01]
      rw [evalSymN_isConst1 hc1, pWord_1_0, he1]
      dsimp only [encSR]; rw [evalSymN_isZero hz1, pWord_1_2, pow_one_list, he2]
      simp [encR_pushRP, encSR_eq_encR_map, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list]
    | .pair 2 0 cz :: rest1', h =>
      simp only at h
      split_ifs at h with htf
      rcases hsm : symScanStageMidR rest1' with _ | ⟨ms', rest2⟩; · rw [hsm] at h; cases h
      rw [hsm] at h; try dsimp only at h
      rcases hp2 : symPeelLeadingWTR rest2 symZero with _ | ⟨B, rt⟩; · rw [hp2] at h; cases h
      rw [hp2] at h; try dsimp only at h
      split_ifs at h with hB
      injection h with h; subst h
      obtain ⟨_, he2⟩ := symPeelLeadingWTR_spec v rest2 symZero B rt hp2
      rw [evalSymN_zero, Nat.sub_zero] at he2
      have he' := symScanStageMidR_spec v rest1' hsm
      refine ⟨⟨le_trans htf (evalSymN_ge_k v tf), rfl⟩, ?_⟩
      dsimp only [encSR, evalTower, buildAdvTowerD01]
      rw [evalSymN_isConst1 hc1, pWord_1_0, he1]
      dsimp only [encSR]; rw [pWord_2_0, he', he2]
      simp only [Nat.mul_zero, Nat.sub_zero, encR_pushRP, encR_rebuildMR,
        encSR_eq_encR_map, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list, pow_zero_list]
      rfl
    | [], h | .mid _ :: _, h | .pair 0 _ _ :: _, h | .pair 1 0 _ :: _, h
    | .pair 1 1 _ :: _, h | .pair 1 (_ + 3) _ :: _, h | .pair 2 (_ + 1) _ :: _, h
    | .pair (_ + 3) _ _ :: _, h => cases h
  | .pair 1 2 c0 :: rest0, tw, h => by
    simp only [symParseTowerD01] at h
    split_ifs at h with hz0
    rcases hp0 : symPeelLeadingWTR rest0 symZero with _ | ⟨B, rt⟩; · rw [hp0] at h; cases h
    rw [hp0] at h; try dsimp only at h
    split_ifs at h with hB
    injection h with h; subst h
    obtain ⟨_, he0⟩ := symPeelLeadingWTR_spec v rest0 symZero B rt hp0
    rw [evalSymN_zero, Nat.sub_zero] at he0
    refine ⟨trivial, ?_⟩
    dsimp only [encSR, evalTower, buildAdvTowerD01]
    rw [evalSymN_isZero hz0, pWord_1_2, pow_one_list, he0]
    simp [encR_pushRP, encSR_eq_encR_map, pWord_1_1, pWord_1_2, pow_one_list]
  | [], _, h | .mid _ :: _, _, h | .pair 0 _ _ :: _, _, h | .pair 1 1 _ :: _, _, h
  | .pair 1 (_ + 3) _ :: _, _, h | .pair (_ + 2) _ _ :: _, _, h => by cases h

private theorem symScanMAndTowerD01_spec (v : Fin 5 → ℕ) :
    ∀ (cur : List SymRTok) {ms : List SymMidItem} {tw : SymTowerD01},
    symScanMAndTowerD01 cur = some (ms, tw) →
      TowerWF (evalTower v tw) ∧
        encSR v cur = encMidR (ms.map (evalMidItem v)) (encR (buildAdvTowerD01 (evalTower v tw) 0))
  | [], _, _, h => by cases h
  | .mid c :: rest, _, _, h => by
    simp only [symScanMAndTowerD01] at h
    rcases hs : symScanMAndTowerD01 rest with _ | ⟨ms0, tw0⟩; · rw [hs] at h; cases h
    rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨htw, he⟩ := symScanMAndTowerD01_spec v rest hs
    refine ⟨htw, ?_⟩
    dsimp only [encSR, List.map, encMidR, evalMidItem, encMidItemR]
    rw [evalSymN_addConst, he]
  | .pair 1 0 c :: rest, _, _, h => by
    simp only [symScanMAndTowerD01] at h
    split_ifs at h with hc1
    rcases hp : symParseTowerD01 (.pair 1 0 c :: rest) with _ | tw0; · rw [hp] at h; cases h
    rw [hp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact symParseTowerD01_spec v hp
  | .pair 1 1 c :: rest, _, _, h => by
    simp only [symScanMAndTowerD01] at h
    rcases hs : symScanMAndTowerD01 rest with _ | ⟨ms0, tw0⟩; · rw [hs] at h; cases h
    rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨htw, he⟩ := symScanMAndTowerD01_spec v rest hs
    refine ⟨htw, ?_⟩
    dsimp only [encSR, List.map, encMidR, evalMidItem, encMidItemR]
    rw [pWord_1_1, evalSymN_addConst, he]
  | .pair 1 2 c :: rest, _, _, h => by
    simp only [symScanMAndTowerD01] at h
    split_ifs at h with hz0
    rcases hp : symParseTowerD01 (.pair 1 2 c :: rest) with _ | tw0; · rw [hp] at h; cases h
    rw [hp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact symParseTowerD01_spec v hp
  | .pair 2 0 c :: rest, _, _, h => by
    simp only [symScanMAndTowerD01] at h
    rcases hs : symScanMAndTowerD01 rest with _ | ⟨ms0, tw0⟩; · rw [hs] at h; cases h
    rw [hs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨htw, he⟩ := symScanMAndTowerD01_spec v rest hs
    refine ⟨htw, ?_⟩
    dsimp only [encSR, List.map, encMidR, evalMidItem, encMidItemR]
    rw [pWord_2_0, evalSymN_addConst, he]
  | .pair 0 _ _ :: _, _, _, h => by cases h
  | .pair 1 (_ + 3) _ :: _, _, _, h => by cases h
  | .pair 2 (_ + 1) _ :: _, _, _, h => by cases h
  | .pair (_ + 3) _ _ :: _, _, _, h => by cases h

def symBuildAdvTowerD01 (tw : SymTowerD01) (N : SymN) : Option (List SymRTok) :=
  match tw with
  | .d0 B rt =>
    match symSub B N with
    | none => none
    | some d =>
      match symPushRP 1 1 d rt with
      | none => none
      | some r1 => symPushRP 1 2 symOne r1
  | .d1Empty tf B rt =>
    match symSub B (symScale 2 N) with
    | none => none
    | some d =>
      match symPushRP 1 1 d rt with
      | none => none
      | some r1 =>
        match symPushRP 1 2 symOne r1 with
        | none => none
        | some r2 =>
          match symPushRP 1 1 (symAdd tf N) r2 with
          | none => none
          | some r3 => symPushRP 1 0 (symConst 2) r3
  | .d1Mid tf cz ms' B rt =>
    match symSub B (symScale 2 N) with
    | none => none
    | some dB =>
      match symSub tf N with
      | none => none
      | some dtf =>
        match symPushRP 1 1 dB rt with
        | none => none
        | some r1 =>
          match symPushRP 1 2 symOne r1 with
          | none => none
          | some r2 =>
            match symPushRP 1 1 (symScale 2 N) r2 with
            | none => none
            | some r3 =>
              match symRebuildMR (.z (symAddConst cz 1) :: ms') r3 with
              | none => none
              | some r4 =>
                match symPushRP 1 1 dtf r4 with
                | none => none
                | some r5 => symPushRP 1 0 (symConst 2) r5

private theorem symBuildAdvTowerD01_spec (v : Fin 5 → ℕ) {tw : SymTowerD01} {N : SymN}
    {out : List SymRTok} (h : symBuildAdvTowerD01 tw N = some out) :
    encSR v out = encR (buildAdvTowerD01 (evalTower v tw) (evalSymN v N)) := by
  cases tw with
  | d0 B rt =>
    dsimp only [symBuildAdvTowerD01] at h
    rcases hs : symSub B N with _ | d; · rw [hs] at h; cases h
    rw [hs] at h; try dsimp only at h
    rcases h1 : symPushRP 1 1 d rt with _ | r1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    obtain ⟨_, hd⟩ := evalSymN_sub (v := v) hs
    dsimp only [evalTower, buildAdvTowerD01]
    rw [encSR_pushRP h, encSR_pushRP h1, encR_pushRP, encR_pushRP,
      evalSymN_one, hd, encSR_eq_encR_map]
  | d1Empty tf B rt =>
    dsimp only [symBuildAdvTowerD01] at h
    rcases hs : symSub B (symScale 2 N) with _ | d; · rw [hs] at h; cases h
    rw [hs] at h; try dsimp only at h
    rcases h1 : symPushRP 1 1 d rt with _ | r1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    rcases h2 : symPushRP 1 2 symOne r1 with _ | r2; · rw [h2] at h; cases h
    rw [h2] at h; try dsimp only at h
    rcases h3 : symPushRP 1 1 (symAdd tf N) r2 with _ | r3; · rw [h3] at h; cases h
    rw [h3] at h; try dsimp only at h
    obtain ⟨_, hd⟩ := evalSymN_sub (v := v) hs
    rw [evalSymN_scale] at hd
    dsimp only [evalTower, buildAdvTowerD01]
    rw [encSR_pushRP h, encSR_pushRP h3, encSR_pushRP h2, encSR_pushRP h1,
      encR_pushRP, encR_pushRP, encR_pushRP, encR_pushRP,
      evalSymN_const, evalSymN_add, evalSymN_one, hd, encSR_eq_encR_map]
  | d1Mid tf cz ms' B rt =>
    dsimp only [symBuildAdvTowerD01] at h
    rcases hsB : symSub B (symScale 2 N) with _ | dB; · rw [hsB] at h; cases h
    rw [hsB] at h; try dsimp only at h
    rcases hstf : symSub tf N with _ | dtf; · rw [hstf] at h; cases h
    rw [hstf] at h; try dsimp only at h
    rcases h1 : symPushRP 1 1 dB rt with _ | r1; · rw [h1] at h; cases h
    rw [h1] at h; try dsimp only at h
    rcases h2 : symPushRP 1 2 symOne r1 with _ | r2; · rw [h2] at h; cases h
    rw [h2] at h; try dsimp only at h
    rcases h3 : symPushRP 1 1 (symScale 2 N) r2 with _ | r3; · rw [h3] at h; cases h
    rw [h3] at h; try dsimp only at h
    rcases h4 : symRebuildMR (.z (symAddConst cz 1) :: ms') r3 with _ | r4; · rw [h4] at h; cases h
    rw [h4] at h; try dsimp only at h
    rcases h5 : symPushRP 1 1 dtf r4 with _ | r5; · rw [h5] at h; cases h
    rw [h5] at h; try dsimp only at h
    obtain ⟨_, hdB⟩ := evalSymN_sub (v := v) hsB; rw [evalSymN_scale] at hdB
    obtain ⟨_, hdtf⟩ := evalSymN_sub (v := v) hstf
    dsimp only [evalTower, buildAdvTowerD01]
    rw [encSR_pushRP h, encSR_pushRP h5, encSR_symRebuildMR v _ _ _ h4,
      encSR_pushRP h3, encSR_pushRP h2, encSR_pushRP h1,
      encR_pushRP, encR_pushRP, encR_rebuildMR, encR_pushRP, encR_pushRP, encR_pushRP,
      evalSymN_const, evalSymN_scale, evalSymN_one, hdB, hdtf, encSR_eq_encR_map]
    dsimp only [List.map, evalMidItem]; rw [evalSymN_addConst]

def symEraEK : SymTowerD01 → Option SymN
  | .d0 B _ =>
    match symDivMod B 6 with
    | some (K, _) => if 1 ≤ K.k then some K else none
    | none => none
  | .d1Empty _ B _ =>
    match symDivMod B 12 with
    | some (K, _) => if 1 ≤ K.k then some K else none
    | none => none
  | .d1Mid tf _ _ B _ =>
    if 1 ≤ tf.k then
      let tf1 : SymN := ⟨tf.c0, tf.c1, tf.c2, tf.c3, tf.c4, tf.k - 1⟩
      match symDivMod tf1 6 with
      | some (K, _) =>
        if 1 ≤ K.k && symLe (symScale 12 K) B then some K
        else
          match symDivMod B 12 with
          | some (K2, _) => if 1 ≤ K2.k && symLe (symScale 6 K2) tf1 then some K2 else none
          | none => none
      | none =>
        match symDivMod B 12 with
        | some (K2, _) => if 1 ≤ K2.k && symLe (symScale 6 K2) tf1 then some K2 else none
        | none => none
    else none

private theorem symEraEK_spec (v : Fin 5 → ℕ) {tw : SymTowerD01} {K : SymN}
    (h : symEraEK tw = some K) :
    1 ≤ evalSymN v K ∧ 6 * evalSymN v K ≤ maxReflD01 (evalTower v tw) := by
  cases tw with
  | d0 B rt =>
    dsimp only [symEraEK] at h
    rcases hdm : symDivMod B 6 with _ | ⟨K0, r⟩; · rw [hdm] at h; cases h
    rw [hdm] at h; try dsimp only at h
    split_ifs at h with hK
    injection h with h; subst h
    obtain ⟨_, _, hdiv⟩ := evalSymN_divMod (v := v) hdm
    have hKz := le_trans hK (evalSymN_ge_k v K0)
    dsimp only [evalTower, maxReflD01]; omega
  | d1Empty tf B rt =>
    dsimp only [symEraEK] at h
    rcases hdm : symDivMod B 12 with _ | ⟨K0, r⟩; · rw [hdm] at h; cases h
    rw [hdm] at h; try dsimp only at h
    split_ifs at h with hK
    injection h with h; subst h
    obtain ⟨_, _, hdiv⟩ := evalSymN_divMod (v := v) hdm
    have hKz := le_trans hK (evalSymN_ge_k v K0)
    dsimp only [evalTower, maxReflD01]; omega
  | d1Mid tf cz ms' B rt =>
    dsimp only [symEraEK] at h
    split_ifs at h with htf
    set tf1 : SymN := ⟨tf.c0, tf.c1, tf.c2, tf.c3, tf.c4, tf.k - 1⟩
    have htf1 : evalSymN v tf1 = evalSymN v tf - 1 := by dsimp only [tf1, evalSymN]; omega
    rcases hdm1 : symDivMod tf1 6 with _ | ⟨K1, r1⟩
    · rw [hdm1] at h; try dsimp only at h
      rcases hdm2 : symDivMod B 12 with _ | ⟨K2, r2⟩; · rw [hdm2] at h; cases h
      rw [hdm2] at h; try dsimp only at h
      by_cases hc : (decide (1 ≤ K2.k) && symLe (symScale 6 K2) tf1) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc))] at h; injection h with h; subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨_, _, hdiv2⟩ := evalSymN_divMod (v := v) hdm2
        have hle := evalSymN_le (v := v) hc.2; rw [evalSymN_scale, htf1] at hle
        have hKz := le_trans hc.1 (evalSymN_ge_k v K2)
        dsimp only [evalTower, maxReflD01]; omega
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc))] at h; cases h
    · rw [hdm1] at h; try dsimp only at h
      by_cases hc1 : (decide (1 ≤ K1.k) && symLe (symScale 12 K1) B) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc1))] at h; injection h with h; subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
        obtain ⟨_, _, hdiv1⟩ := evalSymN_divMod (v := v) hdm1
        have hle := evalSymN_le (v := v) hc1.2; rw [evalSymN_scale] at hle
        have hKz := le_trans hc1.1 (evalSymN_ge_k v K1)
        dsimp only [evalTower, maxReflD01]; omega
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc1))] at h; try dsimp only at h
        rcases hdm2 : symDivMod B 12 with _ | ⟨K2, r2⟩; · rw [hdm2] at h; cases h
        rw [hdm2] at h; try dsimp only at h
        by_cases hc2 : (decide (1 ≤ K2.k) && symLe (symScale 6 K2) tf1) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc2))] at h; injection h with h; subst h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
          obtain ⟨_, _, hdiv2⟩ := evalSymN_divMod (v := v) hdm2
          have hle := evalSymN_le (v := v) hc2.2; rw [evalSymN_scale, htf1] at hle
          have hKz := le_trans hc2.1 (evalSymN_ge_k v K2)
          dsimp only [evalTower, maxReflD01]; omega
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc2))] at h; cases h

def symTryEraED01 (L : List SymLTok) (R : List SymRTok) : Option SymState :=
  match L, R with
  | [.pair 0 0 c0, .pair 1 1 c1], .pair 1 1 cr0 :: .pair 2 0 cz0 :: rRest0 =>
    if symIsZero c0 && symIsZero c1 && symIsZero cr0 then
      match symDecPairR 2 0 cz0 rRest0 with
      | none => none
      | some cur =>
        match symScanMAndTowerD01 cur with
        | some (ms, tw) =>
          match symEraEK tw with
          | some K =>
            let k6 := symScale 6 K
            match symBuildAdvTowerD01 tw k6 with
            | none => none
            | some tw' =>
              match symPushRP 1 1 k6 tw' with
              | none => none
              | some out0 =>
                match symRebuildMR ms out0 with
                | none => none
                | some out1 =>
                  match symPushWRMSem K out1 with
                  | none => none
                  | some out2 =>
                    match symPushRP 2 0 symOne out2 with
                    | none => none
                    | some out3 =>
                      match symPushRP 1 1 symOne out3 with
                      | none => none
                      | some out => some (.mE, [.pair 0 0 symZero, .pair 1 1 symZero], out)
          | none => none
        | none => none
    else none
  | _, _ => none

private theorem symTryEraED01_sound (v : Fin 5 →
  ℕ) {L : List SymLTok} {R : List SymRTok} {s' : SymState}
    (h : symTryEraED01 L R = some s') :
    ReachesPlus target_tm (evalSym v (.mE, L, R)) (evalSym v s') := by
  unfold symTryEraED01 at h
  split at h
  · rename_i c0 c1 cr0 cz0 rRest0
    by_cases hz : (symIsZero c0 && symIsZero c1 && symIsZero cr0) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz))] at h; try dsimp only at h
      simp only [Bool.and_eq_true] at hz
      rcases hz with ⟨⟨hz0, hz1⟩, hzr0⟩
      rcases hd : symDecPairR 2 0 cz0 rRest0 with _ | cur; · rw [hd] at h; cases h
      rw [hd] at h; try dsimp only at h
      rcases hs : symScanMAndTowerD01 cur with _ | ⟨ms, tw⟩; · rw [hs] at h; cases h
      rw [hs] at h; try dsimp only at h
      rcases hK : symEraEK tw with _ | K; · rw [hK] at h; cases h
      rw [hK] at h; try dsimp only at h
      try dsimp only at h
      rcases hb : symBuildAdvTowerD01 tw (symScale 6 K) with _ | tw'; · rw [hb] at h; cases h
      rw [hb] at h; try dsimp only at h
      rcases ho0 : symPushRP 1 1 (symScale 6 K) tw' with _ | out0; · rw [ho0] at h; cases h
      rw [ho0] at h; try dsimp only at h
      rcases ho1 : symRebuildMR ms out0 with _ | out1; · rw [ho1] at h; cases h
      rw [ho1] at h; try dsimp only at h
      rcases ho2 : symPushWRMSem K out1 with _ | out2; · rw [ho2] at h; cases h
      rw [ho2] at h; try dsimp only at h
      rcases ho3 : symPushRP 2 0 symOne out2 with _ | out3; · rw [ho3] at h; cases h
      rw [ho3] at h; try dsimp only at h
      rcases ho4 : symPushRP 1 1 symOne out3 with _ | out; · rw [ho4] at h; cases h
      rw [ho4] at h; injection h with h; subst h
      obtain ⟨htw, henc⟩ := symScanMAndTowerD01_spec v cur hs
      obtain ⟨hK1, hK6⟩ := symEraEK_spec v hK
      have hstart : evalSym v (.mE, [.pair 0 0 c0, .pair 1 1 c1],
          .pair 1 1 cr0 :: .pair 2 0 cz0 :: rRest0) =
          eraECfg (ms.map (evalMidItem v)) (evalTower v tw) 0 := by
        dsimp only [evalSym, eraECfg]
        have hL : encSL v [.pair 0 0 c0, .pair 1 1 c1] = [1, 0, 1, 1] +> default := by
          simp [encSL, evalSymN_isZero hz0, evalSymN_isZero hz1, pWord_0_0, pWord_1_1, pow_one_list]
          rfl
        have hR : encSR v (.pair 1 1 cr0 :: .pair 2 0 cz0 :: rRest0) =
            wT +> (wZ +> encSR v cur) := by
          rw [encSR, evalSymN_isZero hzr0, pWord_1_1, pow_one_list, ← encSR_decPairR hd, pWord_2_0]
        rw [hL, hR, henc]; simp [pow_zero_list]
      have hend : evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero], out) =
          eraECfg (ms.map (evalMidItem v)) (evalTower v tw) (evalSymN v K) := by
        dsimp only [evalSym, eraECfg]
        have hL : encSL v [.pair 0 0 symZero, .pair 1 1 symZero] = [1, 0, 1, 1] +> default := by
          simp [encSL, evalSymN_zero, pWord_0_0, pWord_1_1, pow_one_list]; rfl
        rw [hL, encSR_pushRP ho4, encSR_pushRP ho3, encSR_pushWRMSem ho2,
          encSR_symRebuildMR v _ _ _ ho1, encSR_pushRP ho0, symBuildAdvTowerD01_spec v hb,
          evalSymN_one, evalSymN_scale, pWord_1_1, pWord_2_0, pow_one_list, pow_one_list]
      rw [hstart, hend]
      have hpos : 0 < evalSymN v K * (132 * w3Mid (ms.map (evalMidItem v)) + 865) +
          594 * evalSymN v K * (evalSymN v K - 1) +
          towerCostD01 (evalTower v tw) (6 * evalSymN v K) := by
        have : 1 * (132 * w3Mid (ms.map (evalMidItem v)) + 865) ≤
            evalSymN v K * (132 * w3Mid (ms.map (evalMidItem v)) + 865) :=
          Nat.mul_le_mul_right _ hK1
        omega
      exact ReachesIn.to_plus hpos
        (era_E_loop (ms.map (evalMidItem v)) (evalTower v tw) htw (evalSymN v K) hK6)
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz))] at h; cases h
  · cases h

def symTryEraL11D0Aux (remMidL : SymN) (ms : List SymMidItem) (tw : SymTowerD01) (K : SymN) :
    Option SymState :=
  match symPushWLMSem remMidL [.pair 1 1 symZero, .pair 1 0 symZero] with
  | none => none
  | some luRem =>
    match symPushLP 1 0 symOne luRem with
    | none => none
    | some L_out =>
      let k18 := symScale 18 K
      match symBuildAdvTowerD01 tw k18 with
      | none => none
      | some tw' =>
        match symPushRP 1 1 k18 tw' with
        | none => none
        | some out0 =>
          match symRebuildMR ms out0 with
          | none => none
          | some out1 =>
            match symPushRP 1 1 (symScale 36 K) out1 with
            | none => none
            | some out2 =>
              match symPush1011R out2 with
              | none => none
              | some R_out => some (.mA, L_out, R_out)

def symTryEraL11D0 (L : List SymLTok) (R : List SymRTok) : Option SymState :=
  match L with
  | [.pair 1 0 c0, .mid cm, .pair 1 1 c1, .pair 1 0 c2] =>
    if symIsZero c0 && symIsZero c1 && symIsZero c2 then
      let midL := symAddConst cm 1
      if 11 ≤ midL.k then
        match symPeel1011R R with
        | some rt0 =>
          match symScanMAndTowerD01 rt0 with
          | some (ms, .d0 B rt) =>
            match symDivMod midL 11 with
            | some (K, rem) =>
              if 1 ≤ K.k && symLe (symScale 18 K) B then
                symTryEraL11D0Aux (symConst rem) ms (.d0 B rt) K
              else
                match symDivMod B 18 with
                | some (K2, _) =>
                  if 1 ≤ K2.k then
                    match symSub midL (symScale 11 K2) with
                    | some remM => symTryEraL11D0Aux remM ms (.d0 B rt) K2
                    | none => none
                  else none
                | none => none
            | none =>
              match symDivMod B 18 with
              | some (K2, _) =>
                if 1 ≤ K2.k then
                  match symSub midL (symScale 11 K2) with
                  | some remM => symTryEraL11D0Aux remM ms (.d0 B rt) K2
                  | none => none
                else none
              | none => none
          | _ => none
        | none => none
      else none
    else none
  | _ => none

private theorem symTryEraL11D0Aux_sound (v : Fin 5 → ℕ)
    {cm remMidL B K : SymN} {ms : List SymMidItem} {rt R : List SymRTok} {s' : SymState}
    (hR : encSR v R = [1, 0, 1, 1] +>
      encMidR (ms.map (evalMidItem v)) (encR (buildAdvTowerD01 (.d0 (evalSymN v B) (rt.map
        (evalRTok v))) 0)))
    (hK : 1 ≤ evalSymN v K)
    (hmid : evalSymN v cm + 1 = evalSymN v remMidL + 11 * evalSymN v K)
    (hB : 18 * evalSymN v K ≤ evalSymN v B)
    (h : symTryEraL11D0Aux remMidL ms (.d0 B rt) K = some s') :
    ReachesPlus target_tm
      (cfgA ([0, 1] +> ((wLM ^ (evalSymN v cm + 1)) +> tailL0)) (encSR v R))
      (evalSym v s') := by
  unfold symTryEraL11D0Aux at h
  rcases h1 : symPushWLMSem remMidL [.pair 1 1 symZero, .pair 1 0 symZero] with _ | luRem
  · rw [h1] at h; cases h
  rw [h1] at h; try dsimp only at h
  rcases h2 : symPushLP 1 0 symOne luRem with _ | L_out; · rw [h2] at h; cases h
  rw [h2] at h; try dsimp only at h
  try dsimp only at h
  rcases h3 : symBuildAdvTowerD01 (.d0 B rt) (symScale 18 K) with _ | tw'; · rw [h3] at h; cases h
  rw [h3] at h; try dsimp only at h
  rcases h4 : symPushRP 1 1 (symScale 18 K) tw' with _ | out0; · rw [h4] at h; cases h
  rw [h4] at h; try dsimp only at h
  rcases h5 : symRebuildMR ms out0 with _ | out1; · rw [h5] at h; cases h
  rw [h5] at h; try dsimp only at h
  rcases h6 : symPushRP 1 1 (symScale 36 K) out1 with _ | out2; · rw [h6] at h; cases h
  rw [h6] at h; try dsimp only at h
  rcases h7 : symPush1011R out2 with _ | R_out; · rw [h7] at h; cases h
  rw [h7] at h; injection h with h; subst h
  have hstart : cfgA ([0, 1] +> ((wLM ^ (evalSymN v cm + 1)) +> tailL0)) (encSR v R) =
      eraL11Cfg (evalSymN v remMidL) (ms.map (evalMidItem v)) (evalSymN v B) (encSR v rt)
        (evalSymN v K) 0 := by
    dsimp only [eraL11Cfg]
    have hm0 : evalSymN v cm + 1 = evalSymN v remMidL + 11 * (evalSymN v K - 0) := by omega
    rw [hm0, hR]
    dsimp only [buildAdvTowerD01]
    simp only [encR_pushRP, encSR_eq_encR_map, pWord_1_2, pWord_1_1, pow_one_list,
      Nat.mul_zero, Nat.sub_zero, pow_zero_list]
    rfl
  have hend : evalSym v (.mA, L_out, R_out) =
      eraL11Cfg (evalSymN v remMidL) (ms.map (evalMidItem v)) (evalSymN v B) (encSR v rt)
        (evalSymN v K) (evalSymN v K) := by
    dsimp only [evalSym, eraL11Cfg]
    have htail : encSL v [.pair 1 1 symZero, .pair 1 0 symZero] = tailL0 := by
      simp [encSL, evalSymN_zero, pWord_1_1, pWord_1_0, pow_one_list, tailL0]
    rw [encSL_pushLP h2, encSL_pushWLMSem h1, htail, evalSymN_one, pWord_1_0, pow_one_list,
      encSR_push1011R h7, encSR_pushRP h6, encSR_symRebuildMR v _ _ _ h5, encSR_pushRP h4,
      symBuildAdvTowerD01_spec v h3]
    dsimp only [evalTower, buildAdvTowerD01]
    simp only [encR_pushRP, encSR_eq_encR_map, evalSymN_scale, pWord_1_1, pWord_1_2,
      pow_one_list, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  rw [hstart, hend]
  have hpos : 0 < evalSymN v K * (14440 + 396 * evalSymN v remMidL +
      396 * w3Mid (ms.map (evalMidItem v)) + 4356 * (evalSymN v K - 1)) +
      8514 * evalSymN v K * (evalSymN v K - 1) := by
    have : 1 * (14440 + 396 * evalSymN v remMidL +
        396 * w3Mid (ms.map (evalMidItem v)) + 4356 * (evalSymN v K - 1)) ≤
        evalSymN v K * (14440 + 396 * evalSymN v remMidL +
        396 * w3Mid (ms.map (evalMidItem v)) + 4356 * (evalSymN v K - 1)) :=
      Nat.mul_le_mul_right _ hK
    omega
  exact ReachesIn.to_plus hpos
    (era_L11_d0_loop (evalSymN v remMidL) (ms.map (evalMidItem v)) (evalSymN v B) (encSR v rt)
      (evalSymN v K) hB (evalSymN v K) (Nat.le_refl _))

private theorem symTryEraL11D0_sound (v : Fin 5 →
  ℕ) {L : List SymLTok} {R : List SymRTok} {s' : SymState}
    (h : symTryEraL11D0 L R = some s') :
    ReachesPlus target_tm (evalSym v (.mA, L, R)) (evalSym v s') := by
  unfold symTryEraL11D0 at h
  split at h
  · rename_i c0 cm c1 c2
    by_cases hz : (symIsZero c0 && symIsZero c1 && symIsZero c2) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz))] at h; try dsimp only at h
      simp only [Bool.and_eq_true] at hz
      rcases hz with ⟨⟨hz0, hz1⟩, hz2⟩
      try dsimp only at h
      split_ifs at h with h11
      rcases hp : symPeel1011R R with _ | rt0; · rw [hp] at h; cases h
      rw [hp] at h; try dsimp only at h
      rcases hs : symScanMAndTowerD01 rt0 with _ | ⟨ms, tw⟩; · rw [hs] at h; cases h
      rw [hs] at h; try dsimp only at h
      cases tw with
      | d1Empty _ _ _ => cases h
      | d1Mid _ _ _ _ _ => cases h
      | d0 B rt =>
        obtain ⟨_, henc⟩ := symScanMAndTowerD01_spec v rt0 hs
        have hR : encSR v R = [1, 0, 1, 1] +>
            encMidR (ms.map (evalMidItem v))
              (encR (buildAdvTowerD01 (.d0 (evalSymN v B) (rt.map (evalRTok v))) 0)) := by
          rw [symPeel1011R_spec hp, henc]; rfl
        have hL : evalSym v (.mA, [.pair 1 0 c0, .mid cm, .pair 1 1 c1, .pair 1 0 c2], R) =
            cfgA ([0, 1] +> ((wLM ^ (evalSymN v cm + 1)) +> tailL0)) (encSR v R) := by
          dsimp only [evalSym]
          congr 1
          simp [encSL, evalSymN_isZero hz0, evalSymN_isZero hz1, evalSymN_isZero hz2,
            pWord_1_0, pWord_1_1, pow_one_list, tailL0]
        rw [hL]
        rcases hdm1 : symDivMod (symAddConst cm 1) 11 with _ | ⟨K, rem⟩
        · rw [hdm1] at h; try dsimp only at h
          rcases hdm2 : symDivMod B 18 with _ | ⟨K2, r2⟩; · rw [hdm2] at h; cases h
          rw [hdm2] at h; try dsimp only at h
          split_ifs at h with hK2
          rcases hsub : symSub (symAddConst cm 1) (symScale 11 K2) with _ | remM
          · rw [hsub] at h; cases h
          rw [hsub] at h; try dsimp only at h
          obtain ⟨_, _, hdivB⟩ := evalSymN_divMod (v := v) hdm2
          obtain ⟨hleM, hrem⟩ := evalSymN_sub (v := v) hsub
          rw [evalSymN_addConst, evalSymN_scale] at hleM hrem
          exact symTryEraL11D0Aux_sound v hR (le_trans hK2 (evalSymN_ge_k v K2))
            (by omega) (by omega) h
        · rw [hdm1] at h; try dsimp only at h
          by_cases hc : (decide (1 ≤ K.k) && symLe (symScale 18 K) B) = true
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc))] at h; try dsimp only at h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            obtain ⟨_, _, hdivM⟩ := evalSymN_divMod (v := v) hdm1
            rw [evalSymN_addConst] at hdivM
            have hleB := evalSymN_le (v := v) hc.2; rw [evalSymN_scale] at hleB
            exact symTryEraL11D0Aux_sound v hR (le_trans hc.1 (evalSymN_ge_k v K))
              (by rw [evalSymN_const]; omega) hleB h
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc))] at h; try dsimp only at h
            rcases hdm2 : symDivMod B 18 with _ | ⟨K2, r2⟩; · rw [hdm2] at h; cases h
            rw [hdm2] at h; try dsimp only at h
            split_ifs at h with hK2
            rcases hsub : symSub (symAddConst cm 1) (symScale 11 K2) with _ | remM
            · rw [hsub] at h; cases h
            rw [hsub] at h; try dsimp only at h
            obtain ⟨_, _, hdivB⟩ := evalSymN_divMod (v := v) hdm2
            obtain ⟨hleM, hrem⟩ := evalSymN_sub (v := v) hsub
            rw [evalSymN_addConst, evalSymN_scale] at hleM hrem
            exact symTryEraL11D0Aux_sound v hR (le_trans hK2 (evalSymN_ge_k v K2))
              (by omega) (by omega) h
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz))] at h; cases h
  · cases h

/-! #### `symTryAR10101WZ` (`A_R` Sweep over `wZ^k`) -/

def symTryAR10101WZ (L : List SymLTok) (R : List SymRTok) : Option SymState :=
  match R with
  | .pair 0 0 c0 :: .pair 1 0 c1 :: .pair 1 1 c2 :: .pair 2 0 cz :: rRest =>
    if symIsZero c0 && symIsConst1 c1 && symIsZero c2 then
      match symPushLP 1 1 (symAddConst cz 1) L with
      | none => none
      | some L' => some (.mA, L',
        .pair 0 0 symZero :: .pair 1 0 symOne :: .pair 1 1 symZero :: rRest)
    else none
  | _ => none

private theorem symTryAR10101WZ_sound (v : Fin 5 → ℕ) {L : List SymLTok} {R : List SymRTok}
    {s' : SymState} (h : symTryAR10101WZ L R = some s') :
    ReachesPlus target_tm (evalSym v (.mA, L, R)) (evalSym v s') := by
  unfold symTryAR10101WZ at h
  split at h
  · rename_i c0 c1 c2 cz rRest
    by_cases hc : (symIsZero c0 && symIsConst1 c1 && symIsZero c2) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc))] at h; try dsimp only at h
      simp only [Bool.and_eq_true] at hc
      rcases hc with ⟨⟨h0, h1⟩, h2⟩
      rcases hp : symPushLP 1 1 (symAddConst cz 1) L with _ | L'; · rw [hp] at h; cases h
      rw [hp] at h; injection h with h; subst h
      dsimp only [evalSym]
      rw [encSL_pushLP hp, evalSymN_addConst, pWord_1_1]
      have hrIn : encSR v (.pair 0 0 c0 :: .pair 1 0 c1 :: .pair 1 1 c2 :: .pair 2 0 cz :: rRest) =
          [1, 0, 1, 0, 1, 0, 1, 1] +> ((wZ ^ (evalSymN v cz + 1)) +> encSR v rRest) := by
        simp [encSR, evalSymN_isZero h0, evalSymN_isConst1 h1, evalSymN_isZero h2,
          pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0, pow_succ_list, pow_zero_list]
        rfl
      have hrOut : encSR v (.pair 0 0 symZero :: .pair 1 0 symOne :: .pair 1 1 symZero :: rRest) =
          [1, 0, 1, 0, 1, 0, 1, 1] +> encSR v rRest := by
        simp [encSR, evalSymN_zero, evalSymN_one, pWord_0_0, pWord_1_0, pWord_1_1,
          pow_succ_list, pow_zero_list]
        rfl
      rw [hrIn, hrOut]
      exact ReachesIn.to_plus (by omega) (step_ar_10101_wZ_pow (evalSymN v cz + 1) (encSL v L)
        (encSR v rRest))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc))] at h; cases h
  · cases h

/-! #### Top-Level Symbolic Dispatcher (`symStep`) & Binary-Doubling Runner (`symRunBits`) -/

def symStep (s : SymState) : Option SymState :=
  match s with
  | (.mA, L, R) =>
    match symTryEraL11D0 L R with
    | some res => some res
    | none =>
      match symTryAR10101WZ L R with
      | some res => some res
      | none => symStepTrans (.mA, L, R)
  | (.mD, L, R) =>
    match symTryDL1WZ L R with
    | some res => some res
    | none => symStepTrans (.mD, L, R)
  | (.mE, L, R) =>
    match symTryEraED01 L R with
    | some res => some res
    | none =>
      match symTryEraConv L R with
      | some res => some res
      | none =>
        match symTryEL1101 L R with
        | some res => some res
        | none => symStepTrans (.mE, L, R)
  | (.mHalt, L, R) => symStepTrans (.mHalt, L, R)

private theorem symStep_sound (v : Fin 5 → ℕ) {s s' : SymState}
    (h : symStep s = some s') :
    ReachesPlus target_tm (evalSym v s) (evalSym v s') := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | mHalt => exact symStepTrans_sound v h
  | mD =>
    dsimp only [symStep] at h
    rcases r1 : symTryDL1WZ L R with _ | res1
    · rw [r1] at h; exact symStepTrans_sound v h
    · rw [r1] at h; injection h with h; subst h; exact symTryDL1WZ_sound v r1
  | mA =>
    dsimp only [symStep] at h
    rcases r1 : symTryEraL11D0 L R with _ | res1
    · rw [r1] at h; try dsimp only at h
      rcases r2 : symTryAR10101WZ L R with _ | res2
      · rw [r2] at h; exact symStepTrans_sound v h
      · rw [r2] at h; injection h with h; subst h; exact symTryAR10101WZ_sound v r2
    · rw [r1] at h; injection h with h; subst h; exact symTryEraL11D0_sound v r1
  | mE =>
    dsimp only [symStep] at h
    rcases r1 : symTryEraED01 L R with _ | res1
    · rw [r1] at h; try dsimp only at h
      rcases r2 : symTryEraConv L R with _ | res2
      · rw [r2] at h; try dsimp only at h
        rcases r3 : symTryEL1101 L R with _ | res3
        · rw [r3] at h; exact symStepTrans_sound v h
        · rw [r3] at h; injection h with h; subst h; exact symTryEL1101_sound v r3
      · rw [r2] at h; injection h with h; subst h; exact symTryEraConv_sound v r2
    · rw [r1] at h; injection h with h; subst h; exact symTryEraED01_sound v r1

def symIterPow2 : ℕ → SymState → Option SymState
  | 0, s => symStep s
  | k + 1, s =>
    match symIterPow2 k s with
    | none => none
    | some s1 => symIterPow2 k s1

private theorem symIterPow2_sound (v : Fin 5 → ℕ) :
    ∀ (k : ℕ) {s s' : SymState},
    symIterPow2 k s = some s' →
      ReachesPlus target_tm (evalSym v s) (evalSym v s')
  | 0, _, _, h => symStep_sound v h
  | k + 1, s, s', h => by
    dsimp only [symIterPow2] at h
    rcases h1 : symIterPow2 k s with _ | s1
    · rw [h1] at h; cases h
    · rw [h1] at h; try dsimp only at h
      exact (symIterPow2_sound v k h1).trans (symIterPow2_sound v k h)

def symRunBits : List ℕ → SymState → Option SymState
  | [], s => some s
  | k :: ks, s =>
    match symIterPow2 k s with
    | none => none
    | some s1 => symRunBits ks s1

private theorem symRunBits_sound_star (v : Fin 5 → ℕ) :
    ∀ (ks : List ℕ) {s s' : SymState},
    symRunBits ks s = some s' →
      ReachesStar target_tm (evalSym v s) (evalSym v s')
  | [], _, _, h => by injection h with h; subst h; exact ReachesStar.refl _ _
  | k :: ks, s, s', h => by
    dsimp only [symRunBits] at h
    rcases h1 : symIterPow2 k s with _ | s1
    · rw [h1] at h; cases h
    · rw [h1] at h; try dsimp only at h
      exact (symIterPow2_sound v k h1).to_star.trans (symRunBits_sound_star v ks h)

theorem symRunBits_sound_plus (v : Fin 5 → ℕ) {k : ℕ} {ks : List ℕ}
    {s s' : SymState} (h : symRunBits (k :: ks) s = some s') :
    ReachesPlus target_tm (evalSym v s) (evalSym v s') := by
  dsimp only [symRunBits] at h
  rcases h1 : symIterPow2 k s with _ | s1
  · rw [h1] at h; cases h
  · rw [h1] at h; try dsimp only at h
    exact (symIterPow2_sound v k h1).trans_star (symRunBits_sound_star v ks h)

/-! ### Part 3: Canonical Configurations, Parametric Invariants, & Closure -/

def v5 (a b c d e : ℕ) : Fin 5 → ℕ
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e

def symTail : Fin 6 → List SymLTok
  | 0 => [.pair 1 1 symZero, .pair 1 0 symZero]
  | 1 => [.pair 1 1 symZero, .pair 2 0 symZero]
  | 2 => [.pair 1 1 symZero, .pair 1 0 symZero, .pair 2 0 symZero, .pair 1 0 symZero]
  | 3 => [.pair 1 1 symZero, .pair 2 0 symZero, .pair 3 0 symZero, .pair 1 0 symZero]
  | 4 => [.pair 1 1 symZero, .pair 1 0 (symConst 2), .pair 2 0 symZero, .pair 1 0 symZero]
  | 5 => [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 0 symOne]

def encTail (i : Fin 6) : ListBlank (Fin 2) := encSL (v5 0 0 0 0 0) (symTail i)

private theorem encSL_symTail (v : Fin 5 → ℕ) : ∀ (i : Fin 6), encSL v (symTail i) = encTail i
  | 0 => by simp [symTail, encTail, encSL, evalSymN, symZero]
  | 1 => by simp [symTail, encTail, encSL, evalSymN, symZero]
  | 2 => by simp [symTail, encTail, encSL, evalSymN, symZero]
  | 3 => by simp [symTail, encTail, encSL, evalSymN, symZero]
  | 4 => by simp [symTail, encTail, encSL, evalSymN, symZero, symConst]
  | 5 => by simp [symTail, encTail, encSL, evalSymN, symZero, symOne]

private theorem wRM_eq_wT2_wZ (s : ListBlank (Fin 2)) :
    wRM +> s = (wT ^ 2) +> (wZ +> s) := rfl

private theorem wT_pow_wRM_eq (a : ℕ) (s : ListBlank (Fin 2)) :
    (wT ^ a) +> (wRM +> s) = (wT ^ (a + 2)) +> (wZ +> s) := by
  rw [wRM_eq_wT2_wZ, pow_append_pow]

private theorem wZ_add_pow (a b : ℕ) (s : ListBlank (Fin 2)) :
    (wZ ^ a) +> ((wZ ^ b) +> s) = (wZ ^ (a + b)) +> s :=
  pow_append_pow wZ a b s

private theorem wZ_cons_pow (a : ℕ) (s : ListBlank (Fin 2)) :
    wZ +> ((wZ ^ a) +> s) = (wZ ^ (a + 1)) +> s := by
  rw [Nat.add_comm a 1, ← pow_append_pow, pow_one_list]

private theorem wT_cons_pow (a : ℕ) (s : ListBlank (Fin 2)) :
    wT +> ((wT ^ a) +> s) = (wT ^ (a + 1)) +> s := by
  rw [Nat.add_comm a 1, ← pow_append_pow, pow_one_list]

private theorem nil_append_lb (s : ListBlank (Fin 2)) :
    ([] : List (Fin 2)) +> s = s := rfl

private theorem list_1011_eq (s : ListBlank (Fin 2)) :
    [1, 0, 1, 1] +> s = [1] +> (wT +> s) := rfl

private theorem fin6_ind {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i : Fin 6, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4
  | ⟨5, _⟩ => h5
  | ⟨_ + 6, h⟩ => absurd h (by omega)

theorem reachesPlus_eq_both {a a' b b' : Cfg (Fin 2) (Fin 6)}
    (h : ReachesPlus target_tm a b) (ha : a = a') (hb : b = b') :
    ReachesPlus target_tm a' b' := ha ▸ hb ▸ h

/-! #### Canonical Configurations -/

def mCfg (m z c k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgA ([0, 1] +> ((wLM ^ m) +> tailL0))
    ([1] +> ((wT ^ (6 * k + 7)) +> ((wZ ^ z) +> ((wT ^ (3 * k + 1)) +>
      ([0, 1, 1, 1] +> ((wT ^ c) +> ([0, 1] +> default)))))))

def postL11Cfg (r u z c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgA ([0, 1] +> ((wLM ^ r) +> tailL0))
    ([1] +> ((wT ^ (6 * u + 115)) +> ((wZ ^ z) +> ((wT ^ (3 * u + 55)) +>
      ([0, 1, 1, 1] +> ((wT ^ c) +> ([0, 1] +> default)))))))

def convMLoopCfg (i : Fin 6) (A M Z C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1] +> (wT +> ((wZ ^ (A + 1)) +> ((wLM ^ M) +> encTail i))))
    (wT +> ((wZ ^ Z) +> ((wT ^ C) +> ([0, 1] +> default))))

def convSimpleCfg (i : Fin 6) (A M R0 : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1] +> ((wZ ^ A) +> ((wLM ^ M) +> encTail i)))
    ((wT ^ R0) +> ([0, 1] +> default))

def convEntryCfg (i : Fin 6) (B z A M R0 : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1] +> ((wZ ^ B) +> ((wT ^ (z - 1)) +> (wLM +> ((wZ ^ A) +> ((wLM ^ M) +> encTail i))))))
    ((wT ^ R0) +> ([0, 1] +> default))

def eMidExtra0Cfg (M A d C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wRM ^ M) +> ((wT ^ A) +> (wRM +> (wZ +> ((wT ^ d) +>
      ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default))))))))))

def eMidExtra12Cfg (M A z Bm d C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wRM ^ M) +> ((wT ^ A) +> (wRM +> ((wZ ^ (z - 1)) +>
      ((wT ^ Bm) +> (wRM +> (wZ +> ((wT ^ d) +>
        ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default)))))))))))))

def eMid0Cfg (M A B C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wRM ^ M) +> ((wT ^ A) +> ((([0, 1] : List (Fin 2)) ^ 2) +> ((wT ^ B) +>
      ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default)))))))))

def eMid12Cfg (M A z B C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wRM ^ M) +> ((wT ^ A) +> (wRM +> ((wZ ^ (z - 1)) +>
      ((wT ^ 2) +> ((([0, 1] : List (Fin 2)) ^ 2) +> ((wT ^ B) +>
        ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default))))))))))))

def eCleanCfg (A z B C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wT ^ A) +> (wRM +> ((wZ ^ (z - 1)) +> ((wT ^ B) +>
      ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default)))))))))

def e0111Cfg (A z B C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wT ^ 8) +> ([0, 1, 1, 1] +> ((wT ^ A) +> ((wZ ^ z) +>
      ((wT ^ B) +> ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default))))))))))

def e0101Cfg (A z B C : ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfgE ([1, 0, 1, 1] +> default)
    (wT +> (wZ +> ((wT ^ 9) +> ((([0,
      1] : List (Fin 2)) ^ 2) +> ((wT ^ A) +> (wRM +> ((wZ ^ (z - 1)) +>
      ((wT ^ B) +> ([0, 1, 1, 1] +> ((wT ^ C) +> ([0, 1] +> default)))))))))))

/-! #### Fast Symbolic-to-Canonical Evaluation Bridge Lemmas -/

private theorem add_one_0 : (0 : ℕ) + 1 = 1 := rfl
private theorem add_one_1 : (1 : ℕ) + 1 = 2 := rfl
private theorem add_one_7 : (7 : ℕ) + 1 = 8 := rfl
private theorem add_one_8 : (8 : ℕ) + 1 = 9 := rfl

theorem eval_mCfg_z1 (v : Fin 5 → ℕ) (cm ca cb cc : SymN) (m c k : ℕ)
    (hm : evalSymN v cm + 1 = m) (ha : evalSymN v ca + 3 = 6 * k + 7)
    (hb : evalSymN v cb + 1 = 3 * k + 1) (hc : evalSymN v cc + 1 = c) :
    evalSym v (.mA, [.pair 1 0 symZero, .mid cm, .pair 1 1 symZero, .pair 1 0 symZero],
      [.pair 0 0 symZero, .pair 1 1 ca, .mid symZero, .pair 1 1 cb,
       .pair 1 2 symZero, .pair 1 1 cc, .pair 1 0 symZero]) = mCfg m 1 c k := by
  dsimp only [evalSym, encSL, encSR, mCfg, tailL0]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list,
    hm, hb, hc]
  rw [wT_pow_wRM_eq]
  have ha' : evalSymN v ca + 1 + 2 = 6 * k + 7 := by omega
  rw [ha']

private theorem eval_mCfg_z2 (v : Fin 5 → ℕ) (cm ca cz cb cc : SymN) (m z c k : ℕ)
    (hm : evalSymN v cm + 1 = m) (ha : evalSymN v ca + 1 = 6 * k + 7)
    (hz : evalSymN v cz + 1 = z) (hb : evalSymN v cb + 1 = 3 * k + 1)
    (hc : evalSymN v cc + 1 = c) :
    evalSym v (.mA, [.pair 1 0 symZero, .mid cm, .pair 1 1 symZero, .pair 1 0 symZero],
      [.pair 0 0 symZero, .pair 1 1 ca, .pair 2 0 cz, .pair 1 1 cb,
       .pair 1 2 symZero, .pair 1 1 cc, .pair 1 0 symZero]) = mCfg m z c k := by
  dsimp only [evalSym, encSL, encSR, mCfg, tailL0]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, hm, ha, hz, hb, hc]

private theorem eval_postL11_r0_z1 (v : Fin 5 → ℕ) (ca cb cc : SymN) (u c : ℕ)
    (ha : evalSymN v ca + 3 = 6 * u + 115) (hb : evalSymN v cb + 1 = 3 * u + 55)
    (hc : evalSymN v cc + 1 = c) :
    evalSym v (.mA, [.pair 1 0 symZero, .pair 1 1 symZero, .pair 1 0 symZero],
      [.pair 0 0 symZero, .pair 1 1 ca, .mid symZero, .pair 1 1 cb,
       .pair 1 2 symZero, .pair 1 1 cc, .pair 1 0 symZero]) = postL11Cfg 0 u 1 c := by
  dsimp only [evalSym, encSL, encSR, postL11Cfg, tailL0]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list,
    pow_zero_list,
    nil_append_lb, hb, hc]
  rw [wT_pow_wRM_eq]
  have ha' : evalSymN v ca + 1 + 2 = 6 * u + 115 := by omega
  rw [ha']

private theorem eval_postL11_r0_z2 (v : Fin 5 → ℕ) (ca cz cb cc : SymN) (u z c : ℕ)
    (ha : evalSymN v ca + 1 = 6 * u + 115) (hz : evalSymN v cz + 1 = z)
    (hb : evalSymN v cb + 1 = 3 * u + 55) (hc : evalSymN v cc + 1 = c) :
    evalSym v (.mA, [.pair 1 0 symZero, .pair 1 1 symZero, .pair 1 0 symZero],
      [.pair 0 0 symZero, .pair 1 1 ca, .pair 2 0 cz, .pair 1 1 cb,
       .pair 1 2 symZero, .pair 1 1 cc, .pair 1 0 symZero]) = postL11Cfg 0 u z c := by
  dsimp only [evalSym, encSL, encSR, postL11Cfg, tailL0]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, nil_append_lb, ha, hz, hb, hc]

private theorem eval_postL11_r1_z1 (v : Fin 5 → ℕ) (cr ca cb cc : SymN) (r u c : ℕ)
    (hr : evalSymN v cr + 1 = r) (ha : evalSymN v ca + 3 = 6 * u + 115)
    (hb : evalSymN v cb + 1 = 3 * u + 55) (hc : evalSymN v cc + 1 = c) :
    evalSym v (.mA, [.pair 1 0 symZero, .mid cr, .pair 1 1 symZero, .pair 1 0 symZero],
      [.pair 0 0 symZero, .pair 1 1 ca, .mid symZero, .pair 1 1 cb,
       .pair 1 2 symZero, .pair 1 1 cc, .pair 1 0 symZero]) = postL11Cfg r u 1 c := by
  dsimp only [evalSym, encSL, encSR, postL11Cfg, tailL0]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pow_one_list,
    hr, hb, hc]
  rw [wT_pow_wRM_eq]
  have ha' : evalSymN v ca + 1 + 2 = 6 * u + 115 := by omega
  rw [ha']

private theorem eval_postL11_r1_z2 (v : Fin 5 → ℕ) (cr ca cz cb cc : SymN) (r u z c : ℕ)
    (hr : evalSymN v cr + 1 = r) (ha : evalSymN v ca + 1 = 6 * u + 115)
    (hz : evalSymN v cz + 1 = z) (hb : evalSymN v cb + 1 = 3 * u + 55)
    (hc : evalSymN v cc + 1 = c) :
    evalSym v (.mA, [.pair 1 0 symZero, .mid cr, .pair 1 1 symZero, .pair 1 0 symZero],
      [.pair 0 0 symZero, .pair 1 1 ca, .pair 2 0 cz, .pair 1 1 cb,
       .pair 1 2 symZero, .pair 1 1 cc, .pair 1 0 symZero]) = postL11Cfg r u z c := by
  dsimp only [evalSym, encSL, encSR, postL11Cfg, tailL0]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, hr, ha, hz, hb, hc]

private theorem eval_convMLoop (v : Fin 5 → ℕ) (i : Fin 6) (cA cM cZ cC : SymN) (A M Z C : ℕ)
    (hA : evalSymN v cA + 1 = A) (hM : evalSymN v cM + 1 = M)
    (hZ : evalSymN v cZ + 1 = Z) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE,
      [.pair 0 0 symZero, .pair 1 1 symZero, .pair 2 0 symZero, .pair 2 0 cA, .mid cM] ++ symTail i,
      [.pair 1 1 symZero, .pair 2 0 cZ, .pair 1 1 cC, .pair 1 0 symZero]) =
      convMLoopCfg i A M Z C := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convMLoopCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0, pow_one_list,
    hA, hM, hZ, hC]
  rw [wZ_cons_pow]

private theorem eval_convSimple_1 (v : Fin 5 → ℕ) (i : Fin 6) (cA cM cR : SymN) (A M R0 : ℕ)
    (hA : evalSymN v cA + 1 = A) (hM : evalSymN v cM + 1 = M) (hR : evalSymN v cR + 1 = R0) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 2 0 cA, .mid cM] ++ symTail i,
      [.pair 1 1 cR, .pair 1 0 symZero]) = convSimpleCfg i A M R0 := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convSimpleCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0, pow_one_list,
    hA, hM, hR]

private theorem eval_convSimple_2 (v : Fin 5 → ℕ) (i : Fin 6) (cA1 cA2 cM cR : SymN) (A M R0 : ℕ)
    (hA : evalSymN v cA1 + 1 + (evalSymN v cA2 + 1) = A)
    (hM : evalSymN v cM + 1 = M) (hR : evalSymN v cR + 1 = R0) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 2 0 cA1, .pair 2 0 cA2, .mid cM] ++ symTail i,
      [.pair 1 1 cR, .pair 1 0 symZero]) = convSimpleCfg i A M R0 := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convSimpleCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0, pow_one_list,
    hM, hR]
  rw [wZ_add_pow, hA]

private theorem eval_convEntry_1_z1 (v : Fin 5 → ℕ) (i : Fin 6) (cB cA cM cR : SymN) (B A M R0 : ℕ)
    (hB : evalSymN v cB + 1 = B) (hA : evalSymN v cA + 1 = A)
    (hM : evalSymN v cM + 1 = M) (hR : evalSymN v cR + 1 = R0) :
    evalSym v (.mE,
      [.pair 0 0 symZero, .pair 2 0 cB, .mid symZero, .pair 2 0 cA, .mid cM] ++ symTail i,
      [.pair 1 1 cR, .pair 1 0 symZero]) = convEntryCfg i B 1 A M R0 := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convEntryCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0,
    pow_one_list, pow_zero_list, Nat.sub_self, nil_append_lb, hB, hA, hM, hR]

private theorem eval_convEntry_1_z2 (v : Fin 5 → ℕ) (i : Fin 6) (cB cz cA cM cR : SymN)
    (B z A M R0 : ℕ)
    (hB : evalSymN v cB + 1 = B) (hz : evalSymN v cz + 1 = z - 1)
    (hA : evalSymN v cA + 1 = A) (hM : evalSymN v cM + 1 = M) (hR : evalSymN v cR + 1 = R0) :
    evalSym v (.mE,
      [.pair 0 0 symZero, .pair 2 0 cB, .pair 1 1 cz, .mid symZero, .pair 2 0 cA,
        .mid cM] ++ symTail i,
      [.pair 1 1 cR, .pair 1 0 symZero]) = convEntryCfg i B z A M R0 := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convEntryCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0, pow_one_list,
    hB, hz, hA, hM, hR]

private theorem eval_convEntry_2_z1 (v : Fin 5 → ℕ) (i : Fin 6) (cB1 cB2 cA cM cR : SymN)
    (B A M R0 : ℕ)
    (hB : evalSymN v cB1 + 1 + (evalSymN v cB2 + 1) = B)
    (hA : evalSymN v cA + 1 = A) (hM : evalSymN v cM + 1 = M) (hR : evalSymN v cR + 1 = R0) :
    evalSym v (.mE,
      [.pair 0 0 symZero, .pair 2 0 cB1, .pair 2 0 cB2, .mid symZero, .pair 2 0 cA,
        .mid cM] ++ symTail i,
      [.pair 1 1 cR, .pair 1 0 symZero]) = convEntryCfg i B 1 A M R0 := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convEntryCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0,
    pow_one_list, pow_zero_list, Nat.sub_self, nil_append_lb, hA, hM, hR]
  rw [wZ_add_pow, hB]

private theorem eval_convEntry_2_z2 (v : Fin 5 → ℕ) (i : Fin 6) (cB1 cB2 cz cA cM cR : SymN)
    (B z A M R0 : ℕ)
    (hB : evalSymN v cB1 + 1 + (evalSymN v cB2 + 1) = B) (hz : evalSymN v cz + 1 = z - 1)
    (hA : evalSymN v cA + 1 = A) (hM : evalSymN v cM + 1 = M) (hR : evalSymN v cR + 1 = R0) :
    evalSym v (.mE,
      [.pair 0 0 symZero, .pair 2 0 cB1, .pair 2 0 cB2, .pair 1 1 cz, .mid symZero, .pair 2 0 cA,
        .mid cM] ++ symTail i,
      [.pair 1 1 cR, .pair 1 0 symZero]) = convEntryCfg i B z A M R0 := by
  dsimp only [List.cons_append, List.nil_append, evalSym, encSL, encSR, convEntryCfg]
  rw [encSL_symTail]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0, pow_one_list,
    hz, hA, hM, hR]
  rw [wZ_add_pow, hB]

private theorem eval_eMidExtra0_c0 (v : Fin 5 → ℕ) (cM cA cd : SymN) (M A d : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A) (hd : evalSymN v cd + 1 = d) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero,
       .pair 2 0 symZero, .pair 1 1 cd, .pair 1 2 symZero, .pair 1 0 symZero]) =
      eMidExtra0Cfg M A d 0 := by
  dsimp only [evalSym, encSL, encSR, eMidExtra0Cfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, nil_append_lb, list_1011_eq, hM, hA, hd]

private theorem eval_eMidExtra0_c1 (v : Fin 5 → ℕ) (cM cA cd cC : SymN) (M A d C : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A)
    (hd : evalSymN v cd + 1 = d) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero,
       .pair 2 0 symZero, .pair 1 1 cd, .pair 1 2 symZero, .pair 1 1 cC, .pair 1 0 symZero]) =
      eMidExtra0Cfg M A d C := by
  dsimp only [evalSym, encSL, encSR, eMidExtra0Cfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hM, hA, hd, hC]

private theorem eval_eMidExtra12_z1_c0 (v : Fin 5 → ℕ) (cM cA cBm cd : SymN) (M A Bm d : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A)
    (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero,
       .pair 1 1 cBm, .mid symZero, .pair 2 0 symZero, .pair 1 1 cd, .pair 1 2 symZero,
       .pair 1 0 symZero]) = eMidExtra12Cfg M A 1 Bm d 0 := by
  dsimp only [evalSym, encSL, encSR, eMidExtra12Cfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, Nat.sub_self, nil_append_lb, list_1011_eq, hM, hA, hBm, hd]

private theorem eval_eMidExtra12_z1_c1 (v : Fin 5 → ℕ) (cM cA cBm cd cC : SymN) (M A Bm d C : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A)
    (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero,
       .pair 1 1 cBm, .mid symZero, .pair 2 0 symZero, .pair 1 1 cd, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = eMidExtra12Cfg M A 1 Bm d C := by
  dsimp only [evalSym, encSL, encSR, eMidExtra12Cfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, Nat.sub_self, nil_append_lb, list_1011_eq, hM, hA, hBm, hd, hC]

private theorem eval_eMidExtra12_z2_c0 (v : Fin 5 → ℕ) (cM cA cz cBm cd : SymN) (M A z Bm d : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A) (hz : evalSymN v cz + 1 = z - 1)
    (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero, .pair 2 0 cz,
       .pair 1 1 cBm, .mid symZero, .pair 2 0 symZero, .pair 1 1 cd, .pair 1 2 symZero,
       .pair 1 0 symZero]) = eMidExtra12Cfg M A z Bm d 0 := by
  dsimp only [evalSym, encSL, encSR, eMidExtra12Cfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, nil_append_lb, list_1011_eq, hM, hA, hz, hBm, hd]

private theorem eval_eMidExtra12_z2_c1 (v : Fin 5 → ℕ) (cM cA cz cBm cd cC : SymN)
    (M A z Bm d C : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A) (hz : evalSymN v cz + 1 = z - 1)
    (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero, .pair 2 0 cz,
       .pair 1 1 cBm, .mid symZero, .pair 2 0 symZero, .pair 1 1 cd, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = eMidExtra12Cfg M A z Bm d C := by
  dsimp only [evalSym, encSL, encSR, eMidExtra12Cfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hM, hA, hz, hBm, hd, hC]

private theorem eval_eMid0 (v : Fin 5 → ℕ) (cM cA cB cC : SymN) (M A B C : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A)
    (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .pair 1 0 symOne,
       .pair 1 1 cB, .pair 1 2 symZero, .pair 1 1 cC, .pair 1 0 symZero]) =
      eMid0Cfg M A B C := by
  dsimp only [evalSym, encSL, encSR, eMid0Cfg]
  simp only [evalSymN_zero, evalSymN_one, add_one_0, add_one_1, pWord_0_0, pWord_1_0, pWord_1_1,
    pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hM, hA, hB, hC]

private theorem eval_eMid12_z1 (v : Fin 5 → ℕ) (cM cA cB cC : SymN) (M A B C : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A)
    (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero,
       .pair 1 1 symOne, .pair 1 0 symOne, .pair 1 1 cB, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = eMid12Cfg M A 1 B C := by
  dsimp only [evalSym, encSL, encSR, eMid12Cfg]
  simp only [evalSymN_zero, evalSymN_one, add_one_0, add_one_1, pWord_0_0, pWord_1_0, pWord_1_1,
    pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, Nat.sub_self, nil_append_lb, list_1011_eq, hM, hA, hB, hC]

private theorem eval_eMid12_z2 (v : Fin 5 → ℕ) (cM cA cz cB cC : SymN) (M A z B C : ℕ)
    (hM : evalSymN v cM + 1 = M) (hA : evalSymN v cA + 1 = A) (hz : evalSymN v cz + 1 = z - 1)
    (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .mid cM, .pair 1 1 cA, .mid symZero, .pair 2 0 cz,
       .pair 1 1 symOne, .pair 1 0 symOne, .pair 1 1 cB, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = eMid12Cfg M A z B C := by
  dsimp only [evalSym, encSL, encSR, eMid12Cfg]
  simp only [evalSymN_zero, evalSymN_one, add_one_0, add_one_1, pWord_0_0, pWord_1_0, pWord_1_1,
    pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hM, hA, hz, hB, hC]

private theorem eval_eClean_z1 (v : Fin 5 → ℕ) (cA cB cC : SymN) (A B C : ℕ)
    (hA : evalSymN v cA + 1 = A) (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 1 cA, .mid symZero,
       .pair 1 1 cB, .pair 1 2 symZero, .pair 1 1 cC, .pair 1 0 symZero]) =
      eCleanCfg A 1 B C := by
  dsimp only [evalSym, encSL, encSR, eCleanCfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, pow_zero_list, Nat.sub_self, nil_append_lb, list_1011_eq, hA, hB, hC]

private theorem eval_eClean_z2 (v : Fin 5 → ℕ) (cA cz cB cC : SymN) (A z B C : ℕ)
    (hA : evalSymN v cA + 1 = A) (hz : evalSymN v cz + 1 = z - 1)
    (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 1 cA, .mid symZero, .pair 2 0 cz,
       .pair 1 1 cB, .pair 1 2 symZero, .pair 1 1 cC, .pair 1 0 symZero]) =
      eCleanCfg A z B C := by
  dsimp only [evalSym, encSL, encSR, eCleanCfg]
  simp only [evalSymN_zero, add_one_0, pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hA, hz, hB, hC]

private theorem eval_e0111_z1 (v : Fin 5 → ℕ) (cA cB cC : SymN) (A B C : ℕ)
    (hA : evalSymN v cA + 3 = A) (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 1 (symConst 7), .pair 1 2 symZero,
       .pair 1 1 cA, .mid symZero, .pair 1 1 cB, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = e0111Cfg A 1 B C := by
  dsimp only [evalSym, encSL, encSR, e0111Cfg]
  simp only [evalSymN_zero, evalSymN_const, add_one_0, add_one_7, pWord_0_0, pWord_1_0, pWord_1_1,
    pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hB, hC]
  rw [wT_pow_wRM_eq]
  have hA' : evalSymN v cA + 1 + 2 = A := by omega
  rw [hA']

private theorem eval_e0111_z2 (v : Fin 5 → ℕ) (cA cz cB cC : SymN) (A z B C : ℕ)
    (hA : evalSymN v cA + 1 = A) (hz : evalSymN v cz + 1 = z)
    (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 1 (symConst 7), .pair 1 2 symZero,
       .pair 1 1 cA, .pair 2 0 cz, .pair 1 1 cB, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = e0111Cfg A z B C := by
  dsimp only [evalSym, encSL, encSR, e0111Cfg]
  simp only [evalSymN_zero, evalSymN_const, add_one_0, add_one_7, pWord_0_0, pWord_1_0, pWord_1_1,
    pWord_1_2, pWord_2_0,
    pow_one_list, list_1011_eq, hA, hz, hB, hC]

private theorem eval_e0101_z1 (v : Fin 5 → ℕ) (cA cB cC : SymN) (A B C : ℕ)
    (hA : evalSymN v cA + 1 = A) (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 1 (symConst 8), .pair 1 0 symOne,
       .pair 1 1 cA, .mid symZero, .pair 1 1 cB, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = e0101Cfg A 1 B C := by
  dsimp only [evalSym, encSL, encSR, e0101Cfg]
  simp only [evalSymN_zero, evalSymN_one, evalSymN_const, add_one_0, add_one_1, add_one_8,
    pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0, pow_one_list, pow_zero_list,
    Nat.sub_self, nil_append_lb, list_1011_eq, hA, hB, hC]

private theorem eval_e0101_z2 (v : Fin 5 → ℕ) (cA cz cB cC : SymN) (A z B C : ℕ)
    (hA : evalSymN v cA + 1 = A) (hz : evalSymN v cz + 1 = z - 1)
    (hB : evalSymN v cB + 1 = B) (hC : evalSymN v cC + 1 = C) :
    evalSym v (.mE, [.pair 0 0 symZero, .pair 1 1 symZero],
      [.pair 1 1 symZero, .pair 2 0 symZero, .pair 1 1 (symConst 8), .pair 1 0 symOne,
       .pair 1 1 cA, .mid symZero, .pair 2 0 cz, .pair 1 1 cB, .pair 1 2 symZero,
       .pair 1 1 cC, .pair 1 0 symZero]) = e0101Cfg A z B C := by
  dsimp only [evalSym, encSL, encSR, e0101Cfg]
  simp only [evalSymN_zero, evalSymN_one, evalSymN_const, add_one_0, add_one_1, add_one_8,
    pWord_0_0, pWord_1_0, pWord_1_1, pWord_1_2, pWord_2_0, pow_one_list, list_1011_eq, hA, hz, hB,
      hC]

/-! #### Parametric Invariants -/

def InvM (m z c k : ℕ) : Prop :=
  k ≤ 5 ∧ 1 ≤ z ∧ 33 ≤ m ∧ 9 * m ≤ c ∧ 2100 ≤ c

def InvConvMLoop (i : Fin 6) (A M Z C : ℕ) : Prop :=
  50 ≤ A ∧ 46 ≤ M ∧ 1 ≤ Z ∧ 9 * M + (if i = 4 then 4 else 0) ≤ C ∧ 2120 ≤ C

def InvConvSimple (_i : Fin 6) (A M R0 : ℕ) : Prop :=
  50 ≤ A ∧ 46 ≤ M ∧ 4 ≤ R0 ∧ 9 * M ≤ R0 + 2 * A ∧ 2120 ≤ R0 + 2 * A

def InvConvEntryZ2 (_i : Fin 6) (B A M R0 : ℕ) : Prop :=
  50 ≤ A ∧ 20 ≤ B ∧ 46 ≤ M ∧ 4 ≤ R0 ∧ 9 * M ≤ R0 + 2 * B + A ∧ 2120 ≤ R0 + 2 * B + A

def InvConvEntry (_i : Fin 6) (B z A M R0 : ℕ) : Prop :=
  50 ≤ A ∧ 20 ≤ B ∧ 1 ≤ z ∧ 46 ≤ M ∧ 4 ≤ R0 ∧ 9 * M + 6 ≤ R0 + 2 * B ∧ 2120 ≤ R0 + 2 * B

def InvEmidExtraPost0 (M A Bd rC2 : ℕ) : Prop :=
  rC2 < 6 ∧ 50 ≤ A ∧ 46 ≤ M ∧ 20 ≤ Bd ∧ 9 * M ≤ 2 * Bd + A ∧ 2120 ≤ 2 * Bd + A

def InvEmidExtraPost12 (M A z Bm Bd rC2 : ℕ) : Prop :=
  rC2 < 6 ∧ 1 ≤ z ∧ 50 ≤ A ∧ 46 ≤ M ∧ 20 ≤ Bm ∧ 20 ≤ Bd ∧ (Bd + rC2) % 2 = 1 ∧
    9 * M ≤ 2 * Bd + 2 * Bm ∧ 2120 ≤ 2 * Bd + 2 * Bm

def InvEmidExtra0 (M A d C : ℕ) : Prop :=
  1 ≤ d ∧ 50 ≤ A ∧ 120 ≤ C ∧ 282 ≤ 6 * M + C ∧ 18 * M + 1 ≤ C + 2 * A ∧ 2128 ≤ 2 * C + A

def InvEmidExtra12 (M A z Bm d C : ℕ) : Prop :=
  1 ≤ d ∧ 1 ≤ z ∧ 50 ≤ A ∧ 20 ≤ Bm ∧ 120 ≤ C ∧ 282 ≤ 6 * M + C ∧
    18 * M + 1 ≤ C + 4 * Bm ∧ 2128 ≤ 2 * C + 2 * Bm ∧ (d + C) % 2 = 1

def InvEmid0 (M A B C : ℕ) : Prop :=
  50 ≤ A ∧ 19 ≤ M ∧ 50 ≤ B ∧ 60 ≤ C ∧ 560 ≤ 12 * M + C ∧
    36 * M + 80 ≤ C + 4 * B + 4 * A ∧ 2120 ≤ 2 * C + 2 * B + A

def InvEmid12 (M A z B C : ℕ) : Prop :=
  1 ≤ z ∧ 50 ≤ A ∧ 19 ≤ M ∧ 50 ≤ B ∧ 60 ≤ C ∧ 560 ≤ 12 * M + C ∧
    36 * M + 80 ≤ 3 * C + 4 * B ∧ 1060 ≤ C + B

def InvEclean (A z B C : ℕ) : Prop :=
  1 ≤ z ∧ 50 ≤ A ∧ 50 ≤ B ∧ 282 ≤ C ∧ 1060 ≤ C + B

def ReachesInvM (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m' z' c' k', InvM m' z' c' k' ∧ ReachesPlus target_tm cfg (mCfg m' z' c' k')

/-! #### Stage 7: `InvConvMLoop` → `ReachesInvM` (36 `rfl` lemmas) -/
private theorem rfl_cml_0_z1_r0 :
    symRunBits [7, 6, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2213⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_0_z1_r1 :
    symRunBits [7, 6, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2227⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_0_z2 :
    symRunBits [7, 6, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0,
      2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 30), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
        2109⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_0_z3 :
    symRunBits [7, 6, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symConst 2), .pair 1 1 (⟨0, 0, 0, 1,
      0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 1, 0, 2173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_0_z4 :
    symRunBits [4, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symConst 3), .pair 1 1 (⟨0, 0, 0, 1,
      0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_0_z5 :
    symRunBits [4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 4⟩), .pair 1 1 (⟨0,
      0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_1_z1_r0 :
    symRunBits [7, 5, 4, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
      2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 37⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2216⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_1_z1_r1 :
    symRunBits [7, 5, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 37⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2230⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_1_z2 :
    symRunBits [7, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0,
      2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 24), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
        2112⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_1_z3 :
    symRunBits [7, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symConst 2),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 1, 0, 2176⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_1_z4 :
    symRunBits [4, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symConst 3), .pair 1 1 (⟨0, 0, 0, 1,
      0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_1_z5 :
    symRunBits [4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 4⟩), .pair 1 1 (⟨0,
      0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_2_z1_r0 :
    symRunBits [7, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 39⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2219⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_2_z1_r1 :
    symRunBits [7, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 39⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2233⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_2_z2 :
    symRunBits [7, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 18), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
        2115⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_2_z3 :
    symRunBits [6, 5, 4, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symConst 2), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 1, 0, 2179⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_2_z4 :
    symRunBits [4, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symConst 3), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
        2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_2_z5 :
    symRunBits [4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 4⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0,
        0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_3_z1_r0 :
    symRunBits [6, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 43⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2225⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_3_z1_r1 :
    symRunBits [8, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 32⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2221⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_3_z2 :
    symRunBits [5, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 44⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 6), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2121⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_3_z3 :
    symRunBits [8, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symConst 2), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 33⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 1, 0, 2167⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_3_z4 :
    symRunBits [4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symConst 3), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_3_z5 :
    symRunBits [4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 4⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_4_z1_r0 :
    symRunBits [7, 6, 5, 4, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2210⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_4_z1_r1 :
    symRunBits [7, 6, 5, 4, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2224⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_4_z2 :
    symRunBits [7, 6, 5, 4, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 36), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
        2106⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_4_z3 :
    symRunBits [7, 6, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symConst 2), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 1, 0, 2170⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_4_z4 :
    symRunBits [4, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symConst 3), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_4_z5 :
    symRunBits [4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 4⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_5_z1_r0 :
    symRunBits [6, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 41⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2222⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_5_z1_r1 :
    symRunBits [6, 4, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 41⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 2236⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_5_z2 :
    symRunBits [6, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symZero),
      .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 12), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0,
        2118⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_5_z3 :
    symRunBits [6, 4, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (symConst 2),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 1, 0, 2182⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_5_z4 :
    symRunBits [4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (symConst 3),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cml_5_z5 :
    symRunBits [4, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0,
      4⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2119⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 2124⟩), .pair 1 0 (symZero)]) := rfl

private theorem convMLoop_step_0 (Z : ℕ)
    (ih : ∀ Z' < Z, ∀ (j : Fin 6) (A M C : ℕ), InvConvMLoop j A M Z' C →
      ReachesInvM (convMLoopCfg j A M Z' C))
    (A M C : ℕ) (hinv : InvConvMLoop 0 A M Z C) :
    ReachesInvM (convMLoopCfg 0 A M Z C) := by
  rcases hinv with ⟨hA, hM, hZ, h9M, hC⟩
  have h9M : 9 * M ≤ C := by simpa using h9M
  match hZeq : Z with
  | 1 =>
    have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_0_z1_r0)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 0 (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        35⟩) (symConst 28) (symConst 12) (⟨4, 0, 0, 1, 0,
        2213⟩) (v2 + 36) (4 * v0 + v3 + 2214) 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 36, 1, 4 * v0 + v3 + 2214, 4, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_0_z1_r1)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 0 (⟨2, 0, 0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        35⟩) (symConst 22) (symConst 9) (⟨4, 0, 0, 1, 0,
        2227⟩) (v2 + 36) (4 * v0 + v3 + 2228) 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 36, 1, 4 * v0 + v3 + 2228, 3, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  | 2 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_0_z2) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symOne) (⟨0, 0, 0, 1, 0,
      2119⟩) A M 2 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0, 36⟩) (symConst 30) (⟨1, 0, 0,
      0, 0, 50⟩) (symConst 12) (⟨0, 0, 0, 1, 0,
      2109⟩) (v2 + 37) (v0 + 51) (v3 + 2110) 4
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 37, v0 + 51, v3 + 2110, 4, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      hstep⟩
  | 3 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_0_z3) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 2) (⟨0, 0, 0, 1,
      0, 2119⟩) A M 3 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
      36⟩) (symConst 22) (symConst 9) (⟨1, 0, 0, 1, 0,
      2173⟩) (v2 + 37) (v0 + v3 + 2174) 3
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 37, 1, v0 + v3 + 2174, 3, ⟨by omega, by omega, by omega, by omega, by omega⟩, hstep⟩
  | 0 => omega
  | 4 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_0_z4) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 3) (⟨0, 0, 0, 1,
      0, 2119⟩) A M (4) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 0 v2 v3 0) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (1) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (1) (by omega) 1 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega, by omega,
      by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 5 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_cml_0_z5) (eval_convMLoop
      (v5 v0 v1 v2 v3 0) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 1, 0, 0, 0, 4⟩) (⟨0,
      0, 0, 1, 0, 2119⟩) A M (v1 + 5) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 v1 v2 v3 0) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (v1 + 2) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (v1 + 2) (by omega) 1 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega,
      by omega, by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem convMLoop_step_1 (Z : ℕ)
    (ih : ∀ Z' < Z, ∀ (j : Fin 6) (A M C : ℕ), InvConvMLoop j A M Z' C →
      ReachesInvM (convMLoopCfg j A M Z' C))
    (A M C : ℕ) (hinv : InvConvMLoop 1 A M Z C) :
    ReachesInvM (convMLoopCfg 1 A M Z C) := by
  rcases hinv with ⟨hA, hM, hZ, h9M, hC⟩
  have h9M : 9 * M ≤ C := by simpa using h9M
  match hZeq : Z with
  | 1 =>
    have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_1_z1_r0)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 1 (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        37⟩) (symConst 22) (symConst 9) (⟨4, 0, 0, 1, 0,
        2216⟩) (v2 + 38) (4 * v0 + v3 + 2217) 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 38, 1, 4 * v0 + v3 + 2217, 3, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_1_z1_r1)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 1 (⟨2, 0, 0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        37⟩) (symConst 16) (symConst 6) (⟨4, 0, 0, 1, 0,
        2230⟩) (v2 + 38) (4 * v0 + v3 + 2231) 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 38, 1, 4 * v0 + v3 + 2231, 2, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  | 2 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_1_z2) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symOne) (⟨0, 0, 0, 1, 0,
      2119⟩) A M 2 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0, 38⟩) (symConst 24) (⟨1, 0, 0,
      0, 0, 50⟩) (symConst 9) (⟨0, 0, 0, 1, 0,
      2112⟩) (v2 + 39) (v0 + 51) (v3 + 2113) 3
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 39, v0 + 51, v3 + 2113, 3, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      hstep⟩
  | 3 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_1_z3) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 2) (⟨0, 0, 0, 1,
      0, 2119⟩) A M 3 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
      38⟩) (symConst 16) (symConst 6) (⟨1, 0, 0, 1, 0,
      2176⟩) (v2 + 39) (v0 + v3 + 2177) 2
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 39, 1, v0 + v3 + 2177, 2, ⟨by omega, by omega, by omega, by omega, by omega⟩, hstep⟩
  | 0 => omega
  | 4 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_1_z4) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 3) (⟨0, 0, 0, 1,
      0, 2119⟩) A M (4) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 0 v2 v3 0) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (1) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (1) (by omega) 2 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega, by omega,
      by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 5 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_cml_1_z5) (eval_convMLoop
      (v5 v0 v1 v2 v3 0) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 1, 0, 0, 0, 4⟩) (⟨0,
      0, 0, 1, 0, 2119⟩) A M (v1 + 5) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 v1 v2 v3 0) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (v1 + 2) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (v1 + 2) (by omega) 2 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega,
      by omega, by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem convMLoop_step_2 (Z : ℕ)
    (ih : ∀ Z' < Z, ∀ (j : Fin 6) (A M C : ℕ), InvConvMLoop j A M Z' C →
      ReachesInvM (convMLoopCfg j A M Z' C))
    (A M C : ℕ) (hinv : InvConvMLoop 2 A M Z C) :
    ReachesInvM (convMLoopCfg 2 A M Z C) := by
  rcases hinv with ⟨hA, hM, hZ, h9M, hC⟩
  have h9M : 9 * M ≤ C := by simpa using h9M
  match hZeq : Z with
  | 1 =>
    have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_2_z1_r0)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 2 (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        39⟩) (symConst 16) (symConst 6) (⟨4, 0, 0, 1, 0,
        2219⟩) (v2 + 40) (4 * v0 + v3 + 2220) 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 40, 1, 4 * v0 + v3 + 2220, 2, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_2_z1_r1)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 2 (⟨2, 0, 0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        39⟩) (symConst 10) (symConst 3) (⟨4, 0, 0, 1, 0,
        2233⟩) (v2 + 40) (4 * v0 + v3 + 2234) 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 40, 1, 4 * v0 + v3 + 2234, 1, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  | 2 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_2_z2) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symOne) (⟨0, 0, 0, 1, 0,
      2119⟩) A M 2 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0, 40⟩) (symConst 18) (⟨1, 0, 0,
      0, 0, 50⟩) (symConst 6) (⟨0, 0, 0, 1, 0,
      2115⟩) (v2 + 41) (v0 + 51) (v3 + 2116) 2
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 41, v0 + 51, v3 + 2116, 2, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      hstep⟩
  | 3 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_2_z3) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 2) (⟨0, 0, 0, 1,
      0, 2119⟩) A M 3 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
      40⟩) (symConst 10) (symConst 3) (⟨1, 0, 0, 1, 0,
      2179⟩) (v2 + 41) (v0 + v3 + 2180) 1
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 41, 1, v0 + v3 + 2180, 1, ⟨by omega, by omega, by omega, by omega, by omega⟩, hstep⟩
  | 0 => omega
  | 4 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_2_z4) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 3) (⟨0, 0, 0, 1,
      0, 2119⟩) A M (4) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 0 v2 v3 0) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (1) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (1) (by omega) 5 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega, by omega,
      by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 5 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_cml_2_z5) (eval_convMLoop
      (v5 v0 v1 v2 v3 0) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 1, 0, 0, 0, 4⟩) (⟨0,
      0, 0, 1, 0, 2119⟩) A M (v1 + 5) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 v1 v2 v3 0) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (v1 + 2) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (v1 + 2) (by omega) 5 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega,
      by omega, by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem convMLoop_step_3 (Z : ℕ)
    (ih : ∀ Z' < Z, ∀ (j : Fin 6) (A M C : ℕ), InvConvMLoop j A M Z' C →
      ReachesInvM (convMLoopCfg j A M Z' C))
    (A M C : ℕ) (hinv : InvConvMLoop 3 A M Z C) :
    ReachesInvM (convMLoopCfg 3 A M Z C) := by
  rcases hinv with ⟨hA, hM, hZ, h9M, hC⟩
  have h9M : 9 * M ≤ C := by simpa using h9M
  match hZeq : Z with
  | 1 =>
    have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_3_z1_r0)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 3 (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        43⟩) (symConst 4) (symZero) (⟨4, 0, 0, 1, 0,
        2225⟩) (v2 + 44) (4 * v0 + v3 + 2226) 0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 44, 1, 4 * v0 + v3 + 2226, 0, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_3_z1_r1)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 3 (⟨2, 0, 0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        32⟩) (symConst 34) (symConst 15) (⟨4, 0, 0, 1, 0,
        2221⟩) (v2 + 33) (4 * v0 + v3 + 2222) 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 33, 1, 4 * v0 + v3 + 2222, 5, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  | 2 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_3_z2) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symOne) (⟨0, 0, 0, 1, 0,
      2119⟩) A M 2 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0, 44⟩) (symConst 6) (⟨1, 0, 0,
      0, 0, 50⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2121⟩) (v2 + 45) (v0 + 51) (v3 + 2122) 0
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 45, v0 + 51, v3 + 2122, 0, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      hstep⟩
  | 3 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_3_z3) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 2) (⟨0, 0, 0, 1,
      0, 2119⟩) A M 3 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
      33⟩) (symConst 34) (symConst 15) (⟨1, 0, 0, 1, 0,
      2167⟩) (v2 + 34) (v0 + v3 + 2168) 5
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 34, 1, v0 + v3 + 2168, 5, ⟨by omega, by omega, by omega, by omega, by omega⟩, hstep⟩
  | 0 => omega
  | 4 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_3_z4) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 3) (⟨0, 0, 0, 1,
      0, 2119⟩) A M (4) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 0 v2 v3 0) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (1) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (1) (by omega) 4 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega, by omega,
      by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 5 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_cml_3_z5) (eval_convMLoop
      (v5 v0 v1 v2 v3 0) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 1, 0, 0, 0, 4⟩) (⟨0,
      0, 0, 1, 0, 2119⟩) A M (v1 + 5) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 v1 v2 v3 0) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (v1 + 2) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (v1 + 2) (by omega) 4 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega,
      by omega, by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem convMLoop_step_4 (Z : ℕ)
    (ih : ∀ Z' < Z, ∀ (j : Fin 6) (A M C : ℕ), InvConvMLoop j A M Z' C →
      ReachesInvM (convMLoopCfg j A M Z' C))
    (A M C : ℕ) (hinv : InvConvMLoop 4 A M Z C) :
    ReachesInvM (convMLoopCfg 4 A M Z C) := by
  rcases hinv with ⟨hA, hM, hZ, h9M, hC⟩
  have h9M : 9 * M + 4 ≤ C := by simpa using h9M
  match hZeq : Z with
  | 1 =>
    have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_4_z1_r0)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 4 (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        34⟩) (symConst 34) (symConst 15) (⟨4, 0, 0, 1, 0,
        2210⟩) (v2 + 35) (4 * v0 + v3 + 2211) 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 35, 1, 4 * v0 + v3 + 2211, 5, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_4_z1_r1)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 4 (⟨2, 0, 0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        34⟩) (symConst 28) (symConst 12) (⟨4, 0, 0, 1, 0,
        2224⟩) (v2 + 35) (4 * v0 + v3 + 2225) 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 35, 1, 4 * v0 + v3 + 2225, 4, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  | 2 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_4_z2) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symOne) (⟨0, 0, 0, 1, 0,
      2119⟩) A M 2 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0, 35⟩) (symConst 36) (⟨1, 0, 0,
      0, 0, 50⟩) (symConst 15) (⟨0, 0, 0, 1, 0,
      2106⟩) (v2 + 36) (v0 + 51) (v3 + 2107) 5
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 36, v0 + 51, v3 + 2107, 5, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      hstep⟩
  | 3 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_4_z3) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 2) (⟨0, 0, 0, 1,
      0, 2119⟩) A M 3 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
      35⟩) (symConst 28) (symConst 12) (⟨1, 0, 0, 1, 0,
      2170⟩) (v2 + 36) (v0 + v3 + 2171) 4
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 36, 1, v0 + v3 + 2171, 4, ⟨by omega, by omega, by omega, by omega, by omega⟩, hstep⟩
  | 0 => omega
  | 4 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_4_z4) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 3) (⟨0, 0, 0, 1,
      0, 2119⟩) A M (4) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 0 v2 v3 0) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      46⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 47) (1) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (1) (by omega) 0 (v0 + 50) (v2 + 47) (v3 + 2125) ⟨by omega, by omega, by omega,
      by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 5 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_cml_4_z5) (eval_convMLoop
      (v5 v0 v1 v2 v3 0) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 1, 0, 0, 0, 4⟩) (⟨0,
      0, 0, 1, 0, 2119⟩) A M (v1 + 5) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 v1 v2 v3 0) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      46⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 47) (v1 + 2) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (v1 + 2) (by omega) 0 (v0 + 50) (v2 + 47) (v3 + 2125) ⟨by omega, by omega,
      by omega, by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem convMLoop_step_5 (Z : ℕ)
    (ih : ∀ Z' < Z, ∀ (j : Fin 6) (A M C : ℕ), InvConvMLoop j A M Z' C →
      ReachesInvM (convMLoopCfg j A M Z' C))
    (A M C : ℕ) (hinv : InvConvMLoop 5 A M Z C) :
    ReachesInvM (convMLoopCfg 5 A M Z C) := by
  rcases hinv with ⟨hA, hM, hZ, h9M, hC⟩
  have h9M : 9 * M ≤ C := by simpa using h9M
  match hZeq : Z with
  | 1 =>
    have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_5_z1_r0)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 5 (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        41⟩) (symConst 10) (symConst 3) (⟨4, 0, 0, 1, 0,
        2222⟩) (v2 + 42) (4 * v0 + v3 + 2223) 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 42, 1, 4 * v0 + v3 + 2223, 1, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := C - 2120
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_5_z1_r1)
        (eval_convMLoop (v5 v0 0 v2 v3 0) 5 (⟨2, 0, 0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (symZero) (⟨0, 0, 0, 1, 0, 2119⟩) A M 1 C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        41⟩) (symConst 4) (symZero) (⟨4, 0, 0, 1, 0,
        2236⟩) (v2 + 42) (4 * v0 + v3 + 2237) 0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 42, 1, 4 * v0 + v3 + 2237, 0, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  | 2 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_5_z2) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symOne) (⟨0, 0, 0, 1, 0,
      2119⟩) A M 2 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0, 42⟩) (symConst 12) (⟨1, 0, 0,
      0, 0, 50⟩) (symConst 3) (⟨0, 0, 0, 1, 0,
      2118⟩) (v2 + 43) (v0 + 51) (v3 + 2119) 1
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 43, v0 + 51, v3 + 2119, 1, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      hstep⟩
  | 3 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_5_z3) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 2) (⟨0, 0, 0, 1,
      0, 2119⟩) A M 3 C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
      42⟩) (symConst 4) (symZero) (⟨1, 0, 0, 1, 0,
      2182⟩) (v2 + 43) (v0 + v3 + 2183) 0
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    exact ⟨v2 + 43, 1, v0 + v3 + 2183, 0, ⟨by omega, by omega, by omega, by omega, by omega⟩, hstep⟩
  | 0 => omega
  | 4 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cml_5_z4) (eval_convMLoop
      (v5 v0 0 v2 v3 0) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (symConst 3) (⟨0, 0, 0, 1,
      0, 2119⟩) A M (4) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 0 v2 v3 0) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (symZero) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (1) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (1) (by omega) 3 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega, by omega,
      by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 5 =>
    set v0 := A - 50; set v2 := M - 46; set v3 := C - 2120
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_cml_5_z5) (eval_convMLoop
      (v5 v0 v1 v2 v3 0) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 1, 0, 0, 0, 4⟩) (⟨0,
      0, 0, 1, 0, 2119⟩) A M (v1 + 5) C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convMLoop (v5 v0 v1 v2 v3 0) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0,
      2124⟩) (v0 + 50) (v2 + 46) (v1 + 2) (v3 + 2125)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := ih (v1 + 2) (by omega) 3 (v0 + 50) (v2 + 46) (v3 + 2125) ⟨by omega, by omega,
      by omega, by simp; omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem convMLoop_to_M (Z : ℕ) :
    ∀ (i : Fin 6) (A M C : ℕ), InvConvMLoop i A M Z C →
      ReachesInvM (convMLoopCfg i A M Z C) := by
  induction Z using Nat.strongRecOn with
  | ind Z ih =>
    intro i
    refine fin6_ind (P := fun i => ∀ (A M C : ℕ),
      InvConvMLoop i A M Z C → ReachesInvM (convMLoopCfg i A M Z C))
      (convMLoop_step_0 Z ih) (convMLoop_step_1 Z ih) (convMLoop_step_2 Z ih)
      (convMLoop_step_3 Z ih) (convMLoop_step_4 Z ih) (convMLoop_step_5 Z ih) i

/-! #### Stage 6a: `InvConvSimple` → `ReachesInvM` (12 `rfl` lemmas) -/
private theorem rfl_cs_0_r0 :
    symRunBits [7, 6, 5] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0,
      0, 48⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 33⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 99⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_0_r1 :
    symRunBits [7, 6, 5, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2,
      0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 33⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 89⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_1_r0 :
    symRunBits [7, 5, 4, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0,
      0, 0, 0, 48⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 102⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_1_r1 :
    symRunBits [7, 6, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0,
      0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 92⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_2_r0 :
    symRunBits [7, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0,
      0, 0, 48⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 37⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 105⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_2_r1 :
    symRunBits [7, 5, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0,
      0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 37⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 95⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_3_r0 :
    symRunBits [6, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0,
      0, 0, 48⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 41⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 111⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_3_r1 :
    symRunBits [6, 4, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0,
      0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 41⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 101⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_4_r0 :
    symRunBits [8, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0,
      0, 48⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 32⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 96⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_4_r1 :
    symRunBits [5, 4] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0,
      49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 43⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 104⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_5_r0 :
    symRunBits [6, 5, 4, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2, 0, 0,
      0, 0, 48⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 39⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 108⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cs_5_r1 :
    symRunBits [6, 5, 4, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨2,
      0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 0, 1, 0, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 39⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 1, 0, 98⟩),
        .pair 1 0 (symZero)]) := rfl

private theorem convSimple_to_M (i : Fin 6) (A M R0 : ℕ)
    (hinv : InvConvSimple i A M R0) : ReachesInvM (convSimpleCfg i A M R0) := by
  rcases hinv with ⟨hA, hM, hR0, h9M, h2120⟩
  refine fin6_ind (P := fun i => ReachesInvM (convSimpleCfg i A M R0)) ?_ ?_ ?_ ?_ ?_ ?_ i
  · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_0_r0)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 0 symZero (⟨2, 0, 0, 0, 0, 48⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        33⟩) (symConst 28) (symConst 12) (⟨4, 0, 0, 1, 0,
        99⟩) (v2 + 34) (4 * v0 + v3 + 100) 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 34, 1, 4 * v0 + v3 + 100, 4, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_0_r1)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 0 symZero (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        33⟩) (symConst 34) (symConst 15) (⟨4, 0, 0, 1, 0,
        89⟩) (v2 + 34) (4 * v0 + v3 + 90) 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 34, 1, 4 * v0 + v3 + 90, 5, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
  · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_1_r0)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 1 symZero (⟨2, 0, 0, 0, 0, 48⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        35⟩) (symConst 22) (symConst 9) (⟨4, 0, 0, 1, 0,
        102⟩) (v2 + 36) (4 * v0 + v3 + 103) 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 36, 1, 4 * v0 + v3 + 103, 3, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_1_r1)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 1 symZero (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        35⟩) (symConst 28) (symConst 12) (⟨4, 0, 0, 1, 0,
        92⟩) (v2 + 36) (4 * v0 + v3 + 93) 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 36, 1, 4 * v0 + v3 + 93, 4, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
  · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_2_r0)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 2 symZero (⟨2, 0, 0, 0, 0, 48⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        37⟩) (symConst 16) (symConst 6) (⟨4, 0, 0, 1, 0,
        105⟩) (v2 + 38) (4 * v0 + v3 + 106) 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 38, 1, 4 * v0 + v3 + 106, 2, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_2_r1)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 2 symZero (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        37⟩) (symConst 22) (symConst 9) (⟨4, 0, 0, 1, 0,
        95⟩) (v2 + 38) (4 * v0 + v3 + 96) 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 38, 1, 4 * v0 + v3 + 96, 3, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
  · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_3_r0)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 3 symZero (⟨2, 0, 0, 0, 0, 48⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        41⟩) (symConst 4) (symZero) (⟨4, 0, 0, 1, 0,
        111⟩) (v2 + 42) (4 * v0 + v3 + 112) 0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 42, 1, 4 * v0 + v3 + 112, 0, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_3_r1)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 3 symZero (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        41⟩) (symConst 10) (symConst 3) (⟨4, 0, 0, 1, 0,
        101⟩) (v2 + 42) (4 * v0 + v3 + 102) 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 42, 1, 4 * v0 + v3 + 102, 1, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
  · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_4_r0)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 4 symZero (⟨2, 0, 0, 0, 0, 48⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        32⟩) (symConst 34) (symConst 15) (⟨4, 0, 0, 1, 0,
        96⟩) (v2 + 33) (4 * v0 + v3 + 97) 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 33, 1, 4 * v0 + v3 + 97, 5, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_4_r1)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 4 symZero (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        43⟩) (symConst 4) (symZero) (⟨4, 0, 0, 1, 0,
        104⟩) (v2 + 44) (4 * v0 + v3 + 105) 0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 44, 1, 4 * v0 + v3 + 105, 0, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
  · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
    rcases hA_mod with hrA | hrA
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_5_r0)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 5 symZero (⟨2, 0, 0, 0, 0, 48⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        39⟩) (symConst 10) (symConst 3) (⟨4, 0, 0, 1, 0,
        108⟩) (v2 + 40) (4 * v0 + v3 + 109) 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 40, 1, 4 * v0 + v3 + 109, 1, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩
    · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_cs_5_r1)
        (eval_convSimple_2 (v5 v0 0 v2 v3 0) 5 symZero (⟨2, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        45⟩) (⟨0, 0, 0, 1, 0, 3⟩) A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 0) (⟨0, 0, 1, 0, 0,
        39⟩) (symConst 16) (symConst 6) (⟨4, 0, 0, 1, 0,
        98⟩) (v2 + 40) (4 * v0 + v3 + 99) 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 40, 1, 4 * v0 + v3 + 99, 2, ⟨by omega, by omega, by omega, by omega, by omega⟩,
        hstep⟩

/-! #### Stage 6b: `InvConvEntryZ2` & `InvConvEntry` → `ReachesInvM` (66 `rfl` lemmas) -/
private theorem rfl_cez2_0_b0_a0 :
    symRunBits [7, 6, 5, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1,
      3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 137⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_0_b0_a1 :
    symRunBits [7, 6, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 151⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_0_b1 :
    symRunBits [7, 6, 5, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1,
      3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 93⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b0_z1 :
    symRunBits [7, 6, 5] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 18⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 89⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b0_z3 :
    symRunBits [7, 6, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 18⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 30), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 33⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b0_z4 :
    symRunBits [7, 6, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symConst 2), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 97⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b0_z5 :
    symRunBits [4, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symConst 3), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b0_z6 :
    symRunBits [4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 4⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b1_z1 :
    symRunBits [7, 6, 5, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 19⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 36), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 29⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b1_z3 :
    symRunBits [3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_0_b1_z4 :
    symRunBits [3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 2⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_1_b0_a0 :
    symRunBits [7, 5, 4, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 37⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 140⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_1_b0_a1 :
    symRunBits [7, 5, 4, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1,
      3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 37⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 154⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_1_b1 :
    symRunBits [7, 5, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 19⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 96⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b0_z1 :
    symRunBits [7, 5, 4, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero),
        .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 92⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b0_z3 :
    symRunBits [7, 5, 4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 24), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 36⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b0_z4 :
    symRunBits [7, 5, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symConst 2), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 100⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b0_z5 :
    symRunBits [4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symConst 3), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b0_z6 :
    symRunBits [5] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2, 0,
      18⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 4⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b1_z1 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 36⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 30), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 32⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b1_z3 :
    symRunBits [3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_1_b1_z4 :
    symRunBits [3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 2⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_2_b0_a0 :
    symRunBits [7, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 39⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 143⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_2_b0_a1 :
    symRunBits [7, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 39⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 157⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_2_b1 :
    symRunBits [7, 4, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 99⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b0_z1 :
    symRunBits [7, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 95⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b0_z3 :
    symRunBits [7, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 18), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 39⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b0_z4 :
    symRunBits [7, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 18⟩), .pair 1 1 (symConst 2), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 103⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b0_z5 :
    symRunBits [4, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symConst 3), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1,
        48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b0_z6 :
    symRunBits [4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 4⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0,
        0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b1_z1 :
    symRunBits [7, 5, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 38⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 24), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 9), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 35⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b1_z3 :
    symRunBits [3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_2_b1_z4 :
    symRunBits [3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 2⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_3_b0_a0 :
    symRunBits [6, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 43⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 149⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_3_b0_a1 :
    symRunBits [8, 5, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 32⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 145⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_3_b1 :
    symRunBits [6, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 19⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 105⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b0_z1 :
    symRunBits [6, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 101⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b0_z3 :
    symRunBits [6, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2, 0,
      18⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1,
      0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 44⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 6), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 45⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b0_z4 :
    symRunBits [8, 4, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symConst 2), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 33⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 91⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b0_z5 :
    symRunBits [5, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2, 0,
      18⟩), .pair 1 1 (symConst 3), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b0_z6 :
    symRunBits [5, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2, 0,
      18⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 4⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b1_z1 :
    symRunBits [6, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 12), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 41⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b1_z3 :
    symRunBits [3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_3_b1_z4 :
    symRunBits [3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 2⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_4_b0_a0 :
    symRunBits [8, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 134⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_4_b0_a1 :
    symRunBits [7, 6, 5, 4, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 34⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 148⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_4_b1 :
    symRunBits [8, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2, 0,
      19⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1,
      0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 33⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 90⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b0_z1 :
    symRunBits [8, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 18⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 33⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 34), .mid (symZero),
        .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 86⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b0_z3 :
    symRunBits [7, 6, 5, 4, 3, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero),
      .pair 2 0 (⟨0, 0, 0, 2, 0, 18⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0,
      0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 36), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 15), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 30⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b0_z4 :
    symRunBits [7, 6, 5, 4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 18⟩), .pair 1 1 (symConst 2), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 35⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 28), .mid (symZero),
        .pair 1 1 (symConst 12), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 94⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b0_z5 :
    symRunBits [4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symConst 3), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b0_z6 :
    symRunBits [5] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2, 0,
      18⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 4⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b1_z1 :
    symRunBits [5, 4, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 44⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 6), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 44⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b1_z3 :
    symRunBits [3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_4_b1_z4 :
    symRunBits [3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 2⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_5_b0_a0 :
    symRunBits [6, 5, 4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 41⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 146⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_5_b0_a1 :
    symRunBits [6, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 18⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨2, 0, 0, 0, 0, 50⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 41⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨4, 0, 0, 4, 1, 160⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_cez2_5_b1 :
    symRunBits [6, 5, 4, 2] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 102⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b0_z1 :
    symRunBits [6, 5, 4, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩),
      .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 0, 0, 1,
      3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 10), .mid (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 98⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b0_z3 :
    symRunBits [6, 5, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
      0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 12), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 42⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b0_z4 :
    symRunBits [6, 4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 18⟩), .pair 1 1 (symConst 2), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 42⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 4), .mid (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨1, 0, 0, 4, 1, 106⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b0_z5 :
    symRunBits [4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 18⟩), .pair 1 1 (symConst 3), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b0_z6 :
    symRunBits [4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0,
      0, 2, 0, 18⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 4⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0,
      49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0,
        0, 1⟩), .pair 1 1 (⟨0, 0, 0, 4, 1, 48⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b1_z1 :
    symRunBits [6, 5, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0,
      0, 0, 2, 0, 19⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0,
      45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 0,
      0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (⟨0, 0, 1, 0, 0, 40⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 18), .pair 2 0 (⟨1, 0, 0,
        0, 0, 50⟩), .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1, 38⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b1_z3 :
    symRunBits [3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 2,
      0, 19⟩), .pair 1 1 (symOne), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0,
      1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 0, 4, 1,
        47⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ce_5_b1_z4 :
    symRunBits [3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0,
      2, 0, 19⟩), .pair 1 1 (⟨0, 1, 0, 0, 0, 2⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
      [.pair 1 1 (⟨0, 0, 0, 0, 1, 3⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0,
        0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symOne)], [.pair 1 1 (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨0,
        0, 0, 4, 1, 47⟩), .pair 1 0 (symZero)]) := rfl

private theorem convEntryZ2_to_M (i : Fin 6) (B A M R0 : ℕ)
    (hinv : InvConvEntryZ2 i B A M R0) : ReachesInvM (convEntryCfg i B 2 A M R0) := by
  rcases hinv with ⟨hA, hB, hM, hR0, h9M, h2120⟩
  refine fin6_ind (P := fun i => ReachesInvM (convEntryCfg i B 2 A M R0)) ?_ ?_ ?_ ?_ ?_ ?_ i
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
      rcases hA_mod with hrA | hrA
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_0_b0_a0)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          35⟩) (symConst 28) (symConst 12) (⟨4, 0, 0, 4, 1,
          137⟩) (v2 + 36) (4 * v0 + 4 * v3 + v4 + 138) 4
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 36, 1, 4 * v0 + 4 * v3 + v4 + 138, 4, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_0_b0_a1)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          35⟩) (symConst 22) (symConst 9) (⟨4, 0, 0, 4, 1,
          151⟩) (v2 + 36) (4 * v0 + 4 * v3 + v4 + 152) 3
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 36, 1, 4 * v0 + 4 * v3 + v4 + 152, 3, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
    · set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_0_b1)
        (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 19⟩) symZero (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B 2 A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
        34⟩) (symConst 28) (symConst 12) (⟨1, 0, 0, 4, 1,
        93⟩) (v2 + 35) (v0 + 4 * v3 + v4 + 94) 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 35, 1, v0 + 4 * v3 + v4 + 94, 4, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
      rcases hA_mod with hrA | hrA
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_1_b0_a0)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          37⟩) (symConst 22) (symConst 9) (⟨4, 0, 0, 4, 1,
          140⟩) (v2 + 38) (4 * v0 + 4 * v3 + v4 + 141) 3
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 38, 1, 4 * v0 + 4 * v3 + v4 + 141, 3, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_1_b0_a1)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          37⟩) (symConst 16) (symConst 6) (⟨4, 0, 0, 4, 1,
          154⟩) (v2 + 38) (4 * v0 + 4 * v3 + v4 + 155) 2
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 38, 1, 4 * v0 + 4 * v3 + v4 + 155, 2, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
    · set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_1_b1)
        (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 19⟩) symZero (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B 2 A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
        36⟩) (symConst 22) (symConst 9) (⟨1, 0, 0, 4, 1,
        96⟩) (v2 + 37) (v0 + 4 * v3 + v4 + 97) 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 37, 1, v0 + 4 * v3 + v4 + 97, 3, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
      rcases hA_mod with hrA | hrA
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_2_b0_a0)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          39⟩) (symConst 16) (symConst 6) (⟨4, 0, 0, 4, 1,
          143⟩) (v2 + 40) (4 * v0 + 4 * v3 + v4 + 144) 2
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 40, 1, 4 * v0 + 4 * v3 + v4 + 144, 2, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_2_b0_a1)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          39⟩) (symConst 10) (symConst 3) (⟨4, 0, 0, 4, 1,
          157⟩) (v2 + 40) (4 * v0 + 4 * v3 + v4 + 158) 1
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 40, 1, 4 * v0 + 4 * v3 + v4 + 158, 1, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
    · set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_2_b1)
        (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 19⟩) symZero (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B 2 A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
        38⟩) (symConst 16) (symConst 6) (⟨1, 0, 0, 4, 1,
        99⟩) (v2 + 39) (v0 + 4 * v3 + v4 + 100) 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 39, 1, v0 + 4 * v3 + v4 + 100, 2, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
      rcases hA_mod with hrA | hrA
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_3_b0_a0)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          43⟩) (symConst 4) (symZero) (⟨4, 0, 0, 4, 1,
          149⟩) (v2 + 44) (4 * v0 + 4 * v3 + v4 + 150) 0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 44, 1, 4 * v0 + 4 * v3 + v4 + 150, 0, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_3_b0_a1)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          32⟩) (symConst 34) (symConst 15) (⟨4, 0, 0, 4, 1,
          145⟩) (v2 + 33) (4 * v0 + 4 * v3 + v4 + 146) 5
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 33, 1, 4 * v0 + 4 * v3 + v4 + 146, 5, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
    · set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_3_b1)
        (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 19⟩) symZero (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B 2 A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
        42⟩) (symConst 4) (symZero) (⟨1, 0, 0, 4, 1,
        105⟩) (v2 + 43) (v0 + 4 * v3 + v4 + 106) 0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 43, 1, v0 + 4 * v3 + v4 + 106, 0, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
      rcases hA_mod with hrA | hrA
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_4_b0_a0)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          34⟩) (symConst 34) (symConst 15) (⟨4, 0, 0, 4, 1,
          134⟩) (v2 + 35) (4 * v0 + 4 * v3 + v4 + 135) 5
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 35, 1, 4 * v0 + 4 * v3 + v4 + 135, 5, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_4_b0_a1)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          34⟩) (symConst 28) (symConst 12) (⟨4, 0, 0, 4, 1,
          148⟩) (v2 + 35) (4 * v0 + 4 * v3 + v4 + 149) 4
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 35, 1, 4 * v0 + 4 * v3 + v4 + 149, 4, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
    · set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_4_b1)
        (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 19⟩) symZero (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B 2 A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
        33⟩) (symConst 34) (symConst 15) (⟨1, 0, 0, 4, 1,
        90⟩) (v2 + 34) (v0 + 4 * v3 + v4 + 91) 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 34, 1, v0 + 4 * v3 + v4 + 91, 5, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · have hA_mod : A % 2 = 0 ∨ A % 2 = 1 := by omega
      rcases hA_mod with hrA | hrA
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_5_b0_a0)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          41⟩) (symConst 10) (symConst 3) (⟨4, 0, 0, 4, 1,
          146⟩) (v2 + 42) (4 * v0 + 4 * v3 + v4 + 147) 1
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 42, 1, 4 * v0 + 4 * v3 + v4 + 147, 1, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      · set v0 := (A - 50) / 2; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_5_b0_a1)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 18⟩) symZero (⟨2, 0,
          0, 0, 0, 50⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 2 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          41⟩) (symConst 4) (symZero) (⟨4, 0, 0, 4, 1,
          160⟩) (v2 + 42) (4 * v0 + 4 * v3 + v4 + 161) 0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 42, 1, 4 * v0 + 4 * v3 + v4 + 161, 0, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
    · set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_cez2_5_b1)
        (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 19⟩) symZero (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B 2 A M R0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
        40⟩) (symConst 10) (symConst 3) (⟨1, 0, 0, 4, 1,
        102⟩) (v2 + 41) (v0 + 4 * v3 + v4 + 103) 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      exact ⟨v2 + 41, 1, v0 + 4 * v3 + v4 + 103, 1, ⟨by omega, by omega, by omega, by omega,
        by omega⟩, hstep⟩

private theorem convEntry_to_M (i : Fin 6) (B z A M R0 : ℕ)
    (hinv : InvConvEntry i B z A M R0) : ReachesInvM (convEntryCfg i B z A M R0) := by
  rcases hinv with ⟨hA, hB, hz, hM, hR0, h9M, h2120⟩
  refine fin6_ind (P := fun i => ReachesInvM (convEntryCfg i B z A M R0)) ?_ ?_ ?_ ?_ ?_ ?_ i
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_0_b0_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          34⟩) (symConst 28) (symConst 12) (⟨1, 0, 0, 4, 1,
          89⟩) (v2 + 35) (v0 + 4 * v3 + v4 + 90) 4
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 35, 1, v0 + 4 * v3 + v4 + 90, 4, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 0 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_0_b0_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 18⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 3 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 36⟩) (symConst 30) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 12) (⟨0, 0, 0, 4, 1,
          33⟩) (v2 + 37) (v0 + 51) (4 * v3 + v4 + 34) 4
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 37, v0 + 51, 4 * v3 + v4 + 34, 4, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_0_b0_z4)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 2) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 4 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          36⟩) (symConst 22) (symConst 9) (⟨1, 0, 0, 4, 1,
          97⟩) (v2 + 37) (v0 + 4 * v3 + v4 + 98) 3
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 37, 1, v0 + 4 * v3 + v4 + 98, 3, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 5 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_0_b0_z5)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 3) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (5) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 1 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 6 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_0_b0_z6)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨0, 1, 0, 0,
          0, 4⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 6) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 1 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_0_b1_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 34⟩) (symConst 36) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 15) (⟨0, 0, 0, 4, 1,
          29⟩) (v2 + 35) (v0 + 51) (4 * v3 + v4 + 30) 5
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 35, v0 + 51, 4 * v3 + v4 + 30, 5, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 0 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_0_b1_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 19⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (3) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 0 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_0_b1_z4)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 0 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨0, 1, 0, 0,
          0, 2⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 4) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 0 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_1_b0_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          36⟩) (symConst 22) (symConst 9) (⟨1, 0, 0, 4, 1,
          92⟩) (v2 + 37) (v0 + 4 * v3 + v4 + 93) 3
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 37, 1, v0 + 4 * v3 + v4 + 93, 3, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 1 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_1_b0_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 18⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 3 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 38⟩) (symConst 24) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 9) (⟨0, 0, 0, 4, 1,
          36⟩) (v2 + 39) (v0 + 51) (4 * v3 + v4 + 37) 3
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 39, v0 + 51, 4 * v3 + v4 + 37, 3, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_1_b0_z4)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 2) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 4 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          38⟩) (symConst 16) (symConst 6) (⟨1, 0, 0, 4, 1,
          100⟩) (v2 + 39) (v0 + 4 * v3 + v4 + 101) 2
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 39, 1, v0 + 4 * v3 + v4 + 101, 2, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 5 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_1_b0_z5)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 3) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (5) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 2 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 6 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_1_b0_z6)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨0, 1, 0, 0,
          0, 4⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 6) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 2 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_1_b1_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 36⟩) (symConst 30) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 12) (⟨0, 0, 0, 4, 1,
          32⟩) (v2 + 37) (v0 + 51) (4 * v3 + v4 + 33) 4
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 37, v0 + 51, 4 * v3 + v4 + 33, 4, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 1 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_1_b1_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 19⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (3) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 1 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_1_b1_z4)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 1 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨0, 1, 0, 0,
          0, 2⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 4) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 1 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 1 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_2_b0_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          38⟩) (symConst 16) (symConst 6) (⟨1, 0, 0, 4, 1,
          95⟩) (v2 + 39) (v0 + 4 * v3 + v4 + 96) 2
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 39, 1, v0 + 4 * v3 + v4 + 96, 2, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 2 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_2_b0_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 18⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 3 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 40⟩) (symConst 18) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 6) (⟨0, 0, 0, 4, 1,
          39⟩) (v2 + 41) (v0 + 51) (4 * v3 + v4 + 40) 2
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 41, v0 + 51, 4 * v3 + v4 + 40, 2, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_2_b0_z4)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 2) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 4 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          40⟩) (symConst 10) (symConst 3) (⟨1, 0, 0, 4, 1,
          103⟩) (v2 + 41) (v0 + 4 * v3 + v4 + 104) 1
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 41, 1, v0 + 4 * v3 + v4 + 104, 1, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 5 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_2_b0_z5)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 3) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (5) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 5 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 6 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_2_b0_z6)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨0, 1, 0, 0,
          0, 4⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 6) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 5 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_2_b1_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 38⟩) (symConst 24) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 9) (⟨0, 0, 0, 4, 1,
          35⟩) (v2 + 39) (v0 + 51) (4 * v3 + v4 + 36) 3
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 39, v0 + 51, 4 * v3 + v4 + 36, 3, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 2 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_2_b1_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 19⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (3) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 2 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_2_b1_z4)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 2 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨0, 1, 0, 0,
          0, 2⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 4) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 2 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 2 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_3_b0_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          42⟩) (symConst 4) (symZero) (⟨1, 0, 0, 4, 1,
          101⟩) (v2 + 43) (v0 + 4 * v3 + v4 + 102) 0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 43, 1, v0 + 4 * v3 + v4 + 102, 0, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 3 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_3_b0_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 18⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 3 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 44⟩) (symConst 6) (⟨1, 0,
          0, 0, 0, 50⟩) (symZero) (⟨0, 0, 0, 4, 1,
          45⟩) (v2 + 45) (v0 + 51) (4 * v3 + v4 + 46) 0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 45, v0 + 51, 4 * v3 + v4 + 46, 0, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_3_b0_z4)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 2) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 4 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          33⟩) (symConst 34) (symConst 15) (⟨1, 0, 0, 4, 1,
          91⟩) (v2 + 34) (v0 + 4 * v3 + v4 + 92) 5
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 34, 1, v0 + 4 * v3 + v4 + 92, 5, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 5 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_3_b0_z5)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 3) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (5) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 4 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 6 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_3_b0_z6)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨0, 1, 0, 0,
          0, 4⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 6) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 4 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_3_b1_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 42⟩) (symConst 12) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 3) (⟨0, 0, 0, 4, 1,
          41⟩) (v2 + 43) (v0 + 51) (4 * v3 + v4 + 42) 1
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 43, v0 + 51, 4 * v3 + v4 + 42, 1, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 3 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_3_b1_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 19⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (3) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 3 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_3_b1_z4)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 3 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨0, 1, 0, 0,
          0, 2⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 4) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 3 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_4_b0_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          33⟩) (symConst 34) (symConst 15) (⟨1, 0, 0, 4, 1,
          86⟩) (v2 + 34) (v0 + 4 * v3 + v4 + 87) 5
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 34, 1, v0 + 4 * v3 + v4 + 87, 5, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 4 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_4_b0_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 18⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 3 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 35⟩) (symConst 36) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 15) (⟨0, 0, 0, 4, 1,
          30⟩) (v2 + 36) (v0 + 51) (4 * v3 + v4 + 31) 5
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 36, v0 + 51, 4 * v3 + v4 + 31, 5, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_4_b0_z4)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 2) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 4 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          35⟩) (symConst 28) (symConst 12) (⟨1, 0, 0, 4, 1,
          94⟩) (v2 + 36) (v0 + 4 * v3 + v4 + 95) 4
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 36, 1, v0 + 4 * v3 + v4 + 95, 4, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 5 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_4_b0_z5)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 3) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (5) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          46⟩) (symZero) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 47) (1) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 0 (v0 + 50) (v2 + 47) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 6 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_4_b0_z6)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨0, 1, 0, 0,
          0, 4⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 6) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 0 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 46⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 47) (v1 + 2) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 0 (v0 + 50) (v2 + 47) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_4_b1_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 44⟩) (symConst 6) (⟨1, 0,
          0, 0, 0, 50⟩) (symZero) (⟨0, 0, 0, 4, 1,
          44⟩) (v2 + 45) (v0 + 51) (4 * v3 + v4 + 45) 0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 45, v0 + 51, 4 * v3 + v4 + 45, 0, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 4 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_4_b1_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 19⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (3) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 4 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_4_b1_z4)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 4 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨0, 1, 0, 0,
          0, 2⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 4) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 4 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 4 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  · have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_5_b0_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          40⟩) (symConst 10) (symConst 3) (⟨1, 0, 0, 4, 1,
          98⟩) (v2 + 41) (v0 + 4 * v3 + v4 + 99) 1
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 41, 1, v0 + 4 * v3 + v4 + 99, 1, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 5 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_5_b0_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 18⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 3 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 42⟩) (symConst 12) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 3) (⟨0, 0, 0, 4, 1,
          42⟩) (v2 + 43) (v0 + 51) (4 * v3 + v4 + 43) 1
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 43, v0 + 51, 4 * v3 + v4 + 43, 1, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_5_b0_z4)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 2) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B 4 A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0,
          42⟩) (symConst 4) (symZero) (⟨1, 0, 0, 4, 1,
          106⟩) (v2 + 43) (v0 + 4 * v3 + v4 + 107) 0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 43, 1, v0 + 4 * v3 + v4 + 107, 0, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 5 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_5_b0_z5)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0,
          18⟩) (symConst 3) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (5) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 3 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 6 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_5_b0_z6)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 18⟩) (⟨0, 1, 0, 0,
          0, 4⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 6) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 3 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          48⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 49)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 3 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 49) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · match hz_eq : z with
      | 0 => omega
      | 1 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_5_b1_z1)
          (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨1, 0, 0, 0, 0,
          49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1, 3⟩) B A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_mCfg_z2 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 0, 40⟩) (symConst 18) (⟨1,
          0, 0, 0, 0, 50⟩) (symConst 6) (⟨0, 0, 0, 4, 1,
          38⟩) (v2 + 41) (v0 + 51) (4 * v3 + v4 + 39) 2
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        exact ⟨v2 + 41, v0 + 51, 4 * v3 + v4 + 39, 2, ⟨by omega, by omega, by omega, by omega,
          by omega⟩, hstep⟩
      | 2 => exact convEntryZ2_to_M 5 B A M R0 ⟨hA, hB, hM, hR0, by omega, by omega⟩
      | 3 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ce_5_b1_z3)
          (eval_convEntry_2_z2 (v5 v0 0 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 19⟩) (symOne) (⟨1, 0,
          0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (3) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 0 v2 v3 v4) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
          45⟩) (symZero) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (1) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (1) 5 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
      | v1 + 4 =>
        set v0 := A - 50; set v2 := M - 46; set v3 := (B - 20) / 2; set v4 := R0 - 4
        have hstep :=
          reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ce_5_b1_z4)
          (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 5 symZero (⟨0, 0, 0, 2, 0, 19⟩) (⟨0, 1, 0, 0,
          0, 2⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0, 45⟩) (⟨0, 0, 0, 0, 1,
          3⟩) B (v1 + 4) A M R0
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by
              dsimp only [evalSymN, symZero, symOne, symConst, v5]
              omega)) (eval_convMLoop (v5 v0 v1 v2 v3 v4) 5 (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0,
          0, 45⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 4, 1,
          47⟩) (v0 + 50) (v2 + 46) (v1 + 2) (4 * v3 + v4 + 48)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
            (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
        obtain ⟨m', z', c', k', hm',
          hrest⟩ := convMLoop_to_M (v1 + 2) 5 (v0 + 50) (v2 + 46) (4 * v3 + v4 + 48) ⟨by omega,
          by omega, by omega, by simp; omega, by omega⟩
        exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

/-! #### Stage 5: `InvEmidExtraPost` & `InvEmidExtra` →
  `ReachesInvM` (18 `rfl` lemmas + direct `era_E_loop`) -/
private theorem rfl_ep0_c0 :
    symRunBits [4, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 19⟩),
      .pair 1 2 (symZero), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 1, 0, 0, 19⟩),
        .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0,
        1, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep0_c1 :
    symRunBits [5, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symZero), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 1, 0, 0, 20⟩),
        .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0,
        1, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep0_c2 :
    symRunBits [5, 4, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symOne), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 1, 0, 0, 21⟩),
        .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0,
        1, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep0_c3 :
    symRunBits [6] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 2), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 1, 0, 0, 22⟩),
        .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0,
        1, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep0_c4 :
    symRunBits [6, 3, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 3), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 1, 0, 0, 23⟩),
        .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0,
        1, 46⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep0_c5 :
    symRunBits [6, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 19⟩),
      .pair 1 2 (symZero), .pair 1 1 (symConst 4), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 1, 0, 0, 24⟩),
        .pair 1 1 (symZero), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0,
        1, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z1_c0 :
    symRunBits [5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩), .mid (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 20⟩), .pair 1 2 (symZero),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0, 1, 45⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 4, 0, 0, 52⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z1_c1 :
    symRunBits [6, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩), .mid (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 2, 0, 0, 19⟩), .pair 1 2 (symZero), .pair 1 1 (symZero),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0, 1, 45⟩),
        .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 4, 0, 0, 52⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z1_c2 :
    symRunBits [6, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩), .mid (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 2, 0, 0, 20⟩), .pair 1 2 (symZero), .pair 1 1 (symOne),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0, 1, 46⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0, 56⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z1_c3 :
    symRunBits [6, 4, 3, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩), .mid (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 2), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0, 1, 46⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0, 56⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z1_c4 :
    symRunBits [6, 5, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩), .mid (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 20⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 3), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0, 1, 46⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 4, 0, 0, 60⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z1_c5 :
    symRunBits [6, 5, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩), .mid (symZero), .pair 2 0 (symZero),
      .pair 1 1 (⟨0, 0, 2, 0, 0, 19⟩), .pair 1 2 (symZero), .pair 1 1 (symConst 4),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 0, 0, 1, 46⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 4, 0, 0,
        60⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z2_c0 :
    symRunBits [5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 20⟩), .pair 1 2 (symZero),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 0, 0, 1, 45⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0, 52⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z2_c1 :
    symRunBits [6, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symZero), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 0, 0, 1, 45⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0, 52⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z2_c2 :
    symRunBits [6, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 20⟩), .pair 1 2 (symZero),
      .pair 1 1 (symOne), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 0, 0, 1, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0,
        56⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z2_c3 :
    symRunBits [6, 4, 3, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 2), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 0, 0, 1, 46⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0,
        56⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z2_c4 :
    symRunBits [6, 5, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 20⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 3), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 0, 0, 1, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 4, 0, 0, 60⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ep12_z2_c5 :
    symRunBits [6, 5, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 45⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 19⟩),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨0, 0, 2, 0, 0, 19⟩), .pair 1 2 (symZero),
      .pair 1 1 (symConst 4), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 0, 1, 0, 19⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 0, 0, 1, 46⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (⟨0, 0, 4, 0, 0, 60⟩), .pair 1 0 (symZero)]) := rfl

private theorem eMidExtraPost0_to_M (M A Bd rC2 : ℕ)
    (hinv : InvEmidExtraPost0 M A Bd rC2) : ReachesInvM (eMidExtra0Cfg M A Bd rC2) := by
  rcases hinv with ⟨hrC2, hA, hM, hBd, h9M, h2120⟩
  match hr : rC2 with
  | 0 =>
    set v0 := A - 50; set v2 := Bd - 20; set v4 := M - 46
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 0 v4) rfl_ep0_c0) (eval_eMidExtra0_c0
      (v5 v0 0 v2 0 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      19⟩) M A Bd
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convEntry_2_z2 (v5 v0 0 v2 0 v4) 5 (symZero) (⟨0, 0, 1, 0, 0,
      19⟩) (symZero) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1,
      45⟩) (symConst 3) (v2 + 21) (2) (v0 + 50) (v4 + 46) (4)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := convEntryZ2_to_M 5 (v2 + 21) (v0 + 50) (v4 + 46) (4) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 1 =>
    set v0 := A - 50; set v2 := Bd - 20; set v4 := M - 46
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 0 v4) rfl_ep0_c1) (eval_eMidExtra0_c1
      (v5 v0 0 v2 0 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      19⟩) (symZero) M A Bd 1
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convEntry_2_z2 (v5 v0 0 v2 0 v4) 3 (symZero) (⟨0, 0, 1, 0, 0,
      20⟩) (symZero) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1,
      45⟩) (symConst 3) (v2 + 22) (2) (v0 + 50) (v4 + 46) (4)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := convEntryZ2_to_M 3 (v2 + 22) (v0 + 50) (v4 + 46) (4) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 2 =>
    set v0 := A - 50; set v2 := Bd - 20; set v4 := M - 46
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 0 v4) rfl_ep0_c2) (eval_eMidExtra0_c1
      (v5 v0 0 v2 0 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      19⟩) (symOne) M A Bd 2
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convEntry_2_z2 (v5 v0 0 v2 0 v4) 4 (symZero) (⟨0, 0, 1, 0, 0,
      21⟩) (symZero) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1,
      45⟩) (symConst 3) (v2 + 23) (2) (v0 + 50) (v4 + 46) (4)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := convEntryZ2_to_M 4 (v2 + 23) (v0 + 50) (v4 + 46) (4) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 3 =>
    set v0 := A - 50; set v2 := Bd - 20; set v4 := M - 46
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 0 v4) rfl_ep0_c3) (eval_eMidExtra0_c1
      (v5 v0 0 v2 0 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      19⟩) (symConst 2) M A Bd 3
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convEntry_2_z2 (v5 v0 0 v2 0 v4) 0 (symZero) (⟨0, 0, 1, 0, 0,
      22⟩) (symZero) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1,
      46⟩) (symConst 3) (v2 + 24) (2) (v0 + 50) (v4 + 47) (4)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := convEntryZ2_to_M 0 (v2 + 24) (v0 + 50) (v4 + 47) (4) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 4 =>
    set v0 := A - 50; set v2 := Bd - 20; set v4 := M - 46
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 0 v4) rfl_ep0_c4) (eval_eMidExtra0_c1
      (v5 v0 0 v2 0 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      19⟩) (symConst 3) M A Bd 4
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convEntry_2_z2 (v5 v0 0 v2 0 v4) 1 (symZero) (⟨0, 0, 1, 0, 0,
      23⟩) (symZero) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1,
      46⟩) (symConst 3) (v2 + 25) (2) (v0 + 50) (v4 + 47) (4)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := convEntryZ2_to_M 1 (v2 + 25) (v0 + 50) (v4 + 47) (4) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 5 =>
    set v0 := A - 50; set v2 := Bd - 20; set v4 := M - 46
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 0 v4) rfl_ep0_c5) (eval_eMidExtra0_c1
      (v5 v0 0 v2 0 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      19⟩) (symConst 4) M A Bd 5
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_convEntry_2_z2 (v5 v0 0 v2 0 v4) 2 (symZero) (⟨0, 0, 1, 0, 0,
      24⟩) (symZero) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1,
      46⟩) (symConst 3) (v2 + 26) (2) (v0 + 50) (v4 + 47) (4)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := convEntryZ2_to_M 2 (v2 + 26) (v0 + 50) (v4 + 47) (4) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 6 => omega

private theorem eMidExtraPost12_to_M (M A z Bm Bd rC2 : ℕ)
    (hinv : InvEmidExtraPost12 M A z Bm Bd rC2) : ReachesInvM (eMidExtra12Cfg M A z Bm Bd rC2) := by
  rcases hinv with ⟨hrC2, hz, hA, hM, hBm, hBd, hpar, h9M, h2120⟩
  match hz_eq : z with
  | 0 => omega
  | 1 =>
    match hr : rC2 with
    | 0 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ep12_z1_c0)
        (eval_eMidExtra12_z1_c0 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0, 20⟩) M A Bm Bd
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 3 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 45⟩) (⟨0, 0, 4, 0, 0,
        52⟩) (v3 + 21) (v0 + 50) (v4 + 46) (4 * v2 + 53)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 3 (v3 + 21) (1) (v0 + 50) (v4 + 46) (4 * v2 + 53) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 1 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ep12_z1_c1)
        (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        19⟩) (symZero) M A Bm Bd 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 4 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 45⟩) (⟨0, 0, 4, 0, 0,
        52⟩) (v3 + 21) (v0 + 50) (v4 + 46) (4 * v2 + 53)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 4 (v3 + 21) (1) (v0 + 50) (v4 + 46) (4 * v2 + 53) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 2 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ep12_z1_c2)
        (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        20⟩) (symOne) M A Bm Bd 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 0 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        56⟩) (v3 + 21) (v0 + 50) (v4 + 47) (4 * v2 + 57)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 0 (v3 + 21) (1) (v0 + 50) (v4 + 47) (4 * v2 + 57) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 3 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ep12_z1_c3)
        (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        19⟩) (symConst 2) M A Bm Bd 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 1 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        56⟩) (v3 + 21) (v0 + 50) (v4 + 47) (4 * v2 + 57)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 1 (v3 + 21) (1) (v0 + 50) (v4 + 47) (4 * v2 + 57) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 4 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ep12_z1_c4)
        (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        20⟩) (symConst 3) M A Bm Bd 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 2 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        60⟩) (v3 + 21) (v0 + 50) (v4 + 47) (4 * v2 + 61)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 2 (v3 + 21) (1) (v0 + 50) (v4 + 47) (4 * v2 + 61) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 5 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_ep12_z1_c5)
        (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        19⟩) (symConst 4) M A Bm Bd 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 5 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        60⟩) (v3 + 21) (v0 + 50) (v4 + 47) (4 * v2 + 61)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 5 (v3 + 21) (1) (v0 + 50) (v4 + 47) (4 * v2 + 61) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | _ + 6 => omega
  | v1 + 2 =>
    match hr : rC2 with
    | 0 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ep12_z2_c0)
        (eval_eMidExtra12_z2_c0 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        20⟩) M A (v1 + 2) Bm Bd
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 3 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 45⟩) (⟨0, 0, 4, 0, 0,
        52⟩) (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 46) (4 * v2 + 53)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 3 (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 46) (4 * v2 + 53) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 1 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ep12_z2_c1)
        (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        19⟩) (symZero) M A (v1 + 2) Bm Bd 1
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 4 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 45⟩) (⟨0, 0, 4, 0, 0,
        52⟩) (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 46) (4 * v2 + 53)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 4 (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 46) (4 * v2 + 53) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 2 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ep12_z2_c2)
        (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        20⟩) (symOne) M A (v1 + 2) Bm Bd 2
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 0 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        56⟩) (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 57)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 0 (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 57) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 3 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ep12_z2_c3)
        (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        19⟩) (symConst 2) M A (v1 + 2) Bm Bd 3
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 1 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        56⟩) (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 57)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 1 (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 57) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 4 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ep12_z2_c4)
        (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        20⟩) (symConst 3) M A (v1 + 2) Bm Bd 4
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 2 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        60⟩) (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 61)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 2 (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 61) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 5 =>
      set v0 := A - 50; set v2 := (Bd - 20) / 2; set v3 := Bm - 20; set v4 := M - 46
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_ep12_z2_c5)
        (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 45⟩) (⟨1, 0, 0, 0, 0,
        49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 19⟩) (⟨0, 0, 2, 0, 0,
        19⟩) (symConst 4) M A (v1 + 2) Bm Bd 5
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 5 (symZero) (⟨0, 0, 0, 1, 0,
        19⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 0, 1, 46⟩) (⟨0, 0, 4, 0, 0,
        60⟩) (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 61)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 5 (v3 + 21) (v1 + 2) (v0 + 50) (v4 + 47) (4 * v2 + 61) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | _ + 6 => omega

private theorem eMidExtra0_to_M (M A d C : ℕ)
    (hinv : InvEmidExtra0 M A d C) : ReachesInvM (eMidExtra0Cfg M A d C) := by
  rcases hinv with ⟨hd, hA, hC, h6MC, h18M, h2CA⟩
  set K := C / 6
  set rC2 := C % 6
  have hK : 1 ≤ K := by omega
  have hdiv : 6 * K + rC2 = C := by omega
  let ms : List MidItem := [.mid M, .t A, .mid 1, .z 1, .t d]
  let tw : TowerD01 := .d0 C [.pair 1 0 0]
  have hloop := era_E_loop ms tw (by simp [tw, TowerWF]) K (by simp [tw, maxReflD01]; omega)
  have h0 : eraECfg ms tw 0 = eMidExtra0Cfg M A d C := by
    dsimp only [eraECfg, ms, tw, encMidR, encMidItemR, buildAdvTowerD01, eMidExtra0Cfg]
    simp only [encR_pushRP, encR, pWord_1_2, pWord_1_1, pWord_1_0, add_one_0,
      pow_zero_list, pow_one_list, Nat.mul_zero, Nat.sub_zero, nil_append_lb]
  have hK_cfg : eraECfg ms tw K = eMidExtra0Cfg (M + K) A (d + 6 * K) rC2 := by
    dsimp only [eraECfg, ms, tw, encMidR, encMidItemR, buildAdvTowerD01, eMidExtra0Cfg]
    simp only [encR_pushRP, encR, pWord_1_2, pWord_1_1, pWord_1_0, add_one_0, pow_one_list]
    rw [pow_append_pow wRM K M, pow_append_pow wT d (6 * K)]
    have h1 : K + M = M + K := by omega
    have h2 : C - 6 * K = rC2 := by omega
    rw [h1, h2]
  rw [h0, hK_cfg] at hloop
  have hpos : 0 < K * (132 * w3Mid ms + 865) + 594 * K * (K - 1) + towerCostD01 tw (6 * K) := by
    have : 865 ≤ K * (132 * w3Mid ms + 865) := by
      calc 865 ≤ 1 * (132 * w3Mid ms + 865) := by omega
        _ ≤ K * (132 * w3Mid ms + 865) := Nat.mul_le_mul_right _ hK
    omega
  obtain ⟨m', z', c', k', hm', hrest⟩ := eMidExtraPost0_to_M (M + K) A (d + 6 * K) rC2
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  exact ⟨m', z', c', k', hm', (ReachesIn.to_plus hpos hloop).trans hrest⟩

private theorem eMidExtra12_to_M (M A z Bm d C : ℕ)
    (hinv : InvEmidExtra12 M A z Bm d C) : ReachesInvM (eMidExtra12Cfg M A z Bm d C) := by
  rcases hinv with ⟨hd, hz, hA, hBm, hC, h6MC, h18M, h2CBm, hpar⟩
  set K := C / 6
  set rC2 := C % 6
  have hK : 1 ≤ K := by omega
  have hdiv : 6 * K + rC2 = C := by omega
  let ms : List MidItem := [.mid M, .t A, .mid 1, .z (z - 1), .t Bm, .mid 1, .z 1, .t d]
  let tw : TowerD01 := .d0 C [.pair 1 0 0]
  have hloop := era_E_loop ms tw (by simp [tw, TowerWF]) K (by simp [tw, maxReflD01]; omega)
  have h0 : eraECfg ms tw 0 = eMidExtra12Cfg M A z Bm d C := by
    dsimp only [eraECfg, ms, tw, encMidR, encMidItemR, buildAdvTowerD01, eMidExtra12Cfg]
    simp only [encR_pushRP, encR, pWord_1_2, pWord_1_1, pWord_1_0, add_one_0,
      pow_zero_list, pow_one_list, Nat.mul_zero, Nat.sub_zero, nil_append_lb]
  have hK_cfg : eraECfg ms tw K = eMidExtra12Cfg (M + K) A z Bm (d + 6 * K) rC2 := by
    dsimp only [eraECfg, ms, tw, encMidR, encMidItemR, buildAdvTowerD01, eMidExtra12Cfg]
    simp only [encR_pushRP, encR, pWord_1_2, pWord_1_1, pWord_1_0, add_one_0, pow_one_list]
    rw [pow_append_pow wRM K M, pow_append_pow wT d (6 * K)]
    have h1 : K + M = M + K := by omega
    have h2 : C - 6 * K = rC2 := by omega
    rw [h1, h2]
  rw [h0, hK_cfg] at hloop
  have hpos : 0 < K * (132 * w3Mid ms + 865) + 594 * K * (K - 1) + towerCostD01 tw (6 * K) := by
    have : 865 ≤ K * (132 * w3Mid ms + 865) := by
      calc 865 ≤ 1 * (132 * w3Mid ms + 865) := by omega
        _ ≤ K * (132 * w3Mid ms + 865) := Nat.mul_le_mul_right _ hK
    omega
  obtain ⟨m', z', c', k', hm', hrest⟩ := eMidExtraPost12_to_M (M + K) A z Bm (d + 6 * K) rC2
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  exact ⟨m', z', c', k', hm', (ReachesIn.to_plus hpos hloop).trans hrest⟩

/-! #### Stage 4: `InvEmid0` & `InvEmid12` → `ReachesInvM` (72 `rfl` lemmas) -/
private theorem rfl_em_z0_c0_b0 :
    symRunBits [6, 5, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 59⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 6, 0, 0, 78⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 3), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 156⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c0_b1 :
    symRunBits [5, 4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 59⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 78⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c1_b0 :
    symRunBits [5, 4, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 60⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 81⟩), .mid (⟨0, 0, 1, 0, 1,
        23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0,
        12, 4, 0, 165⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c1_b1 :
    symRunBits [6, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 60⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 79⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c2_b0 :
    symRunBits [6, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 61⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 79⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c2_b1 :
    symRunBits [6, 5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 61⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 6, 0, 0, 79⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 2), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 161⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c3_b0 :
    symRunBits [6, 5, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 62⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 80⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c3_b1 :
    symRunBits [6, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 62⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 82⟩), .mid (⟨0, 0, 1, 0, 1,
        23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c4_b0 :
    symRunBits [7, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 63⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 6, 0, 0, 80⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symOne), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 162⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c4_b1 :
    symRunBits [6, 5, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 63⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 80⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c5_b0 :
    symRunBits [6, 5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 64⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 83⟩), .mid (⟨0, 0, 1, 0, 1,
        23⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c5_b1 :
    symRunBits [7, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 64⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 81⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c6_b0 :
    symRunBits [7, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 65⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 81⟩),
        .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c6_b1 :
    symRunBits [7, 4, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 65⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 6, 0, 0, 81⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symZero), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 167⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c7_b0 :
    symRunBits [7, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 66⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 82⟩),
        .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0,
        12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c7_b1 :
    symRunBits [7, 4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 66⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 84⟩), .mid (⟨0, 0, 1, 0, 1,
        24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c8_b0 :
    symRunBits [7, 6, 5, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 67⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 25⟩), .pair 1 1 (⟨1, 0, 6, 0, 0, 82⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 5), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 162⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c8_b1 :
    symRunBits [7, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 67⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 82⟩),
        .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0,
        12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c9_b0 :
    symRunBits [7, 5, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 68⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 85⟩), .mid (⟨0, 0, 1, 0, 1,
        24⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c9_b1 :
    symRunBits [7, 5, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 68⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 83⟩),
        .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0,
        12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c10_b0 :
    symRunBits [7, 6, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 69⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 83⟩),
        .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0,
        12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c10_b1 :
    symRunBits [7, 6, 5, 4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 69⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 25⟩), .pair 1 1 (⟨1, 0, 6, 0, 0, 83⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 4), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 167⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c11_b0 :
    symRunBits [7, 6, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 70⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 84⟩),
        .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z0_c11_b1 :
    symRunBits [7, 6, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 12, 0, 0, 70⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨1, 0, 6, 0, 0, 86⟩), .mid (⟨0, 0, 1, 0, 1,
        24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c0_b0 :
    symRunBits [6, 5, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 59⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 30⟩), .mid (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 3), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 4, 0, 156⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c0_b1 :
    symRunBits [5, 4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 59⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 30⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c1_b0 :
    symRunBits [5, 4, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 60⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 33⟩), .mid (symZero),
        .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 165⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c1_b1 :
    symRunBits [6, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 60⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 31⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 12, 4,
        0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c2_b0 :
    symRunBits [6, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 61⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 31⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 12, 4,
        0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c2_b1 :
    symRunBits [6, 5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 61⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 31⟩), .mid (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 2), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 4, 0, 161⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c3_b0 :
    symRunBits [6, 5, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 62⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 32⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c3_b1 :
    symRunBits [6, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 62⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 34⟩), .mid (symZero),
        .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4,
        0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c4_b0 :
    symRunBits [7, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 63⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 32⟩), .mid (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symOne), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 4, 0, 162⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c4_b1 :
    symRunBits [6, 5, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 63⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 32⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c5_b0 :
    symRunBits [6, 5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 64⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 35⟩), .mid (symZero),
        .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩), .pair 1 1 (symZero),
        .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12,
        4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c5_b1 :
    symRunBits [7, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 64⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 33⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c6_b0 :
    symRunBits [7, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 65⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 33⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c6_b1 :
    symRunBits [7, 4, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 65⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 33⟩), .mid (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 4, 0, 167⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c7_b0 :
    symRunBits [7, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 66⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 34⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c7_b1 :
    symRunBits [7, 4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 66⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 36⟩), .mid (symZero),
        .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c8_b0 :
    symRunBits [7, 6, 5, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 67⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 25⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 34⟩), .mid (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 5), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 4, 0, 162⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c8_b1 :
    symRunBits [7, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 67⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 34⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c9_b0 :
    symRunBits [7, 5, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 68⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 37⟩), .mid (symZero),
        .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero),
        .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c9_b1 :
    symRunBits [7, 5, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 68⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 35⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c10_b0 :
    symRunBits [7, 6, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 69⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 35⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c10_b1 :
    symRunBits [7, 6, 5, 4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 69⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 25⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 35⟩), .mid (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 4), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 4, 0, 167⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c11_b0 :
    symRunBits [7, 6, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 70⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 36⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z1_c11_b1 :
    symRunBits [7, 6, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2,
      0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 70⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 38⟩), .mid (symZero),
        .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (symZero),
        .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4,
        0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c0_b0 :
    symRunBits [6, 5, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 59⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 6, 0, 0, 30⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 3), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 156⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c0_b1 :
    symRunBits [5, 4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 59⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 30⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c1_b0 :
    symRunBits [5, 4, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 60⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 33⟩), .pair 1 1 (⟨0, 1, 0, 0, 0,
        0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (⟨0, 0, 12, 4,
        0, 165⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c1_b1 :
    symRunBits [6, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
      .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 60⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 31⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c2_b0 :
    symRunBits [6, 4] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
      .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 61⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 31⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c2_b1 :
    symRunBits [6, 5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 61⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 6, 0, 0, 31⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 2), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 161⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c3_b0 :
    symRunBits [6, 5, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
      .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 62⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 32⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c3_b1 :
    symRunBits [6, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 62⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 34⟩), .pair 1 1 (⟨0, 1, 0, 0, 0,
        0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c4_b0 :
    symRunBits [7, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 63⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 6, 0, 0, 32⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symOne), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 162⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c4_b1 :
    symRunBits [6, 5, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 63⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 32⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c5_b0 :
    symRunBits [6, 5, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 64⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 35⟩), .pair 1 1 (⟨0, 1, 0, 0, 0,
        0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 23⟩),
        .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 169⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c5_b1 :
    symRunBits [7, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
      .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 64⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 33⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c6_b0 :
    symRunBits [7, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 65⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 33⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 23⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c6_b1 :
    symRunBits [7, 4, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
      .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 65⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 24⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 6, 0, 0, 33⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symZero), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 167⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c7_b0 :
    symRunBits [7, 4, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 66⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 34⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0,
        173⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c7_b1 :
    symRunBits [7, 4, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 66⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 36⟩), .pair 1 1 (⟨0, 1, 0, 0, 0,
        0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c8_b0 :
    symRunBits [7, 6, 5, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 67⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 25⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 6, 0, 0, 34⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 5), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 162⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c8_b1 :
    symRunBits [7, 5, 3] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
      .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
      .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 12, 0, 0, 67⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 34⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0,
        177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c9_b0 :
    symRunBits [7, 5, 3, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 68⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 37⟩), .pair 1 1 (⟨0, 1, 0, 0, 0,
        0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 173⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c9_b1 :
    symRunBits [7, 5, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 68⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 35⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0,
        177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c10_b0 :
    symRunBits [7, 6, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 69⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 35⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0,
        177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c10_b1 :
    symRunBits [7, 6, 5, 4, 3, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 69⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨0, 0, 1, 0, 1, 25⟩), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 6, 0, 0, 35⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 4), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 12, 4, 0, 167⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c11_b0 :
    symRunBits [7, 6, 4, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 70⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 36⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 1, 24⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_em_z2_c11_b1 :
    symRunBits [7, 6, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (⟨0, 0, 0, 0, 1, 18⟩), .pair 1 1 (⟨1, 0, 0,
      0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne),
      .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 2, 0, 50⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0,
      12, 0, 0, 70⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (⟨0, 0, 6, 0, 0, 38⟩), .pair 1 1 (⟨0, 1, 0, 0, 0,
        0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 1, 24⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (⟨0, 0, 12, 4, 0, 177⟩), .pair 1 0 (symZero)]) := rfl

private theorem eMid0_lo_to_M (M A B C : ℕ)
    (hinv : InvEmid0 M A B C) (hlo : C % 12 < 6) : ReachesInvM (eMid0Cfg M A B C) := by
  rcases hinv with ⟨hA, hM, hB, hC, h12MC, h36M, h2120⟩
  match hrc : C % 12 with
  | 0 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c0_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 59⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra0_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 6, 0, 0,
        78⟩) (symConst 3) (⟨0, 0, 12, 4, 0,
        156⟩) (v2 + v4 + 25) (v0 + 6 * v2 + 79) (4) (12 * v2 + 4 * v3 + 157)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra0_to_M (v2 + v4 + 25) (v0 + 6 * v2 + 79) (4) (12 * v2 + 4 * v3 + 157) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c0_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 59⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 2 (symZero) (⟨1, 0, 6, 0, 0, 78⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (v0 + 6 * v2 + 80) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 2 (v0 + 6 * v2 + 80) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 1 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c1_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 60⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_1 (v5 v0 0 v2 v3 v4) 5 (⟨1, 0, 6, 0, 0, 81⟩) (⟨0, 0, 1, 0,
        1, 23⟩) (⟨0, 0, 12, 4, 0,
        165⟩) (v0 + 6 * v2 + 82) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 166)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 5 (v0 + 6 * v2 + 82) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 166) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c1_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 60⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 5 (symZero) (⟨1, 0, 6, 0, 0, 79⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (v0 + 6 * v2 + 81) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 5 (v0 + 6 * v2 + 81) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 2 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c2_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 61⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 5 (symZero) (⟨1, 0, 6, 0, 0, 79⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (v0 + 6 * v2 + 81) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 5 (v0 + 6 * v2 + 81) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c2_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 61⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra0_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 6, 0, 0,
        79⟩) (symConst 2) (⟨0, 0, 12, 4, 0,
        161⟩) (v2 + v4 + 25) (v0 + 6 * v2 + 80) (3) (12 * v2 + 4 * v3 + 162)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra0_to_M (v2 + v4 + 25) (v0 + 6 * v2 + 80) (3) (12 * v2 + 4 * v3 + 162) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 3 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c3_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 62⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 3 (symZero) (⟨1, 0, 6, 0, 0, 80⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (v0 + 6 * v2 + 82) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 3 (v0 + 6 * v2 + 82) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c3_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 62⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_1 (v5 v0 0 v2 v3 v4) 3 (⟨1, 0, 6, 0, 0, 82⟩) (⟨0, 0, 1, 0,
        1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (v0 + 6 * v2 + 83) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 3 (v0 + 6 * v2 + 83) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 4 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c4_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 63⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra0_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 6, 0, 0,
        80⟩) (symOne) (⟨0, 0, 12, 4, 0,
        162⟩) (v2 + v4 + 25) (v0 + 6 * v2 + 81) (2) (12 * v2 + 4 * v3 + 163)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra0_to_M (v2 + v4 + 25) (v0 + 6 * v2 + 81) (2) (12 * v2 + 4 * v3 + 163) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c4_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 63⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 3 (symZero) (⟨1, 0, 6, 0, 0, 80⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (v0 + 6 * v2 + 82) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 3 (v0 + 6 * v2 + 82) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 5 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c5_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 64⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_1 (v5 v0 0 v2 v3 v4) 4 (⟨1, 0, 6, 0, 0, 83⟩) (⟨0, 0, 1, 0,
        1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (v0 + 6 * v2 + 84) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 4 (v0 + 6 * v2 + 84) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c5_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 64⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 4 (symZero) (⟨1, 0, 6, 0, 0, 81⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (v0 + 6 * v2 + 83) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 4 (v0 + 6 * v2 + 83) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 6 => omega

private theorem eMid0_hi_to_M (M A B C : ℕ)
    (hinv : InvEmid0 M A B C) (hhi : 6 ≤ C % 12) : ReachesInvM (eMid0Cfg M A B C) := by
  rcases hinv with ⟨hA, hM, hB, hC, h12MC, h36M, h2120⟩
  match hrc : C % 12 with
  | 0 | 1 | 2 | 3 | 4 | 5 => omega
  | 6 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c6_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 65⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 4 (symZero) (⟨1, 0, 6, 0, 0, 81⟩) (⟨0,
        0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (v0 + 6 * v2 + 83) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 4 (v0 + 6 * v2 + 83) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c6_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 65⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra0_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 6, 0, 0,
        81⟩) (symZero) (⟨0, 0, 12, 4, 0,
        167⟩) (v2 + v4 + 25) (v0 + 6 * v2 + 82) (1) (12 * v2 + 4 * v3 + 168)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra0_to_M (v2 + v4 + 25) (v0 + 6 * v2 + 82) (1) (12 * v2 + 4 * v3 + 168) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 7 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c7_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 66⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 0 (symZero) (⟨1, 0, 6, 0, 0, 82⟩) (⟨0,
        0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (v0 + 6 * v2 + 84) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 0 (v0 + 6 * v2 + 84) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c7_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 66⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_1 (v5 v0 0 v2 v3 v4) 0 (⟨1, 0, 6, 0, 0, 84⟩) (⟨0, 0, 1, 0,
        1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (v0 + 6 * v2 + 85) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 0 (v0 + 6 * v2 + 85) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 8 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c8_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 67⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra0_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 25⟩) (⟨1, 0, 6, 0, 0,
        82⟩) (symConst 5) (⟨0, 0, 12, 4, 0,
        162⟩) (v2 + v4 + 26) (v0 + 6 * v2 + 83) (6) (12 * v2 + 4 * v3 + 163)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra0_to_M (v2 + v4 + 26) (v0 + 6 * v2 + 83) (6) (12 * v2 + 4 * v3 + 163) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c8_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 67⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 0 (symZero) (⟨1, 0, 6, 0, 0, 82⟩) (⟨0,
        0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (v0 + 6 * v2 + 84) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 0 (v0 + 6 * v2 + 84) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 9 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c9_b0) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0,
        0, 12, 0, 0, 68⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_1 (v5 v0 0 v2 v3 v4) 1 (⟨1, 0, 6, 0, 0, 85⟩) (⟨0, 0, 1, 0,
        1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (v0 + 6 * v2 + 86) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 1 (v0 + 6 * v2 + 86) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c9_b1) (eval_eMid0
        (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0,
        0, 12, 0, 0, 68⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 1 (symZero) (⟨1, 0, 6, 0, 0, 83⟩) (⟨0,
        0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (v0 + 6 * v2 + 85) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 1 (v0 + 6 * v2 + 85) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 10 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c10_b0)
        (eval_eMid0 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2,
        0, 49⟩) (⟨0, 0, 12, 0, 0, 69⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 1 (symZero) (⟨1, 0, 6, 0, 0, 83⟩) (⟨0,
        0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (v0 + 6 * v2 + 85) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 1 (v0 + 6 * v2 + 85) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c10_b1)
        (eval_eMid0 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2,
        0, 50⟩) (⟨0, 0, 12, 0, 0, 69⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra0_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 25⟩) (⟨1, 0, 6, 0, 0,
        83⟩) (symConst 4) (⟨0, 0, 12, 4, 0,
        167⟩) (v2 + v4 + 26) (v0 + 6 * v2 + 84) (5) (12 * v2 + 4 * v3 + 168)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra0_to_M (v2 + v4 + 26) (v0 + 6 * v2 + 84) (5) (12 * v2 + 4 * v3 + 168) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 11 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c11_b0)
        (eval_eMid0 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2,
        0, 49⟩) (⟨0, 0, 12, 0, 0, 70⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_2 (v5 v0 0 v2 v3 v4) 2 (symZero) (⟨1, 0, 6, 0, 0, 84⟩) (⟨0,
        0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (v0 + 6 * v2 + 86) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 2 (v0 + 6 * v2 + 86) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z0_c11_b1)
        (eval_eMid0 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 2,
        0, 50⟩) (⟨0, 0, 12, 0, 0, 70⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convSimple_1 (v5 v0 0 v2 v3 v4) 2 (⟨1, 0, 6, 0, 0, 86⟩) (⟨0, 0, 1, 0,
        1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (v0 + 6 * v2 + 87) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convSimple_to_M 2 (v0 + 6 * v2 + 87) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by omega,
        by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 12 => omega

private theorem eMid0_to_M (M A B C : ℕ)
    (hinv : InvEmid0 M A B C) : ReachesInvM (eMid0Cfg M A B C) := by
  by_cases h : C % 12 < 6
  · exact eMid0_lo_to_M M A B C hinv h
  · exact eMid0_hi_to_M M A B C hinv (by omega)

private theorem eMid12_z1_lo_to_M (M A B C : ℕ)
    (hinv : InvEmid12 M A 1 B C) (hlo : C % 12 < 6) : ReachesInvM (eMid12Cfg M A 1 B C) := by
  rcases hinv with ⟨_, hA, hM, hB, hC, h12MC, h36M, h1060⟩
  match hrc : C % 12 with
  | 0 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c0_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 59⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 6, 0, 0, 30⟩) (symConst 3) (⟨0, 0, 12, 4, 0,
        156⟩) (v2 + v4 + 25) (v0 + 50) (6 * v2 + 31) (4) (12 * v2 + 4 * v3 + 157)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) 1 (6 * v2 + 31) (4) (12 * v2 + 4 * v3 + 157) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c0_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 59⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 2 (symZero) (⟨0, 0, 6, 0, 0,
        30⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 32) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 2 (6 * v2 + 32) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 1 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c1_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 60⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z1 (v5 v0 0 v2 v3 v4) 5 (⟨0, 0, 6, 0, 0, 33⟩) (⟨1, 0, 0, 0,
        0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        165⟩) (6 * v2 + 34) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 166)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 5 (6 * v2 + 34) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 166) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c1_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 60⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 5 (symZero) (⟨0, 0, 6, 0, 0,
        31⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 33) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 5 (6 * v2 + 33) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 2 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c2_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 61⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 5 (symZero) (⟨0, 0, 6, 0, 0,
        31⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 33) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 5 (6 * v2 + 33) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c2_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 61⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 6, 0, 0, 31⟩) (symConst 2) (⟨0, 0, 12, 4, 0,
        161⟩) (v2 + v4 + 25) (v0 + 50) (6 * v2 + 32) (3) (12 * v2 + 4 * v3 + 162)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) 1 (6 * v2 + 32) (3) (12 * v2 + 4 * v3 + 162) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 3 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c3_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 62⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 3 (symZero) (⟨0, 0, 6, 0, 0,
        32⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 34) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 3 (6 * v2 + 34) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c3_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 62⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z1 (v5 v0 0 v2 v3 v4) 3 (⟨0, 0, 6, 0, 0, 34⟩) (⟨1, 0, 0, 0,
        0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 35) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 3 (6 * v2 + 35) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 4 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c4_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 63⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 6, 0, 0, 32⟩) (symOne) (⟨0, 0, 12, 4, 0,
        162⟩) (v2 + v4 + 25) (v0 + 50) (6 * v2 + 33) (2) (12 * v2 + 4 * v3 + 163)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) 1 (6 * v2 + 33) (2) (12 * v2 + 4 * v3 + 163) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c4_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 63⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 3 (symZero) (⟨0, 0, 6, 0, 0,
        32⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 34) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 3 (6 * v2 + 34) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 5 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c5_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 64⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z1 (v5 v0 0 v2 v3 v4) 4 (⟨0, 0, 6, 0, 0, 35⟩) (⟨1, 0, 0, 0,
        0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 36) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 4 (6 * v2 + 36) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c5_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 64⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 4 (symZero) (⟨0, 0, 6, 0, 0,
        33⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 35) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 4 (6 * v2 + 35) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 6 => omega

private theorem eMid12_z1_hi_to_M (M A B C : ℕ)
    (hinv : InvEmid12 M A 1 B C) (hhi : 6 ≤ C % 12) : ReachesInvM (eMid12Cfg M A 1 B C) := by
  rcases hinv with ⟨_, hA, hM, hB, hC, h12MC, h36M, h1060⟩
  match hrc : C % 12 with
  | 0 | 1 | 2 | 3 | 4 | 5 => omega
  | 6 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c6_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 65⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 4 (symZero) (⟨0, 0, 6, 0, 0,
        33⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 35) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 4 (6 * v2 + 35) (1) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c6_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 65⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 6, 0, 0, 33⟩) (symZero) (⟨0, 0, 12, 4, 0,
        167⟩) (v2 + v4 + 25) (v0 + 50) (6 * v2 + 34) (1) (12 * v2 + 4 * v3 + 168)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) 1 (6 * v2 + 34) (1) (12 * v2 + 4 * v3 + 168) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 7 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c7_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 66⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 0 (symZero) (⟨0, 0, 6, 0, 0,
        34⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 36) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 0 (6 * v2 + 36) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c7_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 66⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z1 (v5 v0 0 v2 v3 v4) 0 (⟨0, 0, 6, 0, 0, 36⟩) (⟨1, 0, 0, 0,
        0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 37) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 0 (6 * v2 + 37) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 8 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c8_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 67⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 25⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 6, 0, 0, 34⟩) (symConst 5) (⟨0, 0, 12, 4, 0,
        162⟩) (v2 + v4 + 26) (v0 + 50) (6 * v2 + 35) (6) (12 * v2 + 4 * v3 + 163)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 26) (v0 + 50) 1 (6 * v2 + 35) (6) (12 * v2 + 4 * v3 + 163) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c8_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 67⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 0 (symZero) (⟨0, 0, 6, 0, 0,
        34⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 36) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 0 (6 * v2 + 36) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 9 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c9_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 68⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z1 (v5 v0 0 v2 v3 v4) 1 (⟨0, 0, 6, 0, 0, 37⟩) (⟨1, 0, 0, 0,
        0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 38) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 1 (6 * v2 + 38) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c9_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 68⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 1 (symZero) (⟨0, 0, 6, 0, 0,
        35⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 37) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 1 (6 * v2 + 37) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 10 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c10_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 69⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 1 (symZero) (⟨0, 0, 6, 0, 0,
        35⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 37) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 1 (6 * v2 + 37) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c10_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 69⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z1_c1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 1, 0, 1, 25⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 0, 6, 0, 0, 35⟩) (symConst 4) (⟨0, 0, 12, 4, 0,
        167⟩) (v2 + v4 + 26) (v0 + 50) (6 * v2 + 36) (5) (12 * v2 + 4 * v3 + 168)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 26) (v0 + 50) 1 (6 * v2 + 36) (5) (12 * v2 + 4 * v3 + 168) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 11 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c11_b0)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 49⟩) (⟨0, 0, 12, 0, 0, 70⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 v4) 2 (symZero) (⟨0, 0, 6, 0, 0,
        36⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 38) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 2 (6 * v2 + 38) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 v4) rfl_em_z1_c11_b1)
        (eval_eMid12_z1 (v5 v0 0 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0,
        2, 0, 50⟩) (⟨0, 0, 12, 0, 0, 70⟩) M A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z1 (v5 v0 0 v2 v3 v4) 2 (⟨0, 0, 6, 0, 0, 38⟩) (⟨1, 0, 0, 0,
        0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 39) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 2 (6 * v2 + 39) (1) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178) ⟨by
        omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 12 => omega

private theorem eMid12_z2_lo_to_M (M A v1 B C : ℕ)
    (hinv : InvEmid12 M A (v1 + 2) B C) (hlo : C % 12 < 6) : ReachesInvM (eMid12Cfg M A (v1 + 2) B
      C) := by
  rcases hinv with ⟨_, hA, hM, hB, hC, h12MC, h36M, h1060⟩
  match hrc : C % 12 with
  | 0 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c0_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        59⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 6, 0, 0, 30⟩) (symConst 3) (⟨0, 0, 12, 4, 0,
        156⟩) (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 31) (4) (12 * v2 + 4 * v3 + 157)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 31) (4) (12 * v2 + 4 * v3 +
        157) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c0_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        59⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 2 (symZero) (⟨0, 0, 6, 0, 0,
        30⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 32) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 2 (6 * v2 + 32) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 1 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c1_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        60⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z2 (v5 v0 v1 v2 v3 v4) 5 (⟨0, 0, 6, 0, 0, 33⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        165⟩) (6 * v2 + 34) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 166)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 5 (6 * v2 + 34) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 166)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c1_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        60⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 5 (symZero) (⟨0, 0, 6, 0, 0,
        31⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 33) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 5 (6 * v2 + 33) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 2 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c2_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        61⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 5 (symZero) (⟨0, 0, 6, 0, 0,
        31⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 33) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 5 (6 * v2 + 33) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c2_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        61⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 6, 0, 0, 31⟩) (symConst 2) (⟨0, 0, 12, 4, 0,
        161⟩) (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 32) (3) (12 * v2 + 4 * v3 + 162)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 32) (3) (12 * v2 + 4 * v3 +
        162) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 3 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c3_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        62⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 3 (symZero) (⟨0, 0, 6, 0, 0,
        32⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 34) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 3 (6 * v2 + 34) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c3_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        62⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z2 (v5 v0 v1 v2 v3 v4) 3 (⟨0, 0, 6, 0, 0, 34⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 35) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 3 (6 * v2 + 35) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 4 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c4_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        63⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 6, 0, 0, 32⟩) (symOne) (⟨0, 0, 12, 4, 0,
        162⟩) (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 33) (2) (12 * v2 + 4 * v3 + 163)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 33) (2) (12 * v2 + 4 * v3 +
        163) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c4_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        63⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 3 (symZero) (⟨0, 0, 6, 0, 0,
        32⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 34) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 3 (6 * v2 + 34) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 5 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c5_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        64⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z2 (v5 v0 v1 v2 v3 v4) 4 (⟨0, 0, 6, 0, 0, 35⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        169⟩) (6 * v2 + 36) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 4 (6 * v2 + 36) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 170)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c5_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        64⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 4 (symZero) (⟨0, 0, 6, 0, 0,
        33⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 35) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 4 (6 * v2 + 35) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 6 => omega

private theorem eMid12_z2_hi_to_M (M A v1 B C : ℕ)
    (hinv : InvEmid12 M A (v1 + 2) B C) (hhi : 6 ≤ C % 12) : ReachesInvM (eMid12Cfg M A (v1 + 2) B
      C) := by
  rcases hinv with ⟨_, hA, hM, hB, hC, h12MC, h36M, h1060⟩
  match hrc : C % 12 with
  | 0 | 1 | 2 | 3 | 4 | 5 => omega
  | 6 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c6_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        65⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 4 (symZero) (⟨0, 0, 6, 0, 0,
        33⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 23⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 35) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 4 (6 * v2 + 35) (v1 + 2) (v0 + 50) (v2 + v4 + 24) (12 * v2 + 4 * v3 + 174)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c6_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        65⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 1, 0, 1, 24⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 6, 0, 0, 33⟩) (symZero) (⟨0, 0, 12, 4, 0,
        167⟩) (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 34) (1) (12 * v2 + 4 * v3 + 168)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 25) (v0 + 50) (v1 + 2) (6 * v2 + 34) (1) (12 * v2 + 4 * v3 +
        168) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 7 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c7_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        66⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 0 (symZero) (⟨0, 0, 6, 0, 0,
        34⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 36) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 0 (6 * v2 + 36) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c7_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        66⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z2 (v5 v0 v1 v2 v3 v4) 0 (⟨0, 0, 6, 0, 0, 36⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 37) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 0 (6 * v2 + 37) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 8 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c8_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        67⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 1, 0, 1, 25⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 6, 0, 0, 34⟩) (symConst 5) (⟨0, 0, 12, 4, 0,
        162⟩) (v2 + v4 + 26) (v0 + 50) (v1 + 2) (6 * v2 + 35) (6) (12 * v2 + 4 * v3 + 163)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 26) (v0 + 50) (v1 + 2) (6 * v2 + 35) (6) (12 * v2 + 4 * v3 +
        163) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c8_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        67⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 0 (symZero) (⟨0, 0, 6, 0, 0,
        34⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 36) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 0 (6 * v2 + 36) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 9 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c9_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        68⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z2 (v5 v0 v1 v2 v3 v4) 1 (⟨0, 0, 6, 0, 0, 37⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        173⟩) (6 * v2 + 38) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 1 (6 * v2 + 38) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 174)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c9_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        68⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 1 (symZero) (⟨0, 0, 6, 0, 0,
        35⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 37) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 1 (6 * v2 + 37) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 10 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c10_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        69⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 1 (symZero) (⟨0, 0, 6, 0, 0,
        35⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 37) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 1 (6 * v2 + 37) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c10_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        69⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eMidExtra12_z2_c1 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 1, 0, 1, 25⟩) (⟨1, 0, 0,
        0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 6, 0, 0, 35⟩) (symConst 4) (⟨0, 0, 12, 4, 0,
        167⟩) (v2 + v4 + 26) (v0 + 50) (v1 + 2) (6 * v2 + 36) (5) (12 * v2 + 4 * v3 + 168)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        eMidExtra12_to_M (v2 + v4 + 26) (v0 + 50) (v1 + 2) (6 * v2 + 36) (5) (12 * v2 + 4 * v3 +
        168) ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 11 =>
    have hB_mod : B % 2 = 0 ∨ B % 2 = 1 := by omega
    rcases hB_mod with hrB | hrB
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c11_b0)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 49⟩) (⟨0, 0, 12, 0, 0,
        70⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 v4) 2 (symZero) (⟨0, 0, 6, 0, 0,
        36⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 38) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 2 (6 * v2 + 38) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    · set v0 := A - 50; set v2 := (C - 60) / 12; set v3 := (B - 50) / 2; set v4 := M - 19
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 v4) rfl_em_z2_c11_b1)
        (eval_eMid12_z2 (v5 v0 v1 v2 v3 v4) (⟨0, 0, 0, 0, 1, 18⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨0, 0, 0, 2, 0, 50⟩) (⟨0, 0, 12, 0, 0,
        70⟩) M A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_1_z2 (v5 v0 v1 v2 v3 v4) 2 (⟨0, 0, 6, 0, 0, 38⟩) (⟨0, 1, 0,
        0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 1, 24⟩) (⟨0, 0, 12, 4, 0,
        177⟩) (6 * v2 + 39) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        convEntry_to_M 2 (6 * v2 + 39) (v1 + 2) (v0 + 50) (v2 + v4 + 25) (12 * v2 + 4 * v3 + 178)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 12 => omega

private theorem eMid12_to_M (M A z B C : ℕ)
    (hinv : InvEmid12 M A z B C) : ReachesInvM (eMid12Cfg M A z B C) := by
  match z with
  | 0 => rcases hinv with ⟨hz, _⟩; omega
  | 1 =>
    by_cases h : C % 12 < 6
    · exact eMid12_z1_lo_to_M M A B C hinv h
    · exact eMid12_z1_hi_to_M M A B C hinv (by omega)
  | v1 + 2 =>
    by_cases h : C % 12 < 6
    · exact eMid12_z2_lo_to_M M A v1 B C hinv h
    · exact eMid12_z2_hi_to_M M A v1 B C hinv (by omega)

/-! #### Stage 3: `InvEclean` → `ReachesInvM` (12 `rfl` lemmas) -/
private theorem rfl_ec_z1_c0 :
    symRunBits [4, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0,
      1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 281⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 331⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z1_c1 :
    symRunBits [5, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 282⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 332⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z1_c2 :
    symRunBits [5, 4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 283⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 333⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 46⟩),
        .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z1_c3 :
    symRunBits [6, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0,
      1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 284⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 334⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 47⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z1_c4 :
    symRunBits [6, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 285⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 335⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 47⟩),
        .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z1_c5 :
    symRunBits [6, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0, 286⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 336⟩),
        .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0, 0, 1, 0, 0, 47⟩),
        .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z2_c0 :
    symRunBits [4, 3, 2] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0,
      0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0,
      281⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 331⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 0 (symOne)],
        [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z2_c1 :
    symRunBits [5, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 6, 0, 0, 282⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 332⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 2 0 (symZero), .pair 3 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z2_c2 :
    symRunBits [5, 4, 2, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 6, 0, 0, 283⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 333⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 0, 46⟩), .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z2_c3 :
    symRunBits [6, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0,
      0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 6, 0, 0,
      284⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 334⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 0, 47⟩), .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z2_c4 :
    symRunBits [6, 3, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 6, 0, 0, 285⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 335⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 0, 47⟩), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 1 (symConst 3),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_ec_z2_c5 :
    symRunBits [6, 4, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (⟨1, 0, 0, 0, 0, 49⟩), .mid (symZero),
      .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 6, 0, 0, 286⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 2 0 (⟨0, 0, 6, 1, 0, 336⟩),
        .pair 1 1 (⟨0, 1, 0, 0, 0, 0⟩), .mid (symZero), .pair 2 0 (⟨1, 0, 0, 0, 0, 49⟩), .mid (⟨0,
        0, 1, 0, 0, 47⟩), .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 1 (symConst 3), .pair 1 0 (symZero)]) := rfl

private theorem eClean_to_M (A z B C : ℕ)
    (hinv : InvEclean A z B C) : ReachesInvM (eCleanCfg A z B C) := by
  rcases hinv with ⟨hz, hA, hB, hC, h1060⟩
  match hz_eq : z with
  | 0 => omega
  | 1 =>
    match hrc : C % 6 with
    | 0 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_ec_z1_c0) (eval_eClean_z1
        (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 6, 0, 0,
        281⟩) A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 0) 5 (symZero) (⟨0, 0, 6, 1, 0,
        331⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        46⟩) (symConst 3) (6 * v2 + v3 + 333) (v0 + 50) (v2 + 47) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 5 (6 * v2 + v3 + 333) (1) (v0 + 50) (v2 + 47) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 1 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_ec_z1_c1) (eval_eClean_z1
        (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 6, 0, 0,
        282⟩) A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 0) 3 (symZero) (⟨0, 0, 6, 1, 0,
        332⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        46⟩) (symConst 3) (6 * v2 + v3 + 334) (v0 + 50) (v2 + 47) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 3 (6 * v2 + v3 + 334) (1) (v0 + 50) (v2 + 47) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 2 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_ec_z1_c2) (eval_eClean_z1
        (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 6, 0, 0,
        283⟩) A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 0) 4 (symZero) (⟨0, 0, 6, 1, 0,
        333⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        46⟩) (symConst 3) (6 * v2 + v3 + 335) (v0 + 50) (v2 + 47) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 4 (6 * v2 + v3 + 335) (1) (v0 + 50) (v2 + 47) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 3 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_ec_z1_c3) (eval_eClean_z1
        (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 6, 0, 0,
        284⟩) A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 0) 0 (symZero) (⟨0, 0, 6, 1, 0,
        334⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        47⟩) (symConst 3) (6 * v2 + v3 + 336) (v0 + 50) (v2 + 48) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 0 (6 * v2 + v3 + 336) (1) (v0 + 50) (v2 + 48) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 4 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_ec_z1_c4) (eval_eClean_z1
        (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 6, 0, 0,
        285⟩) A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 0) 1 (symZero) (⟨0, 0, 6, 1, 0,
        335⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        47⟩) (symConst 3) (6 * v2 + v3 + 337) (v0 + 50) (v2 + 48) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 1 (6 * v2 + v3 + 337) (1) (v0 + 50) (v2 + 48) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 5 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_ec_z1_c5) (eval_eClean_z1
        (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 6, 0, 0,
        286⟩) A B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z1 (v5 v0 0 v2 v3 0) 2 (symZero) (⟨0, 0, 6, 1, 0,
        336⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        47⟩) (symConst 3) (6 * v2 + v3 + 338) (v0 + 50) (v2 + 48) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 2 (6 * v2 + v3 + 338) (1) (v0 + 50) (v2 + 48) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | _ + 6 => omega
  | v1 + 2 =>
    match hrc : C % 6 with
    | 0 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_ec_z2_c0)
        (eval_eClean_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0,
        1, 0, 49⟩) (⟨0, 0, 6, 0, 0, 281⟩) A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 0) 5 (symZero) (⟨0, 0, 6, 1, 0,
        331⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        46⟩) (symConst 3) (6 * v2 + v3 + 333) (v1 + 2) (v0 + 50) (v2 + 47) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 5 (6 * v2 + v3 + 333) (v1 + 2) (v0 + 50) (v2 + 47) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 1 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_ec_z2_c1)
        (eval_eClean_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0,
        1, 0, 49⟩) (⟨0, 0, 6, 0, 0, 282⟩) A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 0) 3 (symZero) (⟨0, 0, 6, 1, 0,
        332⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        46⟩) (symConst 3) (6 * v2 + v3 + 334) (v1 + 2) (v0 + 50) (v2 + 47) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 3 (6 * v2 + v3 + 334) (v1 + 2) (v0 + 50) (v2 + 47) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 2 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_ec_z2_c2)
        (eval_eClean_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0,
        1, 0, 49⟩) (⟨0, 0, 6, 0, 0, 283⟩) A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 0) 4 (symZero) (⟨0, 0, 6, 1, 0,
        333⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        46⟩) (symConst 3) (6 * v2 + v3 + 335) (v1 + 2) (v0 + 50) (v2 + 47) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 4 (6 * v2 + v3 + 335) (v1 + 2) (v0 + 50) (v2 + 47) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 3 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_ec_z2_c3)
        (eval_eClean_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0,
        1, 0, 49⟩) (⟨0, 0, 6, 0, 0, 284⟩) A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 0) 0 (symZero) (⟨0, 0, 6, 1, 0,
        334⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        47⟩) (symConst 3) (6 * v2 + v3 + 336) (v1 + 2) (v0 + 50) (v2 + 48) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 0 (6 * v2 + v3 + 336) (v1 + 2) (v0 + 50) (v2 + 48) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 4 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_ec_z2_c4)
        (eval_eClean_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0,
        1, 0, 49⟩) (⟨0, 0, 6, 0, 0, 285⟩) A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 0) 1 (symZero) (⟨0, 0, 6, 1, 0,
        335⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        47⟩) (symConst 3) (6 * v2 + v3 + 337) (v1 + 2) (v0 + 50) (v2 + 48) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 1 (6 * v2 + v3 + 337) (v1 + 2) (v0 + 50) (v2 + 48) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | 5 =>
      set v0 := A - 50; set v2 := (C - 282) / 6; set v3 := B - 50
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_ec_z2_c5)
        (eval_eClean_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0,
        1, 0, 49⟩) (⟨0, 0, 6, 0, 0, 286⟩) A (v1 + 2) B C
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_convEntry_2_z2 (v5 v0 v1 v2 v3 0) 2 (symZero) (⟨0, 0, 6, 1, 0,
        336⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨1, 0, 0, 0, 0, 49⟩) (⟨0, 0, 1, 0, 0,
        47⟩) (symConst 3) (6 * v2 + v3 + 338) (v1 + 2) (v0 + 50) (v2 + 48) (4)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := convEntry_to_M 2 (6 * v2 + v3 + 338) (v1 + 2) (v0 + 50) (v2 + 48) (4) ⟨by omega,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | _ + 6 => omega

/-! #### Stage 2: `e0111Cfg` & `e0101Cfg` → `ReachesInvM` (6 `rfl` lemmas) -/
private theorem rfl_e0111_z1 :
    symRunBits [6, 5, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero),
      .pair 1 1 (⟨6, 0, 0, 0, 0, 107⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨1, 0, 0, 0, 0, 18⟩), .pair 1 1 (⟨6, 0, 0, 0, 0, 121⟩),
        .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 52⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0,
        0, 1, 0, 0, 93⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_e0111_z2 :
    symRunBits [7, 2, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0,
      109⟩), .pair 2 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨1, 0, 0, 0, 0, 18⟩), .pair 1 1 (⟨6, 0, 0, 0, 0, 116⟩),
        .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨0, 0, 0, 1, 0, 54⟩),
        .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 92⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_e0111_z3 :
    symRunBits [7, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero),
      .pair 1 1 (⟨6, 0, 0, 0, 0, 109⟩), .pair 2 0 (symConst 2), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨1, 0, 0, 0, 0, 18⟩), .pair 1 1 (⟨6, 0, 0, 0, 0, 116⟩),
        .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne),
        .pair 1 1 (⟨0, 0, 0, 1, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 92⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_e0111_z4 :
    symRunBits [7, 2, 1, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero),
      .pair 1 1 (⟨6, 0, 0, 0, 0, 109⟩), .pair 2 0 (⟨0, 1, 0, 0, 0, 3⟩), .pair 1 1 (⟨0, 0, 0, 1, 0,
      49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨1, 0, 0, 0, 0, 18⟩), .pair 1 1 (⟨6, 0, 0, 0, 0, 116⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
        .pair 1 1 (⟨0, 0, 0, 1, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 92⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_e0101_z1 :
    symRunBits [7, 5, 4, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 8), .pair 1 0 (symOne),
      .pair 1 1 (⟨6, 0, 0, 0, 0, 115⟩), .mid (symZero), .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩),
      .pair 1 2 (symZero), .pair 1 1 (⟨12, 0, 1, 0, 0, 309⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨1, 0, 0, 0, 0, 19⟩), .pair 1 1 (⟨6, 0, 0, 0, 0, 124⟩),
        .mid (symZero), .pair 1 1 (symOne), .pair 1 0 (symOne), .pair 1 1 (⟨12, 0, 0, 1, 0, 287⟩),
        .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 69⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_e0101_z2 :
    symRunBits [7, 5, 4, 3, 1] (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)],
      [.pair 1 1 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 8), .pair 1 0 (symOne),
      .pair 1 1 (⟨6, 0, 0, 0, 0, 115⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩),
      .pair 1 1 (⟨0, 0, 0, 1, 0, 49⟩), .pair 1 2 (symZero), .pair 1 1 (⟨12, 0, 1, 0, 0, 309⟩),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .mid (⟨1, 0, 0, 0, 0, 19⟩), .pair 1 1 (⟨6, 0, 0, 0, 0, 124⟩),
        .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (symOne), .pair 1 0 (symOne),
        .pair 1 1 (⟨12, 0, 0, 1, 0, 287⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 69⟩),
        .pair 1 0 (symZero)]) := rfl

private theorem e0111_to_M (v0 z B C : ℕ)
    (hz : 1 ≤ z) (hB : 50 ≤ B) (hC : 100 ≤ C)
    (h12 : 340 ≤ 12 * v0 + C) (h36 : 36 * v0 + 765 ≤ 3 * C + 4 * B)
    (h36_0 : 12 * v0 + 180 ≤ C + 4 * B) (h1060 : 1070 ≤ C + B) :
    ReachesInvM (e0111Cfg (6 * v0 + 110) z B C) := by
  match hz_eq : z with
  | 0 => omega
  | 1 =>
    set v2 := C - 100; set v3 := B - 50
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_e0111_z1) (eval_e0111_z1
      (v5 v0 0 v2 v3 0) (⟨6, 0, 0, 0, 0, 107⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      99⟩) (6 * v0 + 110) B C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_eMid0 (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 18⟩) (⟨6, 0, 0, 0, 0, 121⟩) (⟨0,
      0, 0, 1, 0, 52⟩) (⟨0, 0, 1, 0, 0,
      93⟩) (v0 + 19) (6 * v0 + 122) (v3 + 53) (v2 + 94)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := eMid0_to_M (v0 + 19) (6 * v0 + 122) (v3 + 53) (v2 + 94) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 2 =>
    set v2 := C - 100; set v3 := B - 50
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_e0111_z2) (eval_e0111_z2
      (v5 v0 0 v2 v3 0) (⟨6, 0, 0, 0, 0, 109⟩) (symOne) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      99⟩) (6 * v0 + 110) (2) B C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_eMid12_z1 (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 18⟩) (⟨6, 0, 0, 0, 0,
      116⟩) (⟨0, 0, 0, 1, 0, 54⟩) (⟨0, 0, 1, 0, 0,
      92⟩) (v0 + 19) (6 * v0 + 117) (v3 + 55) (v2 + 93)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := eMid12_to_M (v0 + 19) (6 * v0 + 117) 1 (v3 + 55) (v2 + 93) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 3 =>
    set v2 := C - 100; set v3 := B - 50
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_e0111_z3) (eval_e0111_z2
      (v5 v0 0 v2 v3 0) (⟨6, 0, 0, 0, 0, 109⟩) (symConst 2) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0, 1, 0, 0,
      99⟩) (6 * v0 + 110) (3) B C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_eMid12_z2 (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 18⟩) (⟨6, 0, 0, 0, 0,
      116⟩) (symZero) (⟨0, 0, 0, 1, 0, 54⟩) (⟨0, 0, 1, 0, 0,
      92⟩) (v0 + 19) (6 * v0 + 117) (2) (v3 + 55) (v2 + 93)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := eMid12_to_M (v0 + 19) (6 * v0 + 117) (2) (v3 + 55) (v2 + 93) ⟨by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 4 =>
    set v2 := C - 100; set v3 := B - 50
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_e0111_z4) (eval_e0111_z2
      (v5 v0 v1 v2 v3 0) (⟨6, 0, 0, 0, 0, 109⟩) (⟨0, 1, 0, 0, 0, 3⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨0, 0,
      1, 0, 0, 99⟩) (6 * v0 + 110) (v1 + 4) B C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_eMid12_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 18⟩) (⟨6, 0, 0, 0, 0,
      116⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨0, 0, 0, 1, 0, 54⟩) (⟨0, 0, 1, 0, 0,
      92⟩) (v0 + 19) (6 * v0 + 117) (v1 + 3) (v3 + 55) (v2 + 93)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := eMid12_to_M (v0 + 19) (6 * v0 + 117) (v1 + 3) (v3 + 55) (v2 + 93) ⟨by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

private theorem e0101_to_M (v0 z B C : ℕ)
    (hz : 1 ≤ z) (hB : 50 ≤ B) (hC : 12 * v0 + 310 ≤ C) (hC560 : 560 ≤ C) (h1060 : 1062 ≤ C + B) :
    ReachesInvM (e0101Cfg (6 * v0 + 116) z B C) := by
  match hz_eq : z with
  | 0 => omega
  | 1 =>
    set v2 := C - 12 * v0 - 310; set v3 := B - 50
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 0 v2 v3 0) rfl_e0101_z1) (eval_e0101_z1
      (v5 v0 0 v2 v3 0) (⟨6, 0, 0, 0, 0, 115⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨12, 0, 1, 0, 0,
      309⟩) (6 * v0 + 116) B C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_eMid12_z1 (v5 v0 0 v2 v3 0) (⟨1, 0, 0, 0, 0, 19⟩) (⟨6, 0, 0, 0, 0,
      124⟩) (⟨12, 0, 0, 1, 0, 287⟩) (⟨0, 0, 1, 0, 0,
      69⟩) (v0 + 20) (6 * v0 + 125) (12 * v0 + v3 + 288) (v2 + 70)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ := eMid12_to_M (v0 + 20) (6 * v0 + 125) (1) (12 * v0 + v3 + 288) (v2 + 70) ⟨by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | v1 + 2 =>
    set v2 := C - 12 * v0 - 310; set v3 := B - 50
    have hstep :=
      reachesPlus_eq_both (symRunBits_sound_plus (v5 v0 v1 v2 v3 0) rfl_e0101_z2) (eval_e0101_z2
      (v5 v0 v1 v2 v3 0) (⟨6, 0, 0, 0, 0, 115⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨0, 0, 0, 1, 0, 49⟩) (⟨12,
      0, 1, 0, 0, 309⟩) (6 * v0 + 116) (v1 + 2) B C
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by
          dsimp only [evalSymN, symZero, symOne, symConst, v5]
          omega)) (eval_eMid12_z2 (v5 v0 v1 v2 v3 0) (⟨1, 0, 0, 0, 0, 19⟩) (⟨6, 0, 0, 0, 0,
      124⟩) (⟨0, 1, 0, 0, 0, 0⟩) (⟨12, 0, 0, 1, 0, 287⟩) (⟨0, 0, 1, 0, 0,
      69⟩) (v0 + 20) (6 * v0 + 125) (v1 + 2) (12 * v0 + v3 + 288) (v2 + 70)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
        (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
    obtain ⟨m', z', c', k', hm',
      hrest⟩ :=
      eMid12_to_M (v0 + 20) (6 * v0 + 125) (v1 + 2) (12 * v0 + v3 + 288) (v2 + 70) ⟨by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨m', z', c', k', hm', hstep.trans hrest⟩

/-! #### Stage 1: `InvM` → `postL11Cfg` →
  `ReachesInvM` (22 `rfl` lemmas + direct `era_L11_d0_loop`) -/
private theorem rfl_s1_r0_z1 :
    symRunBits [6, 4, 2, 1, 0] (.mA, [.pair 1 0 (symZero), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero), .pair 1 1 (⟨6, 0, 0, 0,
        0, 107⟩), .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 55⟩), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 1, 0, 0, 98⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r0_z2 :
    symRunBits [6, 4, 2, 1, 0] (.mA, [.pair 1 0 (symZero), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero), .pair 1 1 (⟨6, 0, 0, 0,
        0, 109⟩), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 55⟩),
        .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 98⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r1_z1 :
    symRunBits [6, 5, 3, 2, 1] (.mA, [.pair 1 0 (symZero), .mid (symZero), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 118⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 64⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 89⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r1_z2 :
    symRunBits [6, 5, 3, 2, 1] (.mA, [.pair 1 0 (symZero), .mid (symZero), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 118⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 64⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 89⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r2_z1 :
    symRunBits [6, 4, 3, 2] (.mA, [.pair 1 0 (symZero), .mid (symOne), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 120⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 62⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 91⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r2_z2 :
    symRunBits [6, 4, 3, 2] (.mA, [.pair 1 0 (symZero), .mid (symOne), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 120⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 62⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 91⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r3_z1 :
    symRunBits [8, 5] (.mA, [.pair 1 0 (symZero), .mid (symConst 2), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 8), .pair 1 0 (symOne), .pair 1 1 (⟨6, 0, 0, 0,
        0, 115⟩), .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 74⟩), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 1, 0, 0, 79⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r3_z2 :
    symRunBits [8, 5] (.mA, [.pair 1 0 (symZero), .mid (symConst 2), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 8), .pair 1 0 (symOne), .pair 1 1 (⟨6, 0, 0, 0,
        0, 115⟩), .mid (symZero), .pair 2 0 (⟨0, 1, 0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 74⟩),
        .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 79⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r4_z1 :
    symRunBits [7, 5, 1, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 3), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 128⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 68⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 85⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r4_z2 :
    symRunBits [7, 5, 1, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 3), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 128⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 68⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 85⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r5_z1 :
    symRunBits [7, 6, 2] (.mA, [.pair 1 0 (symZero), .mid (symConst 4), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 132⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 71⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 82⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r5_z2 :
    symRunBits [7, 6, 2] (.mA, [.pair 1 0 (symZero), .mid (symConst 4), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 132⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 71⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 82⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r6_z1 :
    symRunBits [7, 6, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 5), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 134⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 70⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 83⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r6_z2 :
    symRunBits [7, 6, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 5), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 134⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 70⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 83⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r7_z1 :
    symRunBits [7, 6, 5, 2, 1, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 6),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0,
      112⟩), .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0,
      0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 138⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 74⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 79⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r7_z2 :
    symRunBits [7, 6, 5, 2, 1, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 6),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0,
      114⟩), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 138⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 74⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 79⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r8_z1 :
    symRunBits [7, 6, 5, 1] (.mA, [.pair 1 0 (symZero), .mid (symConst 7), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 140⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 73⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 80⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r8_z2 :
    symRunBits [7, 6, 5, 1] (.mA, [.pair 1 0 (symZero), .mid (symConst 7), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 140⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 73⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 80⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r9_z1 :
    symRunBits [8, 4, 2, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 8), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 112⟩),
      .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero), .pair 1 1 (⟨6, 0, 0, 0,
        0, 137⟩), .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 70⟩), .pair 1 2 (symZero),
        .pair 1 1 (⟨0, 0, 1, 0, 0, 83⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r9_z2 :
    symRunBits [8, 4, 2, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 8), .pair 1 1 (symZero),
      .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 114⟩), .pair 2 0 (⟨0,
      1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
      0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 7), .pair 1 2 (symZero), .pair 1 1 (⟨6, 0, 0, 0,
        0, 139⟩), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 70⟩),
        .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 83⟩), .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r10_z1 :
    symRunBits [7, 6, 5, 4, 3, 2, 1, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 9),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0,
      112⟩), .mid (symZero), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0,
      0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 146⟩), .mid (symZero), .pair 1 1 (⟨3, 0,
        0, 0, 0, 75⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1, 0, 0, 78⟩),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_s1_r10_z2 :
    symRunBits [7, 6, 5, 4, 3, 2, 1, 0] (.mA, [.pair 1 0 (symZero), .mid (symConst 9),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0,
      114⟩), .pair 2 0 (⟨0, 1, 0, 0, 0, 1⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 54⟩), .pair 1 2 (symZero),
      .pair 1 1 (⟨0, 0, 1, 0, 0, 99⟩), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 1 (symZero)], [.pair 1 1 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (⟨6, 0, 0, 0, 0, 146⟩), .mid (symZero), .pair 2 0 (⟨0, 1,
        0, 0, 0, 0⟩), .pair 1 1 (⟨3, 0, 0, 0, 0, 75⟩), .pair 1 2 (symZero), .pair 1 1 (⟨0, 0, 1,
        0, 0, 78⟩), .pair 1 0 (symZero)]) := rfl

private theorem postL11_to_M (r q k z C0 : ℕ)
    (hr : r < 11) (hk : k ≤ 5) (hz : 1 ≤ z)
    (hC1 : 81 * q + 9 * r + 243 ≤ C0) (hC2 : 2046 ≤ C0 + 18 * q) :
    ReachesInvM (postL11Cfg r (6 * q + k) z C0) := by
  set u := 6 * q + k
  match hreq : r with
  | 0 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r0_z1)
        (eval_postL11_r0_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0,
        1, 0, 0, 99⟩) u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_e0111_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 107⟩) (⟨3, 0, 0, 0, 0,
        55⟩) (⟨0, 0, 1, 0, 0,
        98⟩) (6 * (u) + 110) (3 * u + 56) (v2 + 99)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        e0111_to_M (u) (1) (3 * u + 56) (v2 + 99) (by omega) (by omega) (by omega) (by omega) (by
        omega) (by omega) (by omega)
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r0_z2)
        (eval_postL11_r0_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0, 1⟩) (⟨3, 0,
        0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_e0111_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 109⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 55⟩) (⟨0, 0, 1, 0, 0,
        98⟩) (6 * (u) + 110) (v1 + 2) (3 * u + 56) (v2 + 99)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        e0111_to_M (u) (v1 + 2) (3 * u + 56) (v2 + 99) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 1 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r1_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symZero) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 1 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 118⟩) (⟨3, 0, 0, 0, 0,
        64⟩) (⟨0, 0, 1, 0, 0, 89⟩) (6 * u + 119) (3 * u + 65) (v2 + 90)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 119) (1) (3 * u + 65) (v2 + 90) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r1_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symZero) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 1 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 118⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 64⟩) (⟨0, 0, 1, 0, 0,
        89⟩) (6 * u + 119) (v1 + 2) (3 * u + 65) (v2 + 90)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 119) (v1 + 2) (3 * u + 65) (v2 + 90) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 2 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r2_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symOne) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 2 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 120⟩) (⟨3, 0, 0, 0, 0,
        62⟩) (⟨0, 0, 1, 0, 0, 91⟩) (6 * u + 121) (3 * u + 63) (v2 + 92)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 121) (1) (3 * u + 63) (v2 + 92) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r2_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symOne) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 2 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 120⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 62⟩) (⟨0, 0, 1, 0, 0,
        91⟩) (6 * u + 121) (v1 + 2) (3 * u + 63) (v2 + 92)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 121) (v1 + 2) (3 * u + 63) (v2 + 92) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 3 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r3_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 2) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 3 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_e0101_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 115⟩) (⟨3, 0, 0, 0, 0,
        74⟩) (⟨0, 0, 1, 0, 0, 79⟩) (6 * u + 116) (3 * u + 75) (v2 + 80)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        e0101_to_M u (1) (3 * u + 75) (v2 + 80) (by omega) (by omega) (by omega) (by omega) (by
        omega)
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r3_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 2) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 3 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_e0101_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 115⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 74⟩) (⟨0, 0, 1, 0, 0,
        79⟩) (6 * u + 116) (v1 + 2) (3 * u + 75) (v2 + 80)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        e0101_to_M u (v1 + 2) (3 * u + 75) (v2 + 80) (by omega) (by omega) (by omega) (by omega)
        (by omega)
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 4 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r4_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 3) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 4 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 128⟩) (⟨3, 0, 0, 0, 0,
        68⟩) (⟨0, 0, 1, 0, 0, 85⟩) (6 * u + 129) (3 * u + 69) (v2 + 86)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 129) (1) (3 * u + 69) (v2 + 86) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r4_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 3) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 4 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 128⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 68⟩) (⟨0, 0, 1, 0, 0,
        85⟩) (6 * u + 129) (v1 + 2) (3 * u + 69) (v2 + 86)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 129) (v1 + 2) (3 * u + 69) (v2 + 86) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 5 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r5_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 4) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 5 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 132⟩) (⟨3, 0, 0, 0, 0,
        71⟩) (⟨0, 0, 1, 0, 0, 82⟩) (6 * u + 133) (3 * u + 72) (v2 + 83)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 133) (1) (3 * u + 72) (v2 + 83) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r5_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 4) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 5 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 132⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 71⟩) (⟨0, 0, 1, 0, 0,
        82⟩) (6 * u + 133) (v1 + 2) (3 * u + 72) (v2 + 83)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 133) (v1 + 2) (3 * u + 72) (v2 + 83) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 6 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r6_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 5) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 6 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 134⟩) (⟨3, 0, 0, 0, 0,
        70⟩) (⟨0, 0, 1, 0, 0, 83⟩) (6 * u + 135) (3 * u + 71) (v2 + 84)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 135) (1) (3 * u + 71) (v2 + 84) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r6_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 5) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 6 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 134⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 70⟩) (⟨0, 0, 1, 0, 0,
        83⟩) (6 * u + 135) (v1 + 2) (3 * u + 71) (v2 + 84)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 135) (v1 + 2) (3 * u + 71) (v2 + 84) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 7 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r7_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 6) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 7 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 138⟩) (⟨3, 0, 0, 0, 0,
        74⟩) (⟨0, 0, 1, 0, 0, 79⟩) (6 * u + 139) (3 * u + 75) (v2 + 80)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 139) (1) (3 * u + 75) (v2 + 80) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r7_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 6) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 7 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 138⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 74⟩) (⟨0, 0, 1, 0, 0,
        79⟩) (6 * u + 139) (v1 + 2) (3 * u + 75) (v2 + 80)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 139) (v1 + 2) (3 * u + 75) (v2 + 80) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 8 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r8_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 7) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 8 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 140⟩) (⟨3, 0, 0, 0, 0,
        73⟩) (⟨0, 0, 1, 0, 0, 80⟩) (6 * u + 141) (3 * u + 74) (v2 + 81)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 141) (1) (3 * u + 74) (v2 + 81) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r8_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 7) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 8 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 140⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 73⟩) (⟨0, 0, 1, 0, 0,
        80⟩) (6 * u + 141) (v1 + 2) (3 * u + 74) (v2 + 81)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 141) (v1 + 2) (3 * u + 74) (v2 + 81) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 9 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r9_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 8) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 9 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_e0111_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 137⟩) (⟨3, 0, 0, 0, 0,
        70⟩) (⟨0, 0, 1, 0, 0,
        83⟩) (6 * (u + 5) + 110) (3 * u + 71) (v2 + 84)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        e0111_to_M (u + 5) (1) (3 * u + 71) (v2 + 84) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r9_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 8) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 9 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_e0111_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 139⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 70⟩) (⟨0, 0, 1, 0, 0,
        83⟩) (6 * (u + 5) + 110) (v1 + 2) (3 * u + 71) (v2 + 84)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ :=
        e0111_to_M (u + 5) (v1 + 2) (3 * u + 71) (v2 + 84) (by omega) (by omega) (by omega) (by
        omega) (by omega) (by omega) (by omega)
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | 10 =>
    match hz_eq : z with
    | 0 => omega
    | 1 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u 0 v2 0 0) rfl_s1_r10_z1)
        (eval_postL11_r1_z1 (v5 u 0 v2 0 0) (symConst 9) (⟨6, 0, 0, 0, 0, 112⟩) (⟨3, 0, 0, 0, 0,
        54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 10 u C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z1 (v5 u 0 v2 0 0) (⟨6, 0, 0, 0, 0, 146⟩) (⟨3, 0, 0, 0, 0,
        75⟩) (⟨0, 0, 1, 0, 0, 78⟩) (6 * u + 147) (3 * u + 76) (v2 + 79)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 147) (1) (3 * u + 76) (v2 + 79) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
    | v1 + 2 =>
      set v2 := C0 - 100
      have hstep :=
        reachesPlus_eq_both (symRunBits_sound_plus (v5 u v1 v2 0 0) rfl_s1_r10_z2)
        (eval_postL11_r1_z2 (v5 u v1 v2 0 0) (symConst 9) (⟨6, 0, 0, 0, 0, 114⟩) (⟨0, 1, 0, 0, 0,
        1⟩) (⟨3, 0, 0, 0, 0, 54⟩) (⟨0, 0, 1, 0, 0, 99⟩) 10 u (v1 + 2) C0
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by
            dsimp only [evalSymN, symZero, symOne, symConst, v5]
            omega)) (eval_eClean_z2 (v5 u v1 v2 0 0) (⟨6, 0, 0, 0, 0, 146⟩) (⟨0, 1, 0, 0, 0,
        0⟩) (⟨3, 0, 0, 0, 0, 75⟩) (⟨0, 0, 1, 0, 0,
        78⟩) (6 * u + 147) (v1 + 2) (3 * u + 76) (v2 + 79)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega)
          (by dsimp only [evalSymN, symZero, symOne, symConst, v5]; omega))
      obtain ⟨m', z', c', k', hm',
        hrest⟩ := eClean_to_M (6 * u + 147) (v1 + 2) (3 * u + 76) (v2 + 79) ⟨by omega, by omega,
        by omega, by omega, by omega⟩
      exact ⟨m', z', c', k', hm', hstep.trans hrest⟩
  | _ + 11 => omega

theorem invM_step {m z c k : ℕ} (hinv : InvM m z c k) :
    ReachesInvM (mCfg m z c k) := by
  rcases hinv with ⟨hk, hz, hm, h9m, hc2100⟩
  set K := m / 11
  set r := m % 11
  set q := K - 3
  have hK3 : K = q + 3 := by omega
  have hdiv : r + 11 * K = m := by omega
  have hB : 18 * K ≤ c := by omega
  let ms : List MidItem := [.t (6 * k + 6), .z z, .t (3 * k + 1)]
  have hloop := era_L11_d0_loop r ms c ([0, 1] +> default) K hB K (Nat.le_refl K)
  have h0 : eraL11Cfg r ms c ([0, 1] +> default) K 0 = mCfg m z c k := by
    dsimp only [eraL11Cfg, ms, encMidR, encMidItemR, mCfg]
    simp only [Nat.sub_zero, Nat.mul_zero, pow_zero_list, nil_append_lb, hdiv, list_1011_eq]
    rw [wT_cons_pow]
  have hK_cfg : eraL11Cfg r ms c ([0, 1] +> default) K K =
      postL11Cfg r (6 * q + k) z (c - 18 * K) := by
    dsimp only [eraL11Cfg, ms, encMidR, encMidItemR, postL11Cfg]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, list_1011_eq]
    rw [wT_cons_pow, pow_append_pow, pow_append_pow]
    have h1 : 36 * K + 1 + (6 * k + 6) = 6 * (6 * q + k) + 115 := by omega
    have h2 : 3 * k + 1 + 18 * K = 3 * (6 * q + k) + 55 := by omega
    rw [h1, h2]
  rw [h0, hK_cfg] at hloop
  have hpos : 0 < K * (14440 + 396 * r + 396 * w3Mid ms + 4356 * (K - 1)) +
      8514 * K * (K - 1) := by
    have : 14440 ≤ K * (14440 + 396 * r + 396 * w3Mid ms + 4356 * (K - 1)) := by
      calc 14440 ≤ 1 * (14440 + 396 * r + 396 * w3Mid ms + 4356 * (K - 1)) := by omega
        _ ≤ K * (14440 + 396 * r + 396 * w3Mid ms + 4356 * (K - 1)) :=
            Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨m', z', c', k', hm', hrest⟩ := postL11_to_M r q k z (c - 18 * K)
    (by omega) hk hz (by omega) (by omega)
  exact ⟨m', z', c', k', hm', (ReachesIn.to_plus hpos hloop).trans hrest⟩

/-! #### Blank-Tape Entry & Main Theorem -/

private theorem rfl_entry_239_0 :
    symRunBits [7, 6, 3] (.mA, [], []) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 0 (symConst 2)], [.pair 1 1 (symOne),
        .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 2 1 (symZero), .pair 1 1 (symConst 53),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_1 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .pair 1 0 (symConst 2)], [.pair 1 1 (symOne),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 2 1 (symZero), .pair 1 1 (symConst 53),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (symConst 2),
        .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symConst 7), .mid (symZero), .pair 1 1 (symConst 2),
        .pair 1 2 (symZero), .pair 1 1 (symConst 120), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_2 :
    symRunBits [7, 6, 3] (.mA, [.pair 1 1 (symZero), .pair 2 0 (symZero), .mid (symConst 2),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 0 (symZero),
      .pair 2 0 (symZero), .pair 1 1 (symConst 7), .mid (symZero), .pair 1 1 (symConst 2),
      .pair 1 2 (symZero), .pair 1 1 (symConst 120), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .mid (symZero), .pair 2 0 (symConst 15), .mid (symZero),
        .pair 2 0 (symConst 15), .pair 3 0 (symZero), .mid (symZero), .pair 2 0 (symConst 2),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 2 (symZero), .pair 1 1 (symConst 105),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_3 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .mid (symZero), .pair 2 0 (symConst 15),
      .mid (symZero), .pair 2 0 (symConst 15), .pair 3 0 (symZero), .mid (symZero),
      .pair 2 0 (symConst 2), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 1 2 (symZero),
      .pair 1 1 (symConst 105), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero)], [.pair 1 0 (symConst 2), .mid (symConst 2),
        .pair 1 1 (symConst 23), .pair 1 0 (symOne), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 53), .pair 1 2 (symZero), .pair 1 1 (symConst 69),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_4 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero)], [.pair 1 0 (symConst 2), .mid (symConst 2),
      .pair 1 1 (symConst 23), .pair 1 0 (symOne), .pair 1 1 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (symConst 53), .pair 1 2 (symZero), .pair 1 1 (symConst 69), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 1 0 (symOne), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 0 (symZero), .pair 2 0 (symOne), .mid (symConst 7),
        .pair 1 1 (symConst 22), .mid (symZero), .pair 1 1 (symConst 32), .mid (symZero),
        .pair 2 0 (symZero), .pair 1 2 (symZero), .pair 1 1 (symConst 180),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_5 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .pair 1 0 (symOne), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 0 (symZero), .pair 2 0 (symOne), .mid (symConst 7),
      .pair 1 1 (symConst 22), .mid (symZero), .pair 1 1 (symConst 32), .mid (symZero),
      .pair 2 0 (symZero), .pair 1 2 (symZero), .pair 1 1 (symConst 180), .pair 1 0 (symZero)]) =
      some (.mA, [.mid (symZero), .pair 2 0 (symConst 2), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .mid (symConst 34), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symZero),
        .pair 1 2 (symZero), .pair 1 1 (symConst 472), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_6 :
    symRunBits [7, 6, 3] (.mA, [.mid (symZero), .pair 2 0 (symConst 2), .pair 1 0 (symZero),
      .pair 2 0 (symZero), .mid (symConst 34), .pair 1 1 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 1 2 (symZero), .pair 1 1 (symConst 472), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symConst 2),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .mid (symConst 66),
        .pair 1 1 (symConst 124), .mid (symZero), .pair 1 1 (symConst 472), .pair 1 2 (symZero),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_7 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symConst 2),
      .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 1 (symZero), .mid (symConst 66),
      .pair 1 1 (symConst 124), .mid (symZero), .pair 1 1 (symConst 472), .pair 1 2 (symZero),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 2 0 (symConst 8), .mid (symZero), .pair 2 0 (symConst 20),
        .pair 1 0 (symZero), .pair 2 0 (symZero), .mid (symConst 57), .pair 1 1 (symZero),
        .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
        .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (symConst 1076),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_8 :
    symRunBits [7, 6, 3] (.mA, [.pair 2 0 (symConst 8), .mid (symZero), .pair 2 0 (symConst 20),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .mid (symConst 57), .pair 1 1 (symZero),
      .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
      .pair 1 1 (symZero), .pair 1 2 (symZero), .pair 1 1 (symConst 1076), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .pair 2 0 (symOne), .pair 2 0 (symConst 1085),
        .mid (symZero), .pair 2 0 (symConst 216), .mid (symConst 162), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symZero),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_9 :
    symRunBits [7, 6, 3] (.mA, [.pair 1 0 (symZero), .pair 2 0 (symOne),
      .pair 2 0 (symConst 1085), .mid (symZero), .pair 2 0 (symConst 216), .mid (symConst 162),
      .pair 1 1 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symZero),
      .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .mid (symConst 152),
        .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
        [.pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 28),
        .pair 2 0 (symConst 217), .pair 1 1 (symConst 12), .pair 1 2 (symZero),
        .pair 1 1 (symConst 2164), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_239_10 :
    symRunBits [5, 3, 0] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symZero), .mid (symConst 152),
      .pair 1 1 (symZero), .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)],
      [.pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 28),
      .pair 2 0 (symConst 217), .pair 1 1 (symConst 12), .pair 1 2 (symZero),
      .pair 1 1 (symConst 2164), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (symConst 151), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 36),
        .pair 2 0 (symConst 217), .pair 1 1 (symConst 15), .pair 1 2 (symZero),
        .pair 1 1 (symConst 2161), .pair 1 0 (symZero)]) := rfl

private theorem init_reaches_entry :
    ReachesStar target_tm (init []) (mCfg 152 218 2162 5) := by
  have hinit : evalSym (v5 0 0 0 0 0) (.mA, [], []) = init [] := by
    dsimp only [evalSym, cfgA, encSL, encSR]
    exact init_nil_eq_headRight.symm
  have h_e0 := symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_0
  have h_e1 := h_e0.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_1)
  have h_e2 := h_e1.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_2)
  have h_e3 := h_e2.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_3)
  have h_e4 := h_e3.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_4)
  have h_e5 := h_e4.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_5)
  have h_e6 := h_e5.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_6)
  have h_e7 := h_e6.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_7)
  have h_e8 := h_e7.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_8)
  have h_e9 := h_e8.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_9)
  have h_e10 := h_e9.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_239_10)
  have hstep :=
    reachesPlus_eq_both h_e10 hinit (eval_mCfg_z2 (v5 0 0 0 0 0) (symConst 151) (symConst 36)
    (symConst 217) (symConst 15) (symConst 2161) 152 218 2162 5 rfl rfl rfl rfl rfl)
  exact hstep.to_star

end

def InAttractor (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m z c k, InvM m z c k ∧ cfg = mCfg m z c k

private theorem attractor_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : InAttractor cfg) :
    ∃ cfg', ReachesPlus target_tm cfg cfg' ∧ InAttractor cfg' := by
  rcases h with ⟨m, z, c, k, hinv, rfl⟩
  obtain ⟨m', z', c', k', hm', hstep⟩ := invM_step hinv
  exact ⟨mCfg m' z' c' k', hstep, m', z', c', k', hm', rfl⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  IsNotHalt.of_reachesPlus_invariant
    init_reaches_entry
    ⟨152, 218, 2162, 5, ⟨by omega, by omega, by omega, by omega, by omega⟩, rfl⟩
    attractor_closed


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH
