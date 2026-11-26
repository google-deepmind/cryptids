/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify


/-!
# Busy Beaver Machine `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.Accelerated`
and defines `target_tm` for `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_HHH0RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA`. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_HHH0RA"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

/-! ## Section 1: Core Tape Encoding & 4-Mode Machine Semantics -/

/-- Exact reachability shorthand for `target_tm`. -/
private abbrev Reach (c₁ c₂ : Cfg (Fin 2) (Fin 6)) : Prop :=
  ReachesStar target_tm c₁ c₂

def onesWord : ℕ → List (Fin 2)
  | 0 => []
  | k + 1 => 1 :: onesWord k

def enc1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => (1 :: onesWord a) +> ([0] +> enc1 L)

def rep4 : ℕ → List ℕ
  | 0 => []
  | k + 1 => 4 :: rep4 k

def rep02 : ℕ → List ℕ
  | 0 => []
  | k + 1 => 0 :: 2 :: rep02 k

def inc1 : List ℕ → List ℕ
  | [] => [0]
  | a :: L => (a + 1) :: L

def addTop : ℕ → List ℕ → List ℕ
  | 0, L => L
  | n + 1, L => addTop n (inc1 L)

def cfg_EL1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (enc1 L) <{{4}} (enc1 R)
def cfg_CL1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (enc1 L) <{{2}} (enc1 R)
def cfg_EB1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := ⟨some 4, ⟨0, enc1 L, enc1 R⟩⟩
def cfg_BR1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (enc1 L) {{1}}> (enc1 R)
def cfg_halt (L : List ℕ) : Cfg (Fin 2) (Fin 6) := (((1 : Fin 2) >> enc1 L) {{5}}> default)

local macro "finish_in" : tactic => `(tactic| (
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    List.cons_append, List.nil_append, List.append_nil,
    ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
    ListBlank.cons_default_default, ListBlank.cons_zero_default, zero_cons_default]
  exact ReachesIn.zero (Γ := Fin 2) (Λ := Fin 6) _ _))

local macro "step_in" : tactic => `(tactic| (
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    List.cons_append, List.nil_append, List.append_nil,
    ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
    ListBlank.cons_default_default, ListBlank.cons_zero_default, zero_cons_default]
  refine ReachesIn.step_left (by rfl) ?_
  simp only [Tape.write, Tape.move,
    List.cons_append, List.nil_append, List.append_nil,
    ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
    ListBlank.cons_default_default, ListBlank.cons_zero_default, zero_cons_default]))

local macro "execute_in" n:num : tactic => `(tactic| (
  iterate $n step_in
  finish_in))

private theorem addTop_cons :
    ∀ (n a : ℕ) (L : List ℕ), addTop n (a :: L) = (a + n) :: L
  | 0, _, _ => rfl
  | n + 1, a, L => by
    dsimp only [addTop, inc1]
    rw [addTop_cons n (a + 1) L]
    have h : a + 1 + n = a + (n + 1) := by omega
    rw [h]

private theorem addTop_succ_nil (d : ℕ) : addTop (d + 1) [] = [d] := by
  dsimp only [addTop, inc1]
  rw [addTop_cons d 0 []]
  simp

private theorem rep4_add :
    ∀ (a b : ℕ) (X : List ℕ), rep4 (a + b) ++ X = rep4 a ++ (rep4 b ++ X)
  | 0, _, _ => by simp [rep4]
  | a + 1, b, X => by
    rw [Nat.succ_add]
    dsimp only [rep4, List.cons_append]
    rw [rep4_add a b X]

private theorem rep4_snoc :
    ∀ (k : ℕ) (X : List ℕ), rep4 k ++ (4 :: X) = 4 :: (rep4 k ++ X)
  | 0, _ => rfl
  | k + 1, X => by
    dsimp only [rep4, List.cons_append]
    rw [rep4_snoc k X]

private theorem rep02_snoc :
    ∀ (k : ℕ) (X : List ℕ), rep02 k ++ (0 :: 2 :: X) = 0 :: 2 :: (rep02 k ++ X)
  | 0, _ => rfl
  | k + 1, X => by
    dsimp only [rep02, List.cons_append]
    rw [rep02_snoc k X]

private theorem replicate_zero_snoc :
    ∀ (n : ℕ) (R : List ℕ), List.replicate n 0 ++ (0 :: R) = List.replicate (n + 1) 0 ++ R
  | 0, _ => rfl
  | n + 1, R => by
    dsimp only [List.replicate, List.cons_append]
    rw [replicate_zero_snoc n R]
    rfl

private theorem replicate_two_snoc :
    ∀ (n : ℕ) (L : List ℕ), List.replicate n 2 ++ (2 :: L) = 2 :: (List.replicate n 2 ++ L)
  | 0, _ => rfl
  | n + 1, L => by
    dsimp only [List.replicate, List.cons_append]
    rw [replicate_two_snoc n L]

private theorem enc1_zero_nil : enc1 [0] = (1 : Fin 2) >> default := by
  simp [enc1, onesWord, ListBlank.append]

private theorem one_cons_enc1 (L : List ℕ) : (1 : Fin 2) >> enc1 L = enc1 (inc1 L) := by
  cases L with
  | nil => exact enc1_zero_nil.symm
  | cons _ _ => rfl

private theorem entry_step : Reach (init []) (cfg_BR1 [0] []) := by
  have h : ReachesIn target_tm 1 (init []) (cfg_BR1 [0] []) := by
    dsimp only [cfg_BR1]
    rw [enc1_zero_nil]
    dsimp only [enc1]
    execute_in 1
  exact h.to_star

private theorem step_EB1_nil (L : List ℕ) : Reach (cfg_EB1 L []) (cfg_halt L) := by
  have h : ReachesIn target_tm 1 (cfg_EB1 L []) (cfg_halt L) := by
    dsimp only [cfg_EB1, cfg_halt, enc1]
    execute_in 1
  exact h.to_star

private theorem halts_of_halt (L : List ℕ) : HaltsFrom target_tm (cfg_halt L) :=
  ⟨cfg_halt L, ReachesStar.refl target_tm _, rfl⟩

private theorem halts_of_EB1_nil (L : List ℕ) : HaltsFrom target_tm (cfg_EB1 L []) :=
  HaltsFrom.of_reachesStar (step_EB1_nil L) (halts_of_halt L)

private theorem step_EB1_zero (L R' : List ℕ) :
    Reach (cfg_EB1 L (0 :: R')) (cfg_BR1 (0 :: inc1 L) R') := by
  have h : ReachesIn target_tm 3 (cfg_EB1 L (0 :: R')) (cfg_BR1 (0 :: inc1 L) R') := by
    dsimp only [cfg_EB1, cfg_BR1, enc1, onesWord]
    rw [← one_cons_enc1 L]
    execute_in 3
  exact h.to_star

private theorem step_EB1_succ (d : ℕ) (L R' : List ℕ) :
    Reach (cfg_EB1 L ((d + 1) :: R')) (cfg_EB1 (inc1 L) (d :: R')) := by
  have h : ReachesIn target_tm 3 (cfg_EB1 L ((d + 1) :: R')) (cfg_EB1 (inc1 L) (d :: R')) := by
    dsimp only [cfg_EB1]
    rw [← one_cons_enc1 L]
    dsimp only [enc1, onesWord]
    execute_in 3
  exact h.to_star

private theorem sweep_EB1_cons :
    ∀ (d : ℕ) (L R' : List ℕ),
      Reach (cfg_EB1 L (d :: R')) (cfg_BR1 (0 :: addTop (d + 1) L) R')
  | 0, L, R' => step_EB1_zero L R'
  | d + 1, L, R' => (step_EB1_succ d L R').trans (sweep_EB1_cons d (inc1 L) R')

private theorem step_BR1_nil (L : List ℕ) : Reach (cfg_BR1 L []) (cfg_CL1 L [0]) := by
  have h : ReachesIn target_tm 1 (cfg_BR1 L []) (cfg_CL1 L [0]) := by
    dsimp only [cfg_BR1, cfg_CL1]
    rw [enc1_zero_nil]
    dsimp only [enc1]
    execute_in 1
  exact h.to_star

private theorem step_BR1_zero (L R1 : List ℕ) :
    Reach (cfg_BR1 L (0 :: R1)) (cfg_EB1 (inc1 L) R1) := by
  have h : ReachesIn target_tm 1 (cfg_BR1 L (0 :: R1)) (cfg_EB1 (inc1 L) R1) := by
    dsimp only [cfg_BR1, cfg_EB1]
    rw [← one_cons_enc1 L]
    dsimp only [enc1, onesWord]
    execute_in 1
  exact h.to_star

private theorem step_BR1_ge2 (d1 : ℕ) (L R1 : List ℕ) :
    Reach (cfg_BR1 L ((d1 + 2) :: R1)) (cfg_EL1 (inc1 (inc1 L)) (d1 :: R1)) := by
  have h : ReachesIn target_tm 1 (cfg_BR1 L ((d1 + 2) :: R1)) (cfg_EL1 (inc1 (inc1 L)) (d1 :: R1))
    := by
    dsimp only [cfg_BR1, cfg_EL1]
    rw [← one_cons_enc1 (inc1 L), ← one_cons_enc1 L]
    dsimp only [enc1, onesWord]
    execute_in 1
  exact h.to_star

private theorem step_BR1_one_nil (L : List ℕ) :
    Reach (cfg_BR1 L [1]) (cfg_EL1 (inc1 (inc1 L)) []) := by
  have h : ReachesIn target_tm 1 (cfg_BR1 L [1]) (cfg_EL1 (inc1 (inc1 L)) []) := by
    dsimp only [cfg_BR1, cfg_EL1]
    rw [← one_cons_enc1 (inc1 L), ← one_cons_enc1 L]
    dsimp only [enc1, onesWord]
    execute_in 1
  exact h.to_star

private theorem step_BR1_00 (L R : List ℕ) :
    Reach (cfg_BR1 (0 :: L) (0 :: 0 :: R)) (cfg_BR1 (0 :: 2 :: L) R) :=
  (step_BR1_zero (0 :: L) (0 :: R)).trans (step_EB1_zero (1 :: L) R)

private theorem sweep_BR_00 :
    ∀ (k : ℕ) (L R : List ℕ),
      Reach (cfg_BR1 (0 :: L) (List.replicate (2 * k) 0 ++ R))
        (cfg_BR1 (0 :: (List.replicate k 2 ++ L)) R)
  | 0, _, _ => ReachesStar.refl target_tm _
  | k + 1, L, R => by
    have hrep : List.replicate (2 * (k + 1)) 0 ++ R = 0 :: 0 :: (List.replicate (2 * k) 0 ++ R) :=
      by
      rw [show 2 * (k + 1) = (2 * k) + 2 by omega]
      rfl
    rw [hrep]
    have h1 := step_BR1_00 L (List.replicate (2 * k) 0 ++ R)
    have h2 := sweep_BR_00 k (2 :: L) R
    rw [replicate_two_snoc k L] at h2
    exact h1.trans h2

private theorem step_BR1_0d (d : ℕ) (L R : List ℕ) :
    Reach (cfg_BR1 (0 :: L) (0 :: d :: R)) (cfg_BR1 (0 :: (d + 2) :: L) R) := by
  have h1 := step_BR1_zero (0 :: L) (d :: R)
  have h2 := sweep_EB1_cons d (1 :: L) R
  rw [addTop_cons (d + 1) 1 L, show 1 + (d + 1) = d + 2 by omega] at h2
  exact h1.trans h2

private theorem sweep_BR_p02_one (L R : List ℕ) :
    Reach (cfg_BR1 (0 :: L) (0 :: 2 :: R)) (cfg_BR1 (0 :: 4 :: L) R) :=
  step_BR1_0d 2 L R

private theorem sweep_BR_p02 :
    ∀ (k : ℕ) (L R : List ℕ),
      Reach (cfg_BR1 (0 :: L) (rep02 k ++ R)) (cfg_BR1 (0 :: (rep4 k ++ L)) R)
  | 0, _, _ => ReachesStar.refl target_tm _
  | k + 1, L, R => by
    dsimp only [rep02, List.cons_append]
    have h1 := sweep_BR_p02_one L (rep02 k ++ R)
    have h2 := sweep_BR_p02 k (4 :: L) R
    rw [rep4_snoc k L] at h2
    exact h1.trans h2

private theorem step_EL1_zero (L' R : List ℕ) :
    Reach (cfg_EL1 (0 :: L') R) (cfg_CL1 (inc1 L') (inc1 R)) := by
  have h : ReachesIn target_tm 3 (cfg_EL1 (0 :: L') R) (cfg_CL1 (inc1 L') (inc1 R)) := by
    dsimp only [cfg_EL1, cfg_CL1]
    rw [← one_cons_enc1 L', ← one_cons_enc1 R]
    dsimp only [enc1, onesWord]
    execute_in 3
  exact h.to_star

private theorem step_EL1_one (L' R : List ℕ) :
    Reach (cfg_EL1 (1 :: L') R) (cfg_EB1 L' (0 :: R)) := by
  have h : ReachesIn target_tm 2 (cfg_EL1 (1 :: L') R) (cfg_EB1 L' (0 :: R)) := by
    dsimp only [cfg_EL1, cfg_EB1, enc1, onesWord]
    execute_in 2
  exact h.to_star

private theorem step_EL1_add_two (a : ℕ) (L' R : List ℕ) :
    Reach (cfg_EL1 ((a + 2) :: L') R) (cfg_EL1 (a :: L') (0 :: R)) := by
  have h : ReachesIn target_tm 2 (cfg_EL1 ((a + 2) :: L') R) (cfg_EL1 (a :: L') (0 :: R)) := by
    dsimp only [cfg_EL1, enc1, onesWord]
    execute_in 2
  exact h.to_star

private theorem peel_EL1_even :
    ∀ (k a : ℕ) (L' R : List ℕ),
      Reach (cfg_EL1 ((a + 2 * k) :: L') R) (cfg_EL1 (a :: L') (List.replicate k 0 ++ R))
  | 0, _, _, _ => ReachesStar.refl target_tm _
  | k + 1, a, L', R => by
    have heq : a + 2 * (k + 1) = (a + 2 * k) + 2 := by omega
    rw [heq]
    have h1 := step_EL1_add_two (a + 2 * k) L' R
    have h2 := peel_EL1_even k a L' (0 :: R)
    rw [replicate_zero_snoc k R] at h2
    exact h1.trans h2

private theorem step_EL1_nil_cons (d : ℕ) (R' : List ℕ) :
    Reach (cfg_EL1 [] (d :: R')) (cfg_BR1 [0, d] R') := by
  have h0 : cfg_EL1 [] (d :: R') = cfg_EB1 [] (d :: R') := rfl
  rw [h0]
  have h1 := sweep_EB1_cons d [] R'
  rw [addTop_succ_nil d] at h1
  exact h1

private theorem step_CL1_nil (R : List ℕ) :
    Reach (cfg_CL1 [] R) (cfg_EL1 [] (inc1 R)) := by
  have h : ReachesIn target_tm 1 (cfg_CL1 [] R) (cfg_EL1 [] (inc1 R)) := by
    dsimp only [cfg_CL1, cfg_EL1]
    rw [← one_cons_enc1 R]
    dsimp only [enc1]
    execute_in 1
  exact h.to_star

private theorem step_CL1_zero (L' R : List ℕ) :
    Reach (cfg_CL1 (0 :: L') R) (cfg_CL1 L' (inc1 (inc1 R))) := by
  have h : ReachesIn target_tm 2 (cfg_CL1 (0 :: L') R) (cfg_CL1 L' (inc1 (inc1 R))) := by
    dsimp only [cfg_CL1]
    rw [← one_cons_enc1 (inc1 R), ← one_cons_enc1 R]
    dsimp only [enc1, onesWord]
    execute_in 2
  exact h.to_star

private theorem step_CL1_one (L' R : List ℕ) :
    Reach (cfg_CL1 (1 :: L') R) (cfg_CL1 (inc1 L') (inc1 (inc1 R))) := by
  have h : ReachesIn target_tm 4 (cfg_CL1 (1 :: L') R) (cfg_CL1 (inc1 L') (inc1 (inc1 R))) := by
    dsimp only [cfg_CL1]
    rw [← one_cons_enc1 L', ← one_cons_enc1 (inc1 R), ← one_cons_enc1 R]
    dsimp only [enc1, onesWord]
    execute_in 4
  exact h.to_star

private theorem step_CL1_two (L' R : List ℕ) :
    Reach (cfg_CL1 (2 :: L') R) (cfg_EB1 L' (0 :: inc1 R)) := by
  have h : ReachesIn target_tm 3 (cfg_CL1 (2 :: L') R) (cfg_EB1 L' (0 :: inc1 R)) := by
    dsimp only [cfg_CL1, cfg_EB1, enc1, onesWord]
    rw [← one_cons_enc1 R]
    execute_in 3
  exact h.to_star

private theorem step_CL1_add_three (a : ℕ) (L' R : List ℕ) :
    Reach (cfg_CL1 ((a + 3) :: L') R) (cfg_EL1 (a :: L') (0 :: inc1 R)) := by
  have h : ReachesIn target_tm 3 (cfg_CL1 ((a + 3) :: L') R) (cfg_EL1 (a :: L') (0 :: inc1 R)) := by
    dsimp only [cfg_CL1, cfg_EL1, enc1, onesWord]
    rw [← one_cons_enc1 R]
    execute_in 3
  exact h.to_star

private theorem sweep_EL_f4_one (L R : List ℕ) :
    Reach (cfg_EL1 (0 :: 4 :: L) (0 :: R)) (cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: R)) :=
  ((step_EL1_zero (4 :: L) (0 :: R)).trans (step_CL1_add_three 2 L (1 :: R))).trans
    (step_EL1_add_two 0 L (0 :: 2 :: R))

private theorem sweep_EL_f4 :
    ∀ (k : ℕ) (L R : List ℕ),
      Reach (cfg_EL1 (0 :: (rep4 k ++ L)) (0 :: R)) (cfg_EL1 (0 :: L) (0 :: (rep02 k ++ R)))
  | 0, _, _ => ReachesStar.refl target_tm _
  | k + 1, L, R => by
    dsimp only [rep4, List.cons_append]
    have h1 := sweep_EL_f4_one (rep4 k ++ L) R
    have h2 := sweep_EL_f4 k L (0 :: 2 :: R)
    rw [rep02_snoc k R] at h2
    exact h1.trans h2

private theorem sweep_EL3_f4_one (L R : List ℕ) :
    Reach (cfg_EL1 (3 :: 4 :: L) (0 :: 2 :: 2 :: R))
      (cfg_EL1 (3 :: L) (0 :: 2 :: 2 :: 0 :: 2 :: R)) := by
  have h1 := step_EL1_add_two 1 (4 :: L) (0 :: 2 :: 2 :: R)
  have h2 := step_EL1_one (4 :: L) (0 :: 0 :: 2 :: 2 :: R)
  have h3 := step_EB1_zero (4 :: L) (0 :: 0 :: 2 :: 2 :: R)
  have h4 := step_BR1_zero (0 :: 5 :: L) (0 :: 2 :: 2 :: R)
  have h5 := step_EB1_zero (1 :: 5 :: L) (2 :: 2 :: R)
  have h6 := step_BR1_ge2 0 (0 :: 2 :: 5 :: L) (2 :: R)
  have h7 := step_EL1_add_two 0 (2 :: 5 :: L) (0 :: 2 :: R)
  have h8 := step_EL1_zero (2 :: 5 :: L) (0 :: 0 :: 2 :: R)
  have h9 := step_CL1_add_three 0 (5 :: L) (1 :: 0 :: 2 :: R)
  have h10 := step_EL1_zero (5 :: L) (0 :: 2 :: 0 :: 2 :: R)
  have h11 := step_CL1_add_three 3 L (1 :: 2 :: 0 :: 2 :: R)
  exact ((((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
    h8).trans h9).trans h10).trans h11)

private theorem sweep_EL3_f4 :
    ∀ (k : ℕ) (L R : List ℕ),
      Reach (cfg_EL1 (3 :: (rep4 k ++ L)) (0 :: 2 :: 2 :: R))
        (cfg_EL1 (3 :: L) (0 :: 2 :: 2 :: (rep02 k ++ R)))
  | 0, _, _ => ReachesStar.refl target_tm _
  | k + 1, L, R => by
    dsimp only [rep4, rep02, List.cons_append]
    have h1 := sweep_EL3_f4_one (rep4 k ++ L) R
    have h2 := sweep_EL3_f4 k L (0 :: 2 :: R)
    rw [rep02_snoc k R] at h2
    exact h1.trans h2

/-! ## Section 1b: Suffix-Polymorphic Symbolic 4-Mode Evaluator (`run4`) -/

inductive Mode4 where
  | mEL | mCL | mEB | mBR

private def eval4 (m : Mode4) (L R S : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  match m with
  | .mEL => cfg_EL1 L (R ++ S)
  | .mCL => cfg_CL1 L (R ++ S)
  | .mEB => cfg_EB1 L (R ++ S)
  | .mBR => cfg_BR1 L (R ++ S)

private def step4 : Mode4 × List ℕ × List ℕ → Option (Mode4 × List ℕ × List ℕ)
  | (.mEB, L, d :: R') => some (.mBR, 0 :: addTop (d + 1) L, R')
  | (.mBR, L, 0 :: R') => some (.mEB, inc1 L, R')
  | (.mBR, L, (d + 2) :: R') => some (.mEL, inc1 (inc1 L), d :: R')
  | (.mEL, [], d :: R') => some (.mBR, [0, d], R')
  | (.mEL, 0 :: L', d :: R') => some (.mCL, inc1 L', (d + 1) :: R')
  | (.mEL, 1 :: L', R) => some (.mEB, L', 0 :: R)
  | (.mEL, (a + 2) :: L', R) => some (.mEL, a :: L', 0 :: R)
  | (.mCL, [], d :: R') => some (.mEL, [], (d + 1) :: R')
  | (.mCL, 0 :: L', d :: R') => some (.mCL, L', (d + 2) :: R')
  | (.mCL, 1 :: L', d :: R') => some (.mCL, inc1 L', (d + 2) :: R')
  | (.mCL, 2 :: L', d :: R') => some (.mEB, L', 0 :: (d + 1) :: R')
  | (.mCL, (a + 3) :: L', d :: R') => some (.mEL, a :: L', 0 :: (d + 1) :: R')
  | _ => none

private theorem step4_sound {s s' : Mode4 × List ℕ × List ℕ}
    (h : step4 s = some s') (S : List ℕ) :
    Reach (eval4 s.1 s.2.1 s.2.2 S) (eval4 s'.1 s'.2.1 s'.2.2 S) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | mEB =>
    cases R with
    | nil => cases h
    | cons d R' =>
      cases h
      exact sweep_EB1_cons d L (R' ++ S)
  | mBR =>
    cases R with
    | nil => cases h
    | cons d R' =>
      cases d with
      | zero => cases h; exact step_BR1_zero L (R' ++ S)
      | succ d1 =>
        cases d1 with
        | zero => cases h
        | succ d2 => cases h; exact step_BR1_ge2 d2 L (R' ++ S)
  | mEL =>
    cases L with
    | nil =>
      cases R with
      | nil => cases h
      | cons d R' => cases h; exact step_EL1_nil_cons d (R' ++ S)
    | cons v L' =>
      cases v with
      | zero =>
        cases R with
        | nil => cases h
        | cons d R' => cases h; exact step_EL1_zero L' (d :: (R' ++ S))
      | succ v1 =>
        cases v1 with
        | zero => cases h; exact step_EL1_one L' (R ++ S)
        | succ a => cases h; exact step_EL1_add_two a L' (R ++ S)
  | mCL =>
    cases L with
    | nil =>
      cases R with
      | nil => cases h
      | cons d R' => cases h; exact step_CL1_nil (d :: (R' ++ S))
    | cons v L' =>
      cases R with
      | nil =>
        cases v with
        | zero => cases h
        | succ v1 =>
          cases v1 with
          | zero => cases h
          | succ v2 =>
            cases v2 with
            | zero => cases h
            | succ _ => cases h
      | cons d R' =>
        cases v with
        | zero => cases h; exact step_CL1_zero L' (d :: (R' ++ S))
        | succ v1 =>
          cases v1 with
          | zero => cases h; exact step_CL1_one L' (d :: (R' ++ S))
          | succ v2 =>
            cases v2 with
            | zero => cases h; exact step_CL1_two L' (d :: (R' ++ S))
            | succ a => cases h; exact step_CL1_add_three a L' (d :: (R' ++ S))

private def run4 : ℕ → Mode4 × List ℕ × List ℕ → Option (Mode4 × List ℕ × List ℕ)
  | 0, s => some s
  | n + 1, s =>
    match step4 s with
    | none => none
    | some s₁ => run4 n s₁

private theorem run4_sound :
    ∀ (n : ℕ) {s s' : Mode4 × List ℕ × List ℕ},
      run4 n s = some s' → ∀ S : List ℕ,
        Reach (eval4 s.1 s.2.1 s.2.2 S) (eval4 s'.1 s'.2.1 s'.2.2 S)
  | 0, _, _, h, _ => by
    cases h
    exact ReachesStar.refl target_tm _
  | n + 1, s, s', h, S => by
    dsimp only [run4] at h
    cases hs : step4 s with
    | none => rw [hs] at h; cases h
    | some s₁ =>
      rw [hs] at h
      exact (step4_sound hs S).trans (run4_sound n h S)

private def natListEq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && natListEq xs ys
  | _, _ => false

private theorem natListEq_eq : ∀ {l₁ l₂ : List ℕ}, natListEq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    dsimp only [natListEq] at h
    rw [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, natListEq_eq h.2]

private def mode4Eq : Mode4 → Mode4 → Bool
  | .mEL, .mEL => true
  | .mCL, .mCL => true
  | .mEB, .mEB => true
  | .mBR, .mBR => true
  | _, _ => false

private theorem mode4Eq_eq {m₁ m₂ : Mode4} (h : mode4Eq m₁ m₂ = true) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> first | rfl | cases h

private def checkRun4 (n : ℕ) (s s' : Mode4 × List ℕ × List ℕ) : Bool :=
  match run4 n s with
  | none => false
  | some s₁ => mode4Eq s₁.1 s'.1 && natListEq s₁.2.1 s'.2.1 && natListEq s₁.2.2 s'.2.2

private theorem run4_of_check {n : ℕ} {s s' : Mode4 × List ℕ × List ℕ}
    (h : checkRun4 n s s' = true) (S : List ℕ) :
    Reach (eval4 s.1 s.2.1 s.2.2 S) (eval4 s'.1 s'.2.1 s'.2.2 S) := by
  unfold checkRun4 at h
  cases hr : run4 n s with
  | none => rw [hr] at h; cases h
  | some s₁ =>
    rw [hr] at h
    dsimp only at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    have heq : s₁ = s' := by
      rcases s₁ with ⟨m1, l1, r1⟩
      rcases s' with ⟨m2, l2, r2⟩
      dsimp only at h
      rw [mode4Eq_eq h.1.1, natListEq_eq h.1.2, natListEq_eq h.2]
    subst heq
    exact run4_sound n hr S

/-! ## Section 2: Universal Weight `wf`, `W`, `psi` & Master Theorem `mCL_bump_spec` -/

def wf : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 2
  | 6 => 2
  | n + 7 => (n + 7) / 4 + 2

def W : List ℕ → ℕ
  | [] => 0
  | v :: L => wf v + W L

def psi : List ℕ → ℕ
  | [] => 0
  | v :: M => if Nat.beq v 2 then 2 * W M + 1 else 2 * (wf v + W M)

private theorem psi_cons_two (M : List ℕ) : psi (2 :: M) = 2 * W M + 1 := rfl

private theorem psi_cons_ne2 {v : ℕ} (hv : v ≠ 2) (M : List ℕ) :
    psi (v :: M) = 2 * (wf v + W M) := by
  dsimp only [psi]
  cases hb : Nat.beq v 2 with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) hv

private theorem psi_le (L : List ℕ) : psi L ≤ 2 * W L := by
  cases L with
  | nil => simp [psi, W]
  | cons v M =>
    cases hb : Nat.beq v 2 with
    | true =>
      have hv : v = 2 := Nat.eq_of_beq_eq_true hb
      subst hv
      rw [psi_cons_two]
      dsimp only [W]
      change 2 * W M + 1 ≤ 2 * (1 + W M)
      omega
    | false =>
      have hv : v ≠ 2 := fun h => by subst h; cases hb
      rw [psi_cons_ne2 hv]
      dsimp only [W]
      omega

private theorem wf_add_one_le (v : ℕ) : wf (v + 1) ≤ wf v + 2 := by
  match v with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | n + 7 =>
    change (n + 1 + 7) / 4 + 2 ≤ (n + 7) / 4 + 2 + 2
    omega

private theorem wf_add_one_le_ne4 {v : ℕ} (hv : v ≠ 4) : wf (v + 1) ≤ wf v + 1 := by
  match v with
  | 0 | 1 | 2 | 3 | 5 | 6 => decide
  | 4 => exact absurd rfl hv
  | n + 7 =>
    change (n + 1 + 7) / 4 + 2 ≤ (n + 7) / 4 + 2 + 1
    omega

private theorem wf_even_step (c : ℕ) : wf (2 * (c + 1) + 4) ≤ wf (2 * c + 4) + 2 := by
  match c with
  | 0 | 1 | 2 => decide
  | n + 3 =>
    have h1 : 2 * (n + 3 + 1) + 4 = (2 * n + 5) + 7 := by omega
    have h2 : 2 * (n + 3) + 4 = (2 * n + 3) + 7 := by omega
    rw [h1, h2]
    dsimp only [wf]
    omega

private theorem wf_even_mono {c : ℕ} (hc : 1 ≤ c) : wf (2 * c + 2) ≤ wf (2 * c + 4) := by
  match c with
  | 0 => omega
  | 1 | 2 => decide
  | n + 3 =>
    have h1 : 2 * (n + 3) + 2 = (2 * n + 1) + 7 := by omega
    have h2 : 2 * (n + 3) + 4 = (2 * n + 3) + 7 := by omega
    rw [h1, h2]
    dsimp only [wf]
    omega

private theorem W_inc1_le (L : List ℕ) : W (inc1 L) ≤ W L + 2 := by
  cases L with
  | nil => decide
  | cons v M =>
    dsimp only [inc1, W]
    have h := wf_add_one_le v
    omega

private theorem W_rep4_append (k : ℕ) (L : List ℕ) : W (rep4 k ++ L) = W L := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [rep4, List.cons_append, W]
    change 0 + W (rep4 k ++ L) = W L
    omega

private theorem W_replicate_two (k : ℕ) (L : List ℕ) :
    W (List.replicate k 2 ++ L) = k + W L := by
  induction k with
  | zero => simp
  | succ k ih =>
    dsimp only [List.replicate, List.cons_append, W]
    change 1 + W (List.replicate k 2 ++ L) = k + 1 + W L
    omega

private theorem psi_replicate_two_succ (k : ℕ) (L : List ℕ) :
    psi (List.replicate (k + 1) 2 ++ L) = 2 * (k + W L) + 1 := by
  dsimp only [List.replicate, List.cons_append]
  rw [psi_cons_two, W_replicate_two k L]

private theorem wf_4r3 (r : ℕ) : wf (4 * r + 3) = r + 2 := by
  cases r with
  | zero => rfl
  | succ r =>
    have h : 4 * (r + 1) + 3 = (4 * r) + 7 := by omega
    rw [h]
    dsimp only [wf]
    omega

private theorem wf_4r1_ge2 (r : ℕ) : wf (4 * (r + 2) + 1) = r + 4 := by
  have h : 4 * (r + 2) + 1 = (4 * r + 2) + 7 := by omega
  rw [h]
  dsimp only [wf]
  omega

private theorem wf_4j6 (j : ℕ) : j + 2 ≤ wf (4 * j + 6) := by
  cases j with
  | zero => decide
  | succ j =>
    have h : 4 * (j + 1) + 6 = (4 * j + 3) + 7 := by omega
    rw [h]
    dsimp only [wf]
    omega

private theorem wf_4j8 (j : ℕ) : j + 4 ≤ wf (4 * j + 8) := by
  have h : 4 * j + 8 = (4 * j + 1) + 7 := by omega
  rw [h]
  dsimp only [wf]
  omega

private theorem wf_inc_class (v : ℕ) :
    (v = 4) ∨ (wf (v + 1) ≤ wf v) ∨ (v = 0) ∨ (v = 2) ∨ (v = 6) ∨ (∃ m, v = 4 * (m + 1) + 3) := by
  match v with
  | 0 => exact Or.inr (Or.inr (Or.inl rfl))
  | 1 => exact Or.inr (Or.inl (by decide))
  | 2 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | 3 => exact Or.inr (Or.inl (by decide))
  | 4 => exact Or.inl rfl
  | 5 => exact Or.inr (Or.inl (by decide))
  | 6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | n + 7 =>
    have hq : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hq with h0 | h1 | h2 | h3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n / 4, by omega⟩))))
    · exact Or.inr (Or.inl (by change (n + 1 + 7) / 4 + 2 ≤ (n + 7) / 4 + 2; omega))
    · exact Or.inr (Or.inl (by change (n + 1 + 7) / 4 + 2 ≤ (n + 7) / 4 + 2; omega))
    · exact Or.inr (Or.inl (by change (n + 1 + 7) / 4 + 2 ≤ (n + 7) / 4 + 2; omega))

private def strip4 : List ℕ → ℕ × List ℕ
  | 4 :: L =>
    let r := strip4 L
    (r.1 + 1, r.2)
  | L => (0, L)

private theorem strip4_spec (L : List ℕ) :
    L = rep4 (strip4 L).1 ++ (strip4 L).2 ∧
    (∀ v T, (strip4 L).2 = v :: T → v ≠ 4) := by
  induction L with
  | nil => exact ⟨rfl, fun _ _ h => by cases h⟩
  | cons a M ih =>
    match a with
    | 4 =>
      change 4 :: M = 4 :: (rep4 (strip4 M).1 ++ (strip4 M).2) ∧ _
      exact ⟨congrArg (4 :: ·) ih.1, ih.2⟩
    | 0 | 1 | 2 | 3 | 5 | 6 | _ + 7 =>
      exact ⟨rfl, fun v T h => by injection h with hv; subst hv; omega⟩

/-- Constant-step prefix rule for `M = 5 :: rep4 (k + 1) ++ M'` (`k ≥ 0`, `M'` arbitrary):
`cfg_CL1 (6 :: rep4 (k + 1) ++ M') ((2 * c + 1) :: S)` reaches
`cfg_EL1 (0 :: inc1 M') (rep02 (k + 2) ++ (2 * c) :: S)`. -/
private theorem cl_6_rep4_step (k c : ℕ) (M' S : List ℕ) :
    Reach (cfg_CL1 (6 :: (rep4 (k + 1) ++ M')) ((2 * c + 1) :: S))
          (cfg_EL1 (0 :: inc1 M') (rep02 (k + 2) ++ ((2 * c) :: S))) := by
  have h1 := step_CL1_add_three 3 (rep4 (k + 1) ++ M') ((2 * c + 1) :: S)
  have h2 := step_EL1_add_two 1 (4 :: rep4 k ++ M') (0 :: (2 * c + 2) :: S)
  have h3 := step_EL1_one (4 :: rep4 k ++ M') (0 :: 0 :: (2 * c + 2) :: S)
  have h4 := step_EB1_zero (4 :: rep4 k ++ M') (0 :: 0 :: (2 * c + 2) :: S)
  have h5 := step_BR1_zero (0 :: 5 :: rep4 k ++ M') (0 :: (2 * c + 2) :: S)
  have h6 := step_EB1_zero (1 :: 5 :: rep4 k ++ M') ((2 * c + 2) :: S)
  have h7 := step_BR1_ge2 (2 * c) (0 :: 2 :: 5 :: rep4 k ++ M') S
  have h8 := step_EL1_add_two 0 (2 :: 5 :: rep4 k ++ M') ((2 * c) :: S)
  have h9 := step_EL1_zero (2 :: 5 :: rep4 k ++ M') (0 :: (2 * c) :: S)
  have h10 := step_CL1_add_three 0 (5 :: rep4 k ++ M') (1 :: (2 * c) :: S)
  have h11 := step_EL1_zero (5 :: rep4 k ++ M') (0 :: 2 :: (2 * c) :: S)
  have h12 := step_CL1_add_three 3 (rep4 k ++ M') (1 :: 2 :: (2 * c) :: S)
  have h13 := sweep_EL3_f4 k M' ((2 * c) :: S)
  have h14 := step_EL1_add_two 1 M' (0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h15 := step_EL1_one M' (0 :: 0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h16 := step_EB1_zero M' (0 :: 0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h17 := step_BR1_zero (0 :: inc1 M') (0 :: 2 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h18 := step_EB1_zero (1 :: inc1 M') (2 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h19 := step_BR1_ge2 0 (0 :: 2 :: inc1 M') (2 :: (rep02 k ++ (2 * c) :: S))
  have h20 := step_EL1_add_two 0 (2 :: inc1 M') (0 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h21 := step_EL1_zero (2 :: inc1 M') (0 :: 0 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have h22 := step_CL1_add_three 0 (inc1 M') (1 :: 0 :: 2 :: (rep02 k ++ (2 * c) :: S))
  have hchain := (((((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
    h8).trans h9).trans h10).trans h11).trans h12)
  have hchain2 := ((((((((h13.trans h14).trans h15).trans h16).trans h17).trans h18).trans
    h19).trans
    h20).trans h21).trans h22
  exact hchain.trans hchain2

/--
Concrete base theorem 1: `M = [5]` (`cfg_CL1 [6] ((2*c+1) :: S)`) via `run4` (50 `step4` steps). -/
private theorem cl_6_nil_step (c : ℕ) (S : List ℕ) :
    Reach (cfg_CL1 [6] ((2 * c + 1) :: S))
          (cfg_BR1 (0 :: (2 * c + 2) :: 2 :: 4 :: 4 :: 4 :: []) S) := by
  have h1 := step_CL1_add_three 3 [] ((2 * c + 1) :: S)
  have h2 := step_EL1_add_two 1 [] (0 :: (2 * c + 2) :: S)
  have h3 := step_EL1_one [] (0 :: 0 :: (2 * c + 2) :: S)
  have h4 := step_EB1_zero [] (0 :: 0 :: (2 * c + 2) :: S)
  have h5 := step_BR1_00 [0] ((2 * c + 2) :: S)
  have h6 := step_BR1_ge2 (2 * c) [0, 2, 0] S
  have h7 := step_EL1_add_two 0 [2, 0] ((2 * c) :: S)
  have h8 : Reach (cfg_EL1 [0, 2, 0] (0 :: ((2 * c) :: S)))
                  (cfg_BR1 [0, 2, 4, 4, 4] (0 :: ((2 * c) :: S))) :=
    run4_of_check (n := 50) (s := (.mEL, [0, 2, 0], [0])) (s' := (.mBR, [0, 2, 4, 4, 4], [0]))
      (by decide +kernel) ((2 * c) :: S)
  have h9 := step_BR1_0d (2 * c) [2, 4, 4, 4] S
  exact (((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9

/--
Concrete base theorem 2a: `cfg_BR1 [0, 6] (2 :: 0 :: 2 :: S)` -> `cfg_BR1 (0 :: rep4 6) (0 :: S)`
(98 `step4` steps). -/
private theorem br_6_202_step (S : List ℕ) :
    Reach (cfg_BR1 [0, 6] (2 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: rep4 6) (0 :: S)) :=
  run4_of_check (n := 98) (s := (.mBR, [0, 6], [2, 0, 2])) (s' := (.mBR, 0 :: rep4 6, [0]))
    (by decide +kernel) S

/--
Concrete base theorem 2b: `cfg_BR1 (0 :: rep4 6) (0 :: 0 :: 2 :: S)` -> `cfg_BR1 (0 :: 2 :: rep4 8)
S` (83 `step4` steps). -/
private theorem br_rep4_6_002_step (S : List ℕ) :
    Reach (cfg_BR1 (0 :: rep4 6) (0 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: 2 :: rep4 8) S) :=
  run4_of_check (n := 83) (s := (.mBR, 0 :: rep4 6, [0, 0, 2])) (s' := (.mBR, 0 :: 2 :: rep4 8, []))
    (by decide +kernel) S

/--
Concrete base theorem 3: `cfg_BR1 [0, 4, 6] (0 :: 0 :: 2 :: S)` -> `cfg_BR1 (0 :: 2 :: 2 :: rep4 7)
S` (179 `step4` steps). -/
private theorem br_46_002_step (S : List ℕ) :
    Reach (cfg_BR1 [0, 4, 6] (0 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: 2 :: 2 :: rep4 7) S) :=
  run4_of_check (n := 179) (s := (.mBR, [0, 4, 6], [0, 0, 2])) (s' := (.mBR, 0 :: 2 :: 2 :: rep4
    7, []))
    (by decide +kernel) S

/--
Constant-step prefix theorem for stripping `4 :: 2` in `cfg_BR1 (0 :: 4 :: 2 :: L') (0 :: 0 :: 2 ::
R)`. -/
private theorem br_42_002_step (L' R : List ℕ) :
    Reach (cfg_BR1 (0 :: 4 :: 2 :: L') (0 :: 0 :: 2 :: R))
          (cfg_EL1 (0 :: L') (0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)) := by
  have h1 := step_BR1_00 (4 :: 2 :: L') (2 :: R)
  have h2 := step_BR1_ge2 0 (0 :: 2 :: 4 :: 2 :: L') R
  have h3 := step_EL1_add_two 0 (2 :: 4 :: 2 :: L') (0 :: R)
  have h4 := step_EL1_zero (2 :: 4 :: 2 :: L') (0 :: 0 :: R)
  have h5 := step_CL1_add_three 0 (4 :: 2 :: L') (1 :: 0 :: R)
  have h6 := sweep_EL_f4_one (2 :: L') (2 :: 0 :: R)
  have h7 := step_EL1_zero (2 :: L') (0 :: 0 :: 2 :: 2 :: 0 :: R)
  have h8 := step_CL1_add_three 0 L' (1 :: 0 :: 2 :: 2 :: 0 :: R)
  exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8

/-- Outcome predicate for `mCL_bump_spec` (at any `c : ℕ` and arbitrary suffix `S`). -/
private def GoodOut (M : List ℕ) (c : ℕ) (S : List ℕ) : Prop :=
  (∃ L', Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S)) (cfg_BR1 (0 :: L') S) ∧
         2 * W L' ≤ psi M + 2 * wf (2 * c + 4) ∧
         (c = 0 → (∃ T, M = 5 :: T) → psi L' + 1 ≤ psi M)) ∨
  (∃ L', Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S)) (cfg_BR1 (0 :: L') (0 :: S)) ∧
         2 * W L' + 1 ≤ psi M)

private abbrev ELIH (limit : ℕ) : Prop :=
  ∀ L : List ℕ, psi L < limit → ∀ S : List ℕ,
    (∃ L', Reach (cfg_EL1 (0 :: L) (0 :: S)) (cfg_BR1 (0 :: L') S) ∧ 2 * W L' ≤ psi L) ∨
    (∃ L', Reach (cfg_EL1 (0 :: L) (0 :: S)) (cfg_BR1 (0 :: L') (0 :: S)) ∧ 2 * W L' + 1 ≤ psi L)

/-- Step an arbitrary positive even digit `2 * c + 2` (`2, 4, 6, ...`) using `ihEL`. -/
private theorem step_even_ih {limit : ℕ} (ihEL : ELIH limit) :
    ∀ (c : ℕ) (L : List ℕ), psi L < limit → ∀ (S : List ℕ),
      (∃ L', Reach (cfg_BR1 (0 :: L) ((2 * c + 2) :: S)) (cfg_BR1 (0 :: L') (0 :: S)) ∧
             2 * W L' ≤ psi L) ∨
      (∃ L', Reach (cfg_BR1 (0 :: L) ((2 * c + 2) :: S)) (cfg_BR1 (0 :: L') S) ∧
             (c = 0 → psi L' ≤ psi L ∧ 2 * W L' ≤ psi L + 1 ∧ ∃ T, L' = 2 :: T) ∧
             (1 ≤ c → 2 * W L' ≤ psi L + 2 * wf (2 * c + 2)))
  | 0, L, hL, S => by
    have hst : Reach (cfg_BR1 (0 :: L) (2 :: S)) (cfg_EL1 (0 :: L) (0 :: 0 :: S)) :=
      (step_BR1_ge2 0 (0 :: L) S).trans (step_EL1_add_two 0 L (0 :: S))
    rcases ihEL L hL (0 :: S) with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
    · exact Or.inl ⟨L1, hst.trans hr1, hw1⟩
    · refine Or.inr ⟨2 :: L1, (hst.trans hr1).trans (step_BR1_00 L1 S), ?_, by omega⟩
      intro _
      refine ⟨?_, ?_, ⟨L1, rfl⟩⟩
      · rw [psi_cons_two]; omega
      · dsimp only [W]; change 2 * (1 + W L1) ≤ psi L + 1; omega
  | c + 1, L, hL, S => by
    have hst : Reach (cfg_BR1 (0 :: L) ((2 * (c + 1) + 2) :: S))
                     (cfg_EL1 (0 :: L) (0 :: (2 * c + 2) :: S)) := by
      rw [show 2 * (c + 1) + 2 = (2 * c + 2) + 2 by omega]
      exact (step_BR1_ge2 (2 * c + 2) (0 :: L) S).trans (step_EL1_add_two 0 L ((2 * c + 2) :: S))
    rcases ihEL L hL ((2 * c + 2) :: S) with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
    · have hp1 : psi L1 < limit := by have := psi_le L1; omega
      rcases step_even_ih ihEL c L1 hp1 S with
        ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, h0, hge1⟩
      · exact Or.inl ⟨L2, (hst.trans hr1).trans hr2, by have := psi_le L1; omega⟩
      · refine Or.inr ⟨L2, (hst.trans hr1).trans hr2, by omega, ?_⟩
        intro _
        cases c with
        | zero =>
          rcases h0 rfl with ⟨hp2, _, ⟨T, rfl⟩⟩
          rw [psi_cons_two] at hp2
          have hpl : psi L1 ≤ 2 * W L1 := psi_le L1
          change 2 * (1 + W T) ≤ psi L + 2 * 0
          omega
        | succ c' =>
          have hrec := hge1 (by omega)
          have hmono : wf (2 * (c' + 1) + 2) ≤ wf (2 * (c' + 1) + 4) := wf_even_mono (by omega)
          have hpl : psi L1 ≤ 2 * W L1 := psi_le L1
          have heq : 2 * (c' + 1 + 1) + 2 = 2 * (c' + 1) + 4 := by omega
          rw [heq]
          omega
    · refine Or.inr ⟨(2 * (c + 1) + 2) :: L1, ?_, by omega, ?_⟩
      · have h2 := step_BR1_0d (2 * c + 2) L1 S
        rw [show 2 * c + 2 + 2 = 2 * (c + 1) + 2 by omega] at h2
        exact (hst.trans hr1).trans h2
      · intro _
        dsimp only [W]
        omega

/-- Finish a state `cfg_BR1 (0 :: L) ((2 * c) :: S)` (no extra leading `0`) to a goal `GoodOut`. -/
private theorem finish_no0 {M L S : List ℕ} {c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S)) (cfg_BR1 (0 :: L) ((2 * c) :: S)))
    (hw : 2 * W L + 1 ≤ psi M) :
    GoodOut M c S := by
  cases c with
  | zero => exact Or.inr ⟨L, hr, hw⟩
  | succ c' =>
    have hlt : psi L < psi M := by have := psi_le L; omega
    have hrew : 2 * (c' + 1) = 2 * c' + 2 := by omega
    rw [hrew] at hr
    rcases step_even_ih ihEL c' L hlt S with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, h0, hge1⟩
    · exact Or.inr ⟨L1, hr.trans hr1, by have := psi_le L; omega⟩
    · refine Or.inl ⟨L1, hr.trans hr1, ?_, by omega⟩
      cases c' with
      | zero =>
        rcases h0 rfl with ⟨_, hw1, _⟩
        have hpl : psi L ≤ 2 * W L := psi_le L
        change 2 * W L1 ≤ psi M + 2 * 2
        omega
      | succ c'' =>
        have hrec := hge1 (by omega)
        have hmono : wf (2 * (c'' + 1) + 2) ≤ wf (2 * (c'' + 1) + 4) := wf_even_mono (by omega)
        have heq : 2 * (c'' + 1 + 1) + 4 = 2 * (c'' + 1) + 6 := by omega
        have hmono2 : wf (2 * (c'' + 1) + 4) ≤ wf (2 * (c'' + 1) + 6) := by
          have := wf_even_mono (c := c'' + 2) (by omega)
          rw [show 2 * (c'' + 2) + 2 = 2 * (c'' + 1) + 4 by omega,
              show 2 * (c'' + 2) + 4 = 2 * (c'' + 1) + 6 by omega] at this
          exact this
        have hpl : psi L ≤ 2 * W L := psi_le L
        rw [heq]
        omega

/--
Finish a state `cfg_BR1 (0 :: L) (0 :: (2 * c) :: S)` (with extra leading `0`) to `GoodOut`. -/
private theorem finish_has0 {M L S : List ℕ} {c : ℕ}
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S)) (cfg_BR1 (0 :: L) (0 :: (2 * c) :: S)))
    (hw : 2 * W L + 2 ≤ psi M) :
    GoodOut M c S := by
  have h1 := hr.trans (step_BR1_0d (2 * c) L S)
  refine Or.inl ⟨(2 * c + 2) :: L, h1, ?_, ?_⟩
  · cases c with
    | zero =>
      dsimp only [W]
      change 2 * (1 + W L) ≤ psi M + 2 * 0
      omega
    | succ c' =>
      have hmono : wf (2 * (c' + 1) + 2) ≤ wf (2 * (c' + 1) + 4) := wf_even_mono (by omega)
      dsimp only [W]
      omega
  · intro hc _
    subst hc
    rw [psi_cons_two]
    omega

/-- Single `0 :: 0 :: 2` (`0 :: rep02 1`) step using `ihEL`. -/
private theorem step_p02_one_ih {limit : ℕ} (ihEL : ELIH limit)
    (L : List ℕ) (hL : psi L < limit) (S : List ℕ) :
    (∃ L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: L') (0 :: S)) ∧
           psi L' + 1 ≤ psi L ∧ 2 * W L' ≤ psi L) ∨
    (∃ L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: 2 :: L') S) ∧
           2 * W L' ≤ psi L) := by
  have h0 : Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S)) (cfg_EL1 (0 :: L) (0 :: 2 :: 0 :: S)) := by
    have a1 := step_BR1_00 L (2 :: S)
    have a2 := step_BR1_ge2 0 (0 :: 2 :: L) S
    have a3 := step_EL1_add_two 0 (2 :: L) (0 :: S)
    have a4 := step_EL1_zero (2 :: L) (0 :: 0 :: S)
    have a5 := step_CL1_add_three 0 L (1 :: 0 :: S)
    exact (((a1.trans a2).trans a3).trans a4).trans a5
  rcases ihEL L hL (2 :: 0 :: S) with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · have hp1 : psi L1 < limit := by have := psi_le L1; omega
    have h2 : Reach (cfg_BR1 (0 :: L1) (2 :: 0 :: S)) (cfg_EL1 (0 :: L1) (0 :: 0 :: 0 :: S)) :=
      (step_BR1_ge2 0 (0 :: L1) (0 :: S)).trans (step_EL1_add_two 0 L1 (0 :: 0 :: S))
    rcases ihEL L1 hp1 (0 :: 0 :: S) with ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
    · refine Or.inr ⟨L2, ((h0.trans hr1).trans (h2.trans hr2)).trans (step_BR1_00 L2 S), ?_⟩
      have := psi_le L1; omega
    · refine Or.inl ⟨2 :: L2, ((h0.trans hr1).trans (h2.trans hr2)).trans (step_BR1_00 L2 (0 ::
        S)), ?_, ?_⟩
      · rw [psi_cons_two]; have := psi_le L1; omega
      · dsimp only [W]; change 2 * (1 + W L2) ≤ psi L; have := psi_le L1; omega
  · refine Or.inl ⟨4 :: L1, (h0.trans hr1).trans (sweep_BR_p02_one L1 (0 :: S)), ?_, ?_⟩
    · rw [psi_cons_ne2 (by omega)]; change 2 * (0 + W L1) + 1 ≤ psi L; omega
    · dsimp only [W]; change 2 * (0 + W L1) ≤ psi L; omega

/-- Arbitrary `0 :: rep02 (k + 1)` sweep using `ihEL`. -/
private theorem step_p02_many_ih {limit : ℕ} (ihEL : ELIH limit) :
    ∀ (k : ℕ) (L : List ℕ), psi L < limit → ∀ (S : List ℕ),
      (∃ L', Reach (cfg_BR1 (0 :: L) (0 :: (rep02 (k + 1) ++ S))) (cfg_BR1 (0 :: L') (0 :: S)) ∧
             psi L' + (k + 1) ≤ psi L ∧ 2 * W L' ≤ psi L) ∨
      (∃ a L', Reach (cfg_BR1 (0 :: L) (0 :: (rep02 (k + 1) ++ S)))
                     (cfg_BR1 (0 :: (rep4 a ++ 2 :: L')) S) ∧
               2 * W L' ≤ psi L)
  | 0, L, hL, S => by
    dsimp only [rep02, List.cons_append, List.nil_append]
    rcases step_p02_one_ih ihEL L hL S with ⟨L1, hr1, hp1, hw1⟩ | ⟨L1, hr1, hw1⟩
    · exact Or.inl ⟨L1, hr1, hp1, hw1⟩
    · exact Or.inr ⟨0, L1, hr1, hw1⟩
  | k + 1, L, hL, S => by
    dsimp only [rep02, List.cons_append]
    rcases step_p02_one_ih ihEL L hL (0 :: 2 :: (rep02 k ++ S)) with
      ⟨L1, hr1, hp1, hw1⟩ | ⟨L1, hr1, hw1⟩
    · have hp1' : psi L1 < limit := by omega
      rcases step_p02_many_ih ihEL k L1 hp1' S with
        ⟨L2, hr2, hp2, hw2⟩ | ⟨a, L2, hr2, hw2⟩
      · exact Or.inl ⟨L2, hr1.trans hr2, by omega, by omega⟩
      · exact Or.inr ⟨a, L2, hr1.trans hr2, by omega⟩
    · refine Or.inr ⟨k + 1, L1, hr1.trans (sweep_BR_p02 (k + 1) (2 :: L1) S), hw1⟩

/-- Helper: finish `cfg_BR1 (0 :: L) (0 :: rep02 (k + 1) ++ (2 * c) :: S)` to `GoodOut`
whenever `psi L + 3 ≤ psi M` (by parity, `2 * W L' ≤ psi L` forces `2 * W L' + 4 ≤ psi M` when
`psi M` is EVEN!). -/
private theorem finish_0_p02_2c {M L S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_BR1 (0 :: L) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hp : psi L + 3 ≤ psi M) :
    GoodOut M c S := by
  have hlt : psi L < psi M := by omega
  rcases step_p02_many_ih ihEL k L hlt ((2 * c) :: S) with
    ⟨L1, hr1, _, hw1⟩ | ⟨a, L1, hr1, hw1⟩
  · exact finish_has0 (hr.trans hr1) (by omega)
  · refine finish_no0 ihEL (hr.trans hr1) ?_
    rw [W_rep4_append]
    dsimp only [W]
    change 2 * (1 + W L1) + 1 ≤ psi M
    omega

/-- Helper: finish `cfg_EL1 (0 :: L) (0 :: 2 :: rep02 (k + 1) ++ (2 * c) :: S)`. -/
private theorem finish_EL_p02_2c {M L S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_EL1 (0 :: L) (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hp : psi L + 4 ≤ psi M) :
    GoodOut M c S := by
  have hlt : psi L < psi M := by omega
  rcases ihEL L hlt (2 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
    ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · have hlt1 : psi L1 < psi M := by have := psi_le L1; omega
    have h2 : Reach (cfg_BR1 (0 :: L1) (2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                    (cfg_EL1 (0 :: L1) (0 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))) :=
      (step_BR1_ge2 0 (0 :: L1) (rep02 (k + 1) ++ ((2 * c) :: S))).trans
        (step_EL1_add_two 0 L1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
    rcases ihEL L1 hlt1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
      ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
    · refine finish_0_p02_2c ihEL ((hr.trans hr1).trans (h2.trans hr2)) heven ?_
      have := psi_le L2; have := psi_le L1; omega
    · have hsw := ((hr.trans hr1).trans (h2.trans hr2)).trans
        ((step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
          (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S)))
      refine finish_no0 ihEL hsw ?_
      rw [W_rep4_append]; dsimp only [W]
      change 2 * (1 + W L2) + 1 ≤ psi M
      have := psi_le L1; omega
  · have hsw := (hr.trans hr1).trans
      ((sweep_BR_p02_one L1 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
        (sweep_BR_p02 (k + 1) (4 :: L1) ((2 * c) :: S)))
    refine finish_no0 ihEL hsw ?_
    rw [W_rep4_append]; dsimp only [W]
    change 2 * (0 + W L1) + 1 ≤ psi M
    omega

/-- Helper: finish `cfg_BR1 (0 :: L) (2 :: 2 :: rep02 (k + 1) ++ (2 * c) :: S)`. -/
private theorem finish_BR_22_p02_2c {M L S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_BR1 (0 :: L) (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hp : psi L + 4 ≤ psi M) :
    GoodOut M c S := by
  have hlt : psi L < psi M := by omega
  have h1 : Reach (cfg_BR1 (0 :: L) (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                  (cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))) :=
    (step_BR1_ge2 0 (0 :: L) (2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
      (step_EL1_add_two 0 L (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
  rcases ihEL L hlt (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
    ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · have hsw := ((hr.trans h1).trans hr1).trans
      ((sweep_BR_p02_one L1 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
        (sweep_BR_p02 (k + 1) (4 :: L1) ((2 * c) :: S)))
    refine finish_no0 ihEL hsw ?_
    rw [W_rep4_append]; dsimp only [W]
    change 2 * (0 + W L1) + 1 ≤ psi M; omega
  · have h2 : Reach (cfg_BR1 (0 :: L1) (0 :: 0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                    (cfg_EL1 (0 :: 2 :: L1) (0 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))) :=
      ((step_BR1_00 L1 (2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
        (step_BR1_ge2 0 (0 :: 2 :: L1) (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
        (step_EL1_add_two 0 (2 :: L1) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
    have hp2 : psi (2 :: L1) < psi M := by rw [psi_cons_two]; omega
    rcases ihEL (2 :: L1) hp2 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
      ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
    · rw [psi_cons_two] at hw2
      refine finish_0_p02_2c ihEL (((hr.trans h1).trans hr1).trans (h2.trans hr2)) heven ?_
      have := psi_le L2; omega
    · rw [psi_cons_two] at hw2
      have hsw := (((hr.trans h1).trans hr1).trans (h2.trans hr2)).trans
        ((step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
          (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S)))
      refine finish_no0 ihEL hsw ?_
      rw [W_rep4_append]; dsimp only [W]
      change 2 * (1 + W L2) + 1 ≤ psi M; omega

/-- Helper for `0 :: (rep02 k ++ (2*c) :: S)` where `k` can be `0` or `k' + 1`. -/
private theorem finish_0_p02_opt {M L S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_BR1 (0 :: L) (0 :: (rep02 k ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hL : 2 * W L + 2 ≤ psi M)
    (hL_psi : psi L + 3 ≤ psi M) :
    GoodOut M c S := by
  cases k with
  | zero => exact finish_has0 hr hL
  | succ k' => exact finish_0_p02_2c ihEL hr heven hL_psi

/-- Helper for `br_42_002_step`: finishes `cfg_BR1 (0 :: 4 :: 2 :: T) (0 :: rep02 (k + 1) ++ (2 *
  c) :: S)`
whenever `2 * W T + 4 ≤ psi M` (`heven : psi M % 2 = 0`). -/
private theorem finish_42_0_p02_2c {M T S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_BR1 (0 :: 4 :: 2 :: T) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hT : 2 * W T + 4 ≤ psi M) :
    GoodOut M c S := by
  dsimp only [rep02, List.cons_append] at hr
  have h1 := hr.trans (br_42_002_step T (rep02 k ++ ((2 * c) :: S)))
  -- At `cfg_EL1 (0 :: T) (0 :: 2 :: 0 :: 2 :: 2 :: 0 :: (rep02 k ++ (2 * c) :: S))`
  let R := rep02 k ++ ((2 * c) :: S)
  have hltT : psi T < psi M := by have := psi_le T; omega
  rcases ihEL T hltT (2 :: 0 :: 2 :: 2 :: 0 :: R) with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · -- ATE0 of T: `cfg_BR1 (0 :: L1) (2 :: 0 :: 2 :: 2 :: 0 :: R)`, `2 * W L1 ≤ psi T ≤ psi M - 4`
    have hlt1 : psi L1 < psi M := by have := psi_le L1; have := psi_le T; omega
    have hs1 : Reach (cfg_BR1 (0 :: L1) (2 :: 0 :: 2 :: 2 :: 0 :: R))
                     (cfg_EL1 (0 :: L1) (0 :: 0 :: 0 :: 2 :: 2 :: 0 :: R)) :=
      (step_BR1_ge2 0 (0 :: L1) (0 :: 2 :: 2 :: 0 :: R)).trans
        (step_EL1_add_two 0 L1 (0 :: 0 :: 2 :: 2 :: 0 :: R))
    rcases ihEL L1 hlt1 (0 :: 0 :: 2 :: 2 :: 0 :: R) with ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
    · -- ATE0: `cfg_BR1 (0 :: L2) (0 :: 0 :: 2 :: 2 :: 0 :: R)`, `2*W L2 ≤ psi L1 ≤ psi M - 4`
      have hlt2 : psi L2 < psi M := by have := psi_le L2; have := psi_le L1; have := psi_le T; omega
      rcases step_p02_one_ih ihEL L2 hlt2 (2 :: 0 :: R) with ⟨L3, hr3, hp3, hw3⟩ | ⟨L3, hr3, hw3⟩
      · -- D0: `cfg_BR1 (0 :: L3) (0 :: 2 :: 0 :: R)` -> `4 :: L3` on `0 :: R`
        -- `2*W L3 ≤ psi L2 ≤ psi M - 4`!
        have hs3 := ((((h1.trans hr1).trans (hs1.trans hr2)).trans hr3).trans
          (sweep_BR_p02_one L3 (0 :: R)))
        refine finish_0_p02_opt ihEL hs3 heven ?_ ?_
        · dsimp only [W]; change 2 * (0 + W L3) + 2 ≤ psi M
          have := psi_le L2; have := psi_le L1; have := psi_le T; omega
        · rw [psi_cons_ne2 (by omega)]; change 2 * (0 + W L3) + 3 ≤ psi M
          have := psi_le L2; have := psi_le L1; have := psi_le T; omega
      · -- DROP: `cfg_BR1 (0 :: 2 :: L3) (2 :: 0 :: R)`, `2 * W L3 ≤ psi L2 ≤ psi M - 4`!
        -- `psi (2 :: L3) = 2 * W L3 + 1 ≤ psi M - 3` (ODD!)
        have hlt3 : psi (2 :: L3) < psi M := by
          rw [psi_cons_two]; have := psi_le L2; have := psi_le L1; have := psi_le T; omega
        have hs3 : Reach (cfg_BR1 (0 :: 2 :: L3) (2 :: 0 :: R))
                         (cfg_EL1 (0 :: 2 :: L3) (0 :: 0 :: 0 :: R)) :=
          (step_BR1_ge2 0 (0 :: 2 :: L3) (0 :: R)).trans
            (step_EL1_add_two 0 (2 :: L3) (0 :: 0 :: R))
        rcases ihEL (2 :: L3) hlt3 (0 :: 0 :: R) with ⟨L4, hr4, hw4⟩ | ⟨L4, hr4, hw4⟩
        · -- ATE0: `cfg_BR1 (0 :: L4) (0 :: 0 :: R)` -> `2 :: L4` on `R`!
          -- `2 * W L4 ≤ psi (2 :: L3) ≤ psi M - 3` => EVEN <= ODD => `2 * W L4 ≤ psi M - 4`!
          -- `2 * W (2 :: L4) ≤ psi M - 2`!
          rw [psi_cons_two] at hw4
          have hsw := ((((h1.trans hr1).trans (hs1.trans hr2)).trans hr3).trans (hs3.trans
            hr4)).trans
            ((step_BR1_00 L4 R).trans (sweep_BR_p02 k (2 :: L4) ((2 * c) :: S)))
          refine finish_no0 ihEL hsw ?_
          rw [W_rep4_append]; dsimp only [W]
          change 2 * (1 + W L4) + 1 ≤ psi M
          have := psi_le L2; have := psi_le L1; have := psi_le T; omega
        · -- KEEP0: `cfg_BR1 (0 :: L4) (0 :: 0 :: 0 :: R)` -> `2 :: L4` on `0 :: R`!
          -- `2 * W L4 + 1 ≤ psi (2 :: L3) ≤ psi M - 3` => `2 * W L4 ≤ psi M - 4`!
          -- `psi (2 :: L4) = 2 * W L4 + 1 ≤ psi M - 3`! `2 * W (2 :: L4) ≤ psi M - 2`!
          rw [psi_cons_two] at hw4
          have hsw := ((((h1.trans hr1).trans (hs1.trans hr2)).trans hr3).trans (hs3.trans
            hr4)).trans
            (step_BR1_00 L4 (0 :: R))
          refine finish_0_p02_opt ihEL hsw heven ?_ ?_
          · dsimp only [W]; change 2 * (1 + W L4) + 2 ≤ psi M
            -- WAIT: check! `2 * W L4 + 1 ≤ 2 * W L3 + 1 ≤ psi M - 3` => `2 * W L4 ≤ psi M - 4` =>
            -- `2*(1 + W L4) = 2*W L4 + 2 ≤ psi M - 2`!
            -- So `2*(1+W L4) + 2 = psi M`! Wait if k = 0, `c = 0`: `0 :: 0 :: S -> 2 :: 2 :: L4`
            -- has `2 * W = psi M` AND `psi = psi M - 1`!!
            -- Check! `finish_has0` requires `2 * W L + 2 ≤ psi M`, NOT `+ 4`! Let's check exact
            -- arithmetic!
            have := psi_le L2; have := psi_le L1; have := psi_le T; omega
          · rw [psi_cons_two]; have := psi_le L2; have := psi_le L1; have := psi_le T; omega
    · -- KEEP0: `cfg_BR1 (0 :: L2) (0 :: 0 :: 0 :: 2 :: 2 :: 0 :: R)`, `2*W L2 + 1 ≤ psi L1 ≤ psi
      -- M - 4` => `2*W L2 ≤ psi M - 6`!
      have hs2 := (((h1.trans hr1).trans (hs1.trans hr2)).trans
        ((step_BR1_00 L2 (0 :: 2 :: 2 :: 0 :: R)).trans (sweep_BR_p02_one (2 :: L2) (2 :: 0 :: R))))
      -- Now `cfg_BR1 (0 :: 4 :: 2 :: L2) (2 :: 0 :: R)`, `2 * W (4 :: 2 :: L2) = 2 * W L2 + 2 ≤ psi
      -- M - 4`!
      have hlt2 : psi (4 :: 2 :: L2) < psi M := by
        rw [psi_cons_ne2 (by omega)]; dsimp only [W]
        change 2 * (0 + (1 + W L2)) < psi M; have := psi_le L1; have := psi_le T; omega
      have hs3 : Reach (cfg_BR1 (0 :: 4 :: 2 :: L2) (2 :: 0 :: R))
                       (cfg_EL1 (0 :: 4 :: 2 :: L2) (0 :: 0 :: 0 :: R)) :=
        (step_BR1_ge2 0 (0 :: 4 :: 2 :: L2) (0 :: R)).trans
          (step_EL1_add_two 0 (4 :: 2 :: L2) (0 :: 0 :: R))
      rcases ihEL (4 :: 2 :: L2) hlt2 (0 :: 0 :: R) with ⟨L3, hr3, hw3⟩ | ⟨L3, hr3, hw3⟩
      · rw [psi_cons_ne2 (by omega)] at hw3
        dsimp only [W, wf] at hw3
        have hsw := (hs2.trans (hs3.trans hr3)).trans
          ((step_BR1_00 L3 R).trans (sweep_BR_p02 k (2 :: L3) ((2 * c) :: S)))
        refine finish_no0 ihEL hsw ?_
        rw [W_rep4_append]; dsimp only [W]
        change 2 * (1 + W L3) + 1 ≤ psi M; have := psi_le L1; have := psi_le T; omega
      · rw [psi_cons_ne2 (by omega)] at hw3
        dsimp only [W, wf] at hw3
        have hsw := (hs2.trans (hs3.trans hr3)).trans (step_BR1_00 L3 (0 :: R))
        refine finish_0_p02_opt ihEL hsw heven ?_ ?_
        · dsimp only [W]; change 2 * (1 + W L3) + 2 ≤ psi M; have := psi_le L1; have := psi_le T;
            omega
        · rw [psi_cons_two]; have := psi_le L1; have := psi_le T; omega
  · -- KEEP0 of T: `cfg_BR1 (0 :: L1) (0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)`, `2 * W L1 + 1 ≤ psi T ≤
    -- psi M - 4` => `2 * W L1 ≤ psi M - 6`!
    have hs1 := (h1.trans hr1).trans
      ((sweep_BR_p02_one L1 (0 :: 2 :: 2 :: 0 :: R)).trans (sweep_BR_p02_one (4 :: L1) (2 :: 0 ::
        R)))
    -- At `cfg_BR1 (0 :: 4 :: 4 :: L1) (2 :: 0 :: R)` with `2 * W L1 ≤ psi M - 6`!
    have hlt1 : psi (4 :: 4 :: L1) < psi M := by
      rw [psi_cons_ne2 (by omega)]; dsimp only [W]; change 2 * (0 + (0 + W L1)) < psi M
      have := psi_le T; omega
    have hs2 : Reach (cfg_BR1 (0 :: 4 :: 4 :: L1) (2 :: 0 :: R))
                     (cfg_EL1 (0 :: 4 :: 4 :: L1) (0 :: 0 :: 0 :: R)) :=
      (step_BR1_ge2 0 (0 :: 4 :: 4 :: L1) (0 :: R)).trans
        (step_EL1_add_two 0 (4 :: 4 :: L1) (0 :: 0 :: R))
    rcases ihEL (4 :: 4 :: L1) hlt1 (0 :: 0 :: R) with ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
    · rw [psi_cons_ne2 (by omega)] at hw2
      dsimp only [W, wf] at hw2
      have hsw := (hs1.trans (hs2.trans hr2)).trans
        ((step_BR1_00 L2 R).trans (sweep_BR_p02 k (2 :: L2) ((2 * c) :: S)))
      refine finish_no0 ihEL hsw ?_
      rw [W_rep4_append]; dsimp only [W]
      change 2 * (1 + W L2) + 1 ≤ psi M; have := psi_le T; omega
    · rw [psi_cons_ne2 (by omega)] at hw2
      dsimp only [W, wf] at hw2
      have hsw := (hs1.trans (hs2.trans hr2)).trans (step_BR1_00 L2 (0 :: R))
      refine finish_0_p02_opt ihEL hsw heven ?_ ?_
      · dsimp only [W]; change 2 * (1 + W L2) + 2 ≤ psi M; have := psi_le T; omega
      · rw [psi_cons_two]; have := psi_le T; omega

/-- Helper for Case `x = 6` (`2D`) and `M'' = 4 :: M'''`: `cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: 0 ::
  rep02 (k + 1) ++ (2 * c) :: S)`
when `2 * W L + 4 ≤ psi M` (`heven`). -/
private theorem finish_EL_p02_0_p02_2c {M L S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_EL1 (0 :: L) (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hL : 2 * W L + 4 ≤ psi M) :
    GoodOut M c S := by
  have hlt : psi L < psi M := by have := psi_le L; omega
  rcases ihEL L hlt (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
    ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · -- ATE0: `cfg_BR1 (0 :: L1) (0 :: 2 :: 0 :: rep02 (k+1) ...)` -> `4 :: L1` on `0 :: rep02
    -- (k+1) ...`
    have hsw := (hr.trans hr1).trans (sweep_BR_p02_one L1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
    refine finish_0_p02_2c ihEL hsw heven ?_
    rw [psi_cons_ne2 (by omega)]; change 2 * (0 + W L1) + 3 ≤ psi M; have := psi_le L; omega
  · -- KEEP0: `2 * W L1 + 1 ≤ psi L ≤ psi M - 4` => `2 * W L1 ≤ psi M - 6`!
    have hlt1 : psi L1 < psi M := by have := psi_le L1; have := psi_le L; omega
    rcases step_p02_one_ih ihEL L1 hlt1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
      ⟨L2, hr2, _, hw2⟩ | ⟨L2, hr2, hw2⟩
    · have hsw := ((hr.trans hr1).trans hr2).trans
        ((step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
          (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S)))
      refine finish_no0 ihEL hsw ?_
      rw [W_rep4_append]; dsimp only [W]; change 2 * (1 + W L2) + 1 ≤ psi M
      have := psi_le L1; have := psi_le L; omega
    · refine finish_0_p02_2c ihEL ((hr.trans hr1).trans hr2) heven ?_
      rw [psi_cons_two]; have := psi_le L1; have := psi_le L; omega

/-- Helper for `2D` (`x = 6`): `cfg_EL1 (0 :: Y) (0 :: 2 :: 0 :: 2 :: 0 :: rep02 (k + 1) ++ (2 *
  c) :: S)`
when `2 * W Y + 4 ≤ psi M`. -/
private theorem finish_2D {M Y S : List ℕ} {k c : ℕ}
    (ihEL : ELIH (psi M))
    (hr : Reach (cfg_CL1 (inc1 M) ((2 * c + 1) :: S))
                (cfg_EL1 (0 :: Y) (0 :: 2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    (heven : psi M % 2 = 0)
    (hY : 2 * W Y + 4 ≤ psi M) :
    GoodOut M c S := by
  have hltY : psi Y < psi M := by have := psi_le Y; omega
  rcases ihEL Y hltY (2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
    ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · have hlt1 : psi L1 < psi M := by have := psi_le L1; have := psi_le Y; omega
    have hs1 : Reach (cfg_BR1 (0 :: L1) (2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                     (cfg_EL1 (0 :: L1) (0 :: 0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++
                       ((2 * c) :: S)))) :=
      (step_BR1_ge2 0 (0 :: L1) (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
        (step_EL1_add_two 0 L1 (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
    rcases ihEL L1 hlt1 (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
      ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
    · have hlt2 : psi L2 < psi M := by have := psi_le L2; have := psi_le L1; have := psi_le Y; omega
      rcases step_p02_one_ih ihEL L2 hlt2 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
        ⟨L3, hr3, _, hw3⟩ | ⟨L3, hr3, hw3⟩
      · have hsw := (((hr.trans hr1).trans (hs1.trans hr2)).trans hr3).trans
          ((step_BR1_00 L3 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
            (sweep_BR_p02 (k + 1) (2 :: L3) ((2 * c) :: S)))
        refine finish_no0 ihEL hsw ?_
        rw [W_rep4_append]; dsimp only [W]; change 2 * (1 + W L3) + 1 ≤ psi M
        have := psi_le L2; have := psi_le L1; have := psi_le Y; omega
      · refine finish_0_p02_2c ihEL (((hr.trans hr1).trans (hs1.trans hr2)).trans hr3) heven ?_
        rw [psi_cons_two]; have := psi_le L2; have := psi_le L1; have := psi_le Y; omega
    · have hsw := ((hr.trans hr1).trans (hs1.trans hr2)).trans
        ((step_BR1_00 L2 (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
          (sweep_BR_p02_one (2 :: L2) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
      refine finish_0_p02_2c ihEL hsw heven ?_
      rw [psi_cons_ne2 (by omega)]; dsimp only [W]; change 2 * (0 + (1 + W L2)) + 3 ≤ psi M
      have := psi_le L1; have := psi_le Y; omega
  · have hsw := (hr.trans hr1).trans
      ((sweep_BR_p02_one L1 (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
        (sweep_BR_p02_one (4 :: L1) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
    refine finish_0_p02_2c ihEL hsw heven ?_
    rw [psi_cons_ne2 (by omega)]; dsimp only [W]; change 2 * (0 + (0 + W L1)) + 3 ≤ psi M
    have := psi_le Y; omega

/-- MASTER THEOREM: Unified `mCL (inc1 M) ((2 * c + 1) :: S)` (`c = 0` is `mEL (0 :: M) (0 :: S)`!).
Proved by nested strong induction on `(psi M, M.length)` constructively without excluded middle. -/
private theorem mCL_bump_spec : ∀ (M : List ℕ) (c : ℕ) (S : List ℕ), GoodOut M c S := by
  intro M
  -- Strong induction on `p = psi M` (outer) and `n = M.length` (inner):
  suffices h : ∀ p : ℕ, ∀ n : ℕ, ∀ M : List ℕ, psi M = p → M.length = n →
      ∀ c S, GoodOut M c S from
    fun c S => h (psi M) M.length M rfl rfl c S
  intro p
  refine Nat.strongRecOn p ?_
  intro p ihP n
  refine Nat.strongRecOn n ?_
  intro n ihN M hpM hnM c S
  have ihEL : ELIH (psi M) := by
    intro L hL S'
    have hg := ihP (psi L) (by omega) L.length L rfl rfl 0 S'
    rcases hg with ⟨L', hr, hw, _⟩ | ⟨L', hr, hw⟩
    · refine Or.inl ⟨L', (step_EL1_zero L (0 :: S')).trans hr, ?_⟩
      change 2 * W L' ≤ psi L + 2 * 0 at hw; omega
    · exact Or.inr ⟨L', (step_EL1_zero L (0 :: S')).trans hr, hw⟩
  cases M with
  | nil =>
    -- `cfg_CL1 [0] ((2*c+1) :: S) -> cfg_CL1 [] ((2*c+3) :: S) -> cfg_EL1 [] ((2*c+4) :: S) ->
    -- cfg_BR1 [0, 2*c+4] S`
    have hr := ((step_CL1_zero [] ((2 * c + 1) :: S)).trans
      (step_CL1_nil ((2 * c + 3) :: S))).trans (step_EL1_nil_cons (2 * c + 4) S)
    refine Or.inl ⟨[2 * c + 4], hr, ?_, ?_⟩
    · dsimp only [W, psi]; omega
    · intro _ ⟨_, hne⟩; cases hne
  | cons v M' =>
    match v with
    | 0 =>
      -- `inc1 (0 :: M') = 1 :: M'`; `step_CL1_one` -> `cfg_CL1 (inc1 M') ((2*(c+1)+1) :: S)`
      have hpsiM : psi (0 :: M') = 2 * (2 + W M') := by rw [psi_cons_ne2 (by omega)]; rfl
      have hlt : psi M' < p := by have := psi_le M'; omega
      have h1 : Reach (cfg_CL1 (1 :: M') ((2 * c + 1) :: S))
                      (cfg_CL1 (inc1 M') ((2 * (c + 1) + 1) :: S)) := by
        have := step_CL1_one M' ((2 * c + 1) :: S)
        simpa [inc1, show 2 * c + 1 + 1 + 1 = 2 * (c + 1) + 1 by omega] using this
      rcases ihP (psi M') hlt M'.length M' rfl rfl (c + 1) S with ⟨L', hr, hw, _⟩ | ⟨L', hr, hw⟩
      · refine Or.inl ⟨L', h1.trans hr, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
        have hstep := wf_even_step c
        have := psi_le M'; omega
      · exact Or.inr ⟨L', h1.trans hr, by have := psi_le M'; omega⟩
    | 1 =>
      -- `inc1 (1 :: M') = 2 :: M'`; `step_CL1_two` + `step_EB1_zero` -> `cfg_BR1 (0 :: inc1 M')
      -- ((2*c+2) :: S)`
      have hpsiM : psi (1 :: M') = 2 * (3 + W M') := by rw [psi_cons_ne2 (by omega)]; rfl
      have h1 : Reach (cfg_CL1 (2 :: M') ((2 * c + 1) :: S))
                      (cfg_BR1 (0 :: inc1 M') ((2 * c + 2) :: S)) :=
        (step_CL1_two M' ((2 * c + 1) :: S)).trans (step_EB1_zero M' ((2 * c + 2) :: S))
      have hlt : psi (inc1 M') < psi (1 :: M') := by
        have := psi_le (inc1 M'); have := W_inc1_le M'; omega
      rcases step_even_ih ihEL c (inc1 M') hlt S with
        ⟨L', hr, hw⟩ | ⟨L', hr, h0, hge1⟩
      · exact Or.inr ⟨L', h1.trans hr, by have := psi_le (inc1 M'); have := W_inc1_le M'; omega⟩
      · refine Or.inl ⟨L', h1.trans hr, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
        cases c with
        | zero =>
          rcases h0 rfl with ⟨_, hw, _⟩
          have := psi_le (inc1 M'); have := W_inc1_le M'
          change 2 * W L' ≤ psi (1 :: M') + 2 * 0; omega
        | succ c' =>
          have hrec := hge1 (by omega)
          have hmono := wf_even_mono (c := c' + 1) (by omega)
          have := psi_le (inc1 M'); have := W_inc1_le M'
          omega
    | 2 =>
      -- `inc1 (2 :: M') = 3 :: M'`; `step_CL1_add_three` -> `cfg_EL1 (0 :: M') (0 :: (2*c+2) :: S)`
      have hpsiM : psi (2 :: M') = 2 * W M' + 1 := psi_cons_two M'
      have hlt : psi M' < psi (2 :: M') := by have := psi_le M'; omega
      have h1 : Reach (cfg_CL1 (3 :: M') ((2 * c + 1) :: S))
                      (cfg_EL1 (0 :: M') (0 :: (2 * c + 2) :: S)) :=
        step_CL1_add_three 0 M' ((2 * c + 1) :: S)
      rcases ihEL M' hlt ((2 * c + 2) :: S) with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
      · have hlt1 : psi L1 < psi (2 :: M') := by have := psi_le L1; have := psi_le M'; omega
        rcases step_even_ih ihEL c L1 hlt1 S with ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, h0, hge1⟩
        · exact Or.inr ⟨L2, (h1.trans hr1).trans hr2,
            by have := psi_le L1; have := psi_le M'; omega⟩
        · refine Or.inl ⟨L2, (h1.trans hr1).trans hr2, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
          cases c with
          | zero =>
            rcases h0 rfl with ⟨hp2, _, ⟨T, rfl⟩⟩
            rw [psi_cons_two] at hp2
            have := psi_le L1; have := psi_le M'
            change 2 * (1 + W T) ≤ psi (2 :: M') + 2 * 0; omega
          | succ c' =>
            have hrec := hge1 (by omega)
            have hmono := wf_even_mono (c := c' + 1) (by omega)
            have := psi_le L1; have := psi_le M'; omega
      · refine Or.inl ⟨(2 * c + 4) :: L1, (h1.trans hr1).trans (step_BR1_0d (2 * c + 2) L1 S),
          ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
        dsimp only [W]; have := psi_le M'; omega
    | 3 =>
      -- `inc1 (3 :: M') = 4 :: M'`; ZERO RECURSION!
      have hpsiM : psi (3 :: M') = 2 * (2 + W M') := by rw [psi_cons_ne2 (by omega)]; rfl
      have h1 := ((step_CL1_add_three 1 M' ((2 * c + 1) :: S)).trans
        (step_EL1_one M' (0 :: (2 * c + 2) :: S))).trans
        ((step_EB1_zero M' (0 :: (2 * c + 2) :: S)).trans (step_BR1_0d (2 * c + 2) (inc1 M') S))
      refine Or.inl ⟨(2 * c + 4) :: inc1 M', h1, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
      dsimp only [W]; have := W_inc1_le M'; omega
    | 4 =>
      -- `inc1 (4 :: M') = 5 :: M'`; use `ihN` on `M'` (same/smaller psi, STRICTLY shorter length!)
      have hpsiM : psi (4 :: M') = 2 * W M' := by
        rw [psi_cons_ne2 (by omega)]; change 2 * (0 + W M') = 2 * W M'; omega
      have h1 : Reach (cfg_CL1 (5 :: M') ((2 * c + 1) :: S))
                      (cfg_EL1 (0 :: M') (0 :: 0 :: (2 * c + 2) :: S)) :=
        (step_CL1_add_three 2 M' ((2 * c + 1) :: S)).trans
          (step_EL1_add_two 0 M' (0 :: (2 * c + 2) :: S))
      have hM' : (∃ L1, Reach (cfg_EL1 (0 :: M') (0 :: 0 :: (2 * c + 2) :: S))
                              (cfg_BR1 (0 :: L1) (0 :: (2 * c + 2) :: S)) ∧ 2 * W L1 ≤ psi M') ∨
                 (∃ L1, Reach (cfg_EL1 (0 :: M') (0 :: 0 :: (2 * c + 2) :: S))
                              (cfg_BR1 (0 :: L1) (0 :: 0 :: (2 * c + 2) :: S)) ∧
                                2 * W L1 + 1 ≤ psi M') := by
        have hle : psi M' ≤ p := by have := psi_le M'; omega
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · rcases ihP (psi M') hlt M'.length M' rfl rfl 0 (0 :: (2 * c + 2) :: S) with
            ⟨L1, hr1, hw1, _⟩ | ⟨L1, hr1, hw1⟩
          · exact Or.inl ⟨L1, (step_EL1_zero M' _).trans hr1,
              by change 2 * W L1 ≤ psi M' + 2 * 0 at hw1; omega⟩
          · exact Or.inr ⟨L1, (step_EL1_zero M' _).trans hr1, hw1⟩
        · have hnlt : M'.length < n := by dsimp only [List.length] at hnM; omega
          rcases ihN M'.length hnlt M' heq rfl 0 (0 :: (2 * c + 2) :: S) with
            ⟨L1, hr1, hw1, _⟩ | ⟨L1, hr1, hw1⟩
          · exact Or.inl ⟨L1, (step_EL1_zero M' _).trans hr1,
              by change 2 * W L1 ≤ psi M' + 2 * 0 at hw1; omega⟩
          · exact Or.inr ⟨L1, (step_EL1_zero M' _).trans hr1, hw1⟩
      rcases hM' with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
      · refine Or.inl ⟨(2 * c + 4) :: L1, (h1.trans hr1).trans (step_BR1_0d (2 * c + 2) L1 S),
          ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
        dsimp only [W]; have := psi_le M'; omega
      · have hlt2 : psi (2 :: L1) < psi (4 :: M') := by
          rw [psi_cons_two]; have := psi_le M'; omega
        have h2 := (h1.trans hr1).trans (step_BR1_00 L1 ((2 * c + 2) :: S))
        rcases step_even_ih ihEL c (2 :: L1) hlt2 S with ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, h0, hge1⟩
        · rw [psi_cons_two] at hw2
          exact Or.inr ⟨L2, h2.trans hr2, by have := psi_le M'; omega⟩
        · refine Or.inl ⟨L2, h2.trans hr2, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
          cases c with
          | zero =>
            rcases h0 rfl with ⟨hp2, _, ⟨T, rfl⟩⟩
            rw [psi_cons_two, psi_cons_two] at hp2
            have := psi_le M'; change 2 * (1 + W T) ≤ psi (4 :: M') + 2 * 0; omega
          | succ c' =>
            have hrec := hge1 (by omega)
            rw [psi_cons_two] at hrec
            have hmono := wf_even_mono (c := c' + 1) (by omega)
            have := psi_le M'; omega
    | 5 =>
      have hpsiM : psi (5 :: M') = 2 * (2 + W M') := by rw [psi_cons_ne2 (by omega)]; rfl
      have heven : psi (5 :: M') % 2 = 0 := by omega
      cases M' with
      | nil =>
        -- Concrete 50-step proof via `cl_6_nil_step`!
        refine Or.inl ⟨(2 * c + 2) :: 2 :: 4 :: 4 :: 4 :: [], cl_6_nil_step c S, ?_, ?_⟩
        · cases c with
          | zero => decide
          | succ c' =>
            have hmono := wf_even_mono (c := c' + 1) (by omega)
            dsimp only [W, psi]; change 2 * (wf (2 * (c' + 1) + 2) + (1 + 0)) ≤ 2 * (2 + 0) + 2 *
              wf (2 * (c' + 1) + 4)
            omega
        · intro hc _; subst hc; decide
      | cons hd tl =>
        -- Check whether `hd = 4`!
        cases hbd : Nat.beq hd 4 with
        | false =>
          -- `hd ≠ 4`: NO `sweep_EL3_f4` needed! `W (inc1 (hd :: tl)) ≤ W (hd :: tl) + 1`!
          have hne4 : hd ≠ 4 := fun h => by subst h; cases hbd
          have h1 : Reach (cfg_CL1 (6 :: hd :: tl) ((2 * c + 1) :: S))
                          (cfg_BR1 (0 :: 2 :: inc1 (hd :: tl)) ((2 * c + 2) :: S)) :=
            (((step_CL1_add_three 3 (hd :: tl) ((2 * c + 1) :: S)).trans
              (step_EL1_add_two 1 (hd :: tl) (0 :: (2 * c + 2) :: S))).trans
              (step_EL1_one (hd :: tl) (0 :: 0 :: (2 * c + 2) :: S))).trans
              ((step_EB1_zero (hd :: tl) (0 :: 0 :: (2 * c + 2) :: S)).trans
                (step_BR1_00 (inc1 (hd :: tl)) ((2 * c + 2) :: S)))
          have hwinc : W (inc1 (hd :: tl)) ≤ W (hd :: tl) + 1 := by
            dsimp only [inc1, W]; have := wf_add_one_le_ne4 hne4; omega
          have hltY : psi (2 :: inc1 (hd :: tl)) < psi (5 :: hd :: tl) := by
            rw [psi_cons_two]; omega
          rcases step_even_ih ihEL c (2 :: inc1 (hd :: tl)) hltY S with
            ⟨L', hr, hw⟩ | ⟨L', hr, h0, hge1⟩
          · rw [psi_cons_two] at hw
            exact Or.inr ⟨L', h1.trans hr, by omega⟩
          · refine Or.inl ⟨L', h1.trans hr, ?_, ?_⟩
            · cases c with
              | zero =>
                rcases h0 rfl with ⟨_, hw, _⟩
                rw [psi_cons_two] at hw
                change 2 * W L' ≤ psi (5 :: hd :: tl) + 2 * 0; omega
              | succ c' =>
                have hrec := hge1 (by omega)
                rw [psi_cons_two] at hrec
                have hmono := wf_even_mono (c := c' + 1) (by omega); omega
            · intro hc _
              subst hc
              rcases h0 rfl with ⟨hp', _, _⟩
              rw [psi_cons_two] at hp'; omega
        | true =>
          -- `hd = 4`: strip ALL leading `4`s via `strip4`!
          have hhd : hd = 4 := Nat.eq_of_beq_eq_true hbd
          subst hhd
          obtain ⟨hstr, hne⟩ := strip4_spec tl
          set k := (strip4 tl).1
          set R_tail := (strip4 tl).2
          have hlist : 4 :: tl = rep4 (k + 1) ++ R_tail := by
            dsimp only [rep4, List.cons_append]; exact congrArg (4 :: ·) hstr
          have hw_eq : W (4 :: tl) = W R_tail := by
            rw [hlist, W_rep4_append]
          have hpsi_eq : psi (5 :: 4 :: tl) = 2 * (2 + W R_tail) := by
            rw [hpsiM, hw_eq]
          -- Step via `cl_6_rep4_step` to `cfg_EL1 (0 :: inc1 R_tail) (rep02 (k + 2) ++ (2 * c) ::
          -- S)`!
          have hpre : Reach (cfg_CL1 (6 :: 4 :: tl) ((2 * c + 1) :: S))
                            (cfg_EL1 (0 :: inc1 R_tail) (0 :: 2 :: (rep02 (k + 1) ++
                              ((2 * c) :: S)))) := by
            rw [hlist]; exact cl_6_rep4_step k c R_tail S
          cases hRt : R_tail with
          | nil =>
            -- Concrete `M = 5 :: rep4 (k + 1)` via `br_6_202_step` + `br_rep4_6_002_step`!
            have h0 : Reach (cfg_EL1 [0, 0] (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                            (cfg_BR1 [0, 6] (2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))) :=
              (((step_EL1_zero [0] _).trans (step_CL1_one [] _)).trans
                (step_CL1_zero [] _)).trans
                ((step_CL1_nil _).trans (step_EL1_nil_cons 6 _))
            rw [hRt] at hpre hw_eq hpsi_eq
            have hstart : Reach (cfg_CL1 (6 :: 4 :: tl) ((2 * c + 1) :: S))
                                (cfg_BR1 [0, 6] (2 :: 0 :: 2 :: (rep02 k ++ ((2 * c) :: S)))) :=
              hpre.trans h0
            have h1 := hstart.trans (br_6_202_step (rep02 k ++ ((2 * c) :: S)))
            cases hk : k with
            | zero =>
              rw [hk] at h1
              dsimp only [rep02, List.nil_append] at h1
              refine finish_has0 h1 ?_
              have hw6 : W (rep4 6) = 0 := by decide
              have hw0 : psi (5 :: 4 :: tl) = 4 := by simpa [W] using hpsi_eq
              omega
            | succ k' =>
              rw [hk] at h1
              dsimp only [rep02, List.cons_append] at h1
              have h2 := (h1.trans (br_rep4_6_002_step (rep02 k' ++ ((2 * c) :: S)))).trans
                (sweep_BR_p02 k' (2 :: rep4 8) ((2 * c) :: S))
              refine finish_no0 ihEL h2 ?_
              rw [W_rep4_append]
              have hw8 : W (2 :: rep4 8) = 1 := by decide
              have hw0 : psi (5 :: 4 :: tl) = 4 := by simpa [W] using hpsi_eq
              omega
          | cons x M'' =>
            have hxne4 : x ≠ 4 := hne x M'' hRt
            have hpsi_x : psi (5 :: 4 :: tl) = 2 * (2 + (wf x + W M'')) := by
              rw [hpsi_eq, hRt]; rfl
            rw [hRt] at hpre
            rcases wf_inc_class x with rfl | hle | rfl | rfl | rfl | ⟨m, rfl⟩
            · exact absurd rfl hxne4
            · -- Case 2A: `wf (x + 1) ≤ wf x` -> `W (inc1 (x :: M'')) ≤ W (x :: M'')`!
              refine finish_EL_p02_2c ihEL hpre heven ?_
              have := psi_le ((x + 1) :: M'')
              dsimp only [inc1, W] at this ⊢; omega
            · -- Case 2B: `x = 0` (`inc1 = 1 :: M''`)!
              have h1 := hpre.trans
                (((step_EL1_zero (1 :: M'') _).trans (step_CL1_two M'' _)).trans
                  (step_EB1_zero M'' (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
              refine finish_BR_22_p02_2c ihEL h1 heven ?_
              have := W_inc1_le M''
              have := psi_le (inc1 M'')
              change psi (5 :: 4 :: tl) = 2 * (2 + (2 + W M'')) at hpsi_x
              omega
            · -- Case 2E: `x = 2` (`inc1 = 3 :: M''`)!
              have h1 : Reach (cfg_EL1 (0 :: 3 :: M'') (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) ::
                S))))
                              (cfg_EL1 (0 :: inc1 M'') (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++
                                ((2 * c) :: S)))) := by
                have a1 := step_EL1_zero (3 :: M'') (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a2 := step_CL1_add_three 1 M'' (1 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a3 := step_EL1_one M'' (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a4 := step_EB1_zero M'' (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have b5 := sweep_BR_p02_one (inc1 M'') (2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have b6 := step_BR1_ge2 0 (0 :: 4 :: inc1 M'') (rep02 (k + 1) ++ ((2 * c) :: S))
                have b7 := step_EL1_add_two 0 (4 :: inc1 M'') (0 :: (rep02 (k + 1) ++ ((2 * c) ::
                  S)))
                have b8 := sweep_EL_f4_one (inc1 M'') (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                exact (((((((a1.trans a2).trans a3).trans a4).trans b5).trans b6).trans b7).trans
                  b8)
              have h2 := hpre.trans h1
              change psi (5 :: 4 :: tl) = 2 * (2 + (1 + W M'')) at hpsi_x
              cases M'' with
              | nil =>
                -- Concrete `M = 5 :: rep4 (k + 1) ++ [2]` via `br_46_002_step`!
                have hc1 : Reach (cfg_EL1 [0, 0] (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c)
                  :: S))))
                                 (cfg_BR1 [0, 4, 6] (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))) := by
                  let R0 := 0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))
                  have q1 := step_EL1_zero [0] (0 :: R0)
                  have q2 := step_CL1_one [] (1 :: R0)
                  have q3 := step_CL1_zero [] (3 :: R0)
                  have q4 := step_CL1_nil (5 :: R0)
                  have q5 := step_EL1_nil_cons 6 R0
                  have q6 := sweep_BR_p02_one [6] (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                  exact ((((q1.trans q2).trans q3).trans q4).trans q5).trans q6
                have hc2 : Reach (cfg_BR1 [0, 4, 6] (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                                 (cfg_BR1 (0 :: (rep4 k ++ 2 :: 2 :: rep4 7)) ((2 * c) :: S)) := by
                  dsimp only [rep02, List.cons_append]
                  exact (br_46_002_step (rep02 k ++ ((2 * c) :: S))).trans
                    (sweep_BR_p02 k (2 :: 2 :: rep4 7) ((2 * c) :: S))
                refine finish_no0 ihEL ((h2.trans hc1).trans hc2) ?_
                rw [W_rep4_append]
                have hw7 : W (2 :: 2 :: rep4 7) = 2 := by decide
                have hw0 : psi (5 :: 4 :: tl) = 6 := by simpa [W] using hpsi_x
                omega
              | cons y M''' =>
                cases hby : Nat.beq y 4 with
                | false =>
                  have hyne4 : y ≠ 4 := fun h => by subst h; cases hby
                  refine finish_EL_p02_0_p02_2c ihEL h2 heven ?_
                  dsimp only [inc1, W] at hpsi_x ⊢
                  have := wf_add_one_le_ne4 hyne4; omega
                | true =>
                  -- `y = 4`: `inc1 (4 :: M''') = 5 :: M'''`! Apply FULL `ihP` WITH the strong `5 ::
                  -- _` clause!
                  have hy4 : y = 4 := Nat.eq_of_beq_eq_true hby
                  subst hy4
                  have hpsi5 : psi (5 :: M''') = 2 * (2 + W M''') := by
                    rw [psi_cons_ne2 (by omega)]; rfl
                  have hlt5 : psi (5 :: M''') < p := by
                    dsimp only [W] at hpsi_x
                    change psi (5 :: 4 :: tl) = 2 * (2 + (1 + (0 + W M'''))) at hpsi_x; omega
                  rcases ihP (psi (5 :: M''')) hlt5 (5 :: M''').length (5 :: M''') rfl rfl
                    0 (0 :: 2 :: 0 :: (rep02 (k + 1) ++ ((2 * c) :: S))) with
                    ⟨L1, hr1, hw1, hstr5⟩ | ⟨L1, hr1, hw1⟩
                  · have hreach1 : Reach (cfg_CL1 (6 :: 4 :: tl) ((2 * c + 1) :: S))
                                         (cfg_BR1 (0 :: L1) (0 :: 2 :: 0 :: (rep02 (k + 1) ++
                                           ((2 * c) :: S)))) :=
                      h2.trans ((step_EL1_zero (5 :: M''') _).trans hr1)
                    have hpsL1 : psi L1 + 1 ≤ psi (5 :: M''') := hstr5 rfl ⟨M''', rfl⟩
                    cases L1 with
                    | nil =>
                      have hsw :=
                        hreach1.trans (sweep_BR_p02_one [] (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                      refine finish_0_p02_2c ihEL hsw heven ?_
                      rw [psi_cons_ne2 (by omega)]; dsimp only [W] at hpsi_x ⊢
                      change 2 * (0 + 0) + 3 ≤ psi (5 :: 4 :: tl); omega
                    | cons z Z =>
                      cases hbz : Nat.beq z 2 with
                      | true =>
                        have hz2 : z = 2 := Nat.eq_of_beq_eq_true hbz
                        subst hz2
                        rw [psi_cons_two] at hpsL1
                        have hsw := hreach1.trans
                          (sweep_BR_p02_one (2 :: Z) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                        refine finish_42_0_p02_2c ihEL hsw heven ?_
                        dsimp only [W] at hpsi_x
                        change psi (5 :: 4 :: tl) = 2 * (2 + (1 + (0 + W M'''))) at hpsi_x
                        omega
                      | false =>
                        have hzne2 : z ≠ 2 := fun h => by subst h; cases hbz
                        rw [psi_cons_ne2 hzne2] at hpsL1
                        have hsw := hreach1.trans
                          (sweep_BR_p02_one (z :: Z) (0 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                        refine finish_0_p02_2c ihEL hsw heven ?_
                        rw [psi_cons_ne2 (by omega)]
                        dsimp only [W] at hpsi_x ⊢
                        change psi (5 :: 4 :: tl) = 2 * (2 + (1 + (0 + W M'''))) at hpsi_x
                        change 2 * (0 + (wf z + W Z)) + 3 ≤ psi (5 :: 4 :: tl)
                        omega
                  · -- KEEP0 of `5 :: M'''`: `2 * W L1 + 1 ≤ psi (5 :: M''')` =>
                    -- `2 * W L1 ≤ 2*W M''' + 2 = psi M - 4`!
                    have hreach1 : Reach (cfg_CL1 (6 :: 4 :: tl) ((2 * c + 1) :: S))
                                         (cfg_BR1 (0 :: L1) (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++
                                           ((2 * c) :: S)))) :=
                      h2.trans ((step_EL1_zero (5 :: M''') _).trans hr1)
                    dsimp only [W] at hpsi_x
                    change psi (5 :: 4 :: tl) = 2 * (2 + (1 + (0 + W M'''))) at hpsi_x
                    have hlt1 : psi L1 < psi (5 :: 4 :: tl) := by have := psi_le L1; omega
                    rcases step_p02_one_ih ihEL L1 hlt1 (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                      with
                      ⟨L2, hr2, _, hw2⟩ | ⟨L2, hr2, hw2⟩
                    · have hsw := (hreach1.trans hr2).trans
                        ((step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
                          (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S)))
                      refine finish_no0 ihEL hsw ?_
                      rw [W_rep4_append]; dsimp only [W]; change 2 * (1 + W L2) + 1 ≤
                        psi (5 :: 4 :: tl)
                      have := psi_le L1; omega
                    · refine finish_0_p02_2c ihEL (hreach1.trans hr2) heven ?_
                      rw [psi_cons_two]; have := psi_le L1; omega
            · -- Case 2D: `x = 6` (`inc1 = 7 :: M''`)!
              have h1 : Reach (cfg_EL1 (0 :: 7 :: M'') (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) ::
                S))))
                              (cfg_EL1 (0 :: inc1 M'') (0 :: 2 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++
                                ((2 * c) :: S)))) := by
                have a1 := step_EL1_zero (7 :: M'') (0 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a2 := step_CL1_add_three 5 M'' (1 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a3 := step_EL1_add_two 3 M'' (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a4 := step_EL1_add_two 1 M'' (0 :: 0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c)
                  :: S)))
                have a5 := step_EL1_one M'' (0 :: 0 :: 0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c)
                  :: S)))
                have a6 := step_EB1_zero M'' (0 :: 0 :: 0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c)
                  :: S)))
                have a7 := step_BR1_00 (inc1 M'') (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a8 := sweep_BR_p02_one (2 :: inc1 M'') (2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a9 := step_BR1_ge2 0 (0 :: 4 :: 2 :: inc1 M'') (rep02 (k + 1) ++ ((2 * c) ::
                  S))
                have a10 := step_EL1_add_two 0 (4 :: 2 :: inc1 M'') (0 :: (rep02 (k + 1) ++ ((2 *
                  c) :: S)))
                have a11 := sweep_EL_f4_one (2 :: inc1 M'') (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))
                have a12 := step_EL1_zero (2 :: inc1 M'') (0 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++
                  ((2 * c) :: S)))
                have a13 := step_CL1_add_three 0 (inc1 M'') (1 :: 0 :: 2 :: 0 :: (rep02 (k + 1) ++
                  ((2 * c) :: S)))
                exact ((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans
                  a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13)
              refine finish_2D ihEL (hpre.trans h1) heven ?_
              have := W_inc1_le M''
              change psi (5 :: 4 :: tl) = 2 * (2 + (2 + W M'')) at hpsi_x; omega
            · -- Case 2C: `x = 4 * (m + 1) + 3` (`inc1 = (4 * m + 8) :: M''`)!
              have hwx : wf (4 * (m + 1) + 3) = m + 3 := wf_4r3 (m + 1)
              have h1 : Reach (cfg_EL1 (0 :: (4 * (m + 1) + 3 + 1) :: M'') (0 :: 2 :: (rep02 (k +
                1) ++ ((2 * c) :: S))))
                              (cfg_EL1 (0 :: M'') (0 :: (List.replicate (2 * m + 3) 0 ++
                                (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))) := by
                have a1 := step_EL1_zero ((4 * (m + 1) + 3 + 1) :: M'') (0 :: 2 :: (rep02 (k + 1)
                  ++ ((2 * c) :: S)))
                have hnum : 4 * (m + 1) + 3 + 1 + 1 = (2 * (2 * m + 3)) + 3 := by omega
                rw [show inc1 ((4 * (m + 1) + 3 + 1) :: M'') = (4 * (m + 1) + 3 + 1 + 1) :: M''
                  from rfl, hnum] at a1
                have a2 := step_CL1_add_three (2 * (2 * m + 3)) M'' (1 :: 2 :: (rep02 (k + 1) ++
                  ((2 * c) :: S)))
                have a3 := peel_EL1_even (2 * m + 3) 0 M'' (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 *
                  c) :: S)))
                rw [Nat.zero_add] at a3
                rw [replicate_zero_snoc (2 * m + 3) (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))]
                  at a3
                exact (a1.trans a2).trans a3
              have hltM'' : psi M'' < psi (5 :: 4 :: tl) := by
                have := psi_le M''; rw [hwx] at hpsi_x; omega
              rcases ihEL M'' hltM'' (List.replicate (2 * m + 3) 0 ++ (2 :: 2 :: (rep02 (k + 1) ++
                ((2 * c) :: S)))) with
                ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
              · -- `2*m + 3 = 2*(m+1) + 1` zeros -> pushes `2^(m+1)` then `0 :: 2` ->
                -- `4 :: 2^(m+1) :: L1` on `2 :: rep02(k+1) :: 2c :: S`!
                have hrep : List.replicate (2 * m + 3) 0 ++ (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c)
                  :: S))) =
                    List.replicate (2 * (m + 1)) 0 ++ (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c)
                      :: S))) := by
                  rw [show 2 * m + 3 = 2 * (m + 1) + 1 by omega, ← replicate_zero_snoc (2 * (m +
                    1))]
                have hr1' : Reach (cfg_EL1 (0 :: M'') (0 :: (List.replicate (2 * m + 3) 0 ++ (2 ::
                  2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))))
                                  (cfg_BR1 (0 :: L1) (List.replicate (2 * (m + 1)) 0 ++
                                    (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))) := by
                  simpa only [← hrep] using hr1
                have hs := ((hpre.trans h1).trans hr1').trans
                  ((sweep_BR_00 (m + 1) L1 (0 :: 2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S)))).trans
                    (sweep_BR_p02_one (List.replicate (m + 1) 2 ++ L1) (2 :: (rep02 (k + 1) ++ ((2
                      * c) :: S)))))
                -- At `cfg_BR1 (0 :: 4 :: 2^(m+1) :: L1) (2 :: rep02 (k+1) ++ (2*c) :: S)`
                have hs2 := hs.trans ((step_BR1_ge2 0 (0 :: 4 :: (List.replicate (m + 1) 2 ++ L1))
                    (rep02 (k + 1) ++ ((2 * c) :: S))).trans
                  (step_EL1_add_two 0 (4 :: (List.replicate (m + 1) 2 ++ L1))
                    (0 :: (rep02 (k + 1) ++ ((2 * c) :: S)))))
                have hltL : psi (4 :: (List.replicate (m + 1) 2 ++ L1)) < psi (5 :: 4 :: tl) := by
                  rw [psi_cons_ne2 (by omega), W_replicate_two]; rw [hwx] at hpsi_x
                  have := psi_le M''; change 2 * (0 + (m + 1 + W L1)) < psi (5 :: 4 :: tl); omega
                rcases ihEL (4 :: (List.replicate (m + 1) 2 ++ L1)) hltL (0 :: (rep02 (k + 1) ++
                  ((2 * c) :: S))) with
                  ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, hw2⟩
                · refine finish_0_p02_2c ihEL (hs2.trans hr2) heven ?_
                  rw [psi_cons_ne2 (by omega), W_replicate_two] at hw2
                  rw [hwx] at hpsi_x; have := psi_le L2; have := psi_le M''
                  change 2 * W L2 ≤ 2 * (0 + (m + 1 + W L1)) at hw2; omega
                · have hsw := (hs2.trans hr2).trans
                    ((step_BR1_00 L2 (rep02 (k + 1) ++ ((2 * c) :: S))).trans
                      (sweep_BR_p02 (k + 1) (2 :: L2) ((2 * c) :: S)))
                  refine finish_no0 ihEL hsw ?_
                  rw [W_rep4_append]; dsimp only [W]
                  rw [psi_cons_ne2 (by omega), W_replicate_two] at hw2
                  rw [hwx] at hpsi_x; have := psi_le M''
                  change 2 * W L2 + 1 ≤ 2 * (0 + (m + 1 + W L1)) at hw2
                  change 2 * (1 + W L2) + 1 ≤ psi (5 :: 4 :: tl); omega
              · -- `KEEP0`: `2*m + 4 = 2*(m+2)` zeros -> pushes `2^(m+2)` onto `L1` on
                -- `2 :: 2 :: rep02(k+1) :: 2c :: S`!
                have hrep : 0 :: (List.replicate (2 * m + 3) 0 ++ (2 :: 2 :: (rep02 (k + 1) ++ ((2
                  * c) :: S)))) =
                    List.replicate (2 * (m + 2)) 0 ++ (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) ::
                      S))) := by
                  rw [show 2 * (m + 2) = (2 * m + 3) + 1 by omega]; rfl
                rw [hrep] at hr1
                have hs := ((hpre.trans h1).trans hr1).trans
                  (sweep_BR_00 (m + 2) L1 (2 :: 2 :: (rep02 (k + 1) ++ ((2 * c) :: S))))
                refine finish_BR_22_p02_2c ihEL hs heven ?_
                rw [psi_replicate_two_succ (m + 1) L1]
                rw [hwx] at hpsi_x; have := psi_le M''; omega
    | n + 6 =>
      -- Remaining digits `v ≥ 6`: split mod 4 into `4*r + 3` (`r ≥ 1`), `4*r + 1` (`r ≥ 2`), `4*j +
      -- 6` (`j ≥ 0`), `4*j + 8` (`j ≥ 0`)!
      have hv_ne2 : n + 6 ≠ 2 := by omega
      have hpsiM : psi ((n + 6) :: M') = 2 * (wf (n + 6) + W M') := psi_cons_ne2 hv_ne2 M'
      have hmod : (n + 6) % 4 = 3 ∨ (n + 6) % 4 = 1 ∨ (n + 6) % 4 = 2 ∨ (n + 6) % 4 = 0 := by omega
      rcases hmod with h3 | h1 | h2 | h0
      · -- `v = 4 * r + 3` (`r ≥ 1`): ZERO RECURSION!
        set r := (n + 6) / 4
        have hv_eq : n + 6 = 4 * r + 3 := by omega
        have hwfv : wf (n + 6) = r + 2 := by rw [hv_eq]; exact wf_4r3 r
        have s1 := step_CL1_add_three (1 + 2 * (2 * r)) M' ((2 * c + 1) :: S)
        have hnum : 1 + 2 * (2 * r) + 3 = n + 6 + 1 := by omega
        rw [hnum] at s1
        have s2 := peel_EL1_even (2 * r) 1 M' (0 :: (2 * c + 2) :: S)
        have s3 := step_EL1_one M' (List.replicate (2 * r) 0 ++ (0 :: (2 * c + 2) :: S))
        have s4 := step_EB1_zero M' (List.replicate (2 * r) 0 ++ (0 :: (2 * c + 2) :: S))
        have s5 := sweep_BR_00 r (inc1 M') (0 :: (2 * c + 2) :: S)
        have s6 := step_BR1_0d (2 * c + 2) (List.replicate r 2 ++ inc1 M') S
        have htot := ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
        refine Or.inl ⟨(2 * c + 4) :: (List.replicate r 2 ++ inc1 M'), htot, ?_, fun _ ⟨_, hne⟩ =>
          by cases hne⟩
        dsimp only [W]; rw [W_replicate_two]
        have := W_inc1_le M'; omega
      · -- `v = 4 * (r' + 2) + 1` (`r' ≥ 0`: `9, 13, 17, ...`)
        set r' := (n + 6) / 4 - 2
        have hv_eq : n + 6 = 4 * (r' + 2) + 1 := by omega
        have hwfv : wf (n + 6) = r' + 4 := by rw [hv_eq]; exact wf_4r1_ge2 r'
        have s1 := step_CL1_add_three (1 + 2 * (2 * r' + 3)) M' ((2 * c + 1) :: S)
        have hnum : 1 + 2 * (2 * r' + 3) + 3 = n + 6 + 1 := by omega
        rw [hnum] at s1
        have s2 := peel_EL1_even (2 * r' + 3) 1 M' (0 :: (2 * c + 2) :: S)
        have s3 := step_EL1_one M' (List.replicate (2 * r' + 3) 0 ++ (0 :: (2 * c + 2) :: S))
        have s4 := step_EB1_zero M' (List.replicate (2 * r' + 3) 0 ++ (0 :: (2 * c + 2) :: S))
        have hrep : List.replicate (2 * r' + 3) 0 ++ (0 :: (2 * c + 2) :: S) =
            List.replicate (2 * (r' + 2)) 0 ++ ((2 * c + 2) :: S) := by
          rw [replicate_zero_snoc (2 * r' + 3), show 2 * r' + 3 + 1 = 2 * (r' + 2) by omega]
        have s4' : Reach (cfg_EB1 M' (0 :: (List.replicate (2 * r' + 3) 0 ++ (0 :: (2 * c + 2) ::
          S))))
                         (cfg_BR1 (0 :: inc1 M') (List.replicate (2 * (r' + 2)) 0 ++
                           ((2 * c + 2) :: S))) := by
          simpa only [← hrep] using s4
        have s5 := sweep_BR_00 (r' + 2) (inc1 M') ((2 * c + 2) :: S)
        have hpre := (((s1.trans s2).trans s3).trans s4').trans s5
        have hpsiL : psi (List.replicate (r' + 2) 2 ++ inc1 M') = 2 * (r' + 1 + W (inc1 M')) + 1 :=
          psi_replicate_two_succ (r' + 1) (inc1 M')
        have hltL : psi (List.replicate (r' + 2) 2 ++ inc1 M') < psi ((n + 6) :: M') := by
          have := W_inc1_le M'; omega
        rcases step_even_ih ihEL c (List.replicate (r' + 2) 2 ++ inc1 M') hltL S with
          ⟨L', hr', hw'⟩ | ⟨L', hr', h0', hge1'⟩
        · exact Or.inr ⟨L', hpre.trans hr', by have := W_inc1_le M'; omega⟩
        · refine Or.inl ⟨L', hpre.trans hr', ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
          cases c with
          | zero =>
            rcases h0' rfl with ⟨_, hw', _⟩
            have := W_inc1_le M'; change 2 * W L' ≤ psi ((n + 6) :: M') + 2 * 0; omega
          | succ c' =>
            have hrec := hge1' (by omega)
            have hmono := wf_even_mono (c := c' + 1) (by omega)
            have := W_inc1_le M'; omega
      · -- `v = 4 * j + 6` (`j ≥ 0`: `6, 10, 14, ...`)
        set j := (n + 6 - 6) / 4
        have hv_eq : n + 6 = 4 * j + 6 := by omega
        have hwfv : j + 2 ≤ wf (n + 6) := by rw [hv_eq]; exact wf_4j6 j
        have s1 := step_CL1_add_three (2 * (2 * j + 2)) M' ((2 * c + 1) :: S)
        have hnum : 2 * (2 * j + 2) + 3 = n + 6 + 1 := by omega
        rw [hnum] at s1
        have s2 := peel_EL1_even (2 * j + 2) 0 M' (0 :: (2 * c + 2) :: S)
        rw [Nat.zero_add] at s2
        have hrep0 : List.replicate (2 * j + 2) 0 ++ (0 :: (2 * c + 2) :: S) =
            0 :: (List.replicate (2 * (j + 1)) 0 ++ ((2 * c + 2) :: S)) := by
          rw [replicate_zero_snoc (2 * j + 2), show 2 * j + 2 + 1 = (2 * (j + 1)) + 1 by omega]
          rfl
        rw [hrep0] at s2
        have hltM' : psi M' < psi ((n + 6) :: M') := by have := psi_le M'; omega
        rcases ihEL M' hltM' (List.replicate (2 * (j + 1)) 0 ++ ((2 * c + 2) :: S)) with
          ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
        · have hsw := ((s1.trans s2).trans hr1).trans (sweep_BR_00 (j + 1) L1 ((2 * c + 2) :: S))
          have hpsiL : psi (List.replicate (j + 1) 2 ++ L1) = 2 * (j + W L1) + 1 :=
            psi_replicate_two_succ j L1
          have hltL : psi (List.replicate (j + 1) 2 ++ L1) < psi ((n + 6) :: M') := by
            have := psi_le M'; omega
          rcases step_even_ih ihEL c (List.replicate (j + 1) 2 ++ L1) hltL S with
            ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, h0', hge1'⟩
          · exact Or.inr ⟨L2, hsw.trans hr2, by have := psi_le M'; omega⟩
          · refine Or.inl ⟨L2, hsw.trans hr2, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
            cases c with
            | zero =>
              rcases h0' rfl with ⟨_, hw2, _⟩
              have := psi_le M'; change 2 * W L2 ≤ psi ((n + 6) :: M') + 2 * 0; omega
            | succ c' =>
              have hrec := hge1' (by omega)
              have hmono := wf_even_mono (c := c' + 1) (by omega)
              have := psi_le M'; omega
        · have hrep1 : 0 :: (List.replicate (2 * (j + 1)) 0 ++ ((2 * c + 2) :: S)) =
              List.replicate (2 * (j + 1)) 0 ++ (0 :: (2 * c + 2) :: S) := by
            rw [replicate_zero_snoc (2 * (j + 1))]; rfl
          have hr1' : Reach (cfg_EL1 (0 :: M') (0 :: (List.replicate (2 * (j + 1)) 0 ++ ((2 * c +
            2) :: S))))
                            (cfg_BR1 (0 :: L1) (List.replicate (2 * (j + 1)) 0 ++
                              (0 :: (2 * c + 2) :: S))) := by
            simpa only [← hrep1] using hr1
          have hsw := (((s1.trans s2).trans hr1').trans
            (sweep_BR_00 (j + 1) L1 (0 :: (2 * c + 2) :: S))).trans
            (step_BR1_0d (2 * c + 2) (List.replicate (j + 1) 2 ++ L1) S)
          refine Or.inl ⟨(2 * c + 4) :: (List.replicate (j + 1) 2 ++ L1), hsw,
            ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
          dsimp only [W]; rw [W_replicate_two]; have := psi_le M'; omega
      · -- `v = 4 * j + 8` (`j ≥ 0`: `8, 12, 16, ...`)
        set j := (n + 6 - 8) / 4
        have hv_eq : n + 6 = 4 * j + 8 := by omega
        have hwfv : j + 4 ≤ wf (n + 6) := by rw [hv_eq]; exact wf_4j8 j
        have s1 := step_CL1_add_three (2 * (2 * j + 3)) M' ((2 * c + 1) :: S)
        have hnum : 2 * (2 * j + 3) + 3 = n + 6 + 1 := by omega
        rw [hnum] at s1
        have s2 := peel_EL1_even (2 * j + 3) 0 M' (0 :: (2 * c + 2) :: S)
        rw [Nat.zero_add] at s2
        have hrep0 : List.replicate (2 * j + 3) 0 ++ (0 :: (2 * c + 2) :: S) =
            0 :: (List.replicate (2 * j + 3) 0 ++ ((2 * c + 2) :: S)) := by
          rw [replicate_zero_snoc (2 * j + 3)]; rfl
        rw [hrep0] at s2
        have hltM' : psi M' < psi ((n + 6) :: M') := by have := psi_le M'; omega
        rcases ihEL M' hltM' (List.replicate (2 * j + 3) 0 ++ ((2 * c + 2) :: S)) with
          ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
        · have hrep1 : List.replicate (2 * j + 3) 0 ++ ((2 * c + 2) :: S) =
              List.replicate (2 * (j + 1)) 0 ++ (0 :: (2 * c + 2) :: S) := by
            rw [replicate_zero_snoc (2 * (j + 1)), show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
          have hr1' : Reach (cfg_EL1 (0 :: M') (0 :: (List.replicate (2 * j + 3) 0 ++ ((2 * c + 2)
            :: S))))
                            (cfg_BR1 (0 :: L1) (List.replicate (2 * (j + 1)) 0 ++
                              (0 :: (2 * c + 2) :: S))) := by
            simpa only [← hrep1] using hr1
          have hsw := (((s1.trans s2).trans hr1').trans
            (sweep_BR_00 (j + 1) L1 (0 :: (2 * c + 2) :: S))).trans
            (step_BR1_0d (2 * c + 2) (List.replicate (j + 1) 2 ++ L1) S)
          refine Or.inl ⟨(2 * c + 4) :: (List.replicate (j + 1) 2 ++ L1), hsw,
            ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
          dsimp only [W]; rw [W_replicate_two]; have := psi_le M'; omega
        · have hrep2 : 0 :: (List.replicate (2 * j + 3) 0 ++ ((2 * c + 2) :: S)) =
              List.replicate (2 * (j + 2)) 0 ++ ((2 * c + 2) :: S) := by
            rw [show 2 * (j + 2) = (2 * j + 3) + 1 by omega]; rfl
          rw [hrep2] at hr1
          have hsw := ((s1.trans s2).trans hr1).trans (sweep_BR_00 (j + 2) L1 ((2 * c + 2) :: S))
          have hpsiL : psi (List.replicate (j + 2) 2 ++ L1) = 2 * (j + 1 + W L1) + 1 :=
            psi_replicate_two_succ (j + 1) L1
          have hltL : psi (List.replicate (j + 2) 2 ++ L1) < psi ((n + 6) :: M') := by
            have := psi_le M'; omega
          rcases step_even_ih ihEL c (List.replicate (j + 2) 2 ++ L1) hltL S with
            ⟨L2, hr2, hw2⟩ | ⟨L2, hr2, h0', hge1'⟩
          · exact Or.inr ⟨L2, hsw.trans hr2, by have := psi_le M'; omega⟩
          · refine Or.inl ⟨L2, hsw.trans hr2, ?_, fun _ ⟨_, hne⟩ => by cases hne⟩
            cases c with
            | zero =>
              rcases h0' rfl with ⟨_, hw2, _⟩
              have := psi_le M'; change 2 * W L2 ≤ psi ((n + 6) :: M') + 2 * 0; omega
            | succ c' =>
              have hrec := hge1' (by omega)
              have hmono := wf_even_mono (c := c' + 1) (by omega)
              have := psi_le M'; omega

/-- Unconditional `mEL_spec` (the `c = 0` specialization of `mCL_bump_spec`!). -/
private theorem mEL_spec (L S : List ℕ) :
    (∃ L', Reach (cfg_EL1 (0 :: L) (0 :: S)) (cfg_BR1 (0 :: L') S) ∧ 2 * W L' ≤ psi L) ∨
    (∃ L', Reach (cfg_EL1 (0 :: L) (0 :: S)) (cfg_BR1 (0 :: L') (0 :: S)) ∧ 2 * W L' + 1 ≤ psi L)
      := by
  rcases mCL_bump_spec L 0 S with ⟨L', hr, hw, _⟩ | ⟨L', hr, hw⟩
  · refine Or.inl ⟨L', (step_EL1_zero L (0 :: S)).trans hr, ?_⟩
    change 2 * W L' ≤ psi L + 2 * 0 at hw; omega
  · exact Or.inr ⟨L', (step_EL1_zero L (0 :: S)).trans hr, hw⟩

/-- Unconditional single `0 :: 0 :: 2` (`0 :: rep02 1`) drop/step theorem. -/
private theorem step_p02_one (L S : List ℕ) :
    (∃ L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: L') (0 :: S)) ∧
           psi L' + 1 ≤ psi L ∧ 2 * W L' ≤ psi L) ∨
    (∃ L', Reach (cfg_BR1 (0 :: L) (0 :: 0 :: 2 :: S)) (cfg_BR1 (0 :: 2 :: L') S) ∧
           2 * W L' ≤ psi L) :=
  step_p02_one_ih (limit := psi L + 1) (fun X _ S' => mEL_spec X S') L (by omega) S

/-- Cancellation law `p02_zero_drop`: if `psi L + 1 ≤ n`, then `0 :: rep02 n` ALWAYS drops!
Zero `Nat.sub` underflow: expressed purely via additive inequality `n + 2 * W L' ≤ a' + psi L +
  3`. -/
private theorem p02_zero_drop :
    ∀ p : ℕ, ∀ (L S : List ℕ) (n : ℕ), psi L = p → p + 1 ≤ n →
      ∃ (a' : ℕ) (L' : List ℕ),
        Reach (cfg_BR1 (0 :: L) (0 :: (rep02 n ++ S)))
              (cfg_BR1 (0 :: (rep4 a' ++ L')) S) ∧
        n + 2 * W L' ≤ a' + psi L + 3 ∧ 2 * W L' ≤ psi L + 2 := by
  intro p
  refine Nat.strongRecOn p ?_
  intro p ih L S n hp hn
  cases n with
  | zero => omega
  | succ m =>
    dsimp only [rep02, List.cons_append]
    rcases step_p02_one L (rep02 m ++ S) with ⟨L1, hr1, hp1, _⟩ | ⟨L1, hr1, hw1⟩
    · have hlt : psi L1 < p := by omega
      rcases ih (psi L1) hlt L1 S m rfl (by omega) with ⟨a', L', hr', hadd, hle⟩
      exact ⟨a', L', hr1.trans hr', by omega, by omega⟩
    · refine ⟨m, 2 :: L1, hr1.trans (sweep_BR_p02 m (2 :: L1) S), ?_, ?_⟩
      · dsimp only [W]; change (m + 1) + 2 * (1 + W L1) ≤ m + psi L + 3; omega
      · dsimp only [W]; change 2 * (1 + W L1) ≤ psi L + 2; omega

/-! ## Section 3: Amortized Potential Lemmas (`mEL_pot`, `cross_d2`, `zero_p02`) & Hub Transitions
  -/

/-- 1-head `mEL_pot_1`: if `2 * W L + 1 ≤ a`, then `cfg_EL1 (0 :: rep4 a ++ L) (0 :: S)`
ALWAYS absorbs `0` (NEVER returns `KEEP0`!), dropping `P = a - 2 * W L` by AT MOST `1`! -/
private theorem mEL_pot_1 (a : ℕ) (L S : List ℕ) (ha : 2 * W L + 1 ≤ a) :
    ∃ (a' : ℕ) (L' : List ℕ),
      Reach (cfg_EL1 (0 :: (rep4 a ++ L)) (0 :: S)) (cfg_BR1 (0 :: (rep4 a' ++ L')) S) ∧
      a + 2 * W L' ≤ a' + 2 * W L + 1 := by
  have h1 := sweep_EL_f4 a L S
  rcases mEL_spec L (rep02 a ++ S) with ⟨L1, hr1, hw1⟩ | ⟨L1, hr1, hw1⟩
  · refine ⟨a, L1, (h1.trans hr1).trans (sweep_BR_p02 a L1 S), ?_⟩
    have := psi_le L; omega
  · have hpsiL : psi L ≤ 2 * W L := psi_le L
    have hpsi1 : psi L1 ≤ 2 * W L1 := psi_le L1
    have h2 : 2 * W L1 ≤ 2 * W L - 2 := by omega
    -- Parity miracle: `2 * W L1 + 1 ≤ 2 * W L` (ODD <= EVEN) forces `psi L1 + 2 ≤ 2 * W L`!
    rcases p02_zero_drop (psi L1) L1 S a rfl (by omega) with ⟨a', L', hr', hadd, _⟩
    exact ⟨a', L', (h1.trans hr1).trans hr', by omega⟩

/-- 1-head `cross_d2_1`: crosses `2` on `R`, dropping `P = a - 2 * W L` by AT MOST `1`. -/
private theorem cross_d2_1 (a : ℕ) (L S : List ℕ) (ha : 2 * W L + 1 ≤ a) :
    ∃ (a' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (2 :: S)) (cfg_BR1 (0 :: (rep4 a' ++ L')) (0 :: S)) ∧
      a + 2 * W L' ≤ a' + 2 * W L + 1 := by
  have h0 : Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (2 :: S))
                  (cfg_EL1 (0 :: (rep4 a ++ L)) (0 :: 0 :: S)) :=
    (step_BR1_ge2 0 (0 :: (rep4 a ++ L)) S).trans (step_EL1_add_two 0 (rep4 a ++ L) (0 :: S))
  rcases mEL_pot_1 a L (0 :: S) ha with ⟨a', L', hr', hadd⟩
  exact ⟨a', L', h0.trans hr', hadd⟩

/-- 1-head `zero_p02_1`: sweeps `0 :: rep02 (m + 1) ++ S`, dropping `P` by AT MOST `2`. -/
private theorem zero_p02_1 (m a : ℕ) (L S : List ℕ) (ha : 2 * W L + 2 ≤ a) :
    ∃ (a' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (0 :: (rep02 (m + 1) ++ S)))
            (cfg_BR1 (0 :: (rep4 m ++ 2 :: (rep4 a' ++ L'))) S) ∧
      a + 2 * W L' ≤ a' + 2 * W L + 2 := by
  dsimp only [rep02, List.cons_append]
  have h0 : Reach (cfg_BR1 (0 :: (rep4 a ++ L)) (0 :: 0 :: 2 :: (rep02 m ++ S)))
                  (cfg_EL1 (0 :: (rep4 a ++ L)) (0 :: 2 :: 0 :: (rep02 m ++ S))) := by
    have a1 := step_BR1_00 (rep4 a ++ L) (2 :: (rep02 m ++ S))
    have a2 := step_BR1_ge2 0 (0 :: 2 :: (rep4 a ++ L)) (rep02 m ++ S)
    have a3 := step_EL1_add_two 0 (2 :: (rep4 a ++ L)) (0 :: (rep02 m ++ S))
    have a4 := step_EL1_zero (2 :: (rep4 a ++ L)) (0 :: 0 :: (rep02 m ++ S))
    have a5 := step_CL1_add_three 0 (rep4 a ++ L) (1 :: 0 :: (rep02 m ++ S))
    exact (((a1.trans a2).trans a3).trans a4).trans a5
  rcases mEL_pot_1 a L (2 :: 0 :: (rep02 m ++ S)) (by omega) with ⟨a1, L1, hr1, hd1⟩
  rcases cross_d2_1 a1 L1 (0 :: (rep02 m ++ S)) (by omega) with ⟨a2, L2, hr2, hd2⟩
  have h3 := ((h0.trans hr1).trans hr2).trans
    ((step_BR1_00 (rep4 a2 ++ L2) (rep02 m ++ S)).trans
      (sweep_BR_p02 m (2 :: (rep4 a2 ++ L2)) S))
  exact ⟨a2, L2, h3, by omega⟩

/-- 2-head `mEL_pot_2`: `a0 ≥ 1`, `P = a1 - 2 * W L ≥ 4` → exact `a0 - 1`, `ΔP ≥ -4`! -/
private theorem mEL_pot_2 (a0 a1 : ℕ) (L S : List ℕ) (ha0 : 1 ≤ a0) (ha1 : 2 * W L + 4 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: S))
            (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 a1' ++ L'))) S) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 4 := by
  have h0 : Reach (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: S))
                  (cfg_EL1 (0 :: (rep4 a1 ++ L)) (0 :: 2 :: (rep02 a0 ++ S))) :=
    ((sweep_EL_f4 a0 (2 :: (rep4 a1 ++ L)) S).trans
      (step_EL1_zero (2 :: (rep4 a1 ++ L)) (0 :: (rep02 a0 ++ S)))).trans
      (step_CL1_add_three 0 (rep4 a1 ++ L) (1 :: (rep02 a0 ++ S)))
  rcases mEL_pot_1 a1 L (2 :: (rep02 a0 ++ S)) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases cross_d2_1 b1 L1 (rep02 a0 ++ S) (by omega) with ⟨b2, L2, hr2, hd2⟩
  cases a0 with
  | zero => omega
  | succ m =>
    rcases zero_p02_1 m b2 L2 S (by omega) with ⟨b3, L3, hr3, hd3⟩
    exact ⟨b3, L3, ((h0.trans hr1).trans hr2).trans hr3, by omega⟩

/-- 2-head `cross_d2_2`: exact `a0 - 1`, `ΔP ≥ -4`! -/
private theorem cross_d2_2 (a0 a1 : ℕ) (L S : List ℕ) (ha0 : 1 ≤ a0) (ha1 : 2 * W L + 4 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (2 :: S))
            (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 a1' ++ L'))) (0 :: S)) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 4 := by
  have h0 : Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (2 :: S))
                  (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: 0 :: S)) :=
    (step_BR1_ge2 0 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) S).trans
      (step_EL1_add_two 0 (rep4 a0 ++ 2 :: (rep4 a1 ++ L)) (0 :: S))
  rcases mEL_pot_2 a0 a1 L (0 :: S) ha0 ha1 with ⟨a1', L', hr', hd⟩
  exact ⟨a1', L', h0.trans hr', hd⟩

/-- 2-head `zero_p02_2`: `a0 ≥ 2`, `P ≥ 8` → exact `a0 - 2`, `ΔP ≥ -8`! -/
private theorem zero_p02_2 (m a0 a1 : ℕ) (L S : List ℕ) (ha0 : 2 ≤ a0) (ha1 : 2 * W L + 8 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: (rep02 (m + 1) ++ S)))
            (cfg_BR1 (0 :: (rep4 m ++ 2 :: (rep4 (a0 - 2) ++ 2 :: (rep4 a1' ++ L')))) S) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 8 := by
  dsimp only [rep02, List.cons_append]
  have h0 : Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: 0 :: 2 :: (rep02 m ++ S)))
                  (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) (0 :: 2 :: 0 :: (rep02 m ++
                    S))) := by
    let X := rep4 a0 ++ 2 :: (rep4 a1 ++ L)
    have a1 := step_BR1_00 X (2 :: (rep02 m ++ S))
    have a2 := step_BR1_ge2 0 (0 :: 2 :: X) (rep02 m ++ S)
    have a3 := step_EL1_add_two 0 (2 :: X) (0 :: (rep02 m ++ S))
    have a4 := step_EL1_zero (2 :: X) (0 :: 0 :: (rep02 m ++ S))
    have a5 := step_CL1_add_three 0 X (1 :: 0 :: (rep02 m ++ S))
    exact (((a1.trans a2).trans a3).trans a4).trans a5
  rcases mEL_pot_2 a0 a1 L (2 :: 0 :: (rep02 m ++ S)) (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases cross_d2_2 (a0 - 1) b1 L1 (0 :: (rep02 m ++ S)) (by omega) (by omega) with ⟨b2, L2, hr2,
    hd2⟩
  have hsub : a0 - 1 - 1 = a0 - 2 := by omega
  rw [hsub] at hr2
  have h3 := ((h0.trans hr1).trans hr2).trans
    ((step_BR1_00 (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2)) (rep02 m ++ S)).trans
      (sweep_BR_p02 m (2 :: (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2))) S))
  exact ⟨b2, L2, h3, by omega⟩

/--
3-head `mEL_pot_3`: `a0 ≥ 1`, `a1 ≥ 4`, `P = a2 - 2 * W L ≥ 16` → exact `a0 - 1`, `a1 - 4`, `ΔP ≥
-16`! -/
private theorem mEL_pot_3 (a0 a1 a2 : ℕ) (L S : List ℕ)
    (ha0 : 1 ≤ a0) (ha1 : 4 ≤ a1) (ha2 : 2 * W L + 16 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (0 :: S))
            (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 (a1 - 4) ++ 2 :: (rep4 a2' ++ L')))) S) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 16 := by
  have h0 : Reach (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (0 :: S))
                  (cfg_EL1 (0 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: 2 :: (rep02 a0 ++ S))) :=
    ((sweep_EL_f4 a0 (2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) S).trans
      (step_EL1_zero (2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: (rep02 a0 ++ S)))).trans
      (step_CL1_add_three 0 (rep4 a1 ++ 2 :: (rep4 a2 ++ L)) (1 :: (rep02 a0 ++ S)))
  rcases mEL_pot_2 a1 a2 L (2 :: (rep02 a0 ++ S)) (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases cross_d2_2 (a1 - 1) b1 L1 (rep02 a0 ++ S) (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
  cases a0 with
  | zero => omega
  | succ m =>
    rcases zero_p02_2 m (a1 - 1 - 1) b2 L2 S (by omega) (by omega) with ⟨b3, L3, hr3, hd3⟩
    have hsub : a1 - 1 - 1 - 2 = a1 - 4 := by omega
    rw [hsub] at hr3
    exact ⟨b3, L3, ((h0.trans hr1).trans hr2).trans hr3, by omega⟩

/-- 3-head `cross_d2_3`: exact `a0 - 1`, `a1 - 4`, `ΔP ≥ -16`. -/
private theorem cross_d2_3 (a0 a1 a2 : ℕ) (L S : List ℕ)
    (ha0 : 1 ≤ a0) (ha1 : 4 ≤ a1) (ha2 : 2 * W L + 16 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (2 :: S))
            (cfg_BR1 (0 :: (rep4 (a0 - 1) ++ 2 :: (rep4 (a1 - 4) ++ 2 :: (rep4 a2' ++ L')))) (0 ::
              S)) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 16 := by
  have h0 : Reach (cfg_BR1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (2 :: S))
                  (cfg_EL1 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) (0 :: 0 ::
                    S)) :=
    (step_BR1_ge2 0 (0 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) S).trans
      (step_EL1_add_two 0 (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: S))
  rcases mEL_pot_3 a0 a1 a2 L (0 :: S) ha0 ha1 ha2 with ⟨a2', L', hr', hd⟩
  exact ⟨a2', L', h0.trans hr', hd⟩

/-! ### Hub Transition Theorems (`(0,)`, `(0,3)`, `(0,5,2)`, `(0,5,5)`, Terminal Halt) -/

/-- `(0,)` hub: `a0 + 2 → (0, 5, 5) a0` (6 macro steps, 24 raw TM steps, arbitrary tail `L`). -/
private theorem hub_0_step (a0 : ℕ) (L : List ℕ) :
    Reach (cfg_BR1 (0 :: (rep4 (a0 + 2) ++ L)) [])
          (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ L)) []) := by
  have hrep : rep4 (a0 + 2) ++ L = 4 :: 4 :: (rep4 a0 ++ L) := by
    rw [show a0 + 2 = 2 + a0 by omega, rep4_add 2 a0 L]; rfl
  rw [hrep]
  have h1 := step_BR1_nil (0 :: 4 :: 4 :: (rep4 a0 ++ L))
  have h2 := step_CL1_zero (4 :: 4 :: (rep4 a0 ++ L)) [0]
  have h3 := step_CL1_add_three 1 (4 :: (rep4 a0 ++ L)) [2]
  have h4 := step_EL1_one (4 :: (rep4 a0 ++ L)) [0, 3]
  have h5 := step_EB1_zero (4 :: (rep4 a0 ++ L)) [0, 3]
  have h6 := step_BR1_0d 3 (5 :: (rep4 a0 ++ L)) []
  exact ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6

private theorem br_d3_to_el (L : List ℕ) :
    Reach (cfg_BR1 (0 :: L) [3]) (cfg_EL1 (0 :: L) [0, 1]) :=
  (step_BR1_ge2 1 (0 :: L) []).trans (step_EL1_add_two 0 L [1])

private theorem br_d1_to_el (L : List ℕ) :
    Reach (cfg_BR1 (0 :: L) [1]) (cfg_EL1 (0 :: L) [0]) :=
  (step_BR1_one_nil (0 :: L)).trans (step_EL1_add_two 0 L [])

private theorem hub_03_entry (L : List ℕ) :
    Reach (cfg_BR1 (0 :: 3 :: L) []) (cfg_EL1 (0 :: L) [0, 3]) :=
  ((step_BR1_nil (0 :: 3 :: L)).trans (step_CL1_zero (3 :: L) [0])).trans
    (step_CL1_add_three 0 L [2])

/-- 2-head `(0, 3)` hub: `a0 → a0 - 3`, `ΔP ≤ 12` exact. -/
private theorem hub_03_2 (a0 a1 : ℕ) (L : List ℕ) (ha0 : 3 ≤ a0) (ha1 : 2 * W L + 12 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
            (cfg_BR1 (0 :: (rep4 (a0 - 3) ++ 2 :: (rep4 a1' ++ L'))) []) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 12 := by
  have h0 := hub_03_entry (rep4 a0 ++ 2 :: (rep4 a1 ++ L))
  rcases mEL_pot_2 a0 a1 L [3] (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases mEL_pot_2 (a0 - 1) b1 L1 [1] (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
  rcases mEL_pot_2 (a0 - 1 - 1) b2 L2 [] (by omega) (by omega) with ⟨b3, L3, hr3, hd3⟩
  have hsub : a0 - 1 - 1 - 1 = a0 - 3 := by omega
  rw [hsub] at hr3
  exact ⟨b3, L3, (((((h0.trans hr1).trans (br_d3_to_el _)).trans hr2).trans
    (br_d1_to_el _)).trans hr3), by omega⟩

/-- 3-head `(0, 3)` hub: `a0 → a0 - 3`, `a1 → a1 - 12`, `ΔP ≤ 48` exact. -/
private theorem hub_03_3 (a0 a1 a2 : ℕ) (L : List ℕ)
    (ha0 : 3 ≤ a0) (ha1 : 12 ≤ a1) (ha2 : 2 * W L + 48 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
            (cfg_BR1 (0 :: (rep4 (a0 - 3) ++ 2 :: (rep4 (a1 - 12) ++ 2 :: (rep4 a2' ++ L')))) []) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 48 := by
  have h0 := hub_03_entry (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))
  rcases mEL_pot_3 a0 a1 a2 L [3] (by omega) (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases mEL_pot_3 (a0 - 1) (a1 - 4) b1 L1 [1] (by omega) (by omega) (by omega) with ⟨b2, L2, hr2,
    hd2⟩
  rcases mEL_pot_3 (a0 - 1 - 1) (a1 - 4 - 4) b2 L2 [] (by omega) (by omega) (by omega) with ⟨b3,
    L3, hr3, hd3⟩
  have hsub0 : a0 - 1 - 1 - 1 = a0 - 3 := by omega
  have hsub1 : a1 - 4 - 4 - 4 = a1 - 12 := by omega
  rw [hsub0, hsub1] at hr3
  exact ⟨b3, L3, (((((h0.trans hr1).trans (br_d3_to_el _)).trans hr2).trans
    (br_d1_to_el _)).trans hr3), by omega⟩

/-- Unconditional terminal halt: `(0, 3) [2, a1] ++ L` with `2 * W L + 10 ≤ a1` HALTS! -/
private theorem hub_03_halt (a1 : ℕ) (L : List ℕ) (ha1 : 2 * W L + 10 ≤ a1) :
    HaltsFrom target_tm (cfg_BR1 (0 :: 3 :: (rep4 2 ++ 2 :: (rep4 a1 ++ L))) []) := by
  have h0 := hub_03_entry (rep4 2 ++ 2 :: (rep4 a1 ++ L))
  rcases mEL_pot_2 2 a1 L [3] (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases mEL_pot_2 1 b1 L1 [1] (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
  -- Now at `cfg_BR1 (0 :: 2 :: rep4 b2 ++ L2) [1]`!
  dsimp only [rep4, List.nil_append] at hr2
  have h3 : Reach (cfg_BR1 (0 :: 2 :: (rep4 b2 ++ L2)) [1])
                  (cfg_EL1 (0 :: (rep4 b2 ++ L2)) [0, 2]) :=
    ((br_d1_to_el (2 :: (rep4 b2 ++ L2))).trans
      (step_EL1_zero (2 :: (rep4 b2 ++ L2)) [0])).trans
      (step_CL1_add_three 0 (rep4 b2 ++ L2) [1])
  rcases mEL_pot_1 b2 L2 [2] (by omega) with ⟨b3, L3, hr3, hd3⟩
  rcases cross_d2_1 b3 L3 [] (by omega) with ⟨b4, L4, hr4, _⟩
  have hreach := ((((((h0.trans hr1).trans (br_d3_to_el _)).trans hr2).trans h3).trans
    hr3).trans hr4).trans (step_BR1_zero (0 :: (rep4 b4 ++ L4)) [])
  exact HaltsFrom.of_reachesStar hreach (halts_of_EB1_nil _)

/-- 2-head `(0, 5, 2)` hub: `a0 → a0 - 4`, `ΔP ≤ 16` exact. -/
private theorem hub_052_2 (a0 a1 : ℕ) (L : List ℕ) (ha0 : 4 ≤ a0) (ha1 : 2 * W L + 16 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: 2 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
            (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 4) ++ 2 :: (rep4 a1' ++ L'))) []) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 16 := by
  let X := rep4 a0 ++ 2 :: (rep4 a1 ++ L)
  have h0 : Reach (cfg_BR1 (0 :: 5 :: 2 :: X) []) (cfg_EL1 (0 :: X) [0, 2, 0, 3]) := by
    have s1 := step_BR1_nil (0 :: 5 :: 2 :: X)
    have s2 := step_CL1_zero (5 :: 2 :: X) [0]
    have s3 := step_CL1_add_three 2 (2 :: X) [2]
    have s4 := step_EL1_add_two 0 (2 :: X) [0, 3]
    have s5 := step_EL1_zero (2 :: X) [0, 0, 3]
    have s6 := step_CL1_add_three 0 X [1, 0, 3]
    exact ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
  rcases mEL_pot_2 a0 a1 L [2, 0, 3] (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases cross_d2_2 (a0 - 1) b1 L1 [0, 3] (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
  have hmid : Reach (cfg_BR1 (0 :: (rep4 (a0 - 1 - 1) ++ 2 :: (rep4 b2 ++ L2))) [0, 0, 3])
                    (cfg_EL1 (0 :: (rep4 (a0 - 1 - 1) ++ 2 :: (rep4 b2 ++ L2))) [0, 2, 1]) :=
    (((step_BR1_00 _ [3]).trans (br_d3_to_el _)).trans (step_EL1_zero _ [0, 1])).trans
      (step_CL1_add_three 0 _ [1, 1])
  rcases mEL_pot_2 (a0 - 1 - 1) b2 L2 [2, 1] (by omega) (by omega) with ⟨b3, L3, hr3, hd3⟩
  rcases cross_d2_2 (a0 - 1 - 1 - 1) b3 L3 [1] (by omega) (by omega) with ⟨b4, L4, hr4, hd4⟩
  have hsub : a0 - 1 - 1 - 1 - 1 = a0 - 4 := by omega
  rw [hsub] at hr4
  exact ⟨b4, L4, (((((h0.trans hr1).trans hr2).trans hmid).trans hr3).trans hr4).trans
    (step_BR1_0d 1 _ []), by omega⟩

/-- Constant-step entry of `(0, 5, 5)` over a positive leading block `a = k + 1 ≥ 1`. -/
private theorem hub_055_entry (k : ℕ) (L : List ℕ) :
    Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) [])
          (cfg_BR1 (0 :: inc1 L) (0 :: 2 :: 2 :: (rep02 (k + 1) ++ [0, 0, 3]))) := by
  have h1 := step_BR1_nil (0 :: 5 :: 5 :: (rep4 (k + 1) ++ 2 :: L))
  have h2 := step_CL1_zero (5 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) [0]
  have h3 := step_CL1_add_three 2 (5 :: (rep4 (k + 1) ++ 2 :: L)) [2]
  have h4 := step_EL1_add_two 0 (5 :: (rep4 (k + 1) ++ 2 :: L)) [0, 3]
  have h5 := step_EL1_zero (5 :: (rep4 (k + 1) ++ 2 :: L)) [0, 0, 3]
  have h6 := cl_6_rep4_step k 0 (2 :: L) [0, 3]
  dsimp only [rep02, List.cons_append] at h6
  have h7 := step_EL1_zero (3 :: L) (0 :: 2 :: (rep02 (k + 1) ++ [0, 0, 3]))
  have h8 := step_CL1_add_three 1 L (1 :: 2 :: (rep02 (k + 1) ++ [0, 0, 3]))
  have h9 := step_EL1_one L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ [0, 0, 3]))
  have h10 := step_EB1_zero L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ [0, 0, 3]))
  exact ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans
    h9).trans h10

/--
Constant-step block scanner for `(0, 5, 5)` over a block `b = k + 2 ≥ 2` (`inc1` leaves `5 :: rep4
(k+1)`). -/
private theorem scan_55_ge2 (k : ℕ) (L R : List ℕ) :
    Reach (cfg_BR1 (0 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: 2 :: 2 :: R))
          (cfg_BR1 (0 :: inc1 L) (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))) := by
  have h1 := sweep_BR_p02_one (5 :: (rep4 (k + 1) ++ 2 :: L)) (2 :: R)
  have h2 := step_BR1_ge2 0 (0 :: 4 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) R
  have h3 := step_EL1_add_two 0 (4 :: 5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: R)
  have h4 := sweep_EL_f4_one (5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: R)
  have h5 := step_EL1_zero (5 :: (rep4 (k + 1) ++ 2 :: L)) (0 :: 0 :: 2 :: 0 :: R)
  have h6 := cl_6_rep4_step k 0 (2 :: L) (0 :: 2 :: 0 :: R)
  dsimp only [rep02, List.cons_append] at h6
  have h7 := step_EL1_zero (3 :: L) (0 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))
  have h8 := step_CL1_add_three 1 L (1 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))
  have h9 := step_EL1_one L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))
  have h10 := step_EB1_zero L (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R)))
  exact ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans
    h9).trans h10

private theorem inc1_rep4_succ (n : ℕ) (L : List ℕ) :
    inc1 (rep4 (n + 1) ++ L) = 5 :: (rep4 n ++ L) := rfl

/-- Direct turnaround scanner for the last head block `a = k + 2 ≥ 2` of `(0, 5, 5)` against an
ARBITRARY tail-parametric `L : List ℕ` (NO leading `2 ::` required!): drops `P = a - 2 * W L` by
  AT MOST `8`! -/
private theorem scan_55_tail_any (k : ℕ) (L R : List ℕ) (hk : 2 * W L + 6 ≤ k) :
    ∃ (b : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: (rep4 (k + 1) ++ L)) (0 :: 2 :: 2 :: R))
            (cfg_BR1 (0 :: (rep4 b ++ L')) (0 :: 0 :: 2 :: 0 :: R)) ∧
      (k + 2) + 2 * W L' ≤ b + 2 * W L + 8 := by
  have h1 := sweep_BR_p02_one (5 :: (rep4 (k + 1) ++ L)) (2 :: R)
  have h2 := step_BR1_ge2 0 (0 :: 4 :: 5 :: (rep4 (k + 1) ++ L)) R
  have h3 := step_EL1_add_two 0 (4 :: 5 :: (rep4 (k + 1) ++ L)) (0 :: R)
  have h4 := sweep_EL_f4_one (5 :: (rep4 (k + 1) ++ L)) (0 :: R)
  have h5 := step_EL1_zero (5 :: (rep4 (k + 1) ++ L)) (0 :: 0 :: 2 :: 0 :: R)
  have h6 := cl_6_rep4_step k 0 L (0 :: 2 :: 0 :: R)
  dsimp only [rep02, List.cons_append] at h6
  have hpre : Reach (cfg_BR1 (0 :: 5 :: (rep4 (k + 1) ++ L)) (0 :: 2 :: 2 :: R))
                    (cfg_EL1 (0 :: inc1 L) (0 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: R))))
                      :=
    ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6
  let S := 0 :: 0 :: 2 :: 0 :: R
  let X := inc1 L
  have hWX : W X ≤ W L + 2 := W_inc1_le L
  have hpsiX : psi X ≤ 2 * W L + 4 := by have := psi_le X; omega
  rcases mEL_spec X (2 :: (rep02 (k + 1) ++ S)) with ⟨X1, hr1, hw1⟩ | ⟨X1, hr1, hw1⟩
  · -- ATE0 on `0`: cross `2`, then call `mEL_spec X1`!
    have hcross : Reach (cfg_BR1 (0 :: X1) (2 :: (rep02 (k + 1) ++ S)))
                        (cfg_EL1 (0 :: X1) (0 :: 0 :: (rep02 (k + 1) ++ S))) :=
      (step_BR1_ge2 0 (0 :: X1) (rep02 (k + 1) ++ S)).trans
        (step_EL1_add_two 0 X1 (0 :: (rep02 (k + 1) ++ S)))
    have hpsi1 : psi X1 ≤ 2 * W L + 4 := by have := psi_le X1; omega
    rcases mEL_spec X1 (0 :: (rep02 (k + 1) ++ S)) with ⟨X2, hr2, hw2⟩ | ⟨X2, hr2, hw2⟩
    · have hpsi2 : psi X2 ≤ 2 * W L + 4 := by have := psi_le X2; omega
      rcases p02_zero_drop (psi X2) X2 S (k + 1) rfl (by omega) with ⟨b, L', hr', hadd, _⟩
      exact ⟨b, L', (((hpre.trans hr1).trans hcross).trans hr2).trans hr', by omega⟩
    · have hsw := ((((hpre.trans hr1).trans hcross).trans hr2).trans
        (step_BR1_00 X2 (rep02 (k + 1) ++ S))).trans (sweep_BR_p02 (k + 1) (2 :: X2) S)
      refine ⟨k + 1, 2 :: X2, hsw, ?_⟩
      dsimp only [W]; change (k + 2) + 2 * (1 + W X2) ≤ (k + 1) + 2 * W L + 8; omega
  · -- KEEP0 on `0`: `0 :: 2 :: rep02 (k + 1) = rep02 (k + 2)` sweeps directly!
    have hsw : Reach (cfg_BR1 (0 :: X1) (0 :: 2 :: (rep02 (k + 1) ++ S)))
                     (cfg_BR1 (0 :: (rep4 (k + 2) ++ X1)) S) :=
      sweep_BR_p02 (k + 2) X1 S
    exact ⟨k + 2, X1, (hpre.trans hr1).trans hsw, by omega⟩

/--
1-head `0 :: 0 :: 2 :: 0 :: rep02 m` pair step (`m ≥ 2`, `2 * W L + 5 ≤ b`): produces `rep4 (m - 2)
++ 2 :: rep4 b' ++ L'`, `ΔP ≤ 5`! -/
private theorem step_55_pair_1 (m b : ℕ) (L R : List ℕ) (hm : 2 ≤ m) (hb : 2 * W L + 5 ≤ b) :
    ∃ (b' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 b ++ L)) (0 :: 0 :: 2 :: 0 :: (rep02 m ++ R)))
            (cfg_BR1 (0 :: (rep4 (m - 2) ++ 2 :: (rep4 b' ++ L'))) R) ∧
      b + 2 * W L' ≤ b' + 2 * W L + 5 := by
  have h1 := zero_p02_1 0 b L (0 :: (rep02 m ++ R)) (by omega)
  rcases h1 with ⟨b1, L1, hr1, hd1⟩
  dsimp only [rep4, List.nil_append] at hr1
  cases m with
  | zero => omega
  | succ m1 =>
    cases m1 with
    | zero => omega
    | succ m2 =>
      -- `m = m2 + 2`, so `rep02 (m2 + 2) = 0 :: 2 :: rep02 (m2 + 1)`
      have hr1' : Reach (cfg_BR1 (0 :: (rep4 b ++ L)) (0 :: 0 :: 2 :: 0 :: (rep02 (m2 + 2) ++ R)))
                        (cfg_BR1 (0 :: 2 :: (rep4 b1 ++ L1)) (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++
                          R))) := hr1
      have hmid : Reach (cfg_BR1 (0 :: 2 :: (rep4 b1 ++ L1)) (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++ R)))
                        (cfg_EL1 (0 :: (rep4 b1 ++ L1)) (0 :: 2 :: 2 :: 0 :: (rep02 (m2 + 1) ++
                          R))) := by
        let X := rep4 b1 ++ L1
        let Q := rep02 (m2 + 1) ++ R
        have s1 := step_BR1_00 (2 :: X) (2 :: Q)
        have s2 := step_BR1_ge2 0 (0 :: 2 :: 2 :: X) Q
        have s3 := step_EL1_add_two 0 (2 :: 2 :: X) (0 :: Q)
        have s4 := step_EL1_zero (2 :: 2 :: X) (0 :: 0 :: Q)
        have s5 := step_CL1_add_three 0 (2 :: X) (1 :: 0 :: Q)
        have s6 := step_EL1_zero (2 :: X) (0 :: 2 :: 0 :: Q)
        have s7 := step_CL1_add_three 0 X (1 :: 2 :: 0 :: Q)
        exact (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7
      rcases mEL_pot_1 b1 L1 (2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)) (by omega) with ⟨b2, L2, hr2,
        hd2⟩
      rcases cross_d2_1 b2 L2 (2 :: 0 :: (rep02 (m2 + 1) ++ R)) (by omega) with ⟨b3, L3, hr3, hd3⟩
      have hinc : Reach (cfg_BR1 (0 :: (rep4 b3 ++ L3)) (0 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)))
                        (cfg_BR1 (0 :: (rep4 (b3 + 1) ++ L3)) (0 :: (rep02 (m2 + 1) ++ R))) :=
        sweep_BR_p02_one (rep4 b3 ++ L3) (0 :: (rep02 (m2 + 1) ++ R))
      rcases zero_p02_1 m2 (b3 + 1) L3 R (by omega) with ⟨b4, L4, hr4, hd4⟩
      have hsub : m2 + 2 - 2 = m2 := by omega
      rw [hsub]
      exact ⟨b4, L4, ((((hr1'.trans hmid).trans hr2).trans hr3).trans hinc).trans hr4, by omega⟩

/--
2-head `hub_055_2`: `(0, 5, 5) [a0, a1] ++ L → (0, 3) [a0 - 4, a1'] ++ L'` (arbitrary `L`!), `ΔP ≤
21`! -/
private theorem hub_055_2 (a0 a1 : ℕ) (L : List ℕ)
    (ha0 : 4 ≤ a0) (ha1 : 2 * W L + 21 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
            (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 4) ++ 2 :: (rep4 a1' ++ L'))) []) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 21 := by
  rcases (⟨a0 - 1, by omega⟩ : ∃ k0, a0 = k0 + 1) with ⟨k0, hk0⟩
  rcases (⟨a1 - 2, by omega⟩ : ∃ k1, a1 = k1 + 2) with ⟨k1, hk1⟩
  have hsc1 : Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
                    (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ L))
                             (0 :: 2 :: 2 :: (rep02 a0 ++ [0, 0, 3]))) := by
    rw [hk0, hk1]
    have h := hub_055_entry k0 (rep4 (k1 + 2) ++ L)
    rw [inc1_rep4_succ (k1 + 1) L] at h
    exact h
  rcases scan_55_tail_any k1 L (rep02 a0 ++ [0, 0, 3]) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases step_55_pair_1 a0 b1 L1 [0, 0, 3] (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
  have hmid : Reach (cfg_BR1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2))) [0, 0, 3])
                    (cfg_EL1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 b2 ++ L2))) [0, 2, 1]) :=
    (((step_BR1_00 _ [3]).trans (br_d3_to_el _)).trans (step_EL1_zero _ [0, 1])).trans
      (step_CL1_add_three 0 _ [1, 1])
  rcases mEL_pot_2 (a0 - 2) b2 L2 [2, 1] (by omega) (by omega) with ⟨b3, L3, hr3, hd3⟩
  rcases cross_d2_2 (a0 - 2 - 1) b3 L3 [1] (by omega) (by omega) with ⟨b4, L4, hr4, hd4⟩
  have hsub : a0 - 2 - 1 - 1 = a0 - 4 := by omega
  rw [hsub] at hr4
  exact ⟨b4, L4, (((((hsc1.trans hr1).trans hr2).trans hmid).trans hr3).trans hr4).trans
    (step_BR1_0d 1 _ []), by omega⟩

/--
2-head `0 :: 0 :: 2 :: 0 :: rep02 m` pair step (`m ≥ 2`, `a1 ≥ 6`, `2 * W L + 24 ≤ a2`): `a1 → a1 -
5`, `ΔP ≤ 24`! -/
private theorem step_55_pair_2 (m a1 a2 : ℕ) (L R : List ℕ)
    (hm : 2 ≤ m) (ha1 : 6 ≤ a1) (ha2 : 2 * W L + 24 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: 0 :: 2 :: 0 :: (rep02 m ++ R)))
            (cfg_BR1 (0 :: (rep4 (m - 2) ++ 2 :: (rep4 (a1 - 5) ++ 2 :: (rep4 a2' ++ L')))) R) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 24 := by
  rcases zero_p02_2 0 a1 a2 L (0 :: (rep02 m ++ R)) (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  dsimp only [rep4, List.nil_append] at hr1
  cases m with
  | zero => omega
  | succ m1 =>
    cases m1 with
    | zero => omega
    | succ m2 =>
      have hr1' : Reach (cfg_BR1 (0 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L))) (0 :: 0 :: 2 :: 0 ::
        (rep02 (m2 + 2) ++ R)))
                        (cfg_BR1 (0 :: 2 :: (rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++
                          L1))) (0 :: 0 :: 2 :: (rep02 (m2 + 1) ++ R))) := hr1
      have hmid : Reach (cfg_BR1 (0 :: 2 :: (rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++ L1))) (0 :: 0 :: 2
        :: (rep02 (m2 + 1) ++ R)))
                        (cfg_EL1 (0 :: (rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++
                          L1))) (0 :: 2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R))) := by
        let X := rep4 (a1 - 2) ++ 2 :: (rep4 b1 ++ L1)
        let Q := rep02 (m2 + 1) ++ R
        exact ((((((step_BR1_00 (2 :: X) (2 :: Q)).trans
          (step_BR1_ge2 0 (0 :: 2 :: 2 :: X) Q)).trans
          (step_EL1_add_two 0 (2 :: 2 :: X) (0 :: Q))).trans
          (step_EL1_zero (2 :: 2 :: X) (0 :: 0 :: Q))).trans
          (step_CL1_add_three 0 (2 :: X) (1 :: 0 :: Q))).trans
          (step_EL1_zero (2 :: X) (0 :: 2 :: 0 :: Q))).trans
          (step_CL1_add_three 0 X (1 :: 2 :: 0 :: Q))
      rcases mEL_pot_2 (a1 - 2) b1 L1 (2 :: 2 :: 0 :: (rep02 (m2 + 1) ++ R)) (by omega) (by omega)
        with ⟨b2, L2, hr2, hd2⟩
      rcases cross_d2_2 (a1 - 2 - 1) b2 L2 (2 :: 0 :: (rep02 (m2 + 1) ++ R)) (by omega) (by omega)
        with ⟨b3, L3, hr3, hd3⟩
      have hinc : Reach (cfg_BR1 (0 :: (rep4 (a1 - 2 - 1 - 1) ++ 2 :: (rep4 b3 ++ L3))) (0 :: 2 ::
        0 :: (rep02 (m2 + 1) ++ R)))
                        (cfg_BR1 (0 :: (rep4 (a1 - 3) ++ 2 :: (rep4 b3 ++
                          L3))) (0 :: (rep02 (m2 + 1) ++ R))) := by
        have hrew : 4 :: (rep4 (a1 - 2 - 1 - 1) ++ 2 :: (rep4 b3 ++ L3)) =
            rep4 (a1 - 3) ++ 2 :: (rep4 b3 ++ L3) := by
          rw [show a1 - 3 = (a1 - 2 - 1 - 1) + 1 by omega]; rfl
        rw [← hrew]
        exact sweep_BR_p02_one (rep4 (a1 - 2 - 1 - 1) ++ 2 :: (rep4 b3 ++ L3)) (0 :: (rep02 (m2 +
          1) ++ R))
      rcases zero_p02_2 m2 (a1 - 3) b3 L3 R (by omega) (by omega) with ⟨b4, L4, hr4, hd4⟩
      have hsub1 : a1 - 3 - 2 = a1 - 5 := by omega
      have hsubm : m2 + 2 - 2 = m2 := by omega
      rw [hsub1] at hr4; rw [hsubm]
      exact ⟨b4, L4, ((((hr1'.trans hmid).trans hr2).trans hr3).trans hinc).trans hr4, by omega⟩

/--
3-head `hub_055_3`: `(0, 5, 5) [a0, a1, a2] ++ L → (0, 3) [a0 - 4, a1 - 16, a2'] ++ L'` (arbitrary
`L`!), `ΔP ≤ 69`! -/
private theorem hub_055_3 (a0 a1 a2 : ℕ) (L : List ℕ)
    (ha0 : 4 ≤ a0) (ha1 : 16 ≤ a1) (ha2 : 2 * W L + 69 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
            (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 4) ++ 2 :: (rep4 (a1 - 16) ++ 2 :: (rep4 a2' ++ L'))))
              []) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 69 := by
  rcases (⟨a0 - 1, by omega⟩ : ∃ k0, a0 = k0 + 1) with ⟨k0, hk0⟩
  rcases (⟨a1 - 2, by omega⟩ : ∃ k1, a1 = k1 + 2) with ⟨k1, hk1⟩
  rcases (⟨a2 - 2, by omega⟩ : ∃ k2, a2 = k2 + 2) with ⟨k2, hk2⟩
  have hsc1 : Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
                    (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                             (0 :: 2 :: 2 :: (rep02 a0 ++ [0, 0, 3]))) := by
    rw [hk0, hk1]
    have h := hub_055_entry k0 (rep4 (k1 + 2) ++ 2 :: (rep4 a2 ++ L))
    rw [inc1_rep4_succ (k1 + 1) (2 :: (rep4 a2 ++ L))] at h
    exact h
  have hsc2 : Reach (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                             (0 :: 2 :: 2 :: (rep02 a0 ++ [0, 0, 3])))
                    (cfg_BR1 (0 :: 5 :: (rep4 (k2 + 1) ++ L))
                             (0 :: 2 :: 2 :: (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 a0 ++
                               [0, 0, 3]))))) := by
    rw [hk2]
    have h := scan_55_ge2 k1 (rep4 (k2 + 2) ++ L) (rep02 a0 ++ [0, 0, 3])
    rw [inc1_rep4_succ (k2 + 1) L] at h
    exact h
  rcases scan_55_tail_any k2 L (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 a0 ++ [0, 0, 3])))
    (by omega) with
    ⟨b1, L1, hr1, hd1⟩
  rcases step_55_pair_1 (k1 + 1) b1 L1 (0 :: 0 :: 2 :: 0 :: (rep02 a0 ++ [0, 0, 3])) (by omega)
    (by omega) with
    ⟨b2, L2, hr2, hd2⟩
  rcases step_55_pair_2 a0 (k1 + 1 - 2) b2 L2 [0, 0, 3] (by omega) (by omega) (by omega) with
    ⟨b3, L3, hr3, hd3⟩
  have ha1_eq : k1 + 1 - 2 - 5 = a1 - 8 := by omega
  rw [ha1_eq] at hr3
  have hmid : Reach (cfg_BR1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 (a1 - 8) ++ 2 :: (rep4 b3 ++
    L3)))) [0, 0, 3])
                    (cfg_EL1 (0 :: (rep4 (a0 - 2) ++ 2 :: (rep4 (a1 - 8) ++ 2 :: (rep4 b3 ++
                      L3)))) [0, 2, 1]) :=
    (((step_BR1_00 _ [3]).trans (br_d3_to_el _)).trans (step_EL1_zero _ [0, 1])).trans
      (step_CL1_add_three 0 _ [1, 1])
  rcases mEL_pot_3 (a0 - 2) (a1 - 8) b3 L3 [2, 1] (by omega) (by omega) (by omega) with ⟨b4, L4,
    hr4, hd4⟩
  rcases cross_d2_3 (a0 - 2 - 1) (a1 - 8 - 4) b4 L4 [1] (by omega) (by omega) (by omega) with ⟨b5,
    L5, hr5, hd5⟩
  have hsub0 : a0 - 2 - 1 - 1 = a0 - 4 := by omega
  have hsub1 : a1 - 8 - 4 - 4 = a1 - 16 := by omega
  rw [hsub0, hsub1] at hr5
  exact ⟨b5, L5, (((((((hsc1.trans hsc2).trans hr1).trans hr2).trans hr3).trans hmid).trans
    hr4).trans hr5).trans
    (step_BR1_0d 1 _ []), by omega⟩

/--
Bridge `hub_055_one` (`H 63,350 → H 63,351`): `(0, 5, 5) [1, a1, a2] ++ L → (0, 5, 2) [a1 - 6, a2']
++ L'` (arbitrary `L`!), `ΔP ≤ 29`! -/
private theorem hub_055_one (a1 a2 : ℕ) (L : List ℕ)
    (ha1 : 8 ≤ a1) (ha2 : 2 * W L + 29 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 1 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
            (cfg_BR1 (0 :: 5 :: 2 :: (rep4 (a1 - 6) ++ 2 :: (rep4 a2' ++ L'))) []) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 29 := by
  rcases (⟨a1 - 2, by omega⟩ : ∃ k1, a1 = k1 + 2) with ⟨k1, hk1⟩
  rcases (⟨a2 - 2, by omega⟩ : ∃ k2, a2 = k2 + 2) with ⟨k2, hk2⟩
  have hsc1 : Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 1 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
                    (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                             (0 :: 2 :: 2 :: (rep02 1 ++ [0, 0, 3]))) := by
    rw [hk1]
    have h := hub_055_entry 0 (rep4 (k1 + 2) ++ 2 :: (rep4 a2 ++ L))
    rw [inc1_rep4_succ (k1 + 1) (2 :: (rep4 a2 ++ L))] at h
    exact h
  have hsc2 : Reach (cfg_BR1 (0 :: 5 :: (rep4 (k1 + 1) ++ 2 :: (rep4 a2 ++ L)))
                             (0 :: 2 :: 2 :: (rep02 1 ++ [0, 0, 3])))
                    (cfg_BR1 (0 :: 5 :: (rep4 (k2 + 1) ++ L))
                             (0 :: 2 :: 2 :: (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 1 ++
                               [0, 0, 3]))))) := by
    rw [hk2]
    have h := scan_55_ge2 k1 (rep4 (k2 + 2) ++ L) (rep02 1 ++ [0, 0, 3])
    rw [inc1_rep4_succ (k2 + 1) L] at h
    exact h
  rcases scan_55_tail_any k2 L (rep02 (k1 + 1) ++ (0 :: 0 :: 2 :: 0 :: (rep02 1 ++ [0, 0, 3])))
    (by omega) with
    ⟨b1, L1, hr1, hd1⟩
  rcases step_55_pair_1 (k1 + 1) b1 L1 (0 :: 0 :: 2 :: 0 :: (rep02 1 ++ [0, 0, 3])) (by omega) (by
    omega) with
    ⟨b2, L2, hr2, hd2⟩
  rcases zero_p02_2 0 (k1 + 1 - 2) b2 L2 (0 :: (rep02 1 ++ [0, 0, 3])) (by omega) (by omega) with
    ⟨b3, L3, hr3, hd3⟩
  dsimp only [rep4, rep02, List.nil_append, List.cons_append] at hr3
  have ha1_5 : k1 + 1 - 2 - 2 = a1 - 5 := by omega
  rw [ha1_5] at hr3
  have hmid : Reach (cfg_BR1 (0 :: 2 :: (rep4 (a1 - 5) ++ 2 :: (rep4 b3 ++ L3))) [0, 0, 2, 0, 0, 3])
                    (cfg_EL1 (0 :: (rep4 (a1 - 5) ++ 2 :: (rep4 b3 ++ L3))) [0, 2, 2, 0, 0, 0, 3])
                      := by
    let X := rep4 (a1 - 5) ++ 2 :: (rep4 b3 ++ L3)
    exact ((((((step_BR1_00 (2 :: X) [2, 0, 0, 3]).trans
      (step_BR1_ge2 0 (0 :: 2 :: 2 :: X) [0, 0, 3])).trans
      (step_EL1_add_two 0 (2 :: 2 :: X) [0, 0, 0, 3])).trans
      (step_EL1_zero (2 :: 2 :: X) [0, 0, 0, 0, 3])).trans
      (step_CL1_add_three 0 (2 :: X) [1, 0, 0, 0, 3])).trans
      (step_EL1_zero (2 :: X) [0, 2, 0, 0, 0, 3])).trans
      (step_CL1_add_three 0 X [1, 2, 0, 0, 0, 3])
  rcases mEL_pot_2 (a1 - 5) b3 L3 [2, 2, 0, 0, 0, 3] (by omega) (by omega) with ⟨b4, L4, hr4, hd4⟩
  rcases cross_d2_2 (a1 - 5 - 1) b4 L4 [2, 0, 0, 0, 3] (by omega) (by omega) with ⟨b5, L5, hr5, hd5⟩
  have hfin : Reach (cfg_BR1 (0 :: (rep4 (a1 - 5 - 1 - 1) ++ 2 :: (rep4 b5 ++ L5))) [0, 2, 0, 0,
    0, 3])
                    (cfg_BR1 (0 :: 5 :: 2 :: (rep4 (a1 - 6) ++ 2 :: (rep4 b5 ++ L5))) []) := by
    have hrew : 4 :: (rep4 (a1 - 5 - 1 - 1) ++ 2 :: (rep4 b5 ++ L5)) =
        rep4 (a1 - 6) ++ 2 :: (rep4 b5 ++ L5) := by
      rw [show a1 - 6 = (a1 - 5 - 1 - 1) + 1 by omega]; rfl
    have s1 := sweep_BR_p02_one (rep4 (a1 - 5 - 1 - 1) ++ 2 :: (rep4 b5 ++ L5)) [0, 0, 0, 3]
    rw [hrew] at s1
    exact (s1.trans (step_BR1_00 _ [0, 3])).trans (step_BR1_0d 3 _ [])
  exact ⟨b5, L5, (((((((hsc1.trans hsc2).trans hr1).trans hr2).trans hr3).trans hmid).trans
    hr4).trans hr5).trans hfin, by omega⟩

/-! ### Loops 1 & 2 (`Nat.rec` Iteration for `17,410` and `382,700` Cycles!) -/

/-- One 3-hub 3-head cycle `(0,5,5) → (0,3) → (0,) → (0,5,5)`: `a0 -= 9`, `a1 -= 28`, `ΔP ≤ 117`! -/
private theorem cycle_3_step (a0 a1 a2 : ℕ) (L : List ℕ)
    (ha0 : 9 ≤ a0) (ha1 : 28 ≤ a1) (ha2 : 2 * W L + 117 ≤ a2) :
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
            (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (a0 - 9) ++ 2 :: (rep4 (a1 - 28) ++ 2 :: (rep4 a2' ++
              L')))) []) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 117 := by
  rcases hub_055_3 a0 a1 a2 L (by omega) (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  rcases hub_03_3 (a0 - 4) (a1 - 16) b1 L1 (by omega) (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
  have hsub0 : a0 - 4 - 3 = (a0 - 9) + 2 := by omega
  have hsub1 : a1 - 16 - 12 = a1 - 28 := by omega
  rw [hsub0, hsub1] at hr2
  have hr3 := hub_0_step (a0 - 9) (2 :: (rep4 (a1 - 28) ++ 2 :: (rep4 b2 ++ L2)))
  exact ⟨b2, L2, (hr1.trans hr2).trans hr3, by omega⟩

/-- Iterated 3-head cycle (`n` cycles = `3 * n` hubs): `a0 -= 9*n`, `a1 -= 28*n`, `ΔP ≤ 117*n`! -/
private theorem cycle_3_iter : ∀ (n a0 a1 a2 : ℕ) (L : List ℕ),
    9 * n ≤ a0 → 28 * n ≤ a1 → 2 * W L + 117 * n ≤ a2 →
    ∃ (a2' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 5 :: 5 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ 2 :: (rep4 a2 ++ L)))) [])
            (cfg_BR1 (0 :: 5 :: 5 :: (rep4 (a0 - 9 * n) ++ 2 :: (rep4 (a1 - 28 * n) ++ 2 :: (rep4
              a2' ++ L')))) []) ∧
      a2 + 2 * W L' ≤ a2' + 2 * W L + 117 * n
  | 0, a0, a1, a2, L, _, _, _ => ⟨a2, L, by simp, by omega⟩
  | n + 1, a0, a1, a2, L, ha0, ha1, ha2 => by
    rcases cycle_3_step a0 a1 a2 L (by omega) (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
    rcases cycle_3_iter n (a0 - 9) (a1 - 28) b1 L1 (by omega) (by omega) (by omega) with
      ⟨b2, L2, hr2, hd2⟩
    have hsub0 : a0 - 9 - 9 * n = a0 - 9 * (n + 1) := by omega
    have hsub1 : a1 - 28 - 28 * n = a1 - 28 * (n + 1) := by omega
    rw [hsub0, hsub1] at hr2
    exact ⟨b2, L2, hr1.trans hr2, by omega⟩

/-- One 3-hub 2-head cycle `(0,3) → (0,) → (0,5,5) → (0,3)`: `a0 -= 9`, `ΔP ≤ 33`! -/
private theorem cycle_2_step (a0 a1 : ℕ) (L : List ℕ)
    (ha0 : 9 ≤ a0) (ha1 : 2 * W L + 33 ≤ a1) :
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
            (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 9) ++ 2 :: (rep4 a1' ++ L'))) []) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 33 := by
  rcases hub_03_2 a0 a1 L (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
  have hsub0 : a0 - 3 = (a0 - 5) + 2 := by omega
  rw [hsub0] at hr1
  have hr2 := hub_0_step (a0 - 5) (2 :: (rep4 b1 ++ L1))
  rcases hub_055_2 (a0 - 5) b1 L1 (by omega) (by omega) with ⟨b2, L2, hr3, hd3⟩
  have hsub1 : a0 - 5 - 4 = a0 - 9 := by omega
  rw [hsub1] at hr3
  exact ⟨b2, L2, (hr1.trans hr2).trans hr3, by omega⟩

/-- Iterated 2-head cycle (`n` cycles = `3 * n` hubs): `a0 -= 9*n`, `ΔP ≤ 33*n`! -/
private theorem cycle_2_iter : ∀ (n a0 a1 : ℕ) (L : List ℕ),
    9 * n ≤ a0 → 2 * W L + 33 * n ≤ a1 →
    ∃ (a1' : ℕ) (L' : List ℕ),
      Reach (cfg_BR1 (0 :: 3 :: (rep4 a0 ++ 2 :: (rep4 a1 ++ L))) [])
            (cfg_BR1 (0 :: 3 :: (rep4 (a0 - 9 * n) ++ 2 :: (rep4 a1' ++ L'))) []) ∧
      a1 + 2 * W L' ≤ a1' + 2 * W L + 33 * n
  | 0, a0, a1, L, _, _ => ⟨a1, L, by simp, by omega⟩
  | n + 1, a0, a1, L, ha0, ha1 => by
    rcases cycle_2_step a0 a1 L (by omega) (by omega) with ⟨b1, L1, hr1, hd1⟩
    rcases cycle_2_iter n (a0 - 9) b1 L1 (by omega) (by omega) with ⟨b2, L2, hr2, hd2⟩
    have hsub0 : a0 - 9 - 9 * n = a0 - 9 * (n + 1) := by omega
    rw [hsub0] at hr2
    exact ⟨b2, L2, hr1.trans hr2, by omega⟩

/-- Stage 2 Master Theorem: FROM `H 11,120` with ANY tail `L` satisfying `W L ≤ 14`, the machine
  HALTS
(17,410 3-head cycles → bridge `H 63,350 → H 63,352` → 382,700 2-head cycles → terminal halt at `H
  1,211,452`,
with spare potential margin **4,650,955**!). -/
private theorem halts_from_H11120 (L : List ℕ) (hWL : W L ≤ 14) :
    HaltsFrom target_tm
      (cfg_BR1 (0 :: 5 :: 5 :: (rep4 156691 ++ 2 :: (rep4 3931792 ++ 2 :: (rep4 19317108 ++ L))))
        []) := by
  -- Loop 1: `H 11,120 → H 63,350` (`17,410` cycles = `52,230` hubs)
  rcases cycle_3_iter 17410 156691 3931792 19317108 L (by omega) (by omega) (by omega) with
    ⟨a2_1, L1, hr1, hd1⟩
  rw [show 156691 - 9 * 17410 = 1 by decide,
      show 3931792 - 28 * 17410 = 3444312 by decide] at hr1
  -- Bridge 1: `H 63,350 → H 63,351` (`hub_055_one`)
  rcases hub_055_one 3444312 a2_1 L1 (by omega) (by omega) with ⟨a2_2, L2, hr2, hd2⟩
  rw [show 3444312 - 6 = 3444306 by decide] at hr2
  -- Bridge 2: `H 63,351 → H 63,352` (`hub_052_2`)
  rcases hub_052_2 3444306 a2_2 L2 (by omega) (by omega) with ⟨a2_3, L3, hr3, hd3⟩
  rw [show 3444306 - 4 = 3444302 by decide] at hr3
  -- Loop 2: `H 63,352 → H 1,211,452` (`382,700` cycles = `1,148,100` hubs)
  rcases cycle_2_iter 382700 3444302 a2_3 L3 (by omega) (by omega) with ⟨a2_4, L4, hr4, hd4⟩
  rw [show 3444302 - 9 * 382700 = 2 by decide] at hr4
  -- Terminal Halt at `H 1,211,452` (`hub_03_halt`, spare margin `4,650,965 ≥ 10`!)
  have hhalt := hub_03_halt a2_4 L4 (by omega)
  exact HaltsFrom.of_reachesStar (((hr1.trans hr2).trans hr3).trans hr4) hhalt

/-! ## Section 4: Stage 1 Exact Block-List Kernel Stepper (`init [] → H 11,120`) -/

inductive Pfx where
  | p0 | p03 | p05 | p055

private def pfxEq : Pfx → Pfx → Bool
  | .p0, .p0 => true
  | .p03, .p03 => true
  | .p05, .p05 => true
  | .p055, .p055 => true
  | _, _ => false

private theorem pfxEq_eq {p₁ p₂ : Pfx} (h : pfxEq p₁ p₂ = true) : p₁ = p₂ := by
  cases p₁ <;> cases p₂ <;> first | rfl | cases h

private def encPfx : Pfx → List ℕ
  | .p0   => [0]
  | .p03  => [0, 3]
  | .p05  => [0, 5]
  | .p055 => [0, 5, 5]

private def encBlks : List ℕ → List ℕ
  | [] => []
  | [a] => rep4 a
  | a :: b :: bs => rep4 a ++ 2 :: encBlks (b :: bs)

private def encHub (p : Pfx) (bs : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  cfg_BR1 (encPfx p ++ encBlks bs) []

private theorem encBlks_cons_ne (a : ℕ) {bs : List ℕ} (hne : bs ≠ []) :
    encBlks (a :: bs) = rep4 a ++ 2 :: encBlks bs := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons b tl => rfl

private theorem encBlks_zero_cons {bs : List ℕ} (hne : bs ≠ []) :
    encBlks (0 :: bs) = 2 :: encBlks bs := by
  rw [encBlks_cons_ne 0 hne]; rfl

private theorem encBlks_add_head (a n : ℕ) (bs : List ℕ) :
    rep4 n ++ encBlks (a :: bs) = encBlks ((a + n) :: bs) := by
  cases bs with
  | nil =>
    dsimp only [encBlks]
    have h1 : rep4 (a + n) ++ [] = rep4 n ++ (rep4 a ++ []) := by
      rw [show a + n = n + a by omega, rep4_add n a []]
    simpa only [List.append_nil] using h1.symm
  | cons b tl =>
    dsimp only [encBlks]
    rw [show a + n = n + a by omega, rep4_add n a (2 :: encBlks (b :: tl))]

private theorem W_encBlks_cons : ∀ (bs : List ℕ) (a : ℕ), W (encBlks (a :: bs)) = bs.length
  | [], a => by
    dsimp only [encBlks, List.length]
    have h := W_rep4_append a []
    rw [List.append_nil] at h
    exact h
  | b :: tl, a => by
    dsimp only [encBlks]
    rw [W_rep4_append]
    have ih := W_encBlks_cons tl b
    change 1 + W (encBlks (b :: tl)) = tl.length + 1
    omega

inductive RTag where
  | z0 | z2 | p

private def encR : List (RTag × ℕ) → List ℕ
  | [] => []
  | (.z0, _) :: rs => 0 :: encR rs
  | (.z2, _) :: rs => 2 :: encR rs
  | (.p, n) :: rs => rep02 n ++ encR rs

private theorem ble_true_iff (a b : ℕ) : Nat.ble a b = true ↔ a ≤ b := by
  simp

private noncomputable def forceListCPS {α : Type} : List ℕ → (List ℕ → α) → α
  | [], k => k []
  | x :: xs, k =>
    Nat.rec (forceListCPS xs (fun tl => k (0 :: tl)))
            (fun v _ => forceListCPS xs (fun tl => k (v :: tl)))
            (Nat.add x 1)

private theorem forceListCPS_eq {α : Type} :
    ∀ (l : List ℕ) (k : List ℕ → α), forceListCPS l k = k l
  | [], _ => rfl
  | x :: xs, k => forceListCPS_eq xs (fun tl => k (x :: tl))

/-! ### Exact Linear Operator `subTail` & Soundness -/

private def subTail (d : ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | [a] => some [a + d]
  | b :: c :: bs =>
    if Nat.ble d b then
      match subTail (4 * d) (c :: bs) with
      | none => none
      | some tl => some ((b - d) :: tl)
    else none

private theorem subTail_length : ∀ (bs : List ℕ) (d : ℕ) (out : List ℕ),
    subTail d bs = some out → out.length = bs.length
  | [], _, _, h => by cases h
  | [_], _, out, h => by cases h; rfl
  | b :: c :: tl, d, out, h => by
    dsimp only [subTail] at h
    cases hb : Nat.ble d b with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h
      cases ht : subTail (4 * d) (c :: tl) with
      | none => rw [ht] at h; cases h
      | some tl' =>
        rw [ht] at h
        cases h
        have ih := subTail_length (c :: tl) (4 * d) tl' ht
        dsimp only [List.length] at ih ⊢
        omega

private theorem subTail_ne_nil {d : ℕ} {bs out : List ℕ} (h : subTail d bs = some out) :
    out ≠ [] := by
  have hl := subTail_length bs d out h
  cases bs with
  | nil => cases h
  | cons _ _ =>
    intro hnil
    rw [hnil] at hl
    cases hl

private theorem subTail_zero : ∀ (bs : List ℕ), bs ≠ [] → subTail 0 bs = some bs
  | [], h => absurd rfl h
  | [a], _ => by simp [subTail]
  | b :: c :: tl, _ => by
    dsimp only [subTail]
    have hle : Nat.ble 0 b = true := (ble_true_iff 0 b).mpr (Nat.zero_le b)
    rw [hle, Nat.mul_zero, subTail_zero (c :: tl) (by simp)]
    simp

private theorem subTail_split :
    ∀ (bs : List ℕ) (d1 d2 : ℕ) (out : List ℕ),
      subTail (d1 + d2) bs = some out →
      ∃ mid, subTail d1 bs = some mid ∧ subTail d2 mid = some out
  | [], _, _, _, h => by cases h
  | [a], d1, d2, out, h => by
    cases h
    refine ⟨[a + d1], rfl, ?_⟩
    dsimp only [subTail]
    rw [Nat.add_assoc]
  | b :: c :: tl, d1, d2, out, h => by
    dsimp only [subTail] at h
    cases hb : Nat.ble (d1 + d2) b with
    | false => rw [hb] at h; cases h
    | true =>
      have hle : d1 + d2 ≤ b := (ble_true_iff _ _).mp hb
      rw [hb] at h
      cases ht : subTail (4 * (d1 + d2)) (c :: tl) with
      | none => rw [ht] at h; cases h
      | some out_tl =>
        rw [ht] at h
        cases h
        have hmul : 4 * (d1 + d2) = 4 * d1 + 4 * d2 := by omega
        rw [hmul] at ht
        rcases subTail_split (c :: tl) (4 * d1) (4 * d2) out_tl ht with ⟨mid_tl, hm1, hm2⟩
        have hne : mid_tl ≠ [] := subTail_ne_nil hm1
        cases hmt : mid_tl with
        | nil => exact absurd hmt hne
        | cons mhd mtl =>
          rw [hmt] at hm1 hm2
          refine ⟨(b - d1) :: mhd :: mtl, ?_, ?_⟩
          · dsimp only [subTail]
            have h1 : Nat.ble d1 b = true := (ble_true_iff _ _).mpr (by omega)
            simp [h1, hm1]
          · dsimp only [subTail]
            have h2 : Nat.ble d2 (b - d1) = true := (ble_true_iff _ _).mpr (by omega)
            simp [h2, hm2, show b - d1 - d2 = b - (d1 + d2) by omega]

private theorem mEL_single (a : ℕ) (S : List ℕ) :
    Reach (cfg_EL1 (0 :: rep4 a) (0 :: S)) (cfg_BR1 (0 :: rep4 (a + 1)) S) := by
  have h1 : Reach (cfg_EL1 (0 :: (rep4 a ++ [])) (0 :: S))
                  (cfg_EL1 [0] (0 :: (rep02 a ++ S))) := sweep_EL_f4 a [] S
  rw [List.append_nil] at h1
  have h2 : Reach (cfg_EL1 [0] (0 :: (rep02 a ++ S)))
                  (cfg_BR1 [0, 4] (rep02 a ++ S)) :=
    (((step_EL1_zero [] (0 :: (rep02 a ++ S))).trans
      (step_CL1_zero [] (1 :: (rep02 a ++ S)))).trans
      (step_CL1_nil (3 :: (rep02 a ++ S)))).trans
      (step_EL1_nil_cons 4 (rep02 a ++ S))
  have h3 := sweep_BR_p02 a [4] S
  have hrep : rep4 a ++ [4] = rep4 (a + 1) := by
    rw [show rep4 (a + 1) = 4 :: rep4 a from rfl, rep4_snoc a []]
    simp
  rw [hrep] at h3
  exact (h1.trans h2).trans h3

private theorem mEL_subTail_one :
    ∀ (n : ℕ) (bs out : List ℕ), bs.length = n → subTail 1 bs = some out →
      ∀ S : List ℕ, Reach (cfg_EL1 (0 :: encBlks bs) (0 :: S)) (cfg_BR1 (0 :: encBlks out) S)
  | 0, bs, _, hlen, hsub, _ => by cases bs with | nil => cases hsub | cons _ _ => cases hlen
  | n + 1, bs, out, hlen, hsub, S => by
    cases bs with
    | nil => cases hsub
    | cons a tl =>
      cases tl with
      | nil =>
        cases hsub
        exact mEL_single a S
      | cons b rest =>
        dsimp only [subTail] at hsub
        cases hb : Nat.ble 1 a with
        | false => rw [hb] at hsub; cases hsub
        | true =>
          have ha : 1 ≤ a := (ble_true_iff 1 a).mp hb
          rw [hb] at hsub
          cases ht : subTail 4 (b :: rest) with
          | none => rw [ht] at hsub; cases hsub
          | some out_tl =>
            rw [ht] at hsub
            cases hsub
            have h4 : (4 : ℕ) = 1 + 3 := rfl
            rw [h4] at ht
            rcases subTail_split (b :: rest) 1 3 out_tl ht with ⟨t1, ht1, ht13⟩
            have h3 : (3 : ℕ) = 1 + 2 := rfl
            rw [h3] at ht13
            rcases subTail_split t1 1 2 out_tl ht13 with ⟨t2, ht2, ht22⟩
            have h2 : (2 : ℕ) = 1 + 1 := rfl
            rw [h2] at ht22
            rcases subTail_split t2 1 1 out_tl ht22 with ⟨t3, ht3, ht4⟩
            have hl0 : (b :: rest).length = n := by dsimp only [List.length] at hlen ⊢; omega
            have hl1 : t1.length = n := by rw [subTail_length _ _ _ ht1, hl0]
            have hl2 : t2.length = n := by rw [subTail_length _ _ _ ht2, hl1]
            have hl3 : t3.length = n := by rw [subTail_length _ _ _ ht3, hl2]
            have hout_ne : out_tl ≠ [] := subTail_ne_nil ht4
            rcases (⟨a - 1, by omega⟩ : ∃ m, a = m + 1) with ⟨m, hm⟩
            have hsub_m : a - 1 = m := by omega
            rw [hsub_m, encBlks_cons_ne m hout_ne]
            dsimp only [encBlks]
            rw [hm]
            have s0 : Reach (cfg_EL1 (0 :: (rep4 (m + 1) ++ 2 :: encBlks (b :: rest))) (0 :: S))
                            (cfg_EL1 (0 :: encBlks (b :: rest)) (0 :: 2 :: (rep02 (m + 1) ++ S))) :=
              ((sweep_EL_f4 (m + 1) (2 :: encBlks (b :: rest)) S).trans
                (step_EL1_zero (2 :: encBlks (b :: rest)) (0 :: (rep02 (m + 1) ++ S)))).trans
                (step_CL1_add_three 0 (encBlks (b :: rest)) (1 :: (rep02 (m + 1) ++ S)))
            have s1 := mEL_subTail_one n (b :: rest) t1 hl0 ht1 (2 :: (rep02 (m + 1) ++ S))
            have sc1 : Reach (cfg_BR1 (0 :: encBlks t1) (2 :: (rep02 (m + 1) ++ S)))
                             (cfg_EL1 (0 :: encBlks t1) (0 :: 0 :: (rep02 (m + 1) ++ S))) :=
              (step_BR1_ge2 0 (0 :: encBlks t1) (rep02 (m + 1) ++ S)).trans
                (step_EL1_add_two 0 (encBlks t1) (0 :: (rep02 (m + 1) ++ S)))
            have s2 := mEL_subTail_one n t1 t2 hl1 ht2 (0 :: (rep02 (m + 1) ++ S))
            dsimp only [rep02, List.cons_append] at s2
            have smid : Reach (cfg_BR1 (0 :: encBlks t2) (0 :: 0 :: 2 :: (rep02 m ++ S)))
                              (cfg_EL1 (0 :: encBlks t2) (0 :: 2 :: 0 :: (rep02 m ++ S))) :=
              ((((step_BR1_00 (encBlks t2) (2 :: (rep02 m ++ S))).trans
                (step_BR1_ge2 0 (0 :: 2 :: encBlks t2) (rep02 m ++ S))).trans
                (step_EL1_add_two 0 (2 :: encBlks t2) (0 :: (rep02 m ++ S)))).trans
                (step_EL1_zero (2 :: encBlks t2) (0 :: 0 :: (rep02 m ++ S)))).trans
                (step_CL1_add_three 0 (encBlks t2) (1 :: 0 :: (rep02 m ++ S)))
            have s3 := mEL_subTail_one n t2 t3 hl2 ht3 (2 :: 0 :: (rep02 m ++ S))
            have sc2 : Reach (cfg_BR1 (0 :: encBlks t3) (2 :: 0 :: (rep02 m ++ S)))
                             (cfg_EL1 (0 :: encBlks t3) (0 :: 0 :: 0 :: (rep02 m ++ S))) :=
              (step_BR1_ge2 0 (0 :: encBlks t3) (0 :: (rep02 m ++ S))).trans
                (step_EL1_add_two 0 (encBlks t3) (0 :: 0 :: (rep02 m ++ S)))
            have s4 := mEL_subTail_one n t3 out_tl hl3 ht4 (0 :: 0 :: (rep02 m ++ S))
            have sfin : Reach (cfg_BR1 (0 :: encBlks out_tl) (0 :: 0 :: (rep02 m ++ S)))
                              (cfg_BR1 (0 :: (rep4 m ++ 2 :: encBlks out_tl)) S) :=
              (step_BR1_00 (encBlks out_tl) (rep02 m ++ S)).trans
                (sweep_BR_p02 m (2 :: encBlks out_tl) S)
            exact ((((((s0.trans s1).trans sc1).trans s2).trans smid).trans s3).trans sc2).trans
              (s4.trans sfin)

private theorem mEL_subTail_zero_two {bs out : List ℕ} (hne : bs ≠ [])
    (hsub : subTail 2 bs = some out) (S : List ℕ) :
    Reach (cfg_EL1 (0 :: encBlks (0 :: bs)) (0 :: S)) (cfg_BR1 (0 :: encBlks out) (0 :: S)) := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [h2] at hsub
  rcases subTail_split bs 1 1 out hsub with ⟨mid, hm1, hm2⟩
  rw [encBlks_zero_cons hne]
  have s0 : Reach (cfg_EL1 (0 :: 2 :: encBlks bs) (0 :: S)) (cfg_EL1 (0 :: encBlks bs) (0 :: 2 ::
    S)) :=
    (step_EL1_zero (2 :: encBlks bs) (0 :: S)).trans (step_CL1_add_three 0 (encBlks bs) (1 :: S))
  have s1 := mEL_subTail_one bs.length bs mid rfl hm1 (2 :: S)
  have sc : Reach (cfg_BR1 (0 :: encBlks mid) (2 :: S)) (cfg_EL1 (0 :: encBlks mid) (0 :: 0 :: S))
    :=
    (step_BR1_ge2 0 (0 :: encBlks mid) S).trans (step_EL1_add_two 0 (encBlks mid) (0 :: S))
  have s2 := mEL_subTail_one mid.length mid out rfl hm2 (0 :: S)
  exact ((s0.trans s1).trans sc).trans s2

private theorem zero_p02_subTail {bs out : List ℕ} (n : ℕ)
    (hsub : subTail 2 bs = some out) (S : List ℕ) :
    Reach (cfg_BR1 (0 :: encBlks bs) (0 :: (rep02 (n + 1) ++ S)))
          (cfg_BR1 (0 :: encBlks (n :: out)) S) := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [h2] at hsub
  rcases subTail_split bs 1 1 out hsub with ⟨mid, hm1, hm2⟩
  have hout_ne : out ≠ [] := subTail_ne_nil hm2
  rw [encBlks_cons_ne n hout_ne]
  dsimp only [rep02, List.cons_append]
  have s0 : Reach (cfg_BR1 (0 :: encBlks bs) (0 :: 0 :: 2 :: (rep02 n ++ S)))
                  (cfg_EL1 (0 :: encBlks bs) (0 :: 2 :: 0 :: (rep02 n ++ S))) :=
    ((((step_BR1_00 (encBlks bs) (2 :: (rep02 n ++ S))).trans
      (step_BR1_ge2 0 (0 :: 2 :: encBlks bs) (rep02 n ++ S))).trans
      (step_EL1_add_two 0 (2 :: encBlks bs) (0 :: (rep02 n ++ S)))).trans
      (step_EL1_zero (2 :: encBlks bs) (0 :: 0 :: (rep02 n ++ S)))).trans
      (step_CL1_add_three 0 (encBlks bs) (1 :: 0 :: (rep02 n ++ S)))
  have s1 := mEL_subTail_one bs.length bs mid rfl hm1 (2 :: 0 :: (rep02 n ++ S))
  have sc : Reach (cfg_BR1 (0 :: encBlks mid) (2 :: 0 :: (rep02 n ++ S)))
                  (cfg_EL1 (0 :: encBlks mid) (0 :: 0 :: 0 :: (rep02 n ++ S))) :=
    (step_BR1_ge2 0 (0 :: encBlks mid) (0 :: (rep02 n ++ S))).trans
      (step_EL1_add_two 0 (encBlks mid) (0 :: 0 :: (rep02 n ++ S)))
  have s2 := mEL_subTail_one mid.length mid out rfl hm2 (0 :: 0 :: (rep02 n ++ S))
  have sfin : Reach (cfg_BR1 (0 :: encBlks out) (0 :: 0 :: (rep02 n ++ S)))
                    (cfg_BR1 (0 :: (rep4 n ++ 2 :: encBlks out)) S) :=
    (step_BR1_00 (encBlks out) (rep02 n ++ S)).trans
      (sweep_BR_p02 n (2 :: encBlks out) S)
  exact (((s0.trans s1).trans sc).trans s2).trans sfin

private theorem hub_03_subTail {bs out : List ℕ} (hsub : subTail 3 bs = some out) :
    Reach (encHub .p03 bs) (encHub .p0 out) := by
  have h3 : (3 : ℕ) = 1 + 2 := rfl
  rw [h3] at hsub
  rcases subTail_split bs 1 2 out hsub with ⟨t1, ht1, ht12⟩
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [h2] at ht12
  rcases subTail_split t1 1 1 out ht12 with ⟨t2, ht2, ht3⟩
  have s0 := hub_03_entry (encBlks bs)
  have s1 := mEL_subTail_one bs.length bs t1 rfl ht1 [3]
  have s2 := mEL_subTail_one t1.length t1 t2 rfl ht2 [1]
  have s3 := mEL_subTail_one t2.length t2 out rfl ht3 []
  exact ((((s0.trans s1).trans (br_d3_to_el _)).trans s2).trans (br_d1_to_el _)).trans s3

private theorem hub_05_entry (L : List ℕ) :
    Reach (cfg_BR1 (0 :: 5 :: L) []) (cfg_EL1 (0 :: L) [0, 0, 3]) :=
  (((step_BR1_nil (0 :: 5 :: L)).trans (step_CL1_zero (5 :: L) [0])).trans
    (step_CL1_add_three 2 L [2])).trans (step_EL1_add_two 0 L [0, 3])

private theorem hub_05_subTail_one {bs out : List ℕ} (hsub : subTail 1 bs = some out) :
    Reach (encHub .p05 bs) (encHub .p05 out) :=
  ((hub_05_entry (encBlks bs)).trans
    (mEL_subTail_one bs.length bs out rfl hsub [0, 3])).trans
    (step_BR1_0d 3 (encBlks out) [])

private theorem hub_05_batch : ∀ (m : ℕ) (bs out : List ℕ),
    subTail m bs = some out → Reach (encHub .p05 bs) (encHub .p05 out)
  | 0, bs, out, h => by
    have hne : bs ≠ [] := by cases bs with | nil => cases h | cons _ _ => simp
    rw [subTail_zero bs hne] at h
    cases h
    exact ReachesStar.refl target_tm _
  | m + 1, bs, out, h => by
    rw [show m + 1 = 1 + m by omega] at h
    rcases subTail_split bs 1 m out h with ⟨mid, hm1, hmm⟩
    exact (hub_05_subTail_one hm1).trans (hub_05_batch m mid out hmm)

/-! ### Mutual `evalBody` & `runStream` + Soundness -/

mutual
private def evalBody : ℕ → List ℕ → Option (List ℕ × Bool)
  | 0, _ => none
  | _, [] => none
  | _, [a] => some ([a + 1], false)
  | fuel + 1, a :: b :: tl =>
    if Nat.beq a 0 then
      match subTail 2 (b :: tl) with
      | some out => some (out, true)
      | none =>
        match evalBody fuel (b :: tl) with
        | none => none
        | some (L, has0) =>
          runStream fuel L (if has0 then [(.z0, 0), (.z2, 0)] else [(.z2, 0)])
    else
      match subTail 1 (a :: b :: tl) with
      | some out => some (out, false)
      | none =>
        match evalBody fuel (b :: tl) with
        | none => none
        | some (L, has0) =>
          runStream fuel L (if has0 then [(.z0, 0), (.z2, 0), (.p, a)] else [(.z2, 0), (.p, a)])

private def runStream : ℕ → List ℕ → List (RTag × ℕ) → Option (List ℕ × Bool)
  | 0, _, _ => none
  | _, [], _ => none
  | _, L, [] => some (L, false)
  | fuel + 1, a :: tl, (.p, n) :: rs =>
    runStream fuel ((a + n) :: tl) rs
  | fuel + 1, a :: tl, (.z2, _) :: rs =>
    match evalBody fuel (a :: tl) with
    | none => none
    | some (L2, false) => runStream fuel L2 ((.z0, 0) :: rs)
    | some (L2, true)  => runStream fuel (0 :: L2) rs
  | _, a :: tl, [(.z0, _)] => some (a :: tl, true)
  | fuel + 1, a :: tl, (.z0, _) :: (.z0, _) :: rs =>
    runStream fuel (0 :: a :: tl) rs
  | fuel + 1, a :: tl, (.z0, _) :: (.z2, _) :: rs =>
    runStream fuel ((a + 1) :: tl) rs
  | fuel + 1, a :: tl, (.z0, _) :: (.p, n) :: rs =>
    if Nat.beq n 0 then
      runStream fuel (a :: tl) ((.z0, 0) :: rs)
    else
      match subTail 2 (a :: tl) with
      | some L2 => runStream fuel ((n - 1) :: L2) rs
      | none =>
        runStream fuel (0 :: a :: tl)
          (if Nat.beq n 1 then (.z2, 0) :: rs else (.z2, 0) :: (.p, n - 1) :: rs)
end

private theorem eval_run_sound : ∀ (fuel : ℕ),
    (∀ (bs out : List ℕ) (has0 : Bool),
      evalBody fuel bs = some (out, has0) →
      out ≠ [] ∧ ∀ S : List ℕ,
        Reach (cfg_EL1 (0 :: encBlks bs) (0 :: S))
              (cfg_BR1 (0 :: encBlks out) (if has0 then 0 :: S else S))) ∧
    (∀ (L : List ℕ) (R : List (RTag × ℕ)) (out : List ℕ) (has0 : Bool),
      runStream fuel L R = some (out, has0) →
      out ≠ [] ∧ ∀ S : List ℕ,
        Reach (cfg_BR1 (0 :: encBlks L) (encR R ++ S))
              (cfg_BR1 (0 :: encBlks out) (if has0 then 0 :: S else S)))
  | 0 => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h)⟩
  | fuel + 1 => by
    obtain ⟨ihEL, ihRS⟩ := eval_run_sound fuel
    constructor
    · -- `evalBody (fuel + 1)`
      intro bs out has0 h
      cases bs with
      | nil => cases h
      | cons a tl =>
        cases tl with
        | nil =>
          cases h
          exact ⟨by simp, fun S => mEL_single a S⟩
        | cons b rest =>
          dsimp only [evalBody] at h
          cases ha0 : Nat.beq a 0 with
          | true =>
            have ha : a = 0 := Nat.eq_of_beq_eq_true ha0
            subst ha
            simp only [ha0, ↓reduceIte] at h
            cases hst : subTail 2 (b :: rest) with
            | some out' =>
              rw [hst] at h; cases h
              exact ⟨subTail_ne_nil hst, fun S => mEL_subTail_zero_two (by simp) hst S⟩
            | none =>
              rw [hst] at h
              cases heb : evalBody fuel (b :: rest) with
              | none => rw [heb] at h; cases h
              | some p =>
                rcases p with ⟨L, h0⟩
                rw [heb] at h
                obtain ⟨_, hEL⟩ := ihEL (b :: rest) L h0 heb
                have s0 : ∀ S, Reach (cfg_EL1 (0 :: encBlks (0 :: b :: rest)) (0 :: S))
                                     (cfg_EL1 (0 :: encBlks (b :: rest)) (0 :: 2 :: S)) := fun S =>
                  (step_EL1_zero (2 :: encBlks (b :: rest)) (0 :: S)).trans
                    (step_CL1_add_three 0 (encBlks (b :: rest)) (1 :: S))
                cases h0 with
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  obtain ⟨hne, hRS⟩ := ihRS L [(.z2, 0)] out has0 h
                  refine ⟨hne, fun S => ((s0 S).trans (hEL (2 :: S))).trans (hRS S)⟩
                | true =>
                  simp only [↓reduceIte] at h
                  obtain ⟨hne, hRS⟩ := ihRS L [(.z0, 0), (.z2, 0)] out has0 h
                  refine ⟨hne, fun S => ((s0 S).trans (hEL (2 :: S))).trans (hRS S)⟩
          | false =>
            simp only [ha0, Bool.false_eq_true, ↓reduceIte] at h
            cases hst : subTail 1 (a :: b :: rest) with
            | some out' =>
              rw [hst] at h; cases h
              exact ⟨subTail_ne_nil hst, fun S => mEL_subTail_one _ _ _ rfl hst S⟩
            | none =>
              rw [hst] at h
              cases heb : evalBody fuel (b :: rest) with
              | none => rw [heb] at h; cases h
              | some p =>
                rcases p with ⟨L, h0⟩
                rw [heb] at h
                obtain ⟨_, hEL⟩ := ihEL (b :: rest) L h0 heb
                have s0 : ∀ S, Reach (cfg_EL1 (0 :: encBlks (a :: b :: rest)) (0 :: S))
                                     (cfg_EL1 (0 :: encBlks (b :: rest)) (0 :: 2 :: (rep02 a ++
                                       S))) := fun S =>
                  ((sweep_EL_f4 a (2 :: encBlks (b :: rest)) S).trans
                    (step_EL1_zero (2 :: encBlks (b :: rest)) (0 :: (rep02 a ++ S)))).trans
                    (step_CL1_add_three 0 (encBlks (b :: rest)) (1 :: (rep02 a ++ S)))
                cases h0 with
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  obtain ⟨hne, hRS⟩ := ihRS L [(.z2, 0), (.p, a)] out has0 h
                  refine ⟨hne, fun S => ((s0 S).trans (hEL (2 :: (rep02 a ++ S)))).trans ?_⟩
                  have hRS' := hRS S
                  dsimp only [encR, List.cons_append, List.nil_append] at hRS'
                  simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil] using hRS'
                | true =>
                  simp only [↓reduceIte] at h
                  obtain ⟨hne, hRS⟩ := ihRS L [(.z0, 0), (.z2, 0), (.p, a)] out has0 h
                  refine ⟨hne, fun S => ((s0 S).trans (hEL (2 :: (rep02 a ++ S)))).trans ?_⟩
                  have hRS' := hRS S
                  dsimp only [encR, List.cons_append, List.nil_append] at hRS'
                  simpa only [↓reduceIte, List.append_nil] using hRS'
    · -- `runStream (fuel + 1)`
      intro L R out has0 h
      cases L with
      | nil => cases h
      | cons a tl =>
        cases R with
        | nil =>
          cases h
          exact ⟨by simp, fun _ => ReachesStar.refl target_tm _⟩
        | cons tok rs =>
          rcases tok with ⟨tag, val⟩
          cases tag with
          | p =>
            dsimp only [runStream] at h
            obtain ⟨hne, hRS⟩ := ihRS ((a + val) :: tl) rs out has0 h
            refine ⟨hne, fun S => ?_⟩
            dsimp only [encR]
            rw [List.append_assoc]
            have s1 := sweep_BR_p02 val (encBlks (a :: tl)) (encR rs ++ S)
            rw [encBlks_add_head a val tl] at s1
            exact s1.trans (hRS S)
          | z2 =>
            dsimp only [runStream] at h
            cases heb : evalBody fuel (a :: tl) with
            | none => rw [heb] at h; cases h
            | some p =>
              rcases p with ⟨L2, h2⟩
              rw [heb] at h
              obtain ⟨hL2ne, hEL⟩ := ihEL (a :: tl) L2 h2 heb
              cases h2 with
              | false =>
                obtain ⟨hne, hRS⟩ := ihRS L2 ((.z0, 0) :: rs) out has0 h
                refine ⟨hne, fun S => ?_⟩
                dsimp only [encR, List.cons_append]
                have sc : Reach (cfg_BR1 (0 :: encBlks (a :: tl)) (2 :: (encR rs ++ S)))
                                (cfg_EL1 (0 :: encBlks (a :: tl)) (0 :: 0 :: (encR rs ++ S))) :=
                  (step_BR1_ge2 0 (0 :: encBlks (a :: tl)) (encR rs ++ S)).trans
                    (step_EL1_add_two 0 (encBlks (a :: tl)) (0 :: (encR rs ++ S)))
                exact (sc.trans (hEL (0 :: (encR rs ++ S)))).trans (hRS S)
              | true =>
                obtain ⟨hne, hRS⟩ := ihRS (0 :: L2) rs out has0 h
                refine ⟨hne, fun S => ?_⟩
                dsimp only [encR, List.cons_append]
                have sc : Reach (cfg_BR1 (0 :: encBlks (a :: tl)) (2 :: (encR rs ++ S)))
                                (cfg_EL1 (0 :: encBlks (a :: tl)) (0 :: 0 :: (encR rs ++ S))) :=
                  (step_BR1_ge2 0 (0 :: encBlks (a :: tl)) (encR rs ++ S)).trans
                    (step_EL1_add_two 0 (encBlks (a :: tl)) (0 :: (encR rs ++ S)))
                have s00 := step_BR1_00 (encBlks L2) (encR rs ++ S)
                rw [← encBlks_zero_cons hL2ne] at s00
                exact ((sc.trans (hEL (0 :: (encR rs ++ S)))).trans s00).trans (hRS S)
          | z0 =>
            cases rs with
            | nil =>
              cases h
              exact ⟨by simp, fun _ => ReachesStar.refl target_tm _⟩
            | cons tok2 rs2 =>
              rcases tok2 with ⟨tag2, val2⟩
              cases tag2 with
              | z0 =>
                dsimp only [runStream] at h
                obtain ⟨hne, hRS⟩ := ihRS (0 :: a :: tl) rs2 out has0 h
                refine ⟨hne, fun S => ?_⟩
                dsimp only [encR, List.cons_append]
                have s00 := step_BR1_00 (encBlks (a :: tl)) (encR rs2 ++ S)
                rw [← encBlks_zero_cons (by simp : a :: tl ≠ [])] at s00
                exact s00.trans (hRS S)
              | z2 =>
                dsimp only [runStream] at h
                obtain ⟨hne, hRS⟩ := ihRS ((a + 1) :: tl) rs2 out has0 h
                refine ⟨hne, fun S => ?_⟩
                dsimp only [encR, List.cons_append]
                have s1 := sweep_BR_p02_one (encBlks (a :: tl)) (encR rs2 ++ S)
                have hadd : 4 :: encBlks (a :: tl) = encBlks ((a + 1) :: tl) :=
                  encBlks_add_head a 1 tl
                rw [hadd] at s1
                exact s1.trans (hRS S)
              | p =>
                dsimp only [runStream] at h
                cases hv0 : Nat.beq val2 0 with
                | true =>
                  have hv : val2 = 0 := Nat.eq_of_beq_eq_true hv0
                  subst hv
                  simp only [hv0, ↓reduceIte] at h
                  obtain ⟨hne, hRS⟩ := ihRS (a :: tl) ((.z0, 0) :: rs2) out has0 h
                  exact ⟨hne, fun S => hRS S⟩
                | false =>
                  simp only [hv0, Bool.false_eq_true, ↓reduceIte] at h
                  have hvpos : 1 ≤ val2 := by
                    cases val2 with
                    | zero => cases hv0
                    | succ _ => omega
                  rcases (⟨val2 - 1, by omega⟩ : ∃ m, val2 = m + 1) with ⟨m, hm⟩
                  have hsubm : val2 - 1 = m := by omega
                  cases hst : subTail 2 (a :: tl) with
                  | some L2 =>
                    rw [hst, hsubm] at h
                    obtain ⟨hne, hRS⟩ := ihRS (m :: L2) rs2 out has0 h
                    refine ⟨hne, fun S => ?_⟩
                    dsimp only [encR, List.cons_append]
                    rw [hm, List.append_assoc]
                    exact (zero_p02_subTail m hst (encR rs2 ++ S)).trans (hRS S)
                  | none =>
                    rw [hst] at h
                    cases hm1 : Nat.beq val2 1 with
                    | true =>
                      have h1 : val2 = 1 := Nat.eq_of_beq_eq_true hm1
                      simp only [hm1, ↓reduceIte] at h
                      obtain ⟨hne, hRS⟩ := ihRS (0 :: a :: tl) ((.z2, 0) :: rs2) out has0 h
                      refine ⟨hne, fun S => ?_⟩
                      subst h1
                      dsimp only [encR, rep02, List.cons_append, List.nil_append]
                      have s00 := step_BR1_00 (encBlks (a :: tl)) (2 :: (encR rs2 ++ S))
                      rw [← encBlks_zero_cons (by simp : a :: tl ≠ [])] at s00
                      exact s00.trans (hRS S)
                    | false =>
                      simp only [hm1, hsubm, Bool.false_eq_true, ↓reduceIte] at h
                      obtain ⟨hne, hRS⟩ :=
                        ihRS (0 :: a :: tl) ((.z2, 0) :: (.p, m) :: rs2) out has0 h
                      refine ⟨hne, fun S => ?_⟩
                      dsimp only [encR, List.cons_append]
                      rw [hm, List.append_assoc]
                      dsimp only [rep02, List.cons_append]
                      have s00 :=
                        step_BR1_00 (encBlks (a :: tl)) (2 :: (rep02 m ++ (encR rs2 ++ S)))
                      rw [← encBlks_zero_cons (by simp : a :: tl ≠ [])] at s00
                      have hRS' := hRS S
                      dsimp only [encR, List.cons_append] at hRS'
                      rw [List.append_assoc] at hRS'
                      exact s00.trans hRS'

/-! ### Exact `scan55` & Base Hub Lemmas -/

/-- Shared turnaround on `[0, 0]` (`rep02 (k + 3)`) via `br_6_202_step` + `br_rep4_6_002_step`! -/
private theorem el_00_p02_end (k : ℕ) (S : List ℕ) :
    Reach (cfg_EL1 [0, 0] (rep02 (k + 3) ++ S)) (cfg_BR1 (0 :: encBlks [k, 8]) S) := by
  dsimp only [rep02, List.cons_append]
  have h0 : Reach (cfg_EL1 [0, 0] (0 :: 2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S)))
                  (cfg_BR1 [0, 6] (2 :: 0 :: 2 :: 0 :: 2 :: (rep02 k ++ S))) :=
    (((step_EL1_zero [0] _).trans (step_CL1_one [] _)).trans
      (step_CL1_zero [] _)).trans
      ((step_CL1_nil _).trans (step_EL1_nil_cons 6 _))
  have h1 := br_6_202_step (0 :: 2 :: (rep02 k ++ S))
  have h2 := br_rep4_6_002_step (rep02 k ++ S)
  have h3 := sweep_BR_p02 k (2 :: rep4 8) S
  exact ((h0.trans h1).trans h2).trans h3

/-- `H 1` concrete step: `p0 [0] → p03 [0]`. -/
private theorem hub_0_zero : Reach (encHub .p0 [0]) (encHub .p03 [0]) :=
  (((step_BR1_nil [0]).trans (step_CL1_zero [] [0])).trans
    (step_CL1_nil [2])).trans (step_EL1_nil_cons 3 [])

/-- `H 4` concrete step: `p055 [1] → p05 [0, 6]` (132 `step4` steps). -/
private theorem hub_055_one_single : Reach (encHub .p055 [1]) (encHub .p05 [0, 6]) := by
  have h1 := step_BR1_nil [0, 5, 5, 4]
  have h2 : Reach (cfg_CL1 [0, 5, 5, 4] [0]) (cfg_BR1 (0 :: 5 :: 2 :: rep4 6) []) :=
    run4_of_check (n := 132) (s := (.mCL, [0, 5, 5, 4], [0]))
      (s' := (.mBR, 0 :: 5 :: 2 :: rep4 6, [])) (by decide +kernel) []
  exact h1.trans h2

/-- Single-block `(0, 5, 5) [k + 2]` (`k ≥ 0`): reaches `[k, 8]` at `[0, 0, 3]`. -/
private theorem hub_055_single_ge2 (k : ℕ) :
    Reach (encHub .p055 [k + 2]) (cfg_BR1 (0 :: encBlks [k, 8]) [0, 0, 3]) := by
  have h0 : Reach (cfg_BR1 (0 :: 5 :: 5 :: rep4 (k + 2)) [])
                  (cfg_CL1 (6 :: rep4 (k + 2)) [1, 0, 3]) :=
    ((((step_BR1_nil (0 :: 5 :: 5 :: rep4 (k + 2))).trans
      (step_CL1_zero (5 :: 5 :: rep4 (k + 2)) [0])).trans
      (step_CL1_add_three 2 (5 :: rep4 (k + 2)) [2])).trans
      (step_EL1_add_two 0 (5 :: rep4 (k + 2)) [0, 3])).trans
      (step_EL1_zero (5 :: rep4 (k + 2)) [0, 0, 3])
  have h1 := cl_6_rep4_step (k + 1) 0 [] [0, 3]
  rw [List.append_nil] at h1
  exact (h0.trans h1).trans (el_00_p02_end k [0, 0, 3])

/--
`H 1385` entry rule (`b0 = 0`): `0 :: 5 :: 5 :: 2 :: L → 0 :: inc1 L` at `[0, 2, 2, 0, 0, 3]`. -/
private theorem hub_055_entry_zero (L : List ℕ) :
    Reach (cfg_BR1 (0 :: 5 :: 5 :: 2 :: L) [])
          (cfg_BR1 (0 :: inc1 L) [0, 2, 2, 0, 0, 3]) := by
  have s1 := step_BR1_nil (0 :: 5 :: 5 :: 2 :: L)
  have s2 := step_CL1_zero (5 :: 5 :: 2 :: L) [0]
  have s3 := step_CL1_add_three 2 (5 :: 2 :: L) [2]
  have s4 := step_EL1_add_two 0 (5 :: 2 :: L) [0, 3]
  have s5 := step_EL1_zero (5 :: 2 :: L) [0, 0, 3]
  have s6 := step_CL1_add_three 3 (2 :: L) [1, 0, 3]
  have s7 := step_EL1_add_two 1 (2 :: L) [0, 2, 0, 3]
  have s8 := step_EL1_one (2 :: L) [0, 0, 2, 0, 3]
  have s9 := step_EB1_zero (2 :: L) [0, 0, 2, 0, 3]
  have s10 := step_BR1_00 (3 :: L) [2, 0, 3]
  have s11 := step_BR1_ge2 0 (0 :: 2 :: 3 :: L) [0, 3]
  have s12 := step_EL1_add_two 0 (2 :: 3 :: L) [0, 0, 3]
  have s13 := step_EL1_zero (2 :: 3 :: L) [0, 0, 0, 3]
  have s14 := step_CL1_add_three 0 (3 :: L) [1, 0, 0, 3]
  have s15 := step_EL1_zero (3 :: L) [0, 2, 0, 0, 3]
  have s16 := step_CL1_add_three 1 L [1, 2, 0, 0, 3]
  have s17 := step_EL1_one L [0, 2, 2, 0, 0, 3]
  have s18 := step_EB1_zero L [0, 2, 2, 0, 0, 3]
  have c1 := (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans
    s9
  have c2 := (((((((s10.trans s11).trans s12).trans s13).trans s14).trans s15).trans s16).trans
    s17).trans s18
  exact c1.trans c2

/-- `scan55` Rule A: last block `[k + 3]`. -/
private theorem scan55_end_ge3 (k : ℕ) (R : List ℕ) :
    Reach (cfg_BR1 (0 :: 5 :: rep4 (k + 2)) (0 :: 2 :: 2 :: R))
          (cfg_BR1 (0 :: encBlks [k, 8]) (0 :: 0 :: 2 :: 0 :: R)) := by
  have h0 : Reach (cfg_BR1 (0 :: 5 :: rep4 (k + 2)) (0 :: 2 :: 2 :: R))
                  (cfg_CL1 (6 :: rep4 (k + 2)) (1 :: 0 :: 2 :: 0 :: R)) :=
    ((((sweep_BR_p02_one (5 :: rep4 (k + 2)) (2 :: R)).trans
      (step_BR1_ge2 0 (0 :: 4 :: 5 :: rep4 (k + 2)) R)).trans
      (step_EL1_add_two 0 (4 :: 5 :: rep4 (k + 2)) (0 :: R))).trans
      (sweep_EL_f4_one (5 :: rep4 (k + 2)) (0 :: R))).trans
      (step_EL1_zero (5 :: rep4 (k + 2)) (0 :: 0 :: 2 :: 0 :: R))
  have h1 := cl_6_rep4_step (k + 1) 0 [] (0 :: 2 :: 0 :: R)
  rw [List.append_nil] at h1
  exact (h0.trans h1).trans (el_00_p02_end k (0 :: 0 :: 2 :: 0 :: R))

/-- `scan55` Rule B: penultimate zero `[0, k + 3]` against `0 :: 2 :: R`. -/
private theorem scan55_zero_end_ge3 (k : ℕ) (R : List ℕ) :
    Reach (cfg_BR1 (0 :: 3 :: rep4 (k + 3)) (0 :: 2 :: 2 :: (0 :: 2 :: R)))
          (cfg_BR1 (0 :: encBlks [k, 8]) (0 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)) := by
  let L := rep4 (k + 2)
  have s1 := sweep_BR_p02_one (3 :: 4 :: L) (2 :: 0 :: 2 :: R)
  have s2 := step_BR1_ge2 0 (0 :: 4 :: 3 :: 4 :: L) (0 :: 2 :: R)
  have s3 := step_EL1_add_two 0 (4 :: 3 :: 4 :: L) (0 :: 0 :: 2 :: R)
  have s4 := sweep_EL_f4_one (3 :: 4 :: L) (0 :: 0 :: 2 :: R)
  have s5 := step_EL1_zero (3 :: 4 :: L) (0 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)
  have s6 := step_CL1_add_three 1 (4 :: L) (1 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)
  have s7 := step_EL1_one (4 :: L) (0 :: 2 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)
  have s8 := step_EB1_zero (4 :: L) (0 :: 2 :: 0 :: 2 :: 0 :: 0 :: 2 :: R)
  have s9 := sweep_BR_p02 2 (5 :: L) (0 :: 0 :: 2 :: R)
  have s10 := step_BR1_00 (4 :: 4 :: 5 :: L) (2 :: R)
  have s11 := step_BR1_ge2 0 (0 :: 2 :: 4 :: 4 :: 5 :: L) R
  have s12 := step_EL1_add_two 0 (2 :: 4 :: 4 :: 5 :: L) (0 :: R)
  have s13 := step_EL1_zero (2 :: 4 :: 4 :: 5 :: L) (0 :: 0 :: R)
  have s14 := step_CL1_add_three 0 (4 :: 4 :: 5 :: L) (1 :: 0 :: R)
  have s15 := sweep_EL_f4 2 (5 :: L) (2 :: 0 :: R)
  have s16 := step_EL1_zero (5 :: L) (0 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)
  have c1 := ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8
  have c2 := ((((((s9.trans s10).trans s11).trans s12).trans s13).trans s14).trans s15).trans s16
  have h1 := cl_6_rep4_step (k + 1) 0 [] (0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R)
  rw [List.append_nil] at h1
  exact ((c1.trans c2).trans h1).trans (el_00_p02_end k (0 :: 0 :: 2 :: 0 :: 2 :: 2 :: 0 :: R))

private def scan55 : List ℕ → List (RTag × ℕ) → Option (List ℕ × List (RTag × ℕ))
  | [b], R =>
    if Nat.ble 3 b then
      some ([b - 3, 8], (.z0, 0) :: (.p, 1) :: (.z0, 0) :: R)
    else none
  | [0, c], (.p, m) :: R =>
    if Nat.ble 3 c && Nat.ble 1 m then
      some ([c - 3, 8],
        (.z0, 0) :: (.p, 1) :: (.z0, 0) :: (.z2, 0) :: (.z2, 0) :: (.z0, 0) ::
          (if Nat.beq m 1 then R else (.p, m - 1) :: R))
    else none
  | b :: c :: bs, R =>
    if Nat.ble 2 b then
      scan55 (c :: bs) ((.p, b - 1) :: (.z0, 0) :: (.p, 1) :: (.z0, 0) :: R)
    else none
  | _, _ => none

private theorem scan55_sound : ∀ (bs : List ℕ) (R : List (RTag × ℕ)) (L' : List ℕ) (R' : List
  (RTag × ℕ)),
    scan55 bs R = some (L', R') →
    ∀ S : List ℕ,
      Reach (cfg_BR1 (0 :: inc1 (encBlks bs)) (0 :: 2 :: 2 :: (encR R ++ S)))
            (cfg_BR1 (0 :: encBlks L') (encR R' ++ S))
  | [], _, _, _, h, _ => by cases h
  | [b], R, L', R', h, S => by
    dsimp only [scan55] at h
    cases hb : Nat.ble 3 b with
    | false => rw [hb] at h; cases h
    | true =>
      have hge : 3 ≤ b := (ble_true_iff 3 b).mp hb
      rw [hb] at h; cases h
      rcases (⟨b - 3, by omega⟩ : ∃ k, b = k + 3) with ⟨k, hk⟩
      have hsub : b - 3 = k := by omega
      rw [hsub, hk]
      exact scan55_end_ge3 k (encR R ++ S)
  | b :: c :: tl, R, L', R', h, S => by
    cases b with
    | zero =>
      cases tl with
      | nil =>
        cases R with
        | nil => simp only [scan55] at h; cases h
        | cons r0 rt =>
          rcases r0 with ⟨tag0, m⟩
          cases tag0 with
          | z0 => simp only [scan55] at h; cases h
          | z2 => simp only [scan55] at h; cases h
          | p =>
            simp only [scan55] at h
            cases hcond : (Nat.ble 3 c && Nat.ble 1 m) with
            | false => rw [hcond] at h; cases h
            | true =>
              rw [hcond] at h
              simp only [↓reduceIte] at h
              rw [Bool.and_eq_true] at hcond
              have hc : 3 ≤ c := (ble_true_iff 3 c).mp hcond.1
              have hm : 1 ≤ m := (ble_true_iff 1 m).mp hcond.2
              cases h
              rcases (⟨c - 3, by omega⟩ : ∃ k, c = k + 3) with ⟨k, hk⟩
              rcases (⟨m - 1, by omega⟩ : ∃ m', m = m' + 1) with ⟨m', hm'⟩
              have hsubc : c - 3 = k := by omega
              rw [hsubc, hk, hm']
              dsimp only [encR, encBlks, inc1, rep02, List.cons_append]
              rw [List.append_assoc]
              cases hm1 : Nat.beq (m' + 1) 1 with
              | true =>
                have hzero : m' = 0 := by
                  have := Nat.eq_of_beq_eq_true hm1; omega
                subst hzero
                simp only [↓reduceIte]
                dsimp only [rep02, List.nil_append]
                exact scan55_zero_end_ge3 k (encR rt ++ S)
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [show (m' + 1) - 1 = m' by omega]
                simp only [encR, rep4, List.nil_append, List.cons_append, List.append_assoc]
                exact scan55_zero_end_ge3 k (rep02 m' ++ (encR rt ++ S))
      | cons d rest =>
        simp only [scan55] at h
        cases h
    | succ b1 =>
      simp only [scan55] at h
      cases hb2 : Nat.ble 2 (b1 + 1) with
      | false => rw [hb2] at h; cases h
      | true =>
        have hge : 2 ≤ b1 + 1 := (ble_true_iff 2 (b1 + 1)).mp hb2
        simp only [hb2, ↓reduceIte] at h
        rcases (⟨b1 - 1, by omega⟩ : ∃ k, b1 + 1 = k + 2) with ⟨k, hk⟩
        have hsub : b1 + 1 - 1 = k + 1 := by omega
        rw [hsub] at h
        have ih := scan55_sound (c :: tl) ((.p, k + 1) :: (.z0, 0) :: (.p, 1) :: (.z0, 0) :: R) L'
          R' h S
        dsimp only [encR, rep02, List.cons_append, List.nil_append] at ih
        rw [List.append_assoc] at ih
        have hstep : Reach (cfg_BR1 (0 :: inc1 (encBlks ((b1 + 1) :: c :: tl))) (0 :: 2 :: 2 ::
          (encR R ++ S)))
                           (cfg_BR1 (0 :: inc1 (encBlks (c :: tl)))
                             (0 :: 2 :: 2 :: (rep02 (k + 1) ++ (0 :: 0 :: 2 :: 0 :: (encR R ++
                               S))))) := by
          rw [hk]
          dsimp only [encBlks, rep4, inc1, List.cons_append]
          exact scan_55_ge2 k (encBlks (c :: tl)) (encR R ++ S)
        exact hstep.trans ih

/-! ### Top-Level Hub Stepper `stepHub`, `runHubs`, & Checkers -/

private def finishD3 (fuel : ℕ) (L : List ℕ) (has0 : Bool) : Option (Pfx × List ℕ) :=
  if has0 then some (.p05, L)
  else
    match evalBody fuel L with
    | none => none
    | some (L1, true) => some (.p03, L1)
    | some (L1, false) =>
      match evalBody fuel L1 with
      | none => none
      | some (_, true) => none
      | some (L2, false) => some (.p0, L2)

private theorem finishD3_sound {fuel : ℕ} {L : List ℕ} {has0 : Bool} {p' : Pfx} {bs' : List ℕ}
    (h : finishD3 fuel L has0 = some (p', bs')) :
    Reach (cfg_BR1 (0 :: encBlks L) (if has0 then [0, 3] else [3])) (encHub p' bs') := by
  dsimp only [finishD3] at h
  cases has0 with
  | true =>
    simp only [↓reduceIte] at h
    cases h
    exact step_BR1_0d 3 (encBlks L) []
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases heb1 : evalBody fuel L with
    | none => rw [heb1] at h; cases h
    | some r1 =>
      rcases r1 with ⟨L1, h1⟩
      rw [heb1] at h
      have hEL1 := (eval_run_sound fuel).1 L L1 h1 heb1
      cases h1 with
      | true =>
        have hres := ((br_d3_to_el (encBlks L)).trans (hEL1.2 [1])).trans (step_BR1_0d 1 (encBlks
          L1) [])
        cases h
        exact hres
      | false =>
        dsimp only at h
        cases heb2 : evalBody fuel L1 with
        | none => rw [heb2] at h; cases h
        | some r2 =>
          rcases r2 with ⟨L2, h2⟩
          rw [heb2] at h
          have hEL2 := (eval_run_sound fuel).1 L1 L2 h2 heb2
          cases h2 with
          | true => cases h
          | false =>
            have hres := (((br_d3_to_el (encBlks L)).trans (hEL1.2 [1])).trans
              (br_d1_to_el (encBlks L1))).trans (hEL2.2 [])
            cases h
            exact hres

private def stepHub (fuel : ℕ) : Pfx × List ℕ → Option (Pfx × List ℕ)
  | (.p0, [0]) => some (.p03, [0])
  | (.p0, a :: tl) =>
    if Nat.ble 2 a then some (.p055, (a - 2) :: tl) else none
  | (.p03, bs) =>
    match subTail 3 bs with
    | some out => some (.p0, out)
    | none =>
      match evalBody fuel bs with
      | none => none
      | some (L1, h1) => finishD3 fuel L1 h1
  | (.p05, bs) =>
    match subTail 1 bs with
    | some out => some (.p05, out)
    | none =>
      match evalBody fuel bs with
      | none => none
      | some (L1, true) => finishD3 fuel (0 :: L1) false
      | some (L1, false) => finishD3 fuel L1 true
  | (.p055, [1]) => some (.p05, [0, 6])
  | (.p055, [a]) =>
    if Nat.ble 2 a then
      match runStream fuel [a - 2, 8] [(.z0, 0), (.z0, 0)] with
      | none => none
      | some (Lout, hout) => finishD3 fuel Lout hout
    else none
  | (.p055, 0 :: c :: tl) =>
    match scan55 (c :: tl) [(.z0, 0), (.z0, 0)] with
    | none => none
    | some (Le, Re) =>
      match runStream fuel Le Re with
      | none => none
      | some (Lout, hout) => finishD3 fuel Lout hout
  | (.p055, a :: c :: tl) =>
    match scan55 (c :: tl) [(.p, a), (.z0, 0), (.z0, 0)] with
    | none => none
    | some (Le, Re) =>
      match runStream fuel Le Re with
      | none => none
      | some (Lout, hout) => finishD3 fuel Lout hout
  | _ => none

private theorem stepHub_sound {fuel : ℕ} {s s' : Pfx × List ℕ}
    (h : stepHub fuel s = some s') :
    Reach (encHub s.1 s.2) (encHub s'.1 s'.2) := by
  rcases s with ⟨p, bs⟩
  rcases s' with ⟨p', bs'⟩
  cases p with
  | p0 =>
    cases bs with
    | nil => cases h
    | cons a tl =>
      cases a with
      | zero =>
        cases tl with
        | nil => cases h; exact hub_0_zero
        | cons _ _ => simp only [stepHub] at h; cases h
      | succ a1 =>
        simp only [stepHub] at h
        cases ha : Nat.ble 2 (a1 + 1) with
        | false => rw [ha] at h; cases h
        | true =>
          have hge : 2 ≤ a1 + 1 := (ble_true_iff 2 (a1 + 1)).mp ha
          simp only [ha, ↓reduceIte] at h
          cases h
          have heq : a1 + 1 = (a1 + 1 - 2) + 2 := by omega
          cases tl with
          | nil =>
            dsimp only [encHub, encPfx, encBlks, List.cons_append, List.nil_append]
            have hs := hub_0_step (a1 + 1 - 2) []
            rw [List.append_nil, List.append_nil, ← heq] at hs
            exact hs
          | cons b rest =>
            dsimp only [encHub, encPfx, encBlks, List.cons_append, List.nil_append]
            have hs := hub_0_step (a1 + 1 - 2) (2 :: encBlks (b :: rest))
            rw [← heq] at hs
            exact hs
  | p03 =>
    simp only [stepHub] at h
    cases hst : subTail 3 bs with
    | some out =>
      rw [hst] at h; cases h
      exact hub_03_subTail hst
    | none =>
      rw [hst] at h
      dsimp only at h
      cases heb : evalBody fuel bs with
      | none => rw [heb] at h; cases h
      | some r =>
        rcases r with ⟨L1, h1⟩
        rw [heb] at h
        dsimp only at h
        have hEL := (eval_run_sound fuel).1 bs L1 h1 heb
        exact ((hub_03_entry (encBlks bs)).trans (hEL.2 [3])).trans (finishD3_sound h)
  | p05 =>
    simp only [stepHub] at h
    cases hst : subTail 1 bs with
    | some out =>
      rw [hst] at h; cases h
      exact hub_05_subTail_one hst
    | none =>
      rw [hst] at h
      dsimp only at h
      cases heb : evalBody fuel bs with
      | none => rw [heb] at h; cases h
      | some r =>
        rcases r with ⟨L1, h1⟩
        rw [heb] at h
        have hEL := (eval_run_sound fuel).1 bs L1 h1 heb
        cases h1 with
        | true =>
          have s00 := step_BR1_00 (encBlks L1) [3]
          rw [← encBlks_zero_cons hEL.1] at s00
          exact (((hub_05_entry (encBlks bs)).trans (hEL.2 [0, 3])).trans s00).trans
            (finishD3_sound h)
        | false =>
          exact ((hub_05_entry (encBlks bs)).trans (hEL.2 [0, 3])).trans (finishD3_sound h)
  | p055 =>
    cases bs with
    | nil => cases h
    | cons a tl =>
      cases tl with
      | nil =>
        cases a with
        | zero => simp only [stepHub] at h; cases h
        | succ a1 =>
          cases a1 with
          | zero =>
            cases h; exact hub_055_one_single
          | succ k =>
            simp only [stepHub] at h
            cases hble : Nat.ble 2 (k + 2) with
            | false =>
              have : 2 ≤ k + 2 := by omega
              exact absurd ((ble_true_iff 2 (k + 2)).mpr this) (by rw [hble]; decide)
            | true =>
              simp only [hble, ↓reduceIte, show k + 2 - 2 = k by omega] at h
              cases hrs : runStream fuel [k, 8] [(.z0, 0), (.z0, 0)] with
              | none => rw [hrs] at h; cases h
              | some r =>
                rcases r with ⟨Lout, hout⟩
                rw [hrs] at h
                dsimp only at h
                have hRS := (eval_run_sound fuel).2 [k, 8] [(.z0, 0), (.z0, 0)] Lout hout hrs
                exact ((hub_055_single_ge2 k).trans (hRS.2 [3])).trans (finishD3_sound h)
      | cons c rest =>
        cases a with
        | zero =>
          simp only [stepHub] at h
          cases hsc : scan55 (c :: rest) [(.z0, 0), (.z0, 0)] with
          | none => rw [hsc] at h; cases h
          | some p1 =>
            rcases p1 with ⟨Le, Re⟩
            rw [hsc] at h
            dsimp only at h
            cases hrs : runStream fuel Le Re with
            | none => rw [hrs] at h; cases h
            | some p2 =>
              rcases p2 with ⟨Lout, hout⟩
              rw [hrs] at h
              dsimp only at h
              have s0 := hub_055_entry_zero (encBlks (c :: rest))
              have s1 := scan55_sound (c :: rest) [(.z0, 0), (.z0, 0)] Le Re hsc [3]
              have s2 := (eval_run_sound fuel).2 Le Re Lout hout hrs
              exact ((s0.trans s1).trans (s2.2 [3])).trans (finishD3_sound h)
        | succ k0 =>
          simp only [stepHub] at h
          cases hsc : scan55 (c :: rest) [(.p, k0 + 1), (.z0, 0), (.z0, 0)] with
          | none => rw [hsc] at h; cases h
          | some p1 =>
            rcases p1 with ⟨Le, Re⟩
            rw [hsc] at h
            dsimp only at h
            cases hrs : runStream fuel Le Re with
            | none => rw [hrs] at h; cases h
            | some p2 =>
              rcases p2 with ⟨Lout, hout⟩
              rw [hrs] at h
              dsimp only at h
              have s0 := hub_055_entry k0 (encBlks (c :: rest))
              have s1 := scan55_sound (c :: rest) [(.p, k0 + 1), (.z0, 0), (.z0, 0)] Le Re hsc [3]
              dsimp only [encR, List.cons_append, List.nil_append] at s1
              rw [List.append_assoc] at s1
              have s2 := (eval_run_sound fuel).2 Le Re Lout hout hrs
              exact ((s0.trans s1).trans (s2.2 [3])).trans (finishD3_sound h)

private noncomputable def runHubs : ℕ → Pfx × List ℕ → Option (Pfx × List ℕ)
  | 0, s => some s
  | n + 1, s =>
    match stepHub 200 s with
    | none => none
    | some s₁ => forceListCPS s₁.2 (fun bs' => runHubs n (s₁.1, bs'))

private theorem runHubs_sound :
    ∀ (n : ℕ) {s s' : Pfx × List ℕ},
      runHubs n s = some s' → Reach (encHub s.1 s.2) (encHub s'.1 s'.2)
  | 0, _, _, h => by cases h; exact ReachesStar.refl target_tm _
  | n + 1, s, s', h => by
    dsimp only [runHubs] at h
    cases hs : stepHub 200 s with
    | none => rw [hs] at h; cases h
    | some s₁ =>
      rw [hs] at h
      dsimp only at h
      rw [forceListCPS_eq] at h
      exact (stepHub_sound hs).trans (runHubs_sound n h)

private noncomputable def checkHubs (n : ℕ) (s s' : Pfx × List ℕ) : Bool :=
  match runHubs n s with
  | none => false
  | some s₁ => pfxEq s₁.1 s'.1 && natListEq s₁.2 s'.2

private theorem runHubs_of_check {n : ℕ} {s s' : Pfx × List ℕ}
    (h : checkHubs n s s' = true) :
    Reach (encHub s.1 s.2) (encHub s'.1 s'.2) := by
  unfold checkHubs at h
  cases hr : runHubs n s with
  | none => rw [hr] at h; cases h
  | some s₁ =>
    rw [hr] at h
    dsimp only at h
    rw [Bool.and_eq_true] at h
    have heq : s₁ = s' := by
      rcases s₁ with ⟨p1, b1⟩
      rcases s' with ⟨p2, b2⟩
      dsimp only at h
      rw [pfxEq_eq h.1, natListEq_eq h.2]
    subst heq
    exact runHubs_sound n hr

private noncomputable def checkBatch05 (m : ℕ) (bs bs' : List ℕ) : Bool :=
  match subTail m bs with
  | none => false
  | some out => natListEq out bs'

private theorem batch05_of_check {m : ℕ} {bs bs' : List ℕ}
    (h : checkBatch05 m bs bs' = true) :
    Reach (encHub .p05 bs) (encHub .p05 bs') := by
  unfold checkBatch05 at h
  cases hs : subTail m bs with
  | none => rw [hs] at h; cases h
  | some out =>
    rw [hs] at h
    have heq : out = bs' := natListEq_eq h
    subst heq
    exact hub_05_batch m bs out hs

/-! ### Exact Stage 1 Checkpoints (`H 1 → H 1,387 → H 11,117 → H 11,120`) -/

private noncomputable def st_H1 : Pfx × List ℕ := (.p0, [0])

private noncomputable def st_H200 : Pfx × List ℕ :=
  (.p055, [3555, 20796, 116780, 16748, 59732, 455264, 66792, 0, 458752])

private noncomputable def st_H400 : Pfx × List ℕ :=
  (.p0, [2954, 18920, 109276, 203068, 935376, 7280564, 32712196, 18842664, 25512808, 156638096,
    329758992, 29366492])

private noncomputable def st_H600 : Pfx × List ℕ :=
  (.p03, [2354, 17056, 101820, 173244, 816080, 6803380, 30803460, 65794584, 294236116, 2129785012,
    10180616692, 81012974392, 885699664, 201326592, 1073741824])

private noncomputable def st_H800 : Pfx × List ℕ :=
  (.p055, [1755, 15196, 94380, 143484, 697040, 6327220, 28898820, 58176024, 263761876, 2007888052,
    9693028852, 79062623032, 6735857064, 40093496512, 192694888224, 808988028388, 30386963036])

private noncomputable def st_H1000 : Pfx × List ℕ :=
  (.p0, [1154, 13320, 86876, 113468, 576976, 5846964, 26977796, 50491928, 233025492, 1884942516,
    9201246708, 90245562712, 83788517956, 593260430180, 2979993386148, 16174894751472,
    34298981500032, 80308496796, 29503024616824, 1924145444072])

private noncomputable def st_H1200 : Pfx × List ℕ :=
  (.p03, [554, 11456, 79420, 83644, 457680, 5369780, 25069060, 42856984, 202485716, 1762783412,
    8712610292, 88291017048, 75970335300, 561987699556, 2854902463652, 15674531061488,
    79774990672048, 13540101488692, 62535257873232, 232638500134196, 4402879390568])

private noncomputable def blks_H1387 : List ℕ :=
  [9730, 72516, 56028, 347216, 4927924, 23301636, 35787288, 174206932, 1649668276, 8260149748,
    86481174872, 68730966596, 533030224740, 2739072564388, 15211211464432, 77921712283824,
    6126987935796, 32882803661648, 201728764217476, 1006885783787796, 5186334372888352,
    3666344708518256, 387028092977576, 422212465065984]

private noncomputable def blks_H1409 : List ℕ :=
  [9708, 72428, 55676, 345808, 4922292, 23279108, 35697176, 173846484, 1648226484, 8254382580,
    86458106200, 68638691908, 532661125988, 2737596169380, 15205305884400, 77898089963696,
    6032498655284, 32504846539600, 200216935729284, 1000838469835028, 5162145117077280,
    3569587685273968, 424, 1970324836974592]

private noncomputable def blks_H1410 : List ℕ :=
  [9707, 72424, 55660, 345744, 4922036, 23278084, 35693080, 173830100, 1648160948, 8254120436,
    86457057624, 68634497604, 532644348772, 2737529060516, 15205037448944, 77897016221872,
    6028203687988, 32487666670416, 200148216252548, 1000563591928084, 5161045605449504,
    5544310568761150]

private noncomputable def blks_H2813 : List ℕ :=
  [8304, 66812, 33212, 255952, 4562868, 21841412, 29946392, 150843348, 1556213940, 7886332404,
    84985905496, 62749889092, 509105914724, 2643375324324, 14828422504176, 76390556442800,
    2364571700, 8384310205264, 103734790391940, 614909888485652, 3618430791679776,
    11714769823840062]

private noncomputable def blks_H2814 : List ℕ :=
  [8303, 66808, 33196, 255888, 4562612, 21840388, 29942296, 150826964, 1556148404, 7886070260,
    84984856920, 62745694788, 509089137508, 2643308215460, 14828154068720, 84764334619440,
    103695026849140, 614750834314452, 3617794574994976, 11717314690579262]

private noncomputable def blks_H4888 : List ℕ :=
  [6229, 58512, 12, 123152, 4031668, 19716612, 21447192, 116846548, 1420226740, 7342383604,
    82810110296, 54046708292, 474293191524, 2504124431524, 14271418932976, 82537394076464,
    94787264677236, 579119785626836, 3475270380244512, 12287411469581118]

private noncomputable def blks_H4889 : List ℕ :=
  [6228, 181612, 4031468, 19715812, 21443992, 116833748, 1420175540, 7342178804, 82809291096,
    54043431492, 474280084324, 2504072002724, 14271209217776, 82536555215664, 94783909234036,
    579106363854036, 3475216693153312, 12287626217945918]

private noncomputable def blks_H11117 : List ℕ :=
  [0, 156700, 3931820, 19317220, 19849624, 110456276, 1394665652, 7240139252, 82401132888,
    52410798660, 467749552996, 2477949877412, 14166720716528, 82118601210672, 93112093214068,
    572419099774164, 3448467636833824, 12394622443223870]

private noncomputable def tail13_H11120 : List ℕ :=
  [110454484, 1394658484, 7240110580, 82401018200, 52410339908, 467747717988, 2477942537380,
    14166691356400, 82118483770160, 93111623452020, 572417220725972, 3448460120641056,
    12394652507994942]

private noncomputable def st_H11120 : Pfx × List ℕ :=
  (.p055, 156691 :: 3931792 :: 19317108 :: 19849176 :: tail13_H11120)

private theorem reach_H1_H200 : Reach (encHub st_H1.1 st_H1.2) (encHub st_H200.1 st_H200.2) :=
  runHubs_of_check (n := 199) (by decide +kernel)

private theorem reach_H200_H400 : Reach (encHub st_H200.1 st_H200.2) (encHub st_H400.1 st_H400.2) :=
  runHubs_of_check (n := 200) (by decide +kernel)

private theorem reach_H400_H600 : Reach (encHub st_H400.1 st_H400.2) (encHub st_H600.1 st_H600.2) :=
  runHubs_of_check (n := 200) (by decide +kernel)

private theorem reach_H600_H800 : Reach (encHub st_H600.1 st_H600.2) (encHub st_H800.1 st_H800.2) :=
  runHubs_of_check (n := 200) (by decide +kernel)

private theorem reach_H800_H1000 : Reach (encHub st_H800.1 st_H800.2) (encHub st_H1000.1
  st_H1000.2) :=
  runHubs_of_check (n := 200) (by decide +kernel)

private theorem reach_H1000_H1200 : Reach (encHub st_H1000.1 st_H1000.2) (encHub st_H1200.1
  st_H1200.2) :=
  runHubs_of_check (n := 200) (by decide +kernel)

private theorem reach_H1200_H1387 : Reach (encHub st_H1200.1 st_H1200.2) (encHub .p05 blks_H1387) :=
  runHubs_of_check (n := 187) (s := st_H1200) (s' := (.p05, blks_H1387)) (by decide +kernel)

private theorem reach_H1387_H1409 : Reach (encHub .p05 blks_H1387) (encHub .p05 blks_H1409) :=
  batch05_of_check (m := 22) (by decide +kernel)

private theorem reach_H1409_H1410 : Reach (encHub .p05 blks_H1409) (encHub .p05 blks_H1410) :=
  runHubs_of_check (n := 1) (s := (.p05, blks_H1409)) (s' := (.p05, blks_H1410)) (by decide +kernel)

private theorem reach_H1410_H2813 : Reach (encHub .p05 blks_H1410) (encHub .p05 blks_H2813) :=
  batch05_of_check (m := 1403) (by decide +kernel)

private theorem reach_H2813_H2814 : Reach (encHub .p05 blks_H2813) (encHub .p05 blks_H2814) :=
  runHubs_of_check (n := 1) (s := (.p05, blks_H2813)) (s' := (.p05, blks_H2814)) (by decide +kernel)

private theorem reach_H2814_H4888 : Reach (encHub .p05 blks_H2814) (encHub .p05 blks_H4888) :=
  batch05_of_check (m := 2074) (by decide +kernel)

private theorem reach_H4888_H4889 : Reach (encHub .p05 blks_H4888) (encHub .p05 blks_H4889) :=
  runHubs_of_check (n := 1) (s := (.p05, blks_H4888)) (s' := (.p05, blks_H4889)) (by decide +kernel)

private theorem reach_H4889_H11117 : Reach (encHub .p05 blks_H4889) (encHub .p05 blks_H11117) :=
  batch05_of_check (m := 6228) (by decide +kernel)

private theorem reach_H11117_H11120 : Reach (encHub .p05 blks_H11117) (encHub st_H11120.1
  st_H11120.2) :=
  runHubs_of_check (n := 3) (s := (.p05, blks_H11117)) (s' := st_H11120) (by decide +kernel)

private theorem encHub_p055_3 (a b c : ℕ) (d : ℕ) (rest : List ℕ) :
    encHub .p055 (a :: b :: c :: d :: rest) =
      cfg_BR1 (0 :: 5 :: 5 :: (rep4 a ++ 2 :: (rep4 b ++ 2 :: (rep4 c ++ (2 :: encBlks (d ::
        rest)))))) [] := rfl

private theorem W_cons_two (L : List ℕ) : W (2 :: L) = 1 + W L := rfl

private theorem is_halt_proof : HaltsFrom target_tm (init []) := by
  have h_stage1 : Reach (init []) (encHub st_H11120.1 st_H11120.2) :=
    ((((((((((((((entry_step.trans reach_H1_H200).trans
      reach_H200_H400).trans
      reach_H400_H600).trans
      reach_H600_H800).trans
      reach_H800_H1000).trans
      reach_H1000_H1200).trans
      reach_H1200_H1387).trans
      reach_H1387_H1409).trans
      reach_H1409_H1410).trans
      reach_H1410_H2813).trans
      reach_H2813_H2814).trans
      reach_H2814_H4888).trans
      reach_H4888_H4889).trans
      reach_H4889_H11117).trans
      reach_H11117_H11120
  have hW : W (2 :: encBlks (19849176 :: tail13_H11120)) ≤ 14 := by
    rw [W_cons_two, W_encBlks_cons]
    decide
  have hsp : st_H11120.1 = .p055 := rfl
  have hsb : st_H11120.2 = 156691 :: 3931792 :: 19317108 :: 19849176 :: tail13_H11120 := rfl
  have h_halt : HaltsFrom target_tm (encHub st_H11120.1 st_H11120.2) := by
    rw [hsp, hsb, encHub_p055_3]
    exact halts_from_H11120 (2 :: encBlks (19849176 :: tail13_H11120)) hW
  exact HaltsFrom.of_reachesStar h_stage1 h_halt

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA` halts from the blank tape. -/
theorem is_halt : IsHalt target := by
  rw [← target_tm_eq_target]
  exact Solution.is_halt_proof

end

end BusyBeaver.M_1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_HHH0RA
