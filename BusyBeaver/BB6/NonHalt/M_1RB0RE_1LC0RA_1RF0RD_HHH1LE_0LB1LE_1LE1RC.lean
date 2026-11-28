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
import BusyBeaver.Calculi.ProofKit


/-!
# Busy Beaver Machine `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.ProofKit`
and defines `target_tm` for `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 2, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open scoped BusyBeaver.ProofKit
local macro "step" : tactic => `(tactic| gstep)

def A : Fin 6 := 0

def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

def holdout_0082_mod : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)
set_option maxRecDepth 2000
@[simp] theorem zDh : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] theorem zDt : (default : ListBlank (Fin 2)).tail = default := rfl
theorem append_zero_pow_01 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ k = (s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0] := by
  induction k with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPl (s <+ [0]) [0, 1] k 1, ih]
    have h1 : ((s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ 1 =
        ((s <+ ([1, 0] : List (Fin 2)) ^ k) <+ ([1, 0] : List (Fin 2)) ^ 1) <+ [0] := rfl
    rw [h1, <- zPl s [1, 0] k 1]
theorem default_pow_01 (c : Nat) :
    (default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ c =
    (default <+ ([1, 0] : List (Fin 2)) ^ c) <+ [0] := by
  have h0 : (default : ListBlank (Fin 2)) = default <+ [0] := zZcd.symm
  conv_lhs => rw [h0]
  exact append_zero_pow_01 default c
theorem append_one_pow_10 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [1]) <+ ([1, 0] : List (Fin 2)) ^ k = (s <+ ([0, 1] : List (Fin 2)) ^ k) <+ [1] := by
  induction k with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPl (s <+ [1]) [1, 0] k 1, ih]
    have h1 : ((s <+ ([0, 1] : List (Fin 2)) ^ k) <+ [1]) <+ ([1, 0] : List (Fin 2)) ^ 1 =
        ((s <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2)) ^ 1) <+ [1] := rfl
    rw [h1, <- zPl s [0, 1] k 1]
theorem pow_11_eq_pow_1_mul2 (k : Nat) :
    ([1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [zPsl, ih, h2, zLpa]
    rfl
theorem pow_01_append_0 (k : Nat) (r : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ([0] +> r) =
    [0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r) := by
  induction k generalizing r with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPsr, ih]
    have h1 : ([0, 1] : List (Fin 2)) +> ([0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r)) =
        [0] +> (([1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ k) +> r)) := rfl
    rw [h1, <- zPsr]
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
theorem shift_E_ones_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1] : List (Fin 2)) ^ k +> r)) [holdout_0082_mod]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : (l {{E}}> ([1] +> (([1] : List (Fin 2)) ^ k +> r)))
        [holdout_0082_mod]⊢*
        ((l <+ [1]) {{E}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih (l <+ [1]) r
    rw [zPal] at h2
    exact zSt h1 h2
theorem shift_CB_left_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [holdout_0082_mod]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([0, 1] : List (Fin 2)) ^ k) <+ [0, 1]) {{C}}> ([1] +> r))
        [holdout_0082_mod]⊢*
        ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [zPa1] at h2
    exact zSt h1 h2
theorem shift_D_right_100_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) [holdout_0082_mod]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : (l {{D}}> ([1, 0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
        [holdout_0082_mod]⊢*
        ((l <+ [0, 1]) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih (l <+ [0, 1]) r
    rw [zPal] at h2
    exact zSt h1 h2
theorem shift_FA_left_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> r)) [holdout_0082_mod]⊢*
    (l {{F}}> ([0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{F}}> ([0] +> r))
        [holdout_0082_mod]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> ([0, 1] +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih l (([0, 1] : List (Fin 2)) +> r)
    rw [zPa1] at h2
    exact zSt h1 h2
def E_0082 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ a)
    {{E}}> default
def F_R (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
    {{F}}>
    ([0, 0] +> r)
def F_0082 (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
    {{F}}>
    ([0, 0] +> (([1] : List (Fin 2)) ^ c +> default))
theorem F_0082_eq_F_R (b k c : Nat) :
    F_0082 b k c = F_R b k (([1] : List (Fin 2)) ^ c +> default) := rfl

theorem step_E_b3_to_F_0082 (a b : Nat) :
    (E_0082 a (b + 3)) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 (2 * a + 3)) := by
  unfold E_0082 F_0082
  simp only [zPz, zLan]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List
    (Fin 2)) ^ a) {{E}}> default)
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List (Fin
        2)) ^ a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) a]
    at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
    3)) <+ [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2] at h1 h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
    (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [holdout_0082_mod]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) {{F}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
          (Fin 2)) ^ 1 +> default))))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default,
    <- zPar ([1] : List (Fin 2)) 2 (2 * a + 1) default] at h3
  have ha : 2 + (2 * a + 1) = 2 * a + 3 := by omega
  rw [ha] at h3
  exact zPt (zPsp h1 h2) h3
theorem step_F_b2_k0_0082 (c : Nat) :
    (F_0082 2 0 (c + 1)) [holdout_0082_mod]⊢⁺ (F_0082 5 0 c) := by
  unfold F_0082
  rw [zPsr ([1] : List (Fin 2)) c default]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append]
  execute

def D100 (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k) <+
    [0]) {{D}}>
    ([1, 0, 0] +> r)
def C_bounce (b : Nat) (s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) {{C}}> ([1] +> s)
theorem step_F0_sweep_right_0082 (k : Nat) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
    [holdout_0082_mod]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  have h1 : ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
      [holdout_0082_mod]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    dsimp [ListBlank.append]
    execute
  have h2 := shift_D_right_100_0082 k default r
  exact zPsp h1 h2
theorem F_R_b0_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 0 k r) [holdout_0082_mod]⊢⁺ (D100 0 k r) := by
  unfold F_R D100
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k default ([0] +> r)
  rw [pow_01_append_0 k r] at h1
  have h2 := step_F0_sweep_right_0082 k r
  rw [default_pow_01 k] at h2
  exact zSpp h1 h2
theorem F_R_b1_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 1 k r) [holdout_0082_mod]⊢⁺ (D100 0 (k + 1) r) := by
  unfold F_R D100
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) ([0]
    +> r)
  rw [pow_01_append_0 k r] at h1
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [holdout_0082_mod]⊢⁺
      ((default : ListBlank (Fin 2)) {{F}}>
        ([0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  rw [<- zPsr ([1, 0] : List (Fin 2)) k r] at h2
  have h3 := step_F0_sweep_right_0082 (k + 1) r
  rw [default_pow_01 (k + 1)] at h3
  exact zPt (zSpp h1 h2) h3
theorem F_R_b3_to_D100 (b k : Nat) (r : ListBlank (Fin 2)) :
    (F_R (b + 3) k r) [holdout_0082_mod]⊢⁺ (D100 (b + 1) k r) := by
  unfold F_R D100
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
    3)) ([0] +> r)
  rw [pow_01_append_0 k r] at h1
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2] at h1
  have h2 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
    (Fin 2)) ^ 2) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [holdout_0082_mod]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) {{D}}>
        ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  have h3 := shift_D_right_100_0082 k
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) r
  rw [append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) k] at h3
  exact zPsp (zSpp h1 h2) h3
theorem D100_0_11 (k : Nat) (r : ListBlank (Fin 2)) :
    (D100 0 k ([1, 1] +> r)) [holdout_0082_mod]⊢⁺ (F_R 1 (k + 1) r) := by
  unfold D100 F_R
  simp only [zPz, zLan]
  rw [<- default_pow_01 k]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2))
        ^ 1) <+ [1]) {{F}}>
        ([0, 0] +> r)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  rw [<- zPl default ([0, 1] : List (Fin 2)) k 1,
    <- append_one_pow_10 default (k + 1)] at h1
  exact h1
theorem D100_succ_11 (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 (b + 1) k ([1, 1] +> r)) [holdout_0082_mod]⊢⁺ (F_R (b + 1) (k + 2) r) := by
  unfold D100 F_R
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List
    (Fin 2)) ^ k) <+ [0]) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List (Fin
        2)) ^ k) <+
        ([1, 0] : List (Fin 2)) ^ 2) {{F}}>
        ([0, 0] +> r)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  rw [<- zPl ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) ([1, 0] : List (Fin
    2)) k 2] at h1
  exact h1
theorem D100_nil_to_C_bounce (b k : Nat) :
    (D100 b k default) [holdout_0082_mod]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 3) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
    List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> default))
      [holdout_0082_mod]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
        (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0, 1] : List
    (Fin 2)) k 1] at h1
  have h2 := shift_CB_left_0082 (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
    b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pow_11_eq_pow_1_mul2 (k + 1),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 1)) 1 default] at h2
  have hk : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
theorem D100_one_to_C_bounce (b k : Nat) :
    (D100 b k ([1] +> default)) [holdout_0082_mod]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 5) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
    List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1] +> default)))
      [holdout_0082_mod]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
        (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 2) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0, 1] : List
    (Fin 2)) k 2] at h1
  have h2 := shift_CB_left_0082 (k + 2) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
    b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pow_11_eq_pow_1_mul2 (k + 2),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 2)) 1 default] at h2
  have hk : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
theorem D100_01_to_C_bounce (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 b k ([0, 1] +> r)) [holdout_0082_mod]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 4) +> r)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
    List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([0, 1] +> r)))
      [holdout_0082_mod]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
        (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 2 +> r))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0, 1] : List
    (Fin 2)) k 1] at h1
  have h2 := shift_CB_left_0082 (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
    b) <+ [0])
    (([1] : List (Fin 2)) ^ 2 +> r)
  rw [pow_11_eq_pow_1_mul2 (k + 1),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 1)) 2 r] at h2
  have hk : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
theorem C_bounce_0 (s : ListBlank (Fin 2)) :
    (C_bounce 0 s) [holdout_0082_mod]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}> s) := by
  unfold C_bounce
  simp only [zPz, zLan]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append]
  execute
theorem C_bounce_1 (s : ListBlank (Fin 2)) :
    (C_bounce 1 s) [holdout_0082_mod]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}> s) := by
  unfold C_bounce
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append]
  execute

theorem C_bounce_3 (b : Nat) (s : ListBlank (Fin 2)) :
    (C_bounce (b + 3) s) [holdout_0082_mod]⊢⁺
    (F_R (b + 1) 0 (([1] : List (Fin 2)) ^ 2 +> s)) := by
  unfold C_bounce F_R
  simp only [zPz, zLan]
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append]
  execute
theorem step_F_ksucc_c0 (b k : Nat) :
    (F_0082 b (k + 1) 0) [holdout_0082_mod]⊢⁺ (F_0082 b k 1) := by
  unfold F_0082
  rw [zPl ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) ([1, 0] : List (Fin 2)) k 1]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append]
  execute
theorem step_F_b2_k0_c0 :
    (F_0082 2 0 0) [holdout_0082_mod]⊢⁺ (F_0082 3 0 3) := by
  unfold F_0082
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append]
  execute
theorem C_bounce_0_ones (n : Nat) :
    (C_bounce 0 (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺
    (F_0082 (n + 1) 0 3) := by
  have h1 := C_bounce_0 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones_0082 n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) default
  rw [<- zPl default ([1] : List (Fin 2)) 3 n] at h2
  have hn : 3 + n = n + 3 := by omega
  rw [hn] at h2
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (n + 3)) {{E}}> default) =
      E_0082 0 (n + 3) := rfl
  rw [h_eq] at h2
  exact zPt (zPsp h1 h2) (step_E_b3_to_F_0082 0 n)

theorem C_bounce_1_ones (n : Nat) :
    (C_bounce 1 (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺
    (F_0082 (n + 3) 0 3) := by
  have h1 := C_bounce_1 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones_0082 n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) default
  rw [<- zPl default ([1] : List (Fin 2)) 5 n] at h2
  have hn : 5 + n = (n + 2) + 3 := by omega
  rw [hn] at h2
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ ((n + 2) + 3)) {{E}}>
    default) =
      E_0082 0 ((n + 2) + 3) := rfl
  rw [h_eq] at h2
  have h3 := step_E_b3_to_F_0082 0 (n + 2)
  have hn2 : (n + 2) + 1 = n + 3 := by omega
  rw [hn2] at h3
  exact zPt (zPsp h1 h2) h3

theorem C_bounce_3_ones (b n : Nat) :
    (C_bounce (b + 3) (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺
    (F_0082 (b + 1) 0 (n + 2)) := by
  have h1 := C_bounce_3 b (([1] : List (Fin 2)) ^ n +> default)
  rw [<- zPar ([1] : List (Fin 2)) 2 n default, <- F_0082_eq_F_R] at h1
  have hn : 2 + n = n + 2 := by omega
  rwa [hn] at h1

-- ============================================================================
-- Explicit Hub-to-Hub Macro-Transition Rules on `F_0082`
-- ============================================================================

theorem rule_F_ksucc_c0 (b k : Nat) :
    (F_0082 b (k + 1) 0) [holdout_0082_mod]⊢⁺ (F_0082 b k 1) :=
  step_F_ksucc_c0 b k

theorem rule_F_b0_k0_c0 :
    (F_0082 0 0 0) [holdout_0082_mod]⊢⁺ (F_0082 4 0 3) :=
  zPt (zPt (F_R_b0_to_D100 0 default) (D100_nil_to_C_bounce 0 0)) (C_bounce_0_ones 3)

theorem rule_F_b1_k0_c0 :
    (F_0082 1 0 0) [holdout_0082_mod]⊢⁺ (F_0082 6 0 3) :=
  zPt (zPt (F_R_b1_to_D100 0 default) (D100_nil_to_C_bounce 0 1)) (C_bounce_0_ones 5)

theorem rule_F_b2_k0_c0 :
    (F_0082 2 0 0) [holdout_0082_mod]⊢⁺ (F_0082 3 0 3) :=
  step_F_b2_k0_c0

theorem rule_F_b3_k0_c0 :
    (F_0082 3 0 0) [holdout_0082_mod]⊢⁺ (F_0082 6 0 3) :=
  zPt (zPt (F_R_b3_to_D100 0 0 default) (D100_nil_to_C_bounce 1 0)) (C_bounce_1_ones 3)

theorem rule_F_b5_k0_c0 (b : Nat) :
    (F_0082 (b + 5) 0 0) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 5) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  exact zPt (zPt (F_R_b3_to_D100 (b + 2) 0 default) (D100_nil_to_C_bounce (b + 3) 0))
    (C_bounce_3_ones b 3)

theorem rule_F_b0_c1 (k : Nat) :
    (F_0082 0 k 1) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + 6) 0 3) :=
  zPt (zPt (F_R_b0_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 k))
    (C_bounce_0_ones (2 * k + 5))

theorem rule_F_b1_c1 (k : Nat) :
    (F_0082 1 k 1) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + 8) 0 3) := by
  have h := zPt (zPt (F_R_b1_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 (k + 1)))
    (C_bounce_0_ones (2 * (k + 1) + 5))
  have hk : (2 * (k + 1) + 5) + 1 = 2 * k + 8 := by omega
  rwa [hk] at h

theorem rule_F_b2_k0_c1 (c : Nat) :
    (F_0082 2 0 (c + 1)) [holdout_0082_mod]⊢⁺ (F_0082 5 0 c) :=
  step_F_b2_k0_0082 c

theorem rule_F_b3_c1 (k : Nat) :
    (F_0082 3 k 1) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + 8) 0 3) := by
  have h := zPt (zPt (F_R_b3_to_D100 0 k ([1] +> default)) (D100_one_to_C_bounce 1 k))
    (C_bounce_1_ones (2 * k + 5))
  have hk : (2 * k + 5) + 3 = 2 * k + 8 := by omega
  rwa [hk] at h

theorem rule_F_b5_c1 (b k : Nat) :
    (F_0082 (b + 5) k 1) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 (2 * k + 7)) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  have h := zPt (zPt (F_R_b3_to_D100 (b + 2) k ([1] +> default)) (D100_one_to_C_bounce (b + 3) k))
    (C_bounce_3_ones b (2 * k + 5))
  have hk : (2 * k + 5) + 2 = 2 * k + 7 := by omega
  rwa [hk] at h

theorem rule_F_b0_c2 (k c : Nat) :
    (F_0082 0 k (c + 2)) [holdout_0082_mod]⊢⁺ (F_0082 1 (k + 1) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, zPar ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b0_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 k (([1] : List (Fin 2)) ^ c +> default)
  exact zPt h1 h2

theorem rule_F_b1_c2 (k c : Nat) :
    (F_0082 1 k (c + 2)) [holdout_0082_mod]⊢⁺ (F_0082 1 (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, zPar ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ c +> default)
  exact zPt h1 h2

theorem rule_F_b3_c2 (b k c : Nat) :
    (F_0082 (b + 3) k (c + 2)) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, zPar ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b3_to_D100 b k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_succ_11 b k (([1] : List (Fin 2)) ^ c +> default)
  exact zPt h1 h2

theorem step_F_R_b2_one (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 2 k ([1] +> r)) [holdout_0082_mod]⊢⁺
    (F_R 5 0 (([0, 1] : List (Fin 2)) ^ k +> r)) := by
  unfold F_R
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) ([0,
    1] +> r)
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{F}}>
      ([0] +> (([0, 1] : List (Fin 2)) ^ k +> ([0, 1] +> r))))
      [holdout_0082_mod]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{F}}>
        ([0, 0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
    rw [zPa1 ([0, 1] : List (Fin 2)) k r,
      zPsr ([0, 1] : List (Fin 2)) k r]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append]
    execute
  exact zSpp h1 h2
theorem step_E_01_to_F_R (b : Nat) (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) {{E}}> ([0, 1] +> r))
    [holdout_0082_mod]⊢⁺
    (F_R b 0 r) := by
  unfold F_R
  simp only [zPz, zLan]
  dsimp [ListBlank.append]
  execute

def π : Fin 6 -> Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 4
  | 5 => 0
def mirrorTape : Tape (Fin 2) -> Tape (Fin 2)
  | ⟨head, l, r⟩ => ⟨head, r, l⟩
def mirrorCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map π, mirrorTape c.tape⟩
theorem step_mirror (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (mirrorCfg c) = (step holdout_0082_mod c).map mirrorCfg := by
  rcases c with ⟨_ | q, ⟨head, l, r⟩⟩
  · rfl
  · rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases head with ⟨_ | _ | head, hhead⟩ <;>
    first | rfl | omega
theorem multiStep_mirror (n : Nat) (c : Cfg (Fin 2) (Fin 6)) :
    multiStep target_tm (mirrorCfg c) n = (multiStep holdout_0082_mod c n).map mirrorCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [zMs, zMs, ih]
    cases multiStep holdout_0082_mod c n with
    | none => rfl
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      exact step_mirror c'
theorem stepPlus_mirror {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h : c_1 [holdout_0082_mod]⊢⁺ c_2) :
    (mirrorCfg c_1) [target_tm]⊢⁺ (mirrorCfg c_2) := by
  rcases h with ⟨n, hn, hstep⟩
  refine ⟨n, hn, ?_⟩
  rw [multiStep_mirror, hstep]
  rfl

theorem mirrorCfg_F_403_eq :
    mirrorCfg (F_0082 4 0 3) =
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) {{A}}>
      ([0] +> (([1] : List (Fin 2)) ^ 4 +> default)) := rfl

def Odd_cfg (p k n m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  F_R (2 * p + 1) k
    (([1] : List (Fin 2)) ^ (2 * n) +>
      (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default)))

def ETail_cfg (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) {{E}}>
    (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default)))

theorem rule_F_b2_ksucc_c1 (k c : Nat) :
    (F_0082 2 (k + 1) (c + 1)) [holdout_0082_mod]⊢⁺ (Odd_cfg 2 0 0 k c) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, zPz, zLan]
  rw [F_0082_eq_F_R, zPsr ([1] : List (Fin 2)) c default]
  exact step_F_R_b2_one (k + 1) (([1] : List (Fin 2)) ^ c +> default)

theorem step_Odd_nsucc_p0 (k n m c : Nat) :
    (Odd_cfg 0 k (n + 1) m c) [holdout_0082_mod]⊢⁺ (Odd_cfg 0 (k + 2) n m c) := by
  unfold Odd_cfg
  set r := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hn : 2 * (n + 1) = 2 + 2 * n := by omega
  rw [hn, zPar ([1] : List (Fin 2)) 2 (2 * n) r]
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +> r))
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
  exact zPt h1 h2

theorem step_Odd_nsucc_psucc (p k n m c : Nat) :
    (Odd_cfg (p + 1) k (n + 1) m c) [holdout_0082_mod]⊢⁺ (Odd_cfg p (k + 2) n m c) := by
  unfold Odd_cfg
  set r := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hn : 2 * (n + 1) = 2 + 2 * n := by omega
  have hp : 2 * (p + 1) + 1 = (2 * p) + 3 := by omega
  rw [hn, hp, zPar ([1] : List (Fin 2)) 2 (2 * n) r]
  have h1 := F_R_b3_to_D100 (2 * p) k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n)
    +> r))
  have h2 := D100_succ_11 (2 * p) k (([1] : List (Fin 2)) ^ (2 * n) +> r)
  exact zPt h1 h2

theorem step_Odd_n0_p0 (k m c : Nat) :
    (Odd_cfg 0 k 0 m c) [holdout_0082_mod]⊢⁺ (ETail_cfg k m c) := by
  unfold Odd_cfg ETail_cfg
  simp only [Nat.mul_zero, zPz, zLan]
  rw [zPsr ([0, 1] : List (Fin 2)) m]
  set r' := (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))
  have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce 0 (k + 1) r'
  have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
  have h4 := shift_E_ones_0082 (2 * (k + 1) + 4)
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) r'
  rw [<- zPl default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
  have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
  rw [hk] at h4
  exact zPsp (zPt (zPt h1 h2) h3) h4

theorem step_Odd_n0_p1 (k m c : Nat) :
    (Odd_cfg 1 k 0 m c) [holdout_0082_mod]⊢⁺ (ETail_cfg k m c) := by
  unfold Odd_cfg ETail_cfg
  simp only [Nat.mul_zero, zPz, zLan]
  rw [zPsr ([0, 1] : List (Fin 2)) m]
  set r' := (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))
  have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce 1 k r'
  have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  have h4 := shift_E_ones_0082 (2 * k + 4)
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) r'
  rw [<- zPl default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
  have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
  rw [hk] at h4
  exact zPsp (zPt (zPt h1 h2) h3) h4

theorem step_Odd_n0_p2_m0 (p k c : Nat) :
    (Odd_cfg (p + 2) k 0 0 c) [holdout_0082_mod]⊢⁺ (F_0082 (2 * p + 1) 0 (2 * (k + 3) + c)) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, zPz, zLan]
  rw [zPsr ([0, 1] : List (Fin 2)) 0]
  simp only [zPz, zLan]
  set r' := (([1] : List (Fin 2)) ^ c +> default)
  have hp : 2 * (p + 2) + 1 = (2 * p + 2) + 3 := by omega
  rw [hp]
  have h1 := F_R_b3_to_D100 (2 * p + 2) k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce (2 * p + 3) k r'
  have h3 := C_bounce_3 (2 * p) (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  rw [<- zPar ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
  have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
  rw [hk, <- zPar ([1] : List (Fin 2)) (2 * (k + 3)) c default, <- F_0082_eq_F_R] at h3
  exact zPt (zPt h1 h2) h3

theorem step_Odd_n0_p2_msucc (p k m c : Nat) :
    (Odd_cfg (p + 2) k 0 (m + 1) c) [holdout_0082_mod]⊢⁺ (Odd_cfg p 0 (k + 3) m c) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, zPz, zLan]
  rw [zPsr ([0, 1] : List (Fin 2)) (m + 1)]
  set r' := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hp : 2 * (p + 2) + 1 = (2 * p + 2) + 3 := by omega
  rw [hp]
  have h1 := F_R_b3_to_D100 (2 * p + 2) k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce (2 * p + 3) k r'
  have h3 := C_bounce_3 (2 * p) (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  rw [<- zPar ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
  have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
  rw [hk] at h3
  exact zPt (zPt h1 h2) h3

theorem step_ETail_m0 (k c : Nat) :
    (ETail_cfg k 0 c) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + c + 7) 0 3) := by
  unfold ETail_cfg
  simp only [zPz, zLan]
  have h1 := shift_E_ones_0082 c
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) default
  rw [<- zPl default ([1] : List (Fin 2)) (2 * (k + 4) + 1) c] at h1
  have hk : 2 * (k + 4) + 1 + c = (2 * k + c + 6) + 3 := by omega
  rw [hk] at h1
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ ((2 * k + c + 6) + 3))
    {{E}}> default) =
      E_0082 0 ((2 * k + c + 6) + 3) := rfl
  rw [h_eq] at h1
  have h2 := step_E_b3_to_F_0082 0 (2 * k + c + 6)
  have hk2 : (2 * k + c + 6) + 1 = 2 * k + c + 7 := by omega
  rw [hk2] at h2
  exact zSpp h1 h2

theorem step_ETail_m1 (k c : Nat) :
    (ETail_cfg k 1 c) [holdout_0082_mod]⊢⁺ (F_0082 (2 * (k + 4) + 1) 0 c) := by
  unfold ETail_cfg
  rw [zPsr ([0, 1] : List (Fin 2)) 0]
  simp only [zPz, zLan]
  exact step_E_01_to_F_R (2 * (k + 4) + 1) (([1] : List (Fin 2)) ^ c +> default)

theorem step_ETail_m2 (k m c : Nat) :
    (ETail_cfg k (m + 2) c) [holdout_0082_mod]⊢⁺ (Odd_cfg (k + 4) 0 0 m c) := by
  unfold ETail_cfg Odd_cfg
  simp only [Nat.mul_zero, zPz, zLan]
  rw [zPsr ([0, 1] : List (Fin 2)) (m + 1)]
  exact step_E_01_to_F_R (2 * (k + 4) + 1)
    (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))

-- ============================================================================
-- Symbolic Acceleration State Space & Soundness Bridge
-- ============================================================================

inductive State
  | stA (b k c : ℕ)
  | stOdd (p k n m c : ℕ)
  | stETail (k m c : ℕ)

def start : State := .stA 4 0 3

def next : State → Option State
  | .stA b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.stA 4 0 3)) fun b =>
       Nat.casesOn b (some (.stA 6 0 3)) fun b =>
       Nat.casesOn b (some (.stA 3 0 3)) fun b =>
       Nat.casesOn b (some (.stA 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.stA (b + 1) 0 5))
      fun k => some (.stA b k 1)
  | .stA b k 1 =>
    Nat.casesOn b (some (.stA (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.stA (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.stA 5 0 0)) fun k => some (.stOdd 2 0 0 k 0)) fun b =>
    Nat.casesOn b (some (.stA (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.stA (b + 1) 0 (2 * k + 7))
  | .stA b k (c + 2) =>
    Nat.casesOn b (some (.stA 1 (k + 1) c)) fun b =>
    Nat.casesOn b (some (.stA 1 (k + 2) c)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.stA 5 0 (c + 1))) fun k => some (.stOdd 2 0 0 k (c + 1))) fun b =>
    some (.stA (b + 1) (k + 2) c)
  | .stOdd p k (n + 1) m c =>
    Nat.casesOn p (some (.stOdd 0 (k + 2) n m c)) fun p =>
    some (.stOdd p (k + 2) n m c)
  | .stOdd p k 0 m c =>
    Nat.casesOn p (some (.stETail k m c)) fun p =>
    Nat.casesOn p (some (.stETail k m c)) fun p =>
    Nat.casesOn m (some (.stA (2 * p + 1) 0 (2 * (k + 3) + c))) fun m =>
    some (.stOdd p 0 (k + 3) m c)
  | .stETail k 0 c => some (.stA (2 * k + c + 7) 0 3)
  | .stETail k 1 c => some (.stA (2 * (k + 4) + 1) 0 c)
  | .stETail k (m + 2) c => some (.stOdd (k + 4) 0 0 m c)

def encode_F : State → Cfg (Fin 2) (Fin 6)
  | .stA b k c => F_0082 b k c
  | .stOdd p k n m c => Odd_cfg p k n m c
  | .stETail k m c => ETail_cfg k m c

def encode (s : State) : Cfg (Fin 2) (Fin 6) :=
  mirrorCfg (encode_F s)

theorem init_reaches_start : (init []) [target_tm]⊢⁺ encode start := by
  change (init []) [target_tm]⊢⁺ mirrorCfg (F_0082 4 0 3)
  rw [mirrorCfg_F_403_eq]
  unfold init
  simp only [Tape.mk₁, zPz, zPsl, zCal, zAnl, zLan, zLac]
  execute

theorem step_F_sound {s s' : State} (hnext : next s = some s') :
    (encode_F s) [holdout_0082_mod]⊢⁺ (encode_F s') := by
  match s with
  | .stA b (k + 1) 0 => injection hnext with hs'; subst hs'; exact rule_F_ksucc_c0 b k
  | .stA 0 0 0 => injection hnext with hs'; subst hs'; exact rule_F_b0_k0_c0
  | .stA 1 0 0 => injection hnext with hs'; subst hs'; exact rule_F_b1_k0_c0
  | .stA 2 0 0 => injection hnext with hs'; subst hs'; exact rule_F_b2_k0_c0
  | .stA 3 0 0 => injection hnext with hs'; subst hs'; exact rule_F_b3_k0_c0
  | .stA 4 0 0 => nomatch hnext
  | .stA (b + 5) 0 0 => injection hnext with hs'; subst hs'; exact rule_F_b5_k0_c0 b
  | .stA 0 k 1 => injection hnext with hs'; subst hs'; exact rule_F_b0_c1 k
  | .stA 1 k 1 => injection hnext with hs'; subst hs'; exact rule_F_b1_c1 k
  | .stA 2 0 1 => injection hnext with hs'; subst hs'; exact rule_F_b2_k0_c1 0
  | .stA 2 (k + 1) 1 => injection hnext with hs'; subst hs'; exact rule_F_b2_ksucc_c1 k 0
  | .stA 3 k 1 => injection hnext with hs'; subst hs'; exact rule_F_b3_c1 k
  | .stA 4 k 1 => nomatch hnext
  | .stA (b + 5) k 1 => injection hnext with hs'; subst hs'; exact rule_F_b5_c1 b k
  | .stA 0 k (c + 2) => injection hnext with hs'; subst hs'; exact rule_F_b0_c2 k c
  | .stA 1 k (c + 2) => injection hnext with hs'; subst hs'; exact rule_F_b1_c2 k c
  | .stA 2 0 (c + 2) => injection hnext with hs'; subst hs'; exact rule_F_b2_k0_c1 (c + 1)
  | .stA 2 (k + 1) (c + 2) => injection hnext with hs'; subst hs'; exact rule_F_b2_ksucc_c1 k (c +
    1)
  | .stA (b + 3) k (c + 2) => injection hnext with hs'; subst hs'; exact rule_F_b3_c2 b k c
  | .stOdd 0 k (n + 1) m c => injection hnext with hs'; subst hs'; exact step_Odd_nsucc_p0 k n m c
  | .stOdd (p + 1) k (n + 1) m c =>
      injection hnext with hs'; subst hs'; exact step_Odd_nsucc_psucc p k n m c
  | .stOdd 0 k 0 m c => injection hnext with hs'; subst hs'; exact step_Odd_n0_p0 k m c
  | .stOdd 1 k 0 m c => injection hnext with hs'; subst hs'; exact step_Odd_n0_p1 k m c
  | .stOdd (p + 2) k 0 0 c => injection hnext with hs'; subst hs'; exact step_Odd_n0_p2_m0 p k c
  | .stOdd (p + 2) k 0 (m + 1) c =>
      injection hnext with hs'; subst hs'; exact step_Odd_n0_p2_msucc p k m c
  | .stETail k 0 c => injection hnext with hs'; subst hs'; exact step_ETail_m0 k c
  | .stETail k 1 c => injection hnext with hs'; subst hs'; exact step_ETail_m1 k c
  | .stETail k (m + 2) c => injection hnext with hs'; subst hs'; exact step_ETail_m2 k m c

theorem step_sound {s s' : State} (hnext : next s = some s') :
    (encode s) [target_tm]⊢⁺ (encode s') :=
  stepPlus_mirror (step_F_sound hnext)

def OrbitReachesIn (f : State → Option State) (n : ℕ) (s₁ s₂ : State) : Prop :=
  (Option.bind · f)^[n] (some s₁) = some s₂

def OrbitReachesStar (f : State → Option State) (s₁ s₂ : State) : Prop :=
  ∃ n : ℕ, OrbitReachesIn f n s₁ s₂

def OrbitReachesPlus (f : State → Option State) (s₁ s₂ : State) : Prop :=
  ∃ n : ℕ, n > 0 ∧ OrbitReachesIn f n s₁ s₂

private theorem iterate_bind_none (f : State → Option State) (n : ℕ) :
    (Option.bind · f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Option.bind_none, ih]

theorem OrbitReachesIn.head {f : State → Option State} {n : ℕ} {s₁ s₂ s₃ : State}
    (h₁ : f s₁ = some s₂) (h₂ : OrbitReachesIn f n s₂ s₃) :
    OrbitReachesIn f (n + 1) s₁ s₃ := by
  unfold OrbitReachesIn at *
  rw [Function.iterate_succ_apply]
  simpa [h₁] using h₂

theorem OrbitReachesIn.trans {f : State → Option State} {m n : ℕ} {s₁ s₂ s₃ : State}
    (h₁ : OrbitReachesIn f m s₁ s₂) (h₂ : OrbitReachesIn f n s₂ s₃) :
    OrbitReachesIn f (m + n) s₁ s₃ := by
  unfold OrbitReachesIn at *
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

theorem OrbitReachesStar.refl (f : State → Option State) (s : State) :
    OrbitReachesStar f s s := ⟨0, rfl⟩

theorem OrbitReachesStar.head {f : State → Option State} {s₁ s₂ s₃ : State}
    (h₁ : f s₁ = some s₂) (h₂ : OrbitReachesStar f s₂ s₃) :
    OrbitReachesStar f s₁ s₃ :=
  let ⟨n, hn⟩ := h₂
  ⟨n + 1, OrbitReachesIn.head h₁ hn⟩

theorem OrbitReachesStar.single {f : State → Option State} {s₁ s₂ : State}
    (h : f s₁ = some s₂) :
    OrbitReachesStar f s₁ s₂ :=
  OrbitReachesStar.head h (OrbitReachesStar.refl f s₂)

theorem OrbitReachesStar.trans {f : State → Option State} {s₁ s₂ s₃ : State}
    (h₁ : OrbitReachesStar f s₁ s₂) (h₂ : OrbitReachesStar f s₂ s₃) :
    OrbitReachesStar f s₁ s₃ :=
  let ⟨m, hm⟩ := h₁
  let ⟨n, hn⟩ := h₂
  ⟨m + n, hm.trans hn⟩

theorem OrbitReachesPlus.single {f : State → Option State} {s₁ s₂ : State}
    (h : f s₁ = some s₂) :
    OrbitReachesPlus f s₁ s₂ :=
  ⟨1, Nat.succ_pos 0, OrbitReachesIn.head h rfl⟩

theorem OrbitReachesPlus.to_star {f : State → Option State} {s₁ s₂ : State}
    (h : OrbitReachesPlus f s₁ s₂) :
    OrbitReachesStar f s₁ s₂ :=
  let ⟨n, _, hn⟩ := h
  ⟨n, hn⟩

theorem OrbitReachesPlus.head {f : State → Option State} {s₁ s₂ s₃ : State}
    (h₁ : f s₁ = some s₂) (h₂ : OrbitReachesStar f s₂ s₃) :
    OrbitReachesPlus f s₁ s₃ :=
  let ⟨n, hn⟩ := h₂
  ⟨n + 1, Nat.succ_pos n, OrbitReachesIn.head h₁ hn⟩

theorem OrbitReachesPlus.trans {f : State → Option State} {s₁ s₂ s₃ : State}
    (h₁ : OrbitReachesPlus f s₁ s₂) (h₂ : OrbitReachesPlus f s₂ s₃) :
    OrbitReachesPlus f s₁ s₃ :=
  let ⟨m, hm_pos, hm⟩ := h₁
  let ⟨n, _, hn⟩ := h₂
  ⟨m + n, Nat.add_pos_left hm_pos n, hm.trans hn⟩

theorem OrbitReachesPlus.trans_star {f : State → Option State} {s₁ s₂ s₃ : State}
    (h₁ : OrbitReachesPlus f s₁ s₂) (h₂ : OrbitReachesStar f s₂ s₃) :
    OrbitReachesPlus f s₁ s₃ :=
  let ⟨m, hm_pos, hm⟩ := h₁
  let ⟨n, hn⟩ := h₂
  ⟨m + n, Nat.add_pos_left hm_pos n, hm.trans hn⟩

theorem OrbitReachesStar.trans_plus {f : State → Option State} {s₁ s₂ s₃ : State}
    (h₁ : OrbitReachesStar f s₁ s₂) (h₂ : OrbitReachesPlus f s₂ s₃) :
    OrbitReachesPlus f s₁ s₃ :=
  let ⟨m, hm⟩ := h₁
  let ⟨n, hn_pos, hn⟩ := h₂
  ⟨m + n, Nat.add_pos_right m hn_pos, hm.trans hn⟩

theorem orbitIn_sound {n : ℕ} {s₁ s₂ : State} (h : OrbitReachesIn next n s₁ s₂) :
    (encode s₁) [target_tm]⊢* (encode s₂) := by
  induction n generalizing s₁ with
  | zero =>
    simp only [OrbitReachesIn, Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    exact ⟨0, rfl⟩
  | succ m ih =>
    unfold OrbitReachesIn at h
    rw [Function.iterate_succ_apply] at h
    change (Option.bind · next)^[m] (next s₁) = some s₂ at h
    rcases h1 : next s₁ with _ | s_mid
    · rw [h1, iterate_bind_none] at h
      cases h
    · rw [h1] at h
      exact zPs (zPsp (step_sound h1) (ih h))

theorem orbitPlus_sound {s₁ s₂ : State} (h : OrbitReachesPlus next s₁ s₂) :
    (encode s₁) [target_tm]⊢⁺ (encode s₂) := by
  rcases h with ⟨n, hn, hreach⟩
  rcases n with _ | m
  · omega
  · unfold OrbitReachesIn at hreach
    rw [Function.iterate_succ_apply] at hreach
    change (Option.bind · next)^[m] (next s₁) = some s₂ at hreach
    rcases h1 : next s₁ with _ | s_mid
    · rw [h1, iterate_bind_none] at hreach
      cases hreach
    · rw [h1] at hreach
      exact zPsp (step_sound h1) (orbitIn_sound hreach)

theorem iter_A_drain (j b k c : ℕ) :
    OrbitReachesIn next j (.stA (b + 2 * j + 1) k (c + 2 * j)) (.stA (b + 1) (k + 2 * j) c) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    have h1 : b + 2 * (j + 1) + 1 = (b + 2 * j) + 3 := by omega
    have h2 : c + 2 * (j + 1) = (c + 2 * j) + 2 := by omega
    have h3 : (k + 2) + 2 * j = k + 2 * (j + 1) := by omega
    rw [h1, h2, ← h3]
    exact OrbitReachesIn.head rfl (ih (k + 2))

theorem start_step16 : OrbitReachesIn next 16 start (.stA 28 0 3) := rfl

def cfg_D1 (a u v : ℕ) : State :=
  match v with
  | 0 => .stA (a - 2) 0 (2 * u + 3)
  | c + 1 => .stA a u c

def cfg_Modd (m u v y z : ℕ) : State :=
  match y with
  | 0 => cfg_D1 (2 * m + 1) u (v + z)
  | m' + 1 => .stOdd m u (v / 2) m' z

theorem cfg_Modd_y0_eq_D1 (m u v z : ℕ) :
    cfg_Modd m u v 0 z = cfg_D1 (2 * m + 1) u (v + z) := rfl

theorem drain_D1_v2 (k a u v : ℕ) (hv : v ≥ 1) :
    OrbitReachesStar next (cfg_D1 (a + 2 * k + 1) u (v + 2 * k)) (cfg_D1 (a + 1) (u + 2 * k) v) :=
      by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hv
  have hv_eq : (c + 1) + 2 * k = (c + 2 * k) + 1 := by omega
  rw [hv_eq]
  exact ⟨k, iter_A_drain k a u c⟩

theorem drain_D1_a1_v2 (k u v : ℕ) (hv : v ≥ 1) :
    OrbitReachesStar next (cfg_D1 1 u (v + 2 * k)) (cfg_D1 1 (u + 2 * k) v) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hv
  induction k generalizing u with
  | zero =>
    have h1 : (c + 1) + 2 * 0 = c + 1 := by omega
    have h2 : u + 2 * 0 = u := by omega
    rw [h1, h2]
    exact OrbitReachesStar.refl next _
  | succ k ih =>
    have hv_eq : (c + 1) + 2 * (k + 1) = ((c + 2 * k) + 2) + 1 := by omega
    rw [hv_eq]
    have h1 : next (cfg_D1 1 u (((c + 2 * k) + 2) + 1)) = some (cfg_D1 1 (u + 2) ((c + 1) + 2 *
      k)) := by
      have h_rhs : (c + 1) + 2 * k = (c + 2 * k) + 1 := by omega
      rw [h_rhs]; rfl
    have h2 := ih (u + 2)
    have hu : (u + 2) + 2 * k = u + 2 * (k + 1) := by omega
    rw [hu] at h2
    exact OrbitReachesStar.head h1 h2

theorem accel_D1_double (a u : ℕ) (ha : a ≥ 2) :
    OrbitReachesPlus next (cfg_D1 (a + 2 * u + 7) u 0) (cfg_D1 (a + 1) (2 * u + 4) 0) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha
  have h_in : cfg_D1 ((b + 2) + 2 * u + 7) u 0 =
      cfg_D1 ((b + 4) + 2 * (u + 1) + 1) 0 (2 + 2 * (u + 1)) := by
    have h2 : 2 + 2 * (u + 1) = (1 + 2 * (u + 1)) + 1 := by omega
    rw [h2]
    dsimp [cfg_D1]
    have h1 : (b + 2) + 2 * u + 7 - 2 = (b + 4) + 2 * (u + 1) + 1 := by omega
    have h3 : 2 * u + 3 = 1 + 2 * (u + 1) := by omega
    rw [h1, h3]
  rw [h_in]
  have h1 := drain_D1_v2 (u + 1) (b + 4) 0 2 (by omega)
  have h_step : next (cfg_D1 ((b + 4) + 1) (0 + 2 * (u + 1)) 2) =
      some (cfg_D1 ((b + 2) + 1) (2 * u + 4) 0) := by
    have hb1 : (b + 4) + 1 = b + 5 := by omega
    have hu1 : 0 + 2 * (u + 1) = 2 * u + 2 := by omega
    have hb2 : (b + 2) + 1 - 2 = b + 1 := by omega
    have hu2 : 2 * (2 * u + 4) + 3 = 2 * (2 * u + 2) + 7 := by omega
    dsimp [cfg_D1]
    rw [hb1, hu1, hb2, hu2]
    rfl
  exact OrbitReachesStar.trans_plus h1 (OrbitReachesPlus.single h_step)

theorem rule_Modd_m0_v2 (u v y z : ℕ) (hv : v ≥ 1) :
    OrbitReachesPlus next (cfg_Modd 0 u (v + 2) y z) (cfg_Modd 0 (u + 2) v y z) := by
  rcases y with _ | m'
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hv
    have h1 : c + 1 + 2 + z = (c + z + 2) + 1 := by omega
    have h2 : c + 1 + z = (c + z) + 1 := by omega
    dsimp [cfg_Modd]
    rw [h1, h2]
    exact OrbitReachesPlus.single rfl
  · dsimp [cfg_Modd]
    have hdiv : (v + 2) / 2 = v / 2 + 1 := by omega
    rw [hdiv]
    exact OrbitReachesPlus.single rfl

theorem rule_Modd_m1_v2 (m u v y z : ℕ) (hv : v ≥ 1) :
    OrbitReachesPlus next (cfg_Modd (m + 1) u (v + 2) y z) (cfg_Modd m (u + 2) v y z) := by
  rcases y with _ | m'
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hv
    have h1 : 2 * (m + 1) + 1 = (2 * m) + 3 := by omega
    have h2 : c + 1 + 2 + z = (c + z + 2) + 1 := by omega
    have h3 : c + 1 + z = (c + z) + 1 := by omega
    dsimp [cfg_Modd]
    rw [h1, h2, h3]
    exact OrbitReachesPlus.single rfl
  · dsimp [cfg_Modd]
    have hdiv : (v + 2) / 2 = v / 2 + 1 := by omega
    rw [hdiv]
    exact OrbitReachesPlus.single rfl

theorem rule_Modd_m2_v1 (m u y z : ℕ) :
    OrbitReachesPlus next (cfg_Modd (m + 2) u 1 (y + 1) z) (cfg_Modd m 0 (2 * u + 7) y z) := by
  rcases y with _ | m'
  · dsimp [cfg_Modd]
    have h1 : 2 * u + 7 + z = (2 * (u + 3) + z) + 1 := by omega
    rw [h1]
    exact OrbitReachesPlus.single rfl
  · dsimp [cfg_Modd]
    have hdiv : (2 * u + 7) / 2 = u + 3 := by omega
    rw [hdiv]
    exact OrbitReachesPlus.single rfl

theorem rule_Modd_m0_v1_y1 (u z : ℕ) :
    OrbitReachesPlus next (cfg_Modd 0 u 1 1 z) (cfg_D1 (2 * u + z + 9) 0 0) := by
  dsimp [cfg_Modd, cfg_D1]
  have h1 : 2 * u + z + 9 - 2 = 2 * u + z + 7 := by omega
  rw [h1]
  exact ⟨2, by decide, rfl⟩

theorem rule_Modd_m0_v1_y2 (u y z : ℕ) :
    OrbitReachesPlus next (cfg_Modd 0 u 1 (y + 2) z) (cfg_Modd (u + 4) 0 1 y z) := by
  rcases y with _ | m'
  · dsimp [cfg_Modd]
    have h1 : 1 + z = z + 1 := by omega
    rw [h1]
    exact ⟨2, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩

theorem drain_Modd_v2 (k m u v y z : ℕ) (hv : v ≥ 1) :
    OrbitReachesStar next (cfg_Modd (m + k) u (v + 2 * k) y z) (cfg_Modd m (u + 2 * k) v y z) := by
  induction k generalizing m u v with
  | zero =>
    have h1 : m + 0 = m := by omega
    have h2 : v + 2 * 0 = v := by omega
    have h3 : u + 2 * 0 = u := by omega
    rw [h1, h2, h3]
    exact OrbitReachesStar.refl next _
  | succ k ih =>
    have hm : m + (k + 1) = (m + k) + 1 := by omega
    have hv_eq : v + 2 * (k + 1) = (v + 2 * k) + 2 := by omega
    rw [hm, hv_eq]
    have h_step := rule_Modd_m1_v2 (m + k) u (v + 2 * k) y z (by omega)
    have h_ih := ih m (u + 2) v hv
    have hu : (u + 2) + 2 * k = u + 2 * (k + 1) := by omega
    rw [hu] at h_ih
    exact (OrbitReachesPlus.trans_star h_step h_ih).to_star

theorem drain_Modd_m0_v2 (k u v y z : ℕ) (hv : v ≥ 1) :
    OrbitReachesStar next (cfg_Modd 0 u (v + 2 * k) y z) (cfg_Modd 0 (u + 2 * k) v y z) := by
  induction k generalizing u v with
  | zero =>
    have hv_eq : v + 2 * 0 = v := by omega
    have hu : u + 2 * 0 = u := by omega
    rw [hv_eq, hu]
    exact OrbitReachesStar.refl next _
  | succ k ih =>
    have hv_eq : v + 2 * (k + 1) = (v + 2 * k) + 2 := by omega
    rw [hv_eq]
    have h1 := rule_Modd_m0_v2 u (v + 2 * k) y z (by omega)
    have h2 := ih (u + 2) v hv
    have hu : (u + 2) + 2 * k = u + 2 * (k + 1) := by omega
    rw [hu] at h2
    exact (OrbitReachesPlus.trans_star h1 h2).to_star

private theorem mul_pow2_ge (k n : ℕ) : k * 2 ^ n ≥ k := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h2 : k * 2 ^ (n + 1) = k * 2 ^ n * 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

private theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.pow_add]
  exact mul_pow2_ge (2 ^ a) d

private theorem pow2_ge_two_mul (n : ℕ) (hn : n ≥ 5) : 2 ^ n ≥ 2 * n + 6 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction d with
  | zero => decide
  | succ d ih =>
    rw [Nat.add_right_comm d 1 5, Nat.pow_succ]
    omega

private theorem mul_pow2_ge_linear (u n : ℕ) :
    2 * (u + 4) * 2 ^ n ≥ 2 * (u + 4) + 2 * n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h1 : (u + 4) * 2 ^ n ≥ u + 4 := mul_pow2_ge (u + 4) n
    have h2 : 2 * (u + 4) * 2 ^ (n + 1) = (2 * (u + 4) * 2 ^ n) * 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    have h3 : 2 * (u + 4) * 2 ^ n = 2 * ((u + 4) * 2 ^ n) := Nat.mul_assoc 2 (u + 4) (2 ^ n)
    omega

theorem exp_step_D1_exact (n a u : ℕ) (ha : a ≥ 2) :
    OrbitReachesStar next
      (cfg_D1 (a + (2 * (u + 4) * 2 ^ n - 2 * (u + 4) - 2 * n) + 1) u 0)
      (cfg_D1 (a + 1) ((u + 4) * 2 ^ n - 4) 0) := by
  induction n generalizing a u with
  | zero =>
    have ha0 : a + (2 * (u + 4) * 2 ^ 0 - 2 * (u + 4) - 2 * 0) + 1 = a + 1 := by omega
    have hu0 : (u + 4) * 2 ^ 0 - 4 = u := by omega
    rw [ha0, hu0]
    exact OrbitReachesStar.refl next _
  | succ n ih =>
    let k := (u + 4) * 2 ^ n
    have hk : k ≥ u + 4 := mul_pow2_ge (u + 4) n
    have h2k : 2 * (u + 4) * 2 ^ n = 2 * k := Nat.mul_assoc 2 (u + 4) (2 ^ n)
    have hlin : 2 * k ≥ 2 * (u + 4) + 2 * n := by rw [← h2k]; exact mul_pow2_ge_linear u n
    have hpow : 2 * (u + 4) * 2 ^ (n + 1) = 4 * k := by
      dsimp [k]
      rw [Nat.pow_succ, Nat.mul_assoc 2 (u + 4) (2 ^ n * 2), ← Nat.mul_assoc (u + 4) (2 ^ n) 2]
      omega
    have ha_in : a + (2 * (u + 4) * 2 ^ (n + 1) - 2 * (u + 4) - 2 * (n + 1)) + 1 =
        (a + 2 * (k - 4) + 6) + (2 * (u + 4) * 2 ^ n - 2 * (u + 4) - 2 * n) + 1 := by
      rw [hpow, h2k]; omega
    rw [ha_in]
    have h1 := ih (a + 2 * (k - 4) + 6) u (by omega)
    have ha_mid : (a + 2 * (k - 4) + 6) + 1 = a + 2 * (k - 4) + 7 := by omega
    rw [ha_mid] at h1
    have h2 := accel_D1_double a (k - 4) ha
    have hu_out : 2 * (k - 4) + 4 = (u + 4) * 2 ^ (n + 1) - 4 := by
      have hk2 : (u + 4) * 2 ^ (n + 1) = k * 2 := by dsimp [k]; rw [Nat.pow_succ, Nat.mul_assoc]
      omega
    rw [hu_out] at h2
    exact OrbitReachesStar.trans h1 h2.to_star

theorem enter_Modd_from_D1 (k u z : ℕ)
    (hk : k ≥ 1) (hz : 2 * u + 2 = 2 * k + z) :
    OrbitReachesPlus next (cfg_D1 (2 * k + 4) u 0) (cfg_Modd 2 0 1 (2 * k) z) := by
  have h_in : cfg_D1 (2 * k + 4) u 0 = cfg_D1 (1 + 2 * k + 1) 0 ((z + 2) + 2 * k) := by
    have h2 : (z + 2) + 2 * k = (z + 1 + 2 * k) + 1 := by omega
    rw [h2]
    dsimp [cfg_D1]
    have h1 : 2 * k + 4 - 2 = 1 + 2 * k + 1 := by omega
    have h3 : 2 * u + 3 = (z + 1) + 2 * k := by omega
    rw [h1, h3]
  rw [h_in]
  have h1 := drain_D1_v2 k 1 0 (z + 2) (by omega)
  have h_step : next (cfg_D1 (1 + 1) (0 + 2 * k) (z + 2)) = some (cfg_Modd 2 0 1 (2 * k) z) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (show 2 * k ≥ 1 by omega)
    have hu1 : 0 + 2 * k = m + 1 := by omega
    dsimp [cfg_D1, cfg_Modd]
    rw [hu1, hm]
    rcases z with _ | z <;> rfl
  exact OrbitReachesStar.trans_plus h1 (OrbitReachesPlus.single h_step)

theorem accel_Modd_double (m u y z : ℕ) :
    OrbitReachesPlus next (cfg_Modd (m + u + 5) u 1 (y + 1) z) (cfg_Modd m (2 * u + 6) 1 y z) := by
  have hm : m + u + 5 = (m + u + 3) + 2 := by omega
  rw [hm]
  have h1 := rule_Modd_m2_v1 (m + u + 3) u y z
  have hv : 2 * u + 7 = 1 + 2 * (u + 3) := by omega
  have hm2 : m + u + 3 = m + (u + 3) := by omega
  rw [hm2, hv] at h1
  have h2 := drain_Modd_v2 (u + 3) m 0 1 y z (by omega)
  have hu : 0 + 2 * (u + 3) = 2 * u + 6 := by omega
  rw [hu] at h2
  exact OrbitReachesPlus.trans_star h1 h2

private theorem six_pow2_ge_linear (e : ℕ) :
    6 * 2 ^ e ≥ e + 6 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

theorem exp_step_Modd_exact (e m y z : ℕ) :
    OrbitReachesStar next
      (cfg_Modd (m + (6 * 2 ^ e - 6 - e)) 0 1 (y + e) z)
      (cfg_Modd m (6 * 2 ^ e - 6) 1 y z) := by
  induction e generalizing m y with
  | zero =>
    have hm : m + (6 * 2 ^ 0 - 6 - 0) = m := by omega
    have hy : y + 0 = y := by omega
    have hu : 6 * 2 ^ 0 - 6 = 0 := by omega
    rw [hm, hy, hu]
    exact OrbitReachesStar.refl next _
  | succ e ih =>
    let k := 6 * 2 ^ e
    have hk : k ≥ e + 6 := six_pow2_ge_linear e
    have hpow : 6 * 2 ^ (e + 1) = k + k := by
      dsimp [k]; rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    have hm_in : m + (6 * 2 ^ (e + 1) - 6 - (e + 1)) =
        (m + (k - 6) + 5) + (k - 6 - e) := by omega
    have hy_in : y + (e + 1) = (y + 1) + e := by omega
    rw [hm_in, hy_in]
    have h1 := ih (m + (k - 6) + 5) (y + 1)
    have h2 := accel_Modd_double m (k - 6) y z
    have hu_out : 2 * (k - 6) + 6 = 6 * 2 ^ (e + 1) - 6 := by omega
    rw [hu_out] at h2
    exact OrbitReachesStar.trans h1 h2.to_star

theorem finish_pass_Modd (m u y z : ℕ) (hm : m ≤ u + 3) :
    OrbitReachesPlus next (cfg_Modd (m + 2) u 1 (y + 3) z) (cfg_Modd (2 * u + 10) 0 1 y z) := by
  have hy1 : y + 3 = (y + 2) + 1 := by omega
  rw [hy1]
  have h1 := rule_Modd_m2_v1 m u (y + 2) z
  have h2 := drain_Modd_v2 m 0 0 (1 + 2 * (u + 3 - m)) (y + 2) z (by omega)
  have hm1 : 0 + m = m := by omega
  have hv1 : (1 + 2 * (u + 3 - m)) + 2 * m = 2 * u + 7 := by omega
  rw [hm1, hv1] at h2
  have h12 := OrbitReachesPlus.trans_star h1 h2
  have h3 := drain_Modd_m0_v2 (u + 3 - m) (0 + 2 * m) 1 (y + 2) z (by omega)
  have h123 := OrbitReachesPlus.trans_star h12 h3
  have hu3 : 0 + 2 * m + 2 * (u + 3 - m) = 2 * u + 6 := by omega
  rw [hu3] at h123
  have h4 := rule_Modd_m0_v1_y2 (2 * u + 6) y z
  have hu4 : (2 * u + 6) + 4 = 2 * u + 10 := by omega
  rw [hu4] at h4
  exact OrbitReachesPlus.trans h123 h4

theorem finish_exit_Modd_y2 (m u z : ℕ) (hm : m ≤ u + 3) :
    OrbitReachesPlus next (cfg_Modd (m + 2) u 1 2 z) (cfg_D1 (4 * u + z + 21) 0 0) := by
  have h1 := rule_Modd_m2_v1 m u 1 z
  have h2 := drain_Modd_v2 m 0 0 (1 + 2 * (u + 3 - m)) 1 z (by omega)
  have hm1 : 0 + m = m := by omega
  have hv1 : (1 + 2 * (u + 3 - m)) + 2 * m = 2 * u + 7 := by omega
  rw [hm1, hv1] at h2
  have h12 := OrbitReachesPlus.trans_star h1 h2
  have h3 := drain_Modd_m0_v2 (u + 3 - m) (0 + 2 * m) 1 1 z (by omega)
  have h123 := OrbitReachesPlus.trans_star h12 h3
  have hu3 : 0 + 2 * m + 2 * (u + 3 - m) = 2 * u + 6 := by omega
  rw [hu3] at h123
  have h4 := rule_Modd_m0_v1_y1 (2 * u + 6) z
  have ha_out : 2 * (2 * u + 6) + z + 9 = 4 * u + z + 21 := by omega
  rw [ha_out] at h4
  exact OrbitReachesPlus.trans h123 h4

theorem pass0_Modd (y z : ℕ) :
    OrbitReachesPlus next (cfg_Modd 2 0 1 (y + 3) z) (cfg_Modd 10 0 1 y z) :=
  finish_pass_Modd 0 0 y z (by omega)

theorem single_pass_Modd_pos (e y z : ℕ) :
    OrbitReachesPlus next
      (cfg_Modd (6 * 2 ^ e - 2) 0 1 (y + e + 3) z)
      (cfg_Modd (6 * 2 ^ (e + 1) - 2) 0 1 y z) := by
  have hk : 6 * 2 ^ e ≥ e + 6 := six_pow2_ge_linear e
  have h1 := exp_step_Modd_exact e (e + 4) (y + 3) z
  have hm_in : (e + 4) + (6 * 2 ^ e - 6 - e) = 6 * 2 ^ e - 2 := by omega
  have hy_in : (y + 3) + e = y + e + 3 := by omega
  rw [hm_in, hy_in] at h1
  have hm_mid : e + 4 = (e + 2) + 2 := by omega
  rw [hm_mid] at h1
  have h2 := finish_pass_Modd (e + 2) (6 * 2 ^ e - 6) y z (by omega)
  have hu_out : 2 * (6 * 2 ^ e - 6) + 10 = 6 * 2 ^ (e + 1) - 2 := by
    have hpow : 6 * 2 ^ (e + 1) = (6 * 2 ^ e) * 2 := by rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega
  rw [hu_out] at h2
  exact OrbitReachesStar.trans_plus h1 h2

private theorem tri_succ (e : ℕ) :
    (e + 1) * (e + 6) / 2 = e * (e + 5) / 2 + (e + 3) := by
  have h1 : (e + 1) * (e + 6) = e * (e + 5) + e + (e + 6) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_succ]
  have h : (e + 1) * (e + 6) = e * (e + 5) + (e + 3) * 2 := by omega
  rw [h, Nat.add_mul_div_right _ _ (by decide : 0 < 2)]

private theorem two_mul_tri (E : ℕ) : 2 * (E * (E + 5) / 2) = E * (E + 5) := by
  induction E with
  | zero => rfl
  | succ e ih =>
    have h0 : (e + 1) * (e + 6) = e * (e + 5) + e + (e + 6) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_succ]
    have h1 : e + 1 + 5 = e + 6 := rfl
    rw [h1, tri_succ, Nat.mul_add, ih]
    omega

theorem multi_pass_Modd_pos (E y z : ℕ) (hE : E ≥ 1) :
    OrbitReachesPlus next
      (cfg_Modd 2 0 1 (y + E * (E + 5) / 2) z)
      (cfg_Modd (6 * 2 ^ E - 2) 0 1 y z) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hE
  clear hE
  induction d generalizing y with
  | zero =>
    have h0 : y + 1 * (1 + 5) / 2 = y + 3 := by omega
    have h1 : 6 * 2 ^ 1 - 2 = 10 := by decide
    rw [h0, h1]
    exact pass0_Modd y z
  | succ d ih =>
    have htri := tri_succ (d + 1)
    have hy : y + (d + 1 + 1) * (d + 1 + 6) / 2 =
        (y + (d + 1) + 3) + (d + 1) * (d + 1 + 5) / 2 := by omega
    rw [hy]
    have h1 := ih (y + (d + 1) + 3)
    have h2 := single_pass_Modd_pos (d + 1) y z
    exact OrbitReachesPlus.trans h1 h2

theorem exit_Modd_y1 (E z : ℕ) :
    OrbitReachesPlus next
      (cfg_Modd (6 * 2 ^ E - 2) 0 1 1 z)
      (cfg_D1 (12 * 2 ^ E - 7) 0 (z + 7)) := by
  have hk := six_pow2_ge_linear E
  have hm : 6 * 2 ^ E - 2 = (6 * 2 ^ E - 4) + 2 := by omega
  rw [hm]
  have h1 := rule_Modd_m2_v1 (6 * 2 ^ E - 4) 0 0 z
  rw [cfg_Modd_y0_eq_D1] at h1
  have ha : 2 * (6 * 2 ^ E - 4) + 1 = 12 * 2 ^ E - 7 := by omega
  have hv : 2 * 0 + 7 + z = z + 7 := by omega
  rw [ha, hv] at h1
  exact h1

theorem exit_Modd_mid (E y z : ℕ) (hy1 : y ≥ 2) (hy2 : y ≤ E + 1) :
    OrbitReachesPlus next
      (cfg_Modd (6 * 2 ^ E - 2) 0 1 y z)
      (cfg_D1 (12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3) 0 (12 * 2 ^ (y - 1) + z - 5)) := by
  let r := y - 1
  have hrE : r ≤ E := by omega
  have hpow_ge : 6 * 2 ^ E ≥ 6 * 2 ^ r := by
    have hsub : E = r + (E - r) := by omega
    rw [hsub, Nat.pow_add, ← Nat.mul_assoc]
    exact mul_pow2_ge (6 * 2 ^ r) (E - r)
  have hlin_r : 6 * 2 ^ r ≥ r + 6 := six_pow2_ge_linear r
  let m_rem := 6 * 2 ^ E - 6 * 2 ^ r + r + 4
  have h1 := exp_step_Modd_exact r m_rem 1 z
  have hm_in : m_rem + (6 * 2 ^ r - 6 - r) = 6 * 2 ^ E - 2 := by dsimp [m_rem]; omega
  have hy_in : 1 + r = y := by dsimp [r]; omega
  rw [hm_in, hy_in] at h1
  have hm_mid : m_rem = (m_rem - 2) + 2 := by dsimp [m_rem]; omega
  rw [hm_mid] at h1
  have h2 := rule_Modd_m2_v1 (m_rem - 2) (6 * 2 ^ r - 6) 0 z
  rw [cfg_Modd_y0_eq_D1] at h2
  have ha_out : 2 * (m_rem - 2) + 1 = 12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3 := by
    dsimp [m_rem, r]; omega
  have hv_out : 2 * (6 * 2 ^ r - 6) + 7 + z = 12 * 2 ^ (y - 1) + z - 5 := by
    dsimp [r]; omega
  rw [ha_out, hv_out] at h2
  exact OrbitReachesStar.trans_plus h1 h2

theorem exit_Modd_yE2 (E z : ℕ) :
    OrbitReachesPlus next
      (cfg_Modd (6 * 2 ^ E - 2) 0 1 (E + 2) z)
      (cfg_D1 (12 * 2 ^ (E + 1) + z - 3) 0 0) := by
  have hk : 6 * 2 ^ E ≥ E + 6 := six_pow2_ge_linear E
  have h1 := exp_step_Modd_exact E (E + 4) 2 z
  have hm_in : (E + 4) + (6 * 2 ^ E - 6 - E) = 6 * 2 ^ E - 2 := by omega
  have hy_in : 2 + E = E + 2 := by omega
  rw [hm_in, hy_in] at h1
  have hm_mid : E + 4 = (E + 2) + 2 := by omega
  rw [hm_mid] at h1
  have h2 := finish_exit_Modd_y2 (E + 2) (6 * 2 ^ E - 6) z (by omega)
  have ha_out : 4 * (6 * 2 ^ E - 6) + z + 21 = 12 * 2 ^ (E + 1) + z - 3 := by
    have hpow : 12 * 2 ^ (E + 1) = (6 * 2 ^ E) * 4 := by
      rw [Nat.pow_succ]
      omega
    omega
  rw [ha_out] at h2
  exact OrbitReachesStar.trans_plus h1 h2

theorem odd_v1_ge_a1_reload (m kv : ℕ) (h : m ≤ kv) :
    OrbitReachesPlus next (cfg_D1 (2 * m + 1) 0 (2 * kv + 1)) (cfg_D1 (4 * kv + 8) 0 0) := by
  have h1 := drain_D1_v2 m 0 0 (1 + 2 * (kv - m)) (by omega)
  have ha : 0 + 2 * m + 1 = 2 * m + 1 := by omega
  have hv : (1 + 2 * (kv - m)) + 2 * m = 2 * kv + 1 := by omega
  have ha0 : 0 + 1 = 1 := rfl
  rw [ha, hv, ha0] at h1
  have h2 := drain_D1_a1_v2 (kv - m) (0 + 2 * m) 1 (by omega)
  have h12 := OrbitReachesStar.trans h1 h2
  have hu2 : 0 + 2 * m + 2 * (kv - m) = 2 * kv := by omega
  rw [hu2] at h12
  have h3 : OrbitReachesPlus next (cfg_D1 1 (2 * kv) 1) (cfg_D1 (4 * kv + 8) 0 0) := by
    rcases kv with _ | kv
    · exact ⟨1, by decide, rfl⟩
    · dsimp [cfg_D1]
      have h_step1 : next (.stA 1 (2 * (kv + 1)) 0) = some (.stA 1 (2 * kv + 1) 1) := by
        have hk_eq : 2 * (kv + 1) = (2 * kv + 1) + 1 := by omega
        rw [hk_eq]; rfl
      have h_step2 : next (.stA 1 (2 * kv + 1) 1) = some (.stA (4 * (kv + 1) + 8 - 2) 0 3) := by
        have hb_eq : 2 * (2 * kv + 1) + 8 = 4 * (kv + 1) + 8 - 2 := by omega
        rw [← hb_eq]; rfl
      exact OrbitReachesPlus.head h_step1 (OrbitReachesStar.single h_step2)
  exact OrbitReachesStar.trans_plus h12 h3

theorem odd_drain_v1 (ma kv : ℕ) (hma : ma ≥ 1) :
    OrbitReachesPlus next
      (cfg_D1 (2 * ma + 2 * kv + 3) 0 (2 * kv + 1))
      (cfg_D1 (2 * ma + 1) (2 * kv + 1) 0) := by
  have h1 := drain_D1_v2 kv (2 * ma + 2) 0 1 (by omega)
  have ha : (2 * ma + 2) + 2 * kv + 1 = 2 * ma + 2 * kv + 3 := by omega
  have hv : 1 + 2 * kv = 2 * kv + 1 := by omega
  have ha2 : (2 * ma + 2) + 1 = 2 * ma + 3 := by omega
  have hu2 : 0 + 2 * kv = 2 * kv := by omega
  rw [ha, hv, ha2, hu2] at h1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hma
  have h2 : OrbitReachesPlus next (cfg_D1 (2 * (d + 1) + 3) (2 * kv) 1)
      (cfg_D1 (2 * (d + 1) + 1) (2 * kv + 1) 0) := by
    rcases kv with _ | kv
    · dsimp [cfg_D1]
      have hb1 : 2 * (d + 1) + 3 = (2 * d) + 5 := by omega
      have hb2 : 2 * (d + 1) + 1 - 2 = (2 * d) + 1 := by omega
      rw [hb1, hb2]
      exact ⟨1, by decide, rfl⟩
    · dsimp [cfg_D1]
      have hb1 : 2 * (d + 1) + 3 = (2 * d) + 5 := by omega
      have hk1 : 2 * (kv + 1) = (2 * kv + 1) + 1 := by omega
      have hb2 : 2 * (d + 1) + 1 - 2 = (2 * d) + 1 := by omega
      have hc2 : 2 * (2 * (kv + 1) + 1) + 3 = 2 * (2 * kv + 1) + 7 := by omega
      rw [hc2, hb1, hk1, hb2]
      exact ⟨2, by decide, rfl⟩
  exact OrbitReachesStar.trans_plus h1 h2

theorem odd_rem_ge3_reload (m u : ℕ) (hm : m ≤ u + 2) :
    OrbitReachesPlus next (cfg_D1 (2 * m + 3) u 0) (cfg_D1 (4 * u + 14) 0 0) := by
  have h_in : cfg_D1 (2 * m + 3) u 0 = cfg_D1 (2 * m + 1) 0 (2 * u + 4) := by
    dsimp [cfg_D1]
    have h1 : 2 * m + 3 - 2 = 2 * m + 1 := by omega
    rw [h1]
  rw [h_in]
  have h_cases : m = u + 2 ∨ m ≤ u + 1 := by omega
  rcases h_cases with rfl | hm1
  · have h1 := drain_D1_v2 (u + 1) 2 0 2 (by omega)
    have ha : 2 + 2 * (u + 1) + 1 = 2 * (u + 2) + 1 := by omega
    have hv : 2 + 2 * (u + 1) = 2 * u + 4 := by omega
    have ha2 : 2 + 1 = 3 := rfl
    have hu2 : 0 + 2 * (u + 1) = 2 * u + 2 := by omega
    rw [ha, hv, ha2, hu2] at h1
    have h2 : next (cfg_D1 3 (2 * u + 2) 2) = some (cfg_D1 (4 * u + 14) 0 0) := by
      dsimp [cfg_D1]
      have hb : 2 * (2 * u + 2) + 8 = 4 * u + 14 - 2 := by omega
      rw [← hb]; rfl
    exact OrbitReachesStar.trans_plus h1 (OrbitReachesPlus.single h2)
  · have h1 := drain_D1_v2 m 0 0 (2 + 2 * (u + 1 - m)) (by omega)
    have ha : 0 + 2 * m + 1 = 2 * m + 1 := by omega
    have hv : (2 + 2 * (u + 1 - m)) + 2 * m = 2 * u + 4 := by omega
    have ha2 : 0 + 1 = 1 := rfl
    rw [ha, hv, ha2] at h1
    have h2 := drain_D1_a1_v2 (u + 1 - m) (0 + 2 * m) 2 (by omega)
    have h12 := OrbitReachesStar.trans h1 h2
    have hu2 : 0 + 2 * m + 2 * (u + 1 - m) = 2 * u + 2 := by omega
    rw [hu2] at h12
    have h3 : next (cfg_D1 1 (2 * u + 2) 2) = some (cfg_D1 (4 * u + 14) 0 0) := by
      dsimp [cfg_D1]
      have hb : 2 * (2 * u + 2) + 8 = 4 * u + 14 - 2 := by omega
      rw [← hb]; rfl
    exact OrbitReachesStar.trans_plus h12 (OrbitReachesPlus.single h3)

theorem era_mid_ge3_step (a0 n k0 z E y ma kv r m_rem2 A_next : ℕ)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : k0 ≥ 1)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : E ≥ 1)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2 * y)
    (hy1 : y ≥ 2)
    (hy2 : y ≤ E + 1)
    (ha1 : 12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3 = 2 * ma + 2 * kv + 3)
    (hv1 : 12 * 2 ^ (y - 1) + z - 5 = 2 * kv + 1)
    (ha2 : 2 * ma + 1 = (2 * m_rem2 + 2) + (2 * (2 * kv + 5) * 2 ^ r - 2 * (2 * kv + 5) - 2 * r) +
      1)
    (hm2 : m_rem2 ≤ (2 * kv + 5) * 2 ^ r - 2)
    (hAnext : A_next = 4 * ((2 * kv + 5) * 2 ^ r - 4) + 14) :
    OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) := by
  have h1 := exp_step_D1_exact n (2 * k0 + 3) 0 (by omega)
  have hA_in : (2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1 = a0 := by omega
  have hA_mid : (2 * k0 + 3) + 1 = 2 * k0 + 4 := by omega
  have hu_mid : (0 + 4) * 2 ^ n - 4 = 4 * 2 ^ n - 4 := by omega
  rw [hA_in, hA_mid, hu_mid] at h1
  have h2 := enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz
  have h12 := OrbitReachesStar.trans_plus h1 h2
  have htri := two_mul_tri E
  have hy_split : 2 * k0 = y + E * (E + 5) / 2 := by omega
  rw [hy_split] at h12
  have h3 := multi_pass_Modd_pos E y z hE
  have h123 := OrbitReachesPlus.trans h12 h3
  have h4 := exit_Modd_mid E y z hy1 hy2
  rw [ha1, hv1] at h4
  have h1234 := OrbitReachesPlus.trans h123 h4
  have h5 := odd_drain_v1 ma kv (by omega)
  have h12345 := OrbitReachesPlus.trans h1234 h5
  rw [ha2] at h12345
  have h6 := exp_step_D1_exact r (2 * m_rem2 + 2) (2 * kv + 1) (by omega)
  have hu6 : (2 * kv + 1 + 4) = 2 * kv + 5 := by omega
  have ha6 : (2 * m_rem2 + 2) + 1 = 2 * m_rem2 + 3 := by omega
  rw [hu6, ha6] at h6
  have h123456 := OrbitReachesPlus.trans_star h12345 h6
  have h7 := odd_rem_ge3_reload m_rem2 ((2 * kv + 5) * 2 ^ r - 4) (by omega)
  rw [← hAnext] at h7
  exact OrbitReachesPlus.trans h123456 h7

theorem era_yE2_ge3_step (a0 n k0 z E r m_rem2 A_next : ℕ)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : k0 ≥ 1)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : E ≥ 1)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2 * (E + 2))
    (ha1 : 12 * 2 ^ (E + 1) + z - 3 = (2 * m_rem2 + 2) + (8 * 2 ^ r - 8 - 2 * r) + 1)
    (hm2 : m_rem2 ≤ 4 * 2 ^ r - 2)
    (hAnext : A_next = 4 * (4 * 2 ^ r - 4) + 14) :
    OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) := by
  have h1 := exp_step_D1_exact n (2 * k0 + 3) 0 (by omega)
  have hA_in : (2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1 = a0 := by omega
  have hA_mid : (2 * k0 + 3) + 1 = 2 * k0 + 4 := by omega
  have hu_mid : (0 + 4) * 2 ^ n - 4 = 4 * 2 ^ n - 4 := by omega
  rw [hA_in, hA_mid, hu_mid] at h1
  have h2 := enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz
  have h12 := OrbitReachesStar.trans_plus h1 h2
  have htri := two_mul_tri E
  have hy_split : 2 * k0 = (E + 2) + E * (E + 5) / 2 := by omega
  rw [hy_split] at h12
  have h3 := multi_pass_Modd_pos E (E + 2) z hE
  have h123 := OrbitReachesPlus.trans h12 h3
  have h4 := exit_Modd_yE2 E z
  rw [ha1] at h4
  have h1234 := OrbitReachesPlus.trans h123 h4
  have h5 := exp_step_D1_exact r (2 * m_rem2 + 2) 0 (by omega)
  have hu5 : (0 + 4) = 4 := rfl
  have ha5 : (2 * m_rem2 + 2) + 1 = 2 * m_rem2 + 3 := by omega
  rw [hu5, ha5] at h5
  have h12345 := OrbitReachesPlus.trans_star h1234 h5
  have h6 := odd_rem_ge3_reload m_rem2 (4 * 2 ^ r - 4) (by omega)
  rw [← hAnext] at h6
  exact OrbitReachesPlus.trans h12345 h6

theorem era_mid_v1_ge_a1_step (a0 n k0 z E y m kv A_next : ℕ)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : k0 ≥ 1)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : E ≥ 1)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2 * y)
    (hy1 : y ≥ 2)
    (hy2 : y ≤ E + 1)
    (ha1 : 12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3 = 2 * m + 1)
    (hv1 : 12 * 2 ^ (y - 1) + z - 5 = 2 * kv + 1)
    (hm : m ≤ kv)
    (hAnext : A_next = 4 * kv + 8) :
    OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) := by
  have h1 := exp_step_D1_exact n (2 * k0 + 3) 0 (by omega)
  have hA_in : (2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1 = a0 := by omega
  have hA_mid : (2 * k0 + 3) + 1 = 2 * k0 + 4 := by omega
  have hu_mid : (0 + 4) * 2 ^ n - 4 = 4 * 2 ^ n - 4 := by omega
  rw [hA_in, hA_mid, hu_mid] at h1
  have h2 := enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz
  have h12 := OrbitReachesStar.trans_plus h1 h2
  have htri := two_mul_tri E
  have hy_split : 2 * k0 = y + E * (E + 5) / 2 := by omega
  rw [hy_split] at h12
  have h3 := multi_pass_Modd_pos E y z hE
  have h123 := OrbitReachesPlus.trans h12 h3
  have h4 := exit_Modd_mid E y z hy1 hy2
  rw [ha1, hv1] at h4
  have h1234 := OrbitReachesPlus.trans h123 h4
  have h5 := odd_v1_ge_a1_reload m kv hm
  rw [← hAnext] at h5
  exact OrbitReachesPlus.trans h1234 h5

theorem era_y1_v1_ge_a1_step (a0 n k0 z E m kv A_next : ℕ)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : k0 ≥ 1)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : E ≥ 1)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2)
    (ha1 : 12 * 2 ^ E - 7 = 2 * m + 1)
    (hv1 : z + 7 = 2 * kv + 1)
    (hm : m ≤ kv)
    (hAnext : A_next = 4 * kv + 8) :
    OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) := by
  have h1 := exp_step_D1_exact n (2 * k0 + 3) 0 (by omega)
  have hA_in : (2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1 = a0 := by omega
  have hA_mid : (2 * k0 + 3) + 1 = 2 * k0 + 4 := by omega
  have hu_mid : (0 + 4) * 2 ^ n - 4 = 4 * 2 ^ n - 4 := by omega
  rw [hA_in, hA_mid, hu_mid] at h1
  have h2 := enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz
  have h12 := OrbitReachesStar.trans_plus h1 h2
  have htri := two_mul_tri E
  have hy_split : 2 * k0 = 1 + E * (E + 5) / 2 := by omega
  rw [hy_split] at h12
  have h3 := multi_pass_Modd_pos E 1 z hE
  have h123 := OrbitReachesPlus.trans h12 h3
  have h4 := exit_Modd_y1 E z
  rw [ha1, hv1] at h4
  have h1234 := OrbitReachesPlus.trans h123 h4
  have h5 := odd_v1_ge_a1_reload m kv hm
  rw [← hAnext] at h5
  exact OrbitReachesPlus.trans h1234 h5

private theorem sq_sub3_add2 (a0 : ℕ) (hA : a0 ≥ 3) :
    (a0 - 3) * (a0 + 2) + a0 + 6 = a0 * a0 := by
  have h1 : (a0 - 3) * (a0 + 2) = (a0 - 3) * a0 + (a0 - 3) * 2 := Nat.mul_add (a0 - 3) a0 2
  have h2 : (a0 - 3) * a0 + 3 * a0 = a0 * a0 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hA]
  omega

private theorem sq_add (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
  omega

private theorem mul_coef (c1 c2 x y : ℕ) : (c1 * x) * (c2 * y) = (c1 * c2) * (x * y) := by
  rw [Nat.mul_assoc c1 x (c2 * y), ← Nat.mul_assoc x c2 y, Nat.mul_comm x c2,
      Nat.mul_assoc c2 x y, ← Nat.mul_assoc c1 c2 (x * y)]

theorem era0_590 : OrbitReachesPlus next start (cfg_D1 30 0 0) :=
  ⟨16, by decide, start_step16⟩

theorem era1_590 : OrbitReachesPlus next (cfg_D1 30 0 0) (cfg_D1 126 0 0) :=
  era_yE2_ge3_step 30 2 3 20 1 3 6 126
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem era2_590 : OrbitReachesPlus next (cfg_D1 126 0 0) (cfg_D1 316 0 0) :=
  era_mid_v1_ge_a1_step 126 4 5 112 2 3 4 77 316
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem era3_590 : OrbitReachesPlus next (cfg_D1 316 0 0) (cfg_D1 16382 0 0) :=
  era_yE2_ge3_step 316 5 37 176 9 10 2147 16382
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem era4_590 : OrbitReachesPlus next (cfg_D1 16382 0 0) (cfg_D1 32766 0 0) :=
  era_yE2_ge3_step 16382 11 12 16354 4 11 189 32766
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem era5_590 : OrbitReachesPlus next (cfg_D1 32766 0 0) (cfg_D1 65492 0 0) :=
  era_y1_v1_ge_a1_step 32766 12 13 32736 5 188 16371 65492
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)

def cfg_Tower (M k : ℕ) : State :=
  cfg_D1 (12 * 2 ^ (2 * M - 3) + 2 * k * 2 ^ M - 2) 0 0

def TowerInv (M k : ℕ) : Prop :=
  M ≥ 128 ∧ k ≥ 4 ∧ 3 * M ≤ k * k ∧ 4 * (k * k) ≤ 2 ^ (M - 2)

set_option maxHeartbeats 1000000 in
-- Increased heartbeat limit for heavy kernel/tactic evaluation.
theorem era6_590 : OrbitReachesPlus next (cfg_D1 65492 0 0) (cfg_Tower 128 9216) := by
  unfold cfg_Tower
  exact era_mid_ge3_step 65492 12 16376 10 253 115
    (6 * 2 ^ 253 - 12 * 2 ^ 114 + 113)
    (6 * 2 ^ 114 + 2)
    137
    (3 * 2 ^ 253 - 8 * 2 ^ 137 - 174224571863520493293247799005065324265214)
    (12 * 2 ^ (2 * 128 - 3) + 2 * 9216 * 2 ^ 128 - 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem start_reaches_tower_590 :
    OrbitReachesPlus next start (cfg_Tower 128 9216) := by
  have h1 := OrbitReachesPlus.trans era0_590 era1_590
  have h2 := OrbitReachesPlus.trans h1 era2_590
  have h3 := OrbitReachesPlus.trans h2 era3_590
  have h4 := OrbitReachesPlus.trans h3 era4_590
  have h5 := OrbitReachesPlus.trans h4 era5_590
  exact OrbitReachesPlus.trans h5 era6_590

theorem tower_inv_init_590 : TowerInv 128 9216 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

private theorem four_mul_assoc (a b c : ℕ) :
    4 * (a * (b * c)) = 2 * (a * b) * (c * 2) := by
  have h1 : 4 * (a * (b * c)) = 4 * (a * b) * c := by
    rw [← Nat.mul_assoc a b c, ← Nat.mul_assoc 4 (a * b) c]
  have h2 : 2 * (a * b) * (c * 2) = (2 * (a * b) * 2) * c := by
    rw [Nat.mul_comm c 2, ← Nat.mul_assoc (2 * (a * b)) 2 c]
  have h3 : 4 * (a * b) = 2 * (a * b) * 2 := by omega
  rw [h1, h2, h3]

set_option maxHeartbeats 1000000 in
-- Increased heartbeat limit for heavy kernel/tactic evaluation.
theorem tower_step_core
    (M k K2 P KP P2 n k0 kz z E y Q r R QR KZR kv ma m_rem2 M' g k' a0 A_next : ℕ)
    (hM : M ≥ 128) (hk : k ≥ 4) (h3M : 3 * M ≤ k * k) (h4k2 : 4 * (k * k) ≤ 2 ^ (M - 2))
    (hK2_def : K2 = k * k)
    (hP_def : P = 2 ^ (M - 2))
    (hKP_def : KP = k * P)
    (hP2_def : P2 = P * P)
    (hn_def : n = 2 * M - 3)
    (hk0_def : k0 = 4 * P2 + 4 * KP + 2 * M - 2)
    (hkz_def : kz = 4 * P2 - 4 * KP - 2 * M - 1)
    (hz_def : z = 2 * kz)
    (hE_def : E = 4 * P + 2 * k - 3)
    (hy_def : y = 2 * P - 2 * K2 + k + 4 * M - 1)
    (hQ_def : Q = 2 ^ (y - 1))
    (hr_def : r = E - 1 - y)
    (hR_def : R = 2 ^ r)
    (hQR_def : QR = Q * R)
    (hKZR_def : KZR = (2 * kz - 1) * R)
    (hkv_def : kv = 6 * Q + kz - 3)
    (hma_def : ma = 24 * QR - 12 * Q - kz + y + 3)
    (hm_rem2_def : m_rem2 = 12 * QR - KZR + kz + E)
    (hM'_def : M' = 2 * P + k)
    (hg_def : g = 2 * K2 - 4 * M - 1)
    (hk'_def : k' = (z - 1) * 2 ^ (g - 1))
    (hA_def : a0 = 12 * 2 ^ (2 * M - 3) + 2 * k * 2 ^ M - 2)
    (hAnext_def : A_next = 12 * 2 ^ (2 * M' - 3) + 2 * k' * 2 ^ M' - 2) :
    OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) ∧ TowerInv M' k' := by
  have hK2_ge_3M : K2 ≥ 3 * M := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hK2_ge_4k : K2 ≥ 4 * k := by
    have h1 := Nat.mul_le_mul_right k hk
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hP_ge_4K2 : P ≥ 4 * K2 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hP_lin : P ≥ 2 * (M - 2) + 6 := by
    rw [hP_def]
    exact pow2_ge_two_mul (M - 2) (by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega)
  have hP_pos : P ≥ 1 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hKP_ge_4P : KP ≥ 4 * P := by
    have h1 := Nat.mul_le_mul_right P hk
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hP_ge_16k : P ≥ 16 * k := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hP2_ge_16KP : P2 ≥ 16 * KP := by
    have h1 := Nat.mul_le_mul_right P hP_ge_16k
    have h2 : 16 * k * P = 16 * KP := by rw [hKP_def, Nat.mul_assoc]
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have h2M : 2 ^ M = 4 * P := by
    have hsub : M = (M - 2) + 2 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    rw [hsub, Nat.pow_add, ← hP_def]
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have h2k2M : 2 * k * 2 ^ M = 8 * KP := by
    rw [h2M, hKP_def, Nat.mul_assoc 2 k (4 * P), ← Nat.mul_assoc k 4 P, Nat.mul_comm k 4,
        Nat.mul_assoc 4 k P, ← Nat.mul_assoc 2 4 (k * P)]
  have h2M3 : 2 ^ (2 * M - 3) = 2 * P2 := by
    have hsub : 2 * M - 3 = (M - 2) + (M - 2) + 1 := by
      clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    rw [hsub, Nat.pow_add, Nat.pow_add, ← hP_def, ← hP2_def]
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hy_ge_P : y ≥ P + 4 * M - 1 := by
    clear hma_def hm_rem2_def hA_def hAnext_def; omega
  have hy_le_E : y + 1 ≤ E := by clear hma_def hm_rem2_def hA_def hAnext_def; omega
  have hQR : 2 ^ E = 4 * QR := by
    have hsub : E = (y - 1) + r + 2 := by clear hma_def hm_rem2_def hA_def hAnext_def; omega
    rw [hsub, Nat.pow_add, Nat.pow_add, ← hQ_def, ← hR_def, ← hQR_def]
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hQ_ge_16P2 : Q ≥ 16 * P2 := by
    have hy_exp : (M - 2) + (M - 2) + 4 ≤ y - 1 := by
      clear hma_def hm_rem2_def hA_def hAnext_def; omega
    have hmono := pow2_mono hy_exp
    rw [Nat.pow_add, Nat.pow_add, ← hP_def, ← hP2_def, ← hQ_def] at hmono
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hR_ge : R ≥ 2 * r + 6 := by
    rw [hR_def]
    exact pow2_ge_two_mul r (by clear hma_def hm_rem2_def hA_def hAnext_def; omega)
  have hQR_ge_2Q : QR ≥ 2 * Q := by
    have h1 : R ≥ 2 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    have h2 := Nat.mul_le_mul_left Q h1
    have h3 : Q * 2 = 2 * Q := Nat.mul_comm Q 2
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hKZR_ge : KZR ≥ 2 * kz - 1 := by
    have h1 : R ≥ 1 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    have h2 := Nat.mul_le_mul_left (2 * kz - 1) h1
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have h6QR_ge_KZR : 6 * QR ≥ KZR := by
    have h1 : 6 * Q ≥ 2 * kz - 1 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    have h2 := Nat.mul_le_mul_right R h1
    have h3 : 6 * Q * R = 6 * QR := by rw [hQR_def, Nat.mul_assoc]
    clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hkv5 : 2 * kv + 5 = 12 * Q + (2 * kz - 1) := by
      clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
  have hkvR : (2 * kv + 5) * R = 12 * QR + KZR := by
    rw [hkv5, Nat.add_mul, Nat.mul_assoc, ← hQR_def, ← hKZR_def]
  refine ⟨?_, ?_⟩
  · apply era_mid_ge3_step a0 n k0 z E y ma kv r m_rem2 A_next
    · rw [hA_def, hn_def, h2M3, h2k2M]; clear hy_def hma_def hm_rem2_def hAnext_def; omega
    · clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    · rw [hn_def, h2M3]; clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    · clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    · have hA_sq := sq_sub3_add2 (4 * P + 2 * k)
        (by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega)
      have h_e : (4 * P + 2 * k) - 3 = E := hE_def.symm
      have h_e5 : (4 * P + 2 * k) + 2 = E + 5 := by
        clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
      rw [h_e, h_e5, sq_add (4 * P) (2 * k), mul_coef 4 4 P P, mul_coef 4 2 P k,
          mul_coef 2 2 k k, Nat.mul_comm P k, ← hP2_def, ← hKP_def, ← hK2_def] at hA_sq
      clear hma_def hm_rem2_def hA_def hAnext_def; omega
    · clear hma_def hm_rem2_def hA_def hAnext_def; omega
    · clear hma_def hm_rem2_def hA_def hAnext_def; omega
    · rw [hQR, ← hQ_def]; clear hy_def hm_rem2_def hA_def hAnext_def; omega
    · rw [← hQ_def]; clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
    · rw [← hR_def]
      have h2kvR : 2 * (2 * kv + 5) * R = 2 * (12 * QR + KZR) := by
        rw [Nat.mul_assoc]
        exact congrArg (2 * ·) hkvR
      rw [h2kvR, hkv5]
      clear hK2_def hP_def hKP_def hP2_def hQ_def hR_def hQR_def hKZR_def hkvR h2kvR hk'_def
        hy_def hA_def hAnext_def
      omega
    · rw [← hR_def, hkvR]
      clear hK2_def hP_def hKP_def hP2_def hQ_def hR_def hQR_def hKZR_def hk'_def hy_def hma_def
        hA_def hAnext_def
      omega
    · rw [hAnext_def, ← hR_def, hkvR]
      have h_rhs : 4 * (12 * QR + KZR - 4) + 14 = 12 * (4 * QR) + 4 * KZR - 2 := by
        clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
      rw [h_rhs, ← hQR]
      have hE_M' : E = 2 * M' - 3 := by clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
      have hr_split : r = (g - 1) + (M' - 1) := by
        clear hma_def hm_rem2_def hA_def hAnext_def; omega
      have h4R : 4 * KZR = 2 * k' * 2 ^ M' := by
        have hM'1 : M' = (M' - 1) + 1 := by
          clear hy_def hma_def hm_rem2_def hA_def hAnext_def; omega
        have hpowM' : 2 ^ M' = 2 ^ (M' - 1) * 2 :=
          (congrArg (2 ^ ·) hM'1).trans (Nat.pow_succ 2 (M' - 1))
        have hpowR : R = 2 ^ (g - 1) * 2 ^ (M' - 1) := by rw [hR_def, hr_split, Nat.pow_add]
        rw [hKZR_def, hpowR, hk'_def, hz_def, hpowM']
        exact four_mul_assoc (2 * kz - 1) (2 ^ (g - 1)) (2 ^ (M' - 1))
      rw [hE_M', h4R]
  · clear hy_def hma_def hm_rem2_def hA_def hAnext_def
    have hg_ge : g - 1 ≥ M := by omega
    have h2g_ge_M' : 2 ^ (g - 1) ≥ M' := by
      have h1 : 2 ^ (g - 1) ≥ 2 ^ M := pow2_mono hg_ge
      rw [h2M] at h1
      omega
    have hz1_ge : z - 1 ≥ 3 := by omega
    have hk'_ge_3M' : k' ≥ 3 * M' := by
      rw [hk'_def]
      have hmul := Nat.mul_le_mul hz1_ge h2g_ge_M'
      omega
    have hk'_sq : k' * k' ≥ 3 * M' := by
      have h1 : k' * k' ≥ k' * 1 := Nat.mul_le_mul_left k' (by omega)
      omega
    refine ⟨by omega, by omega, hk'_sq, ?_⟩
    have hz_lt : z - 1 ≤ 2 ^ (2 * M - 1) := by
      have h2M1_exp : 2 * M - 1 = (2 * M - 3) + 2 := by omega
      rw [h2M1_exp, Nat.pow_add, h2M3]
      omega
    have hk'_le : k' ≤ 2 ^ (2 * K2 - 2) := by
      rw [hk'_def]
      have h1 : (z - 1) * 2 ^ (g - 1) ≤ 2 ^ (2 * M - 1) * 2 ^ (g - 1) :=
        Nat.mul_le_mul_right (2 ^ (g - 1)) hz_lt
      rw [← Nat.pow_add] at h1
      have hexp : (2 * M - 1) + (g - 1) ≤ 2 * K2 - 2 := by omega
      exact Nat.le_trans h1 (pow2_mono hexp)
    have h4k'2 : 4 * (k' * k') ≤ 2 ^ (4 * K2 - 2) := by
      have h1 : k' * k' ≤ 2 ^ (2 * K2 - 2) * 2 ^ (2 * K2 - 2) :=
        Nat.mul_le_mul hk'_le hk'_le
      have h2 : 4 * (k' * k') ≤ 2 ^ 2 * (2 ^ (2 * K2 - 2) * 2 ^ (2 * K2 - 2)) :=
        Nat.mul_le_mul_left 4 h1
      rw [← Nat.pow_add, ← Nat.pow_add] at h2
      have hexp : 2 + ((2 * K2 - 2) + (2 * K2 - 2)) = 4 * K2 - 2 := by omega
      rwa [hexp] at h2
    have hexp_M' : 4 * K2 - 2 ≤ M' - 2 := by omega
    exact Nat.le_trans h4k'2 (pow2_mono hexp_M')

theorem tower_step (M k : ℕ) (hinv : TowerInv M k) :
    ∃ M' k', OrbitReachesPlus next (cfg_Tower M k) (cfg_Tower M' k') ∧ TowerInv M' k' := by
  rcases hinv with ⟨hM, hk, h3M, h4k2⟩
  exact ⟨_, _, tower_step_core M k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hM hk h3M h4k2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl⟩

def InTowerSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ M k, cfg = encode (cfg_Tower M k) ∧ TowerInv M k

theorem init_reaches_tower_590 :
    (init []) [target_tm]⊢⁺ encode (cfg_Tower 128 9216) :=
  zPt init_reaches_start (orbitPlus_sound start_reaches_tower_590)

theorem tower_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : InTowerSystem cfg) :
    ∃ cfg', (cfg [target_tm]⊢⁺ cfg') ∧ InTowerSystem cfg' := by
  rcases h with ⟨M, k, rfl, hinv⟩
  obtain ⟨M', k', hstep, hinv'⟩ := tower_step M k hinv
  exact ⟨encode (cfg_Tower M' k'), orbitPlus_sound hstep, ⟨M', k', rfl, hinv'⟩⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact IsNotHalt.of_reachesPlus_invariant
    (zPs init_reaches_tower_590)
    ⟨128, 9216, rfl, tower_inv_init_590⟩
    tower_system_closed

private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC
