/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LD_1RC1RF_0RD1RA_1LE1RC_0LA0LD_0RC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LD_1RC1RF_0RD1RA_1LE1RC_0LA0LD_0RC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_1RC1RF_0RD1RA_1LE1RC_0LA0LD_0RCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LD_1RC1RF_0RD1RA_1LE1RC_0LA0LD_0RC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

@[simp] lemma zMz {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma z0i : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] lemma append_assoc (l₁ l₂ : zF) (s : zB) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp [ih]
@[simp] lemma zPz {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z0j {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl

lemma zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]
lemma z0Q {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, zSm tm c₁ c₂ h⟩
lemma zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c₁ c₂ c₃ n m hn hm⟩
lemma zSt_eq {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)} (h₁ : c₁ [target_tm]⊢* c₂) (heq : c₂ = c₃) :
    c₁ [target_tm]⊢* c₃ := heq ▸ h₁
lemma zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma z0R {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c₁ c₂ c₃ n m hn hm⟩
lemma zSpp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), zMt tm c₁ c₂ c₃ n m hn hm⟩
lemma z0T {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  z0R (z0Q tm c₁ c₂ h₁) h₂

macro "finish" : tactic =>
  `(tactic| (try simp only [append_cons, append_nil, List.cons_append, List.nil_append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, z0i, zDh, zDt]) <;> exists 0 <;> fail)
macro "step_tm" : tactic =>
  `(tactic| (try dsimp only [append_cons, append_nil]) <;> (try refine zPs ?_) <;>
    refine z0T (by (try simp only [append_cons, append_nil, Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [append_cons, append_nil, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z0i, zDh, zDt])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5)

abbrev W0 : zF := [0]
abbrev W1 : zF := [1]
abbrev stS : Fin 6 := D
abbrev stT : Fin 6 := C
abbrev stU : Fin 6 := A
abbrev stV : Fin 6 := A

@[simp]
def LC : List Nat → zB
  | [] => default
  | a :: l => ([0] : zF) +> ((W1 ^ a) +> LC l)


@[simp]
def RC : List Nat → zB
  | [] => default
  | a :: r => (W1 ^ a) +> (([0] : zF) +> RC r)

def S (l : List Nat) (b : Nat) (r : List Nat) : Cfg (Fin 2) (Fin 6) :=
  ((W1 ^ b) +> LC l) <{{stS}} (RC r)
def T (l : List Nat) (b : Nat) (r : List Nat) : Cfg (Fin 2) (Fin 6) :=
  ((W1 ^ b) +> LC l) {{stT}}> (RC r)
def U (l : List Nat) (b : Nat) (r : List Nat) : Cfg (Fin 2) (Fin 6) :=
  ((W1 ^ b) +> LC l) <{{stU}} (RC r)
def V (l : List Nat) (b : Nat) (r : List Nat) : Cfg (Fin 2) (Fin 6) :=
  ((W1 ^ b) +> LC l) {{stV}}> (RC r)

lemma Lblanks (l : List Nat) : LC l = LC (l ++ [0]) := by
  induction l with
  | nil => simp [LC, W1, z0i]
  | cons a l ih => simp only [LC, List.cons_append]; rw [← ih]

lemma Rblank (r : List Nat) : RC r = RC (r ++ [0]) := by
  induction r with
  | nil => simp [RC, W1, z0i]
  | cons a r ih => simp only [RC, List.cons_append]; rw [← ih]

lemma Sblankl (l : List Nat) (a : Nat) (r : List Nat) : S l a r = S (l ++ [0]) a r := by
  dsimp only [S]; rw [← Lblanks]
lemma Ublankl (l : List Nat) (a : Nat) (r : List Nat) : U l a r = U (l ++ [0]) a r := by
  dsimp only [U]; rw [← Lblanks]
lemma Sblankr (l : List Nat) (a : Nat) (r : List Nat) : S l a r = S l a (r ++ [0]) := by
  dsimp only [S]; rw [← Rblank]
lemma Tblankr (l : List Nat) (a : Nat) (r : List Nat) : T l a r = T l a (r ++ [0]) := by
  dsimp only [T]; rw [← Rblank]
lemma Ublankr (l : List Nat) (a : Nat) (r : List Nat) : U l a r = U l a (r ++ [0]) := by
  dsimp only [U]; rw [← Rblank]
lemma Vblankr (l : List Nat) (a : Nat) (r : List Nat) : V l a r = V l a (r ++ [0]) := by
  dsimp only [V]; rw [← Rblank]

lemma Sblankl0 (a : Nat) (r : List Nat) : S [] a r = S [0, 0] a r := by
  dsimp [S]; simp [LC, W1, z0i]
lemma Ublankl0 (a : Nat) (r : List Nat) : U [] a r = U [0] a r := by
  dsimp [U]; simp [LC, W1, z0i]
lemma Tblankr2 (l : List Nat) (a : Nat) : T l a [0, 0] = T l a [0, 0, 0] := by
  dsimp [T]; simp [RC, W1, z0i]

lemma Spos (l : List Nat) (a : Nat) (r : List Nat) :
    (S l (a + 1) r) [target_tm]⊢* (T l (a + 1) r) := by
  simp only [S, T, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Spos_progress (l : List Nat) (a : Nat) (r : List Nat) :
    (S l (a + 1) r) [target_tm]⊢⁺ (T l (a + 1) r) := by
  simp only [S, T, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Szero (l : List Nat) (a c : Nat) (r : List Nat) :
    (S ((a + 1) :: l) 0 (c :: r)) [target_tm]⊢* (S l a (0 :: (c + 1) :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Sedge (l : List Nat) (a c : Nat) (r : List Nat) :
    (S (0 :: a :: l) 0 (c :: r)) [target_tm]⊢* (U l a (0 :: (c + 1) :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Upos (l : List Nat) (a : Nat) (r : List Nat) :
    (U l (a + 1) r) [target_tm]⊢* (S l a (0 :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Uzero0 (l : List Nat) (a : Nat) (r : List Nat) :
    (U (a :: l) 0 (0 :: r)) [target_tm]⊢* (T l (a + 2) r) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Uzero1 (l : List Nat) (a : Nat) (r : List Nat) :
    (U (a :: l) 0 (1 :: r)) [target_tm]⊢* (T ((a + 2) :: l) 0 r) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Tzero (l : List Nat) (a c : Nat) (r : List Nat) :
    (T l a (0 :: 0 :: c :: r)) [target_tm]⊢* (U l a (0 :: (c + 1) :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Tmix (l : List Nat) (a c : Nat) (r : List Nat) :
    (T l a (0 :: (c + 1) :: r)) [target_tm]⊢* (T (a :: l) 1 (c :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Tpos (l : List Nat) (a c : Nat) (r : List Nat) :
    (T l a ((c + 1) :: r)) [target_tm]⊢* (V l (a + 1) (c :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Vpos (l : List Nat) (a c : Nat) (r : List Nat) :
    (V l a ((c + 1) :: r)) [target_tm]⊢* (S l a (0 :: c :: r)) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Vzero0 (l : List Nat) (a : Nat) (r : List Nat) :
    (V l a (0 :: 0 :: r)) [target_tm]⊢* (T l (a + 2) r) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma Vzero1 (l : List Nat) (a : Nat) (r : List Nat) :
    (V l a (0 :: 1 :: r)) [target_tm]⊢* (T ((a + 2) :: l) 0 r) := by
  simp only [S, T, U, V, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

lemma init_to_T : (init []) [target_tm]⊢* (T [] 2 []) := by
  simp only [init, Tape.mk₁, T, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]; execute

abbrev rep (x n : Nat) : List Nat := List.replicate n x

@[simp] lemma rep_zero (x : Nat) : rep x 0 = [] := rfl
@[simp] lemma rep_succ (x n : Nat) : rep x (n + 1) = x :: rep x n := rfl

lemma rep_snoc (x n : Nat) (l : List Nat) : rep x n ++ x :: l = rep x (n + 1) ++ l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep_succ, List.cons_append, ih]

lemma Tmixs (n : Nat) (l : List Nat) (a : Nat) (r : List Nat) :
    (T l a (0 :: (rep 1 (n + 1) ++ r))) [target_tm]⊢*
    (T (rep 1 n ++ a :: l) 1 (0 :: r)) := by
  induction n generalizing l a with
  | zero => exact Tmix l a 0 r
  | succ n ih =>
    have h1 := Tmix l a 0 (rep 1 (n + 1) ++ r)
    have h2 := ih (a :: l) 1
    rw [rep_snoc] at h2
    exact zSt h1 h2

lemma Szeros (n : Nat) (l : List Nat) (c : Nat) (r : List Nat) :
    (S (rep 1 (n + 1) ++ l) 0 (c :: r)) [target_tm]⊢*
    (S l 0 (0 :: (rep 1 n ++ (c + 1) :: r))) := by
  induction n generalizing c r with
  | zero => exact Szero l 0 c r
  | succ n ih =>
    have h1 := Szero (rep 1 (n + 1) ++ l) 0 c r
    have h2 := ih 0 ((c + 1) :: r)
    rw [rep_snoc] at h2
    exact zSt h1 h2

lemma Triple (l : List Nat) (a c : Nat) (r : List Nat) :
    (T l a ((c + 3) :: r)) [target_tm]⊢* (T ((a + 1) :: l) 1 (c :: r)) :=
  zSt (Tpos l a (c + 2) r)
    (zSt (Vpos l (a + 1) (c + 1) r)
      (zSt (Spos l a (0 :: (c + 1) :: r))
        (Tmix l (a + 1) c r)))

lemma Triples (n : Nat) (l : List Nat) (a c : Nat) (r : List Nat) :
    (T l a (((n + 1) * 3 + c) :: r)) [target_tm]⊢*
    (T (rep 2 n ++ (a + 1) :: l) 1 (c :: r)) := by
  induction n generalizing l a with
  | zero =>
    rw [show (0 + 1) * 3 + c = c + 3 by omega]
    exact Triple l a c r
  | succ n ih =>
    rw [show (n + 1 + 1) * 3 + c = ((n + 1) * 3 + c) + 3 by omega]
    have h1 := Triple l a ((n + 1) * 3 + c) r
    have h2 := ih ((a + 1) :: l) 1
    rw [rep_snoc] at h2
    exact zSt h1 h2

lemma Pairs (n : Nat) (l r : List Nat) :
    (T l 0 (rep 1 (n * 2) ++ r)) [target_tm]⊢*
    (T (rep 3 n ++ l) 0 r) := by
  induction n generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [show (n + 1) * 2 = n * 2 + 2 by omega]
    have h1 := Tpos l 0 0 (1 :: (rep 1 (n * 2) ++ r))
    have h2 := Vzero1 l 1 (rep 1 (n * 2) ++ r)
    have h3 := ih (3 :: l)
    rw [rep_snoc] at h3
    exact zSt h1 (zSt h2 h3)

lemma CycleStep (a : Nat) (l : List Nat) (n c : Nat) (r : List Nat) :
    (S ((a + 1) :: l) 1 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l a (0 :: (rep 1 (n + 2) ++ 0 :: (c + 1) :: r))) := by
  have h1 := Spos ((a + 1) :: l) 0 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))
  have h2 := Tmixs n ((a + 1) :: l) 1 (0 :: c :: r)
  rw [rep_snoc] at h2
  have h3 := Tzero (rep 1 (n + 1) ++ (a + 1) :: l) 1 c r
  have h4 := Upos (rep 1 (n + 1) ++ (a + 1) :: l) 0 (0 :: (c + 1) :: r)
  have h5 := Szeros n ((a + 1) :: l) 0 (0 :: (c + 1) :: r)
  rw [rep_snoc] at h5
  have h6 := Szero l a 0 (rep 1 (n + 1) ++ 0 :: (c + 1) :: r)
  exact zSt h1 (zSt h2 (zSt h3 (zSt h4 (zSt h5 h6))))

lemma CycleCarry (b : Nat) (l : List Nat) (n c : Nat) (r : List Nat) :
    (S l (b + 1) (0 :: (rep 1 (n + 2) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l b (0 :: (rep 1 (n + 2) ++ 0 :: (c + 1) :: r))) := by
  have h1 := Spos l b (0 :: (rep 1 (n + 2) ++ 0 :: c :: r))
  have h2 := Tmixs (n + 1) l (b + 1) (0 :: c :: r)
  have h3 := Tzero (rep 1 (n + 1) ++ (b + 1) :: l) 1 c r
  have h4 := Upos (rep 1 (n + 1) ++ (b + 1) :: l) 0 (0 :: (c + 1) :: r)
  have h5 := Szeros n ((b + 1) :: l) 0 (0 :: (c + 1) :: r)
  rw [rep_snoc] at h5
  have h6 := Szero l b 0 (rep 1 (n + 1) ++ 0 :: (c + 1) :: r)
  exact zSt h1 (zSt h2 (zSt h3 (zSt h4 (zSt h5 h6))))

lemma Cycle2 (l : List Nat) (n c : Nat) (r : List Nat) :
    (S (2 :: l) 1 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l 1 (0 :: (rep 1 (n + 2) ++ 0 :: (c + 1) :: r))) :=
  CycleStep 1 l n c r

lemma Cycle (l : List Nat) (n c : Nat) (r : List Nat) :
    (S (3 :: l) 1 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l 1 (0 :: (rep 1 (n + 2) ++ 0 :: (c + 2) :: r))) :=
  zSt (CycleStep 2 l n c r) (CycleCarry 1 l n (c + 1) r)

lemma Cycle4 (l : List Nat) (n c : Nat) (r : List Nat) :
    (S (4 :: l) 1 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l 1 (0 :: (rep 1 (n + 2) ++ 0 :: (c + 3) :: r))) :=
  zSt (CycleStep 3 l n c r) (zSt (CycleCarry 2 l n (c + 1) r) (CycleCarry 1 l n (c + 2) r))

lemma Cycles (m n : Nat) (l : List Nat) (c : Nat) (r : List Nat) :
    (S (rep 3 m ++ l) 1 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l 1 (0 :: (rep 1 (n + 1 + m) ++ 0 :: (m * 2 + c) :: r))) := by
  induction m generalizing n c with
  | zero =>
    rw [show 0 * 2 + c = c by omega, show n + 1 + 0 = n + 1 by omega]
    exact ⟨0, rfl⟩
  | succ m ih =>
    simp only [rep_succ, List.cons_append]
    have h1 := Cycle (rep 3 m ++ l) n c r
    have h2 := ih (n + 1) (c + 2)
    rw [show n + 1 + 1 + m = n + 1 + (m + 1) by omega,
        show m * 2 + (c + 2) = (m + 1) * 2 + c by omega] at h2
    exact zSt h1 h2

lemma Cycles2 (m n : Nat) (l : List Nat) (c : Nat) (r : List Nat) :
    (S (rep 2 m ++ l) 1 (0 :: (rep 1 (n + 1) ++ 0 :: c :: r))) [target_tm]⊢*
    (S l 1 (0 :: (rep 1 (n + 1 + m) ++ 0 :: (m + c) :: r))) := by
  induction m generalizing n c with
  | zero =>
    rw [show 0 + c = c by omega, show n + 1 + 0 = n + 1 by omega]
    exact ⟨0, rfl⟩
  | succ m ih =>
    simp only [rep_succ, List.cons_append]
    have h1 := Cycle2 (rep 2 m ++ l) n c r
    have h2 := ih (n + 1) (c + 1)
    rw [show n + 1 + 1 + m = n + 1 + (m + 1) by omega,
        show m + (c + 1) = (m + 1) + c by omega] at h2
    exact zSt h1 h2

lemma cap_head (r : List Nat) :
    (T ([]) 2 (0 :: 1 :: 0 :: 6 :: 1 :: r)) [target_tm]⊢* (T ([4, 2, 2, 0, 5]) 0 (r)) := by
  have h0 := Tmix ([]) 2 0 (0 :: 6 :: 1 :: r)
  have h1 := Tzero ([2]) 1 6 (1 :: r)
  have h2 := Upos ([2]) 0 (0 :: 7 :: 1 :: r)
  have h3 := Szero ([]) 1 0 (0 :: 7 :: 1 :: r)
  have h4 := Spos ([]) 0 (0 :: 1 :: 0 :: 7 :: 1 :: r)
  have h5 := Tmix ([]) 1 0 (0 :: 7 :: 1 :: r)
  have h6 := Tzero ([1]) 1 7 (1 :: r)
  have h7 := Upos ([1]) 0 (0 :: 8 :: 1 :: r)
  have h8 := Szero ([]) 0 0 (0 :: 8 :: 1 :: r)
  rw [Sblankl0 0 (0 :: 1 :: 0 :: 8 :: 1 :: r)] at h8
  have h10 := Sedge ([]) 0 0 (1 :: 0 :: 8 :: 1 :: r)
  rw [Ublankl0 0 (0 :: 1 :: 1 :: 0 :: 8 :: 1 :: r)] at h10
  have h12 := Uzero0 ([]) 0 (1 :: 1 :: 0 :: 8 :: 1 :: r)
  have h13 := Tpos ([]) 2 0 (1 :: 0 :: 8 :: 1 :: r)
  have h14 := Vzero1 ([]) 3 (0 :: 8 :: 1 :: r)
  have h15 := Tmix ([5]) 0 7 (1 :: r)
  have h16 := Triple ([0, 5]) 1 4 (1 :: r)
  have h17 := Triple ([2, 0, 5]) 1 1 (1 :: r)
  have h18 := Tpos ([2, 2, 0, 5]) 1 0 (1 :: r)
  have h19 := Vzero1 ([2, 2, 0, 5]) 2 (r)
  exact (zSt h0 (zSt h1 (zSt h2 (zSt h3 (zSt h4 (zSt h5 (zSt h6 (zSt h7 (zSt h8 (zSt h10 (zSt h12 (zSt h13 (zSt h14 (zSt h15 (zSt h16 (zSt h17 (zSt h18 h19)))))))))))))))))

lemma cap_mid_const (l : List Nat) :
    (T (2 :: l) 1 ([2])) [target_tm]⊢* (S (l) 1 ([0, 1, 0, 2])) := by
  have h0 := Tpos (2 :: l) 1 1 ([])
  have h1 := Vpos (2 :: l) 2 0 ([])
  have h2 := Spos (2 :: l) 1 ([0, 0])
  rw [Tblankr2 (2 :: l) 2] at h2
  have h4 := Tzero (2 :: l) 2 0 ([])
  have h5 := Upos (2 :: l) 1 ([0, 1])
  have h6 := Spos (2 :: l) 0 ([0, 0, 1])
  have h7 := Tzero (2 :: l) 1 1 ([])
  have h8 := Upos (2 :: l) 0 ([0, 2])
  have h9 := Szero (l) 1 0 ([0, 2])
  exact (zSt h0 (zSt h1 (zSt h2 (zSt h4 (zSt h5 (zSt h6 (zSt h7 (zSt h8 h9))))))))

lemma cap_tail (r : List Nat) :
    (S ([0, 5]) 0 (0 :: 1 :: r)) [target_tm]⊢⁺ (T ([]) 2 (0 :: 1 :: 0 :: 6 :: r)) := by
  have h0 := Sedge ([]) 5 0 (1 :: r)
  have h1 := Upos ([]) 4 (0 :: 1 :: 1 :: r)
  have h2 := Spos ([]) 3 (0 :: 0 :: 1 :: 1 :: r)
  have h3 := Tzero ([]) 4 1 (1 :: r)
  have h4 := Upos ([]) 3 (0 :: 2 :: 1 :: r)
  have h5 := Spos ([]) 2 (0 :: 0 :: 2 :: 1 :: r)
  have h6 := Tzero ([]) 3 2 (1 :: r)
  have h7 := Upos ([]) 2 (0 :: 3 :: 1 :: r)
  have h8 := Spos ([]) 1 (0 :: 0 :: 3 :: 1 :: r)
  have h9 := Tzero ([]) 2 3 (1 :: r)
  have h10 := Upos ([]) 1 (0 :: 4 :: 1 :: r)
  have h11 := Spos ([]) 0 (0 :: 0 :: 4 :: 1 :: r)
  have h12 := Tzero ([]) 1 4 (1 :: r)
  have h13 := Upos ([]) 0 (0 :: 5 :: 1 :: r)
  rw [Sblankl0 0 (0 :: 0 :: 5 :: 1 :: r)] at h13
  have h15 := Sedge ([]) 0 0 (0 :: 5 :: 1 :: r)
  rw [Ublankl0 0 (0 :: 1 :: 0 :: 5 :: 1 :: r)] at h15
  have h17 := Uzero0 ([]) 0 (1 :: 0 :: 5 :: 1 :: r)
  have h18 := Tpos ([]) 2 0 (0 :: 5 :: 1 :: r)
  have h19 := Vzero0 ([]) 3 (5 :: 1 :: r)
  have h20 := Triple ([]) 5 2 (1 :: r)
  have h21 := Tpos ([6]) 1 1 (1 :: r)
  have h22 := Vpos ([6]) 2 0 (1 :: r)
  have h23 := Spos ([6]) 1 (0 :: 0 :: 1 :: r)
  have h24 := Tzero ([6]) 2 1 (r)
  have h25 := Upos ([6]) 1 (0 :: 2 :: r)
  have h26 := Spos ([6]) 0 (0 :: 0 :: 2 :: r)
  have h27 := Tzero ([6]) 1 2 (r)
  have h28 := Upos ([6]) 0 (0 :: 3 :: r)
  have h29 := Szero ([]) 5 0 (0 :: 3 :: r)
  have h30 := Spos ([]) 4 (0 :: 1 :: 0 :: 3 :: r)
  have h31 := Tmix ([]) 5 0 (0 :: 3 :: r)
  have h32 := Tzero ([5]) 1 3 (r)
  have h33 := Upos ([5]) 0 (0 :: 4 :: r)
  have h34 := Szero ([]) 4 0 (0 :: 4 :: r)
  have h35 := Spos ([]) 3 (0 :: 1 :: 0 :: 4 :: r)
  have h36 := Tmix ([]) 4 0 (0 :: 4 :: r)
  have h37 := Tzero ([4]) 1 4 (r)
  have h38 := Upos ([4]) 0 (0 :: 5 :: r)
  have h39 := Szero ([]) 3 0 (0 :: 5 :: r)
  have h40 := Spos ([]) 2 (0 :: 1 :: 0 :: 5 :: r)
  have h41 := Tmix ([]) 3 0 (0 :: 5 :: r)
  have h42 := Tzero ([3]) 1 5 (r)
  have h43 := Upos ([3]) 0 (0 :: 6 :: r)
  have h44 := Szero ([]) 2 0 (0 :: 6 :: r)
  have h45 := Spos_progress ([]) 1 (0 :: 1 :: 0 :: 6 :: r)
  exact (zSpp h0 (zSpp h1 (zSpp h2 (zSpp h3 (zSpp h4 (zSpp h5 (zSpp h6 (zSpp h7 (zSpp h8 (zSpp h9 (zSpp h10 (zSpp h11 (zSpp h12 (zSpp h13 (zSpp h15 (zSpp h17 (zSpp h18 (zSpp h19 (zSpp h20 (zSpp h21 (zSpp h22 (zSpp h23 (zSpp h24 (zSpp h25 (zSpp h26 (zSpp h27 (zSpp h28 (zSpp h29 (zSpp h30 (zSpp h31 (zSpp h32 (zSpp h33 (zSpp h34 (zSpp h35 (zSpp h36 (zSpp h37 (zSpp h38 (zSpp h39 (zSpp h40 (zSpp h41 (zSpp h42 (zSpp h43 (zSpp h44 h45)))))))))))))))))))))))))))))))))))))))))))


def cap (n : Nat) : Cfg (Fin 2) (Fin 6) :=
  T [] 2 (0 :: 1 :: 0 :: 6 :: (rep 1 (n * 2 + 4) ++ [0, n * 3 + 11]))

lemma cap_step (n : Nat) : (cap n) [target_tm]⊢⁺ (cap (n + 1)) := by
  unfold cap
  have heq1 : rep 1 (n * 2 + 3) ++ [0, n * 3 + 11] = rep 1 ((n + 1) * 2) ++ [1, 0, n * 3 + 11] := by
    rw [← rep_snoc, show (n + 1) * 2 = n * 2 + 2 by omega]
  have s1 := zSt_eq (cap_head (rep 1 (n * 2 + 3) ++ [0, n * 3 + 11])) (congrArg (T [4, 2, 2, 0, 5] 0) heq1)
  have s2 := Pairs (n + 1) [4, 2, 2, 0, 5] [1, 0, n * 3 + 11]
  have heq3 : [n * 3 + 11] = [((n + 2) + 1) * 3 + 2] := by
    rw [show n * 3 + 11 = ((n + 2) + 1) * 3 + 2 by omega]
  have s3 := zSt_eq (zSt (Tpos (rep 3 (n + 1) ++ [4, 2, 2, 0, 5]) 0 0 [0, n * 3 + 11])
                         (Vzero0 (rep 3 (n + 1) ++ [4, 2, 2, 0, 5]) 1 [n * 3 + 11]))
                    (congrArg (T (rep 3 (n + 1) ++ [4, 2, 2, 0, 5]) 3) heq3)
  have s4 := Triples (n + 2) (rep 3 (n + 1) ++ [4, 2, 2, 0, 5]) 3 2 []
  have s5 := cap_mid_const (rep 2 (n + 1) ++ 4 :: (rep 3 (n + 1) ++ [4, 2, 2, 0, 5]))
  have s6 := Cycles2 (n + 1) 0 (4 :: (rep 3 (n + 1) ++ [4, 2, 2, 0, 5])) 2 []
  rw [show 0 + 1 + (n + 1) = n + 2 by omega, show (n + 1) + 2 = n + 3 by omega] at s6
  have s7 := Cycle4 (rep 3 (n + 1) ++ [4, 2, 2, 0, 5]) (n + 1) (n + 3) []
  have s8 := Cycles (n + 1) (n + 2) [4, 2, 2, 0, 5] (n + 6) []
  rw [show n + 2 + 1 + (n + 1) = n * 2 + 4 by omega, show (n + 1) * 2 + (n + 6) = n * 3 + 8 by omega] at s8
  have s9 := Cycle4 [2, 2, 0, 5] (n * 2 + 3) (n * 3 + 8) []
  have s10 := Cycles2 2 (n * 2 + 4) [0, 5] (n * 3 + 11) []
  rw [show n * 2 + 4 + 1 + 2 = n * 2 + 7 by omega, show 2 + (n * 3 + 11) = n * 3 + 13 by omega] at s10
  have s11 := Spos [0, 5] 0 (0 :: (rep 1 (n * 2 + 7) ++ [0, n * 3 + 13]))
  have s12 := Tmixs (n * 2 + 6) [0, 5] 1 [0, n * 3 + 13]
  rw [rep_snoc] at s12
  have s13 := Tzero (rep 1 (n * 2 + 7) ++ [0, 5]) 1 (n * 3 + 13) []
  have s14 := Upos (rep 1 (n * 2 + 7) ++ [0, 5]) 0 [0, n * 3 + 14]
  have s15 := Szeros (n * 2 + 6) [0, 5] 0 [0, n * 3 + 14]
  have heq15 : rep 1 (n * 2 + 6) ++ [1, 0, n * 3 + 14] = 1 :: (rep 1 ((n + 1) * 2 + 4) ++ [0, (n + 1) * 3 + 11]) := by
    rw [rep_snoc, show n * 2 + 7 = (n + 1) * 2 + 5 by omega, show n * 3 + 14 = (n + 1) * 3 + 11 by omega]; rfl
  rw [heq15] at s15
  have s16 := cap_tail (rep 1 ((n + 1) * 2 + 4) ++ [0, (n + 1) * 3 + 11])
  exact zSpp s1 (zSpp s2 (zSpp s3 (zSpp s4 (zSpp s5 (zSpp s6 (zSpp s7 (zSpp s8 (zSpp s9 (zSpp s10 (zSpp s11 (zSpp s12 (zSpp s13 (zSpp s14 (zSpp s15 s16))))))))))))))

-- ============================================================================
-- Fast Kernel RLE Evaluator
-- ============================================================================

noncomputable section

inductive RList where
  | nil : RList
  | cons (val : Nat) (cnt : Nat) (tail : RList) : RList
deriving DecidableEq

inductive Phase where
  | pS | pT | pU | pV
deriving DecidableEq

inductive CfgRLE where
  | mk (p : Phase) (l : RList) (a : Nat) (r : RList) : CfgRLE
deriving DecidableEq

@[simp]
def decodeR : RList → List Nat
  | .nil => []
  | .cons v k t => rep v (k + 1) ++ decodeR t

@[simp]
def decodeCfg : CfgRLE → Cfg (Fin 2) (Fin 6)
  | .mk .pS l a r => S (decodeR l) a (decodeR r)
  | .mk .pT l a r => T (decodeR l) a (decodeR r)
  | .mk .pU l a r => U (decodeR l) a (decodeR r)
  | .mk .pV l a r => V (decodeR l) a (decodeR r)

def bindNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k m) (Nat.add 1 n)

@[simp]
lemma bindNat_eq {α : Type} (n : Nat) (k : Nat → α) : bindNat n k = k n := by
  unfold bindNat
  rw [show Nat.add 1 n = n + 1 from Nat.add_comm 1 n]

def pushRep_cons_branch (same : Bool) (v k w m : Nat) (t : RList) : RList :=
  Bool.rec
    (RList.cons v k (RList.cons w m t))
    (bindNat (Nat.add k (Nat.add m 1)) (fun km => RList.cons v km t))
    same

def pushRep (v k : Nat) (l : RList) : RList :=
  RList.rec
    (RList.cons v k RList.nil)
    (fun w m t _ => pushRep_cons_branch (Nat.beq v w) v k w m t)
    l

def push1 (v : Nat) (l : RList) : RList := pushRep v 0 l

def pushRepN (v n : Nat) (l : RList) : RList :=
  Nat.rec l (fun k _ => pushRep v k l) n

def popR_cons_branch {α : Type} (is0 : Bool) (v c : Nat) (t : RList) (k : Nat → RList → α) : α :=
  Bool.rec
    (bindNat (Nat.sub c 1) (fun c' => k v (RList.cons v c' t)))
    (k v t)
    is0

def popRList {α : Type} (xs : RList) (k : Nat → RList → α) : α :=
  RList.rec
    (k 0 RList.nil)
    (fun v c t _ => popR_cons_branch (Nat.beq c 0) v c t k)
    xs

def step_U_a0_c (x0 : Nat) (l1 r1 : RList) (c : Nat) : CfgRLE :=
  Bool.rec
    (Bool.rec
      (CfgRLE.mk Phase.pU (push1 x0 l1) 0 (push1 c r1))
      (bindNat (Nat.add x0 2) (fun x02 => CfgRLE.mk Phase.pT (push1 x02 l1) 0 r1))
      (Nat.beq c 1))
    (bindNat (Nat.add x0 2) (fun x02 => CfgRLE.mk Phase.pT l1 x02 r1))
    (Nat.beq c 0)

def step_U (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  Bool.rec
    (bindNat (Nat.sub a 1) (fun a' => CfgRLE.mk Phase.pS l a' (push1 0 r)))
    (popRList l (fun x0 l1 => popRList r (fun c r1 => step_U_a0_c x0 l1 r1 c)))
    (Nat.beq a 0)

def step_V_c0_0 (l : RList) (a : Nat) (c1 : Nat) (r2 : RList) : CfgRLE :=
  Bool.rec
    (Bool.rec
      (CfgRLE.mk Phase.pV l a (push1 0 (push1 c1 r2)))
      (bindNat (Nat.add a 2) (fun a2 => CfgRLE.mk Phase.pT (push1 a2 l) 0 r2))
      (Nat.beq c1 1))
    (bindNat (Nat.add a 2) (fun a2 => CfgRLE.mk Phase.pT l a2 r2))
    (Nat.beq c1 0)

def step_V (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  popRList r (fun c0 r1 =>
    Bool.rec
      (bindNat (Nat.sub c0 1) (fun c0' => CfgRLE.mk Phase.pS l a (push1 0 (push1 c0' r1))))
      (popRList r1 (fun c1 r2 => step_V_c0_0 l a c1 r2))
      (Nat.beq c0 0))

def step_T_c0_0_fallback (l : RList) (a : Nat) (r1 : RList) : CfgRLE :=
  popRList r1 (fun c1 r2 =>
    Bool.rec
      (bindNat (Nat.sub c1 1) (fun c1' => CfgRLE.mk Phase.pT (push1 a l) 1 (push1 c1' r2)))
      (popRList r2 (fun c2 r3 =>
        bindNat (Nat.add c2 1) (fun c2' => CfgRLE.mk Phase.pU l a (push1 0 (push1 c2' r3)))))
      (Nat.beq c1 0))

def step_T_c0_0 (l : RList) (a : Nat) (r1 : RList) : CfgRLE :=
  RList.rec
    (step_T_c0_0_fallback l a RList.nil)
    (fun v1 k1 t1 _ =>
      Bool.rec
        (step_T_c0_0_fallback l a (RList.cons v1 k1 t1))
        (CfgRLE.mk Phase.pT (pushRepN 1 k1 (push1 a l)) 1 (push1 0 t1))
        (Nat.beq v1 1))
    r1

def step_T_base (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  popRList r (fun c0 r1 =>
    Bool.rec
      (Bool.rec
        (bindNat (Nat.sub c0 1) (fun c0' => CfgRLE.mk Phase.pV l (Nat.add a 1) (push1 c0' r1)))
        (bindNat (Nat.div c0 3) (fun q =>
         bindNat (Nat.sub q 1) (fun q1 =>
         bindNat (Nat.mod c0 3) (fun rem =>
         bindNat (Nat.add a 1) (fun a1 =>
           CfgRLE.mk Phase.pT (pushRepN 2 q1 (push1 a1 l)) 1 (push1 rem r1))))))
        (Nat.ble 3 c0))
      (step_T_c0_0 l a r1)
      (Nat.beq c0 0))

def step_T (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  RList.rec
    (step_T_base l a RList.nil)
    (fun v k t _ =>
      Bool.rec
        (step_T_base l a (RList.cons v k t))
        (bindNat (Nat.div (Nat.add k 1) 2) (fun m =>
         bindNat (Nat.mod (Nat.add k 1) 2) (fun rem1 =>
           CfgRLE.mk Phase.pT (pushRepN 3 m l) 0
             (Bool.rec (push1 1 t) t (Nat.beq rem1 0)))))
        (Bool.and (Nat.beq a 0) (Bool.and (Nat.beq v 1) (Bool.not (Nat.beq k 0)))))
    r

def step_S_a0_fallback (l : RList) (c : Nat) (r1 : RList) : CfgRLE :=
  popRList l (fun x0 l1 =>
    Bool.rec
      (bindNat (Nat.sub x0 1) (fun x0' =>
       bindNat (Nat.add c 1) (fun c1 =>
         CfgRLE.mk Phase.pS l1 x0' (push1 0 (push1 c1 r1)))))
      (popRList l1 (fun x1 l2 =>
       bindNat (Nat.add c 1) (fun c1 =>
         CfgRLE.mk Phase.pU l2 x1 (push1 0 (push1 c1 r1)))))
      (Nat.beq x0 0))

def step_S_a0 (l r : RList) : CfgRLE :=
  popRList r (fun c r1 =>
    RList.rec
      (step_S_a0_fallback RList.nil c r1)
      (fun v k t _ =>
        Bool.rec
          (step_S_a0_fallback (RList.cons v k t) c r1)
          (bindNat (Nat.add c 1) (fun c1 =>
            CfgRLE.mk Phase.pS t 0 (push1 0 (pushRepN 1 k (push1 c1 r1)))))
          (Nat.beq v 1))
      l)

def do_cycle (is3 : Bool) (k_l : Nat) (l_tail : RList) (n : Nat) (r3 : RList) : CfgRLE :=
  popRList r3 (fun c r_tail =>
    bindNat (Nat.add k_l 1) (fun m =>
    bindNat (Nat.add n m) (fun nm =>
    Bool.rec
      (bindNat (Nat.add m c) (fun mc =>
        CfgRLE.mk Phase.pS l_tail 1 (push1 0 (pushRep 1 nm (push1 0 (push1 mc r_tail))))))
      (bindNat (Nat.add (Nat.mul m 2) c) (fun m2c =>
        CfgRLE.mk Phase.pS l_tail 1 (push1 0 (pushRep 1 nm (push1 0 (push1 m2c r_tail))))))
      is3)))

def step_S_pos (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  RList.rec
    (CfgRLE.mk Phase.pT RList.nil a r)
    (fun v k_l l_tail _ =>
      RList.rec
        (CfgRLE.mk Phase.pT (RList.cons v k_l l_tail) a RList.nil)
        (fun v0 c0 r_a _ =>
          RList.rec
            (CfgRLE.mk Phase.pT (RList.cons v k_l l_tail) a (RList.cons v0 c0 RList.nil))
            (fun v1 n r_b _ =>
              RList.rec
                (CfgRLE.mk Phase.pT (RList.cons v k_l l_tail) a (RList.cons v0 c0 (RList.cons v1 n RList.nil)))
                (fun v2 c2 r3 _ =>
                  Bool.rec
                    (CfgRLE.mk Phase.pT (RList.cons v k_l l_tail) a (RList.cons v0 c0 (RList.cons v1 n (RList.cons v2 c2 r3))))
                    (do_cycle (Nat.beq v 3) k_l l_tail n r3)
                    (Bool.and (Nat.beq a 1)
                      (Bool.and (Bool.or (Nat.beq v 2) (Nat.beq v 3))
                        (Bool.and (Nat.beq v0 0)
                          (Bool.and (Nat.beq c0 0)
                            (Bool.and (Nat.beq v1 1)
                              (Bool.and (Nat.beq v2 0) (Nat.beq c2 0))))))))
                r_b)
            r_a)
        r)
    l

def step_S (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  Bool.rec
    (step_S_pos l a r)
    (step_S_a0 l r)
    (Nat.beq a 0)

def rle_step_unpacked (p : Phase) (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  Phase.rec (step_S l a r) (step_T l a r) (step_U l a r) (step_V l a r) p

def rp_step (_ : Nat) (ih : Phase → RList → Nat → RList → CfgRLE)
    (p : Phase) (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  CfgRLE.rec ih (ih p l a r)

def run_pow (k : Nat) (p : Phase) (l : RList) (a : Nat) (r : RList) : CfgRLE :=
  (Nat.rec rle_step_unpacked rp_step k : Phase → RList → Nat → RList → CfgRLE) p l a r

def run_seq : List Nat → CfgRLE → CfgRLE
  | [], c => c
  | k :: ks, c => CfgRLE.rec (fun p l a r => run_seq ks (run_pow k p l a r)) c

-- ============================================================================
-- Soundness Proof of Fast Kernel RLE Evaluator
-- ============================================================================

lemma rep_add (v m n : Nat) (xs : List Nat) :
    rep v m ++ (rep v n ++ xs) = rep v (m + n) ++ xs := by
  induction m with
  | zero => simp [rep_zero, Nat.zero_add]
  | succ m ih => simp only [Nat.succ_add, rep_succ, List.cons_append, ih]

@[simp]
lemma decodeR_pushRep (v k : Nat) (l : RList) :
    decodeR (pushRep v k l) = rep v (k + 1) ++ decodeR l := by
  cases l with
  | nil => simp [pushRep, decodeR]
  | cons w m t =>
    dsimp only [pushRep]
    cases hvw : Nat.beq v w with
    | false => rfl
    | true =>
      have heq : v = w := Nat.eq_of_beq_eq_true hvw
      subst heq
      change decodeR (bindNat (k + (m + 1)) (fun km => RList.cons v km t)) = _
      rw [bindNat_eq]
      dsimp only [decodeR]
      rw [rep_add, show (k + 1) + (m + 1) = k + (m + 1) + 1 by omega]

@[simp]
lemma decodeR_push1 (v : Nat) (l : RList) :
    decodeR (push1 v l) = v :: decodeR l :=
  decodeR_pushRep v 0 l

@[simp]
lemma decodeR_pushRepN (v n : Nat) (l : RList) :
    decodeR (pushRepN v n l) = rep v n ++ decodeR l := by
  cases n with
  | zero => rfl
  | succ k => exact decodeR_pushRep v k l

lemma decodeR_cons_pos {v c : Nat} (t : RList) (hc : Nat.beq c 0 = false) :
    decodeR (RList.cons v c t) = v :: decodeR (RList.cons v (c - 1) t) := by
  have hne : c ≠ 0 := Nat.ne_of_beq_eq_false hc
  have heq : c + 1 = (c - 1) + 1 + 1 := by omega
  dsimp only [decodeR]
  rw [heq, rep_succ, List.cons_append]

lemma popRList_spec {F : List Nat → Cfg (Fin 2) (Fin 6)} (h0 : F [] = F [0])
    (xs : RList) (k : Nat → RList → CfgRLE)
    (hk : ∀ v t, (F (v :: decodeR t)) [target_tm]⊢* (decodeCfg (k v t))) :
    (F (decodeR xs)) [target_tm]⊢* (decodeCfg (popRList xs k)) := by
  cases xs with
  | nil =>
    change (F []) [target_tm]⊢* (decodeCfg (k 0 RList.nil))
    rw [h0]
    exact hk 0 RList.nil
  | cons v c t =>
    dsimp only [popRList]
    cases hc : Nat.beq c 0 with
    | true =>
      have hc0 : c = 0 := Nat.eq_of_beq_eq_true hc
      subst hc0
      exact hk v t
    | false =>
      change (F (decodeR (RList.cons v c t))) [target_tm]⊢*
        (decodeCfg (bindNat (c - 1) (fun c' => k v (RList.cons v c' t))))
      rw [bindNat_eq, decodeR_cons_pos t hc]
      exact hk v (RList.cons v (c - 1) t)

lemma S_nil_l (a : Nat) (r : List Nat) : S [] a r = S [0] a r := Sblankl [] a r
lemma S_nil_l1 (x0 a : Nat) (r : List Nat) : S [x0] a r = S [x0, 0] a r := Sblankl [x0] a r
lemma U_nil_l (a : Nat) (r : List Nat) : U [] a r = U [0] a r := Ublankl [] a r
lemma S_nil_r (l : List Nat) (a : Nat) : S l a [] = S l a [0] := Sblankr l a []
lemma S_nil_r3 (l : List Nat) (a n : Nat) :
    S l a (0 :: (rep 1 (n + 1) ++ [0])) = S l a (0 :: (rep 1 (n + 1) ++ [0, 0])) := by
  have h := Sblankr l a (0 :: (rep 1 (n + 1) ++ [0]))
  simpa only [List.cons_append, List.append_assoc, List.nil_append] using h
lemma U_nil_r (l : List Nat) (a : Nat) : U l a [] = U l a [0] := Ublankr l a []
lemma T_nil_r (l : List Nat) (a : Nat) : T l a [] = T l a [0] := Tblankr l a []
lemma T_nil_r1 (l : List Nat) (a c0 : Nat) : T l a [c0] = T l a [c0, 0] := Tblankr l a [c0]
lemma T_nil_r2 (l : List Nat) (a c0 c1 : Nat) : T l a [c0, c1] = T l a [c0, c1, 0] := Tblankr l a [c0, c1]
lemma V_nil_r (l : List Nat) (a : Nat) : V l a [] = V l a [0] := Vblankr l a []
lemma V_nil_r1 (l : List Nat) (a c0 : Nat) : V l a [c0] = V l a [c0, 0] := Vblankr l a [c0]

lemma nat_not_le_of_ble_eq_false {a b : Nat} (h : Nat.ble a b = false) : ¬ (a ≤ b) := by
  intro hle
  have h1 : Nat.ble a b = true := Nat.ble_eq_true_of_le hle
  rw [h] at h1
  contradiction

lemma step_U_spec (l : RList) (a : Nat) (r : RList) :
    (U (decodeR l) a (decodeR r)) [target_tm]⊢* (decodeCfg (step_U l a r)) := by
  unfold step_U
  cases ha : Nat.beq a 0 with
  | false =>
    have hne : a ≠ 0 := Nat.ne_of_beq_eq_false ha
    change _ [target_tm]⊢* (decodeCfg (bindNat (a - 1) (fun a' => CfgRLE.mk Phase.pS l a' (push1 0 r))))
    simp only [bindNat_eq, decodeCfg, decodeR_push1]
    rw [show a = (a - 1) + 1 by omega]
    exact Upos (decodeR l) (a - 1) (decodeR r)
  | true =>
    have ha0 : a = 0 := Nat.eq_of_beq_eq_true ha
    subst ha0
    refine popRList_spec (F := fun xs => U xs 0 (decodeR r)) (U_nil_l 0 (decodeR r)) l _ (fun x0 l1 => ?_)
    refine popRList_spec (F := fun ys => U (x0 :: decodeR l1) 0 ys) (U_nil_r (x0 :: decodeR l1) 0) r _ (fun c r1 => ?_)
    unfold step_U_a0_c
    cases hc0 : Nat.beq c 0 with
    | true =>
      have hc : c = 0 := Nat.eq_of_beq_eq_true hc0
      subst hc
      change _ [target_tm]⊢* (decodeCfg (bindNat (x0 + 2) (fun x02 => CfgRLE.mk Phase.pT l1 x02 r1)))
      simp only [bindNat_eq, decodeCfg]
      exact Uzero0 (decodeR l1) x0 (decodeR r1)
    | false =>
      dsimp only
      cases hc1 : Nat.beq c 1 with
      | true =>
        have hc : c = 1 := Nat.eq_of_beq_eq_true hc1
        subst hc
        change _ [target_tm]⊢* (decodeCfg (bindNat (x0 + 2) (fun x02 => CfgRLE.mk Phase.pT (push1 x02 l1) 0 r1)))
        simp only [bindNat_eq, decodeCfg, decodeR_push1]
        exact Uzero1 (decodeR l1) x0 (decodeR r1)
      | false =>
        simp only [decodeCfg, decodeR_push1]
        exact ⟨0, rfl⟩

lemma step_V_spec (l : RList) (a : Nat) (r : RList) :
    (V (decodeR l) a (decodeR r)) [target_tm]⊢* (decodeCfg (step_V l a r)) := by
  unfold step_V
  refine popRList_spec (F := fun ys => V (decodeR l) a ys) (V_nil_r (decodeR l) a) r _ (fun c0 r1 => ?_)
  cases hc0 : Nat.beq c0 0 with
  | false =>
    have hne : c0 ≠ 0 := Nat.ne_of_beq_eq_false hc0
    change _ [target_tm]⊢* (decodeCfg (bindNat (c0 - 1) (fun c0' => CfgRLE.mk Phase.pS l a (push1 0 (push1 c0' r1)))))
    simp only [bindNat_eq, decodeCfg, decodeR_push1]
    rw [show c0 = (c0 - 1) + 1 by omega]
    exact Vpos (decodeR l) a (c0 - 1) (decodeR r1)
  | true =>
    have hc : c0 = 0 := Nat.eq_of_beq_eq_true hc0
    subst hc
    refine popRList_spec (F := fun ys => V (decodeR l) a (0 :: ys)) (V_nil_r1 (decodeR l) a 0) r1 _ (fun c1 r2 => ?_)
    unfold step_V_c0_0
    cases hc1 : Nat.beq c1 0 with
    | true =>
      have hc1_0 : c1 = 0 := Nat.eq_of_beq_eq_true hc1
      subst hc1_0
      change _ [target_tm]⊢* (decodeCfg (bindNat (a + 2) (fun a2 => CfgRLE.mk Phase.pT l a2 r2)))
      simp only [bindNat_eq, decodeCfg]
      exact Vzero0 (decodeR l) a (decodeR r2)
    | false =>
      dsimp only
      cases hc1_1 : Nat.beq c1 1 with
      | true =>
        have hc1_eq : c1 = 1 := Nat.eq_of_beq_eq_true hc1_1
        subst hc1_eq
        change _ [target_tm]⊢* (decodeCfg (bindNat (a + 2) (fun a2 => CfgRLE.mk Phase.pT (push1 a2 l) 0 r2)))
        simp only [bindNat_eq, decodeCfg, decodeR_push1]
        exact Vzero1 (decodeR l) a (decodeR r2)
      | false =>
        simp only [decodeCfg, decodeR_push1]
        exact ⟨0, rfl⟩

lemma step_T_c0_0_fallback_spec (l : RList) (a : Nat) (r1 : RList) :
    (T (decodeR l) a (0 :: decodeR r1)) [target_tm]⊢* (decodeCfg (step_T_c0_0_fallback l a r1)) := by
  unfold step_T_c0_0_fallback
  refine popRList_spec (F := fun ys => T (decodeR l) a (0 :: ys)) (T_nil_r1 (decodeR l) a 0) r1 _ (fun c1 r2 => ?_)
  cases hc1 : Nat.beq c1 0 with
  | false =>
    have hne : c1 ≠ 0 := Nat.ne_of_beq_eq_false hc1
    change _ [target_tm]⊢* (decodeCfg (bindNat (c1 - 1) (fun c1' => CfgRLE.mk Phase.pT (push1 a l) 1 (push1 c1' r2))))
    simp only [bindNat_eq, decodeCfg, decodeR_push1]
    rw [show c1 = (c1 - 1) + 1 by omega]
    exact Tmix (decodeR l) a (c1 - 1) (decodeR r2)
  | true =>
    have hc1_0 : c1 = 0 := Nat.eq_of_beq_eq_true hc1
    subst hc1_0
    refine popRList_spec (F := fun ys => T (decodeR l) a (0 :: 0 :: ys)) (T_nil_r2 (decodeR l) a 0 0) r2 _ (fun c2 r3 => ?_)
    change _ [target_tm]⊢* (decodeCfg (bindNat (c2 + 1) (fun c2' => CfgRLE.mk Phase.pU l a (push1 0 (push1 c2' r3)))))
    simp only [bindNat_eq, decodeCfg, decodeR_push1]
    exact Tzero (decodeR l) a c2 (decodeR r3)

lemma step_T_c0_0_spec (l : RList) (a : Nat) (r1 : RList) :
    (T (decodeR l) a (0 :: decodeR r1)) [target_tm]⊢* (decodeCfg (step_T_c0_0 l a r1)) := by
  cases r1 with
  | nil => exact step_T_c0_0_fallback_spec l a RList.nil
  | cons v1 k1 t1 =>
    dsimp only [step_T_c0_0]
    cases hv1 : Nat.beq v1 1 with
    | false => exact step_T_c0_0_fallback_spec l a (RList.cons v1 k1 t1)
    | true =>
      have hv : v1 = 1 := Nat.eq_of_beq_eq_true hv1
      subst hv
      simp only [decodeCfg, decodeR_pushRepN, decodeR_push1, decodeR]
      exact Tmixs k1 (decodeR l) a (decodeR t1)

lemma step_T_base_spec (l : RList) (a : Nat) (r : RList) :
    (T (decodeR l) a (decodeR r)) [target_tm]⊢* (decodeCfg (step_T_base l a r)) := by
  unfold step_T_base
  refine popRList_spec (F := fun ys => T (decodeR l) a ys) (T_nil_r (decodeR l) a) r _ (fun c0 r1 => ?_)
  cases hc0 : Nat.beq c0 0 with
  | true =>
    have hc : c0 = 0 := Nat.eq_of_beq_eq_true hc0
    subst hc
    exact step_T_c0_0_spec l a r1
  | false =>
    have hne : c0 ≠ 0 := Nat.ne_of_beq_eq_false hc0
    dsimp only
    cases hc3 : Nat.ble 3 c0 with
    | false =>
      change _ [target_tm]⊢* (decodeCfg (bindNat (c0 - 1) (fun c0' => CfgRLE.mk Phase.pV l (a + 1) (push1 c0' r1))))
      simp only [bindNat_eq, decodeCfg, decodeR_push1]
      rw [show c0 = (c0 - 1) + 1 by omega]
      exact Tpos (decodeR l) a (c0 - 1) (decodeR r1)
    | true =>
      have hle : 3 ≤ c0 := Nat.le_of_ble_eq_true hc3
      change _ [target_tm]⊢* (decodeCfg
        (bindNat (c0 / 3) (fun q => bindNat (q - 1) (fun q1 => bindNat (c0 % 3) (fun rem =>
         bindNat (a + 1) (fun a1 => CfgRLE.mk Phase.pT (pushRepN 2 q1 (push1 a1 l)) 1 (push1 rem r1)))))))
      simp only [bindNat_eq, decodeCfg, decodeR_pushRepN, decodeR_push1]
      have hdiv : ((c0 / 3 - 1) + 1) * 3 + c0 % 3 = c0 := by omega
      have hstep := Triples (c0 / 3 - 1) (decodeR l) a (c0 % 3) (decodeR r1)
      rw [hdiv] at hstep
      exact hstep

lemma step_T_spec (l : RList) (a : Nat) (r : RList) :
    (T (decodeR l) a (decodeR r)) [target_tm]⊢* (decodeCfg (step_T l a r)) := by
  cases r with
  | nil => exact step_T_base_spec l a RList.nil
  | cons v k t =>
    dsimp only [step_T]
    cases hok : Bool.and (Nat.beq a 0) (Bool.and (Nat.beq v 1) (Bool.not (Nat.beq k 0))) with
    | false => exact step_T_base_spec l a (RList.cons v k t)
    | true =>
      have ⟨ha, hvk⟩ := Bool.and_eq_true_iff.mp hok
      have ⟨hv, _⟩ := Bool.and_eq_true_iff.mp hvk
      have ha0 : a = 0 := Nat.eq_of_beq_eq_true ha
      have hv1 : v = 1 := Nat.eq_of_beq_eq_true hv
      subst ha0; subst hv1
      change _ [target_tm]⊢* (decodeCfg
        (bindNat ((k + 1) / 2) (fun m => bindNat ((k + 1) % 2) (fun rem1 =>
          CfgRLE.mk Phase.pT (pushRepN 3 m l) 0 (Bool.rec (push1 1 t) t (Nat.beq rem1 0))))))
      simp only [bindNat_eq]
      cases hrem : Nat.beq ((k + 1) % 2) 0 with
      | true =>
        have hrem0 : (k + 1) % 2 = 0 := Nat.eq_of_beq_eq_true hrem
        have hk : ((k + 1) / 2) * 2 = k + 1 := by omega
        simp only [decodeCfg, decodeR_pushRepN, decodeR]
        have hstep := Pairs ((k + 1) / 2) (decodeR l) (decodeR t)
        rw [hk] at hstep
        exact hstep
      | false =>
        have hrem_ne : (k + 1) % 2 ≠ 0 := Nat.ne_of_beq_eq_false hrem
        have hk : ((k + 1) / 2) * 2 + 1 = k + 1 := by omega
        simp only [decodeCfg, decodeR_pushRepN, decodeR_push1, decodeR]
        have hstep := Pairs ((k + 1) / 2) (decodeR l) (1 :: decodeR t)
        rw [rep_snoc, hk] at hstep
        exact hstep

lemma step_S_a0_fallback_spec (l : RList) (c : Nat) (r1 : RList) :
    (S (decodeR l) 0 (c :: decodeR r1)) [target_tm]⊢* (decodeCfg (step_S_a0_fallback l c r1)) := by
  unfold step_S_a0_fallback
  refine popRList_spec (F := fun xs => S xs 0 (c :: decodeR r1)) (S_nil_l 0 (c :: decodeR r1)) l _ (fun x0 l1 => ?_)
  cases hx0 : Nat.beq x0 0 with
  | false =>
    have hne : x0 ≠ 0 := Nat.ne_of_beq_eq_false hx0
    change _ [target_tm]⊢* (decodeCfg
      (bindNat (x0 - 1) (fun x0' => bindNat (c + 1) (fun c1 => CfgRLE.mk Phase.pS l1 x0' (push1 0 (push1 c1 r1))))))
    simp only [bindNat_eq, decodeCfg, decodeR_push1]
    rw [show x0 = (x0 - 1) + 1 by omega]
    exact Szero (decodeR l1) (x0 - 1) c (decodeR r1)
  | true =>
    have hx0_0 : x0 = 0 := Nat.eq_of_beq_eq_true hx0
    subst hx0_0
    refine popRList_spec (F := fun xs => S (0 :: xs) 0 (c :: decodeR r1)) (S_nil_l1 0 0 (c :: decodeR r1)) l1 _ (fun x1 l2 => ?_)
    change _ [target_tm]⊢* (decodeCfg
      (bindNat (c + 1) (fun c1 => CfgRLE.mk Phase.pU l2 x1 (push1 0 (push1 c1 r1)))))
    simp only [bindNat_eq, decodeCfg, decodeR_push1]
    exact Sedge (decodeR l2) x1 c (decodeR r1)

lemma step_S_a0_spec (l r : RList) :
    (S (decodeR l) 0 (decodeR r)) [target_tm]⊢* (decodeCfg (step_S_a0 l r)) := by
  unfold step_S_a0
  refine popRList_spec (F := fun ys => S (decodeR l) 0 ys) (S_nil_r (decodeR l) 0) r _ (fun c r1 => ?_)
  cases l with
  | nil => exact step_S_a0_fallback_spec RList.nil c r1
  | cons v k t =>
    dsimp only
    cases hv : Nat.beq v 1 with
    | false => exact step_S_a0_fallback_spec (RList.cons v k t) c r1
    | true =>
      have hv1 : v = 1 := Nat.eq_of_beq_eq_true hv
      subst hv1
      change _ [target_tm]⊢* (decodeCfg
        (bindNat (c + 1) (fun c1 => CfgRLE.mk Phase.pS t 0 (push1 0 (pushRepN 1 k (push1 c1 r1))))))
      simp only [bindNat_eq, decodeCfg, decodeR_push1, decodeR_pushRepN, decodeR]
      exact Szeros k (decodeR t) c (decodeR r1)

lemma step_S_pos_spec (l : RList) (a : Nat) (r : RList) (ha : Nat.beq a 0 = false) :
    (S (decodeR l) a (decodeR r)) [target_tm]⊢* (decodeCfg (step_S_pos l a r)) := by
  have hne : a ≠ 0 := Nat.ne_of_beq_eq_false ha
  have hspos : (S (decodeR l) a (decodeR r)) [target_tm]⊢* (T (decodeR l) a (decodeR r)) := by
    rw [show a = (a - 1) + 1 by omega]; exact Spos (decodeR l) (a - 1) (decodeR r)
  cases l with
  | nil => exact hspos
  | cons v k_l l_tail =>
    cases r with
    | nil => exact hspos
    | cons v0 c0 r_a =>
      cases r_a with
      | nil => exact hspos
      | cons v1 n r_b =>
        cases r_b with
        | nil => exact hspos
        | cons v2 c2 r3 =>
          dsimp only [step_S_pos]
          cases hok : Bool.and (Nat.beq a 1)
            (Bool.and (Bool.or (Nat.beq v 2) (Nat.beq v 3))
              (Bool.and (Nat.beq v0 0)
                (Bool.and (Nat.beq c0 0)
                  (Bool.and (Nat.beq v1 1)
                    (Bool.and (Nat.beq v2 0) (Nat.beq c2 0)))))) with
          | false => exact hspos
          | true =>
            have ⟨ha1, h1⟩ := Bool.and_eq_true_iff.mp hok
            have ⟨hv23, h2⟩ := Bool.and_eq_true_iff.mp h1
            have ⟨hv0, h3⟩ := Bool.and_eq_true_iff.mp h2
            have ⟨hc0, h4⟩ := Bool.and_eq_true_iff.mp h3
            have ⟨hv1, h5⟩ := Bool.and_eq_true_iff.mp h4
            have ⟨hv2, hc2⟩ := Bool.and_eq_true_iff.mp h5
            have ha_eq : a = 1 := Nat.eq_of_beq_eq_true ha1
            have hv0_eq : v0 = 0 := Nat.eq_of_beq_eq_true hv0
            have hc0_eq : c0 = 0 := Nat.eq_of_beq_eq_true hc0
            have hv1_eq : v1 = 1 := Nat.eq_of_beq_eq_true hv1
            have hv2_eq : v2 = 0 := Nat.eq_of_beq_eq_true hv2
            have hc2_eq : c2 = 0 := Nat.eq_of_beq_eq_true hc2
            subst ha_eq; subst hv0_eq; subst hc0_eq; subst hv1_eq; subst hv2_eq; subst hc2_eq
            unfold do_cycle
            change (S (decodeR (RList.cons v k_l l_tail)) 1 (0 :: (rep 1 (n + 1) ++ 0 :: decodeR r3))) [target_tm]⊢* _
            refine popRList_spec (F := fun ys => S (decodeR (RList.cons v k_l l_tail)) 1 (0 :: (rep 1 (n + 1) ++ 0 :: ys)))
              (S_nil_r3 (decodeR (RList.cons v k_l l_tail)) 1 n) r3 _ (fun c r_tail => ?_)
            simp only [bindNat_eq]
            cases hv3 : Nat.beq v 3 with
            | true =>
              have hv_eq : v = 3 := Nat.eq_of_beq_eq_true hv3
              subst hv_eq
              change _ [target_tm]⊢* (decodeCfg
                (CfgRLE.mk Phase.pS l_tail 1 (push1 0 (pushRep 1 (n + (k_l + 1)) (push1 0 (push1 ((k_l + 1) * 2 + c) r_tail))))))
              simp only [decodeCfg, decodeR_push1, decodeR_pushRep, decodeR]
              have hcyc := Cycles (k_l + 1) n (decodeR l_tail) c (decodeR r_tail)
              rw [show n + 1 + (k_l + 1) = n + (k_l + 1) + 1 by omega] at hcyc
              exact hcyc
            | false =>
              have hv2 : Nat.beq v 2 = true := by
                cases Bool.or_eq_true_iff.mp hv23 with
                | inl h => exact h
                | inr h => rw [hv3] at h; contradiction
              have hv_eq : v = 2 := Nat.eq_of_beq_eq_true hv2
              subst hv_eq
              change _ [target_tm]⊢* (decodeCfg
                (CfgRLE.mk Phase.pS l_tail 1 (push1 0 (pushRep 1 (n + (k_l + 1)) (push1 0 (push1 ((k_l + 1) + c) r_tail))))))
              simp only [decodeCfg, decodeR_push1, decodeR_pushRep, decodeR]
              have hcyc := Cycles2 (k_l + 1) n (decodeR l_tail) c (decodeR r_tail)
              rw [show n + 1 + (k_l + 1) = n + (k_l + 1) + 1 by omega] at hcyc
              exact hcyc

lemma step_S_spec (l : RList) (a : Nat) (r : RList) :
    (S (decodeR l) a (decodeR r)) [target_tm]⊢* (decodeCfg (step_S l a r)) := by
  unfold step_S
  cases ha : Nat.beq a 0 with
  | true =>
    have ha0 : a = 0 := Nat.eq_of_beq_eq_true ha
    subst ha0
    exact step_S_a0_spec l r
  | false =>
    exact step_S_pos_spec l a r ha

lemma rle_step_unpacked_spec (p : Phase) (l : RList) (a : Nat) (r : RList) :
    (decodeCfg (CfgRLE.mk p l a r)) [target_tm]⊢* (decodeCfg (rle_step_unpacked p l a r)) := by
  cases p with
  | pS => exact step_S_spec l a r
  | pT => exact step_T_spec l a r
  | pU => exact step_U_spec l a r
  | pV => exact step_V_spec l a r

lemma run_pow_spec (k : Nat) (p : Phase) (l : RList) (a : Nat) (r : RList) :
    (decodeCfg (CfgRLE.mk p l a r)) [target_tm]⊢* (decodeCfg (run_pow k p l a r)) := by
  induction k generalizing p l a r with
  | zero => exact rle_step_unpacked_spec p l a r
  | succ k ih =>
    change (decodeCfg (CfgRLE.mk p l a r)) [target_tm]⊢* (decodeCfg (CfgRLE.rec (run_pow k) (run_pow k p l a r)))
    have h1 := ih p l a r
    cases hc : run_pow k p l a r with
    | mk p' l' a' r' =>
      rw [hc] at h1
      exact zSt h1 (ih p' l' a' r')

lemma run_seq_spec (ks : List Nat) (c : CfgRLE) :
    (decodeCfg c) [target_tm]⊢* (decodeCfg (run_seq ks c)) := by
  induction ks generalizing c with
  | nil => exact ⟨0, rfl⟩
  | cons k ks ih =>
    cases c with
    | mk p l a r =>
      change (decodeCfg (CfgRLE.mk p l a r)) [target_tm]⊢* (decodeCfg (run_seq ks (run_pow k p l a r)))
      exact zSt (run_pow_spec k p l a r) (ih (run_pow k p l a r))

def cfg_init : CfgRLE := CfgRLE.mk Phase.pT RList.nil 2 RList.nil
def cfg_cap : CfgRLE :=
  CfgRLE.mk Phase.pT RList.nil 2
    (RList.cons 0 0 (RList.cons 1 0 (RList.cons 0 0 (RList.cons 6 0
      (RList.cons 1 681 (RList.cons 0 0 (RList.cons 1028 0 RList.nil)))))))

set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

theorem reach_cap_rle :
    run_seq [15, 13, 11, 10, 7, 6, 4, 1, 0] cfg_init = cfg_cap := by decide +kernel

lemma init_to_cap : (init []) [target_tm]⊢* (cap 339) := by
  have h1 := init_to_T
  have h2 := run_seq_spec [15, 13, 11, 10, 7, 6, 4, 1, 0] cfg_init
  rw [reach_cap_rle] at h2
  exact zSt h1 h2

end

lemma multiStep_none_add {c : Cfg (Fin 2) (Fin 6)} {k : Nat}
    (h : multiStep target_tm c k = none) (d : Nat) :
    multiStep target_tm c (k + d) = none := by
  rw [zMa, h]; rfl

theorem reach_arbitrarily_long :
    ∀ m : Nat, ∃ N : Nat, m ≤ N ∧ multiStep target_tm (init []) N = some (cap (m + 339))
  | 0 => by
    obtain ⟨N₀, hN₀⟩ := init_to_cap
    exact ⟨N₀, Nat.zero_le N₀, hN₀⟩
  | m + 1 => by
    obtain ⟨N, h_le, hN⟩ := reach_arbitrarily_long m
    obtain ⟨k, hk_pos, hk⟩ := cap_step (m + 339)
    rw [show (m + 339) + 1 = m + 1 + 339 by omega] at hk
    exact ⟨N + k, by omega, zMt target_tm _ _ _ N k hN hk⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨k, hk⟩
  cases h_step : step target_tm cfg with
  | some cfg' => rfl
  | none =>
    have h_none : multiStep target_tm (init []) (k + 1) = none := by
      rw [zMs, hk]; exact h_step
    obtain ⟨N, h_ge, hN⟩ := reach_arbitrarily_long (k + 1)
    have h_split : N = (k + 1) + (N - (k + 1)) := by omega
    have h_none_N : multiStep target_tm (init []) N = none := by
      rw [h_split]
      exact multiStep_none_add h_none (N - (k + 1))
    rw [hN] at h_none_N
    contradiction

end BusyBeaver.M_1RB0LD_1RC1RF_0RD1RA_1LE1RC_0LA0LD_0RCHHH
