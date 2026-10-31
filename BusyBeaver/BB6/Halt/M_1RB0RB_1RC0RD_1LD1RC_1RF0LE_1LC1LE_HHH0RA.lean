/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RB_1RC0RD_1LD1RC_1RF0LE_1LC1LE_---0RA` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RB_1RC0RD_1LD1RC_1RF0LE_1LC1LE_---0RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RB_1RC0RD_1LD1RC_1RF0LE_1LC1LE_HHH0RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RB_1RC0RD_1LD1RC_1RF0LE_1LC1LE_---0RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5


-- ============================================================================
-- Section 5: Base Lemmas & Shift Rules for Holdout #476 (TM39)
-- ============================================================================


local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
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
@[simp] lemma zPz {α : Type} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z0j {α : Type} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
lemma z0k {α : Type} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih => simp [z0j, Nat.succ_add, ih, List.append_assoc]
lemma z0l {α : Type} (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) := by
  induction n with
  | zero => simp [z0j]
  | succ n ih => simp [z0j, List.append_assoc, ih]

lemma zSm (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]
lemma z0P (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ := ⟨1, zSm tm c₁ c₂ h⟩
lemma z0Q (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, zSm tm c₁ c₂ h⟩
lemma zMa (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c₁ c₂ c₃ n m hn hm⟩
lemma zPs {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma z0R {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c₁ c₂ c₃ n m hn hm⟩
lemma z0T {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
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
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

def IsHaltFrom (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg, (c [target_tm]⊢* cfg) ∧ (step target_tm cfg).isNone

lemma halt_from_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢* c₂) (h₂ : IsHaltFrom c₂) : IsHaltFrom c₁ := by
  rcases h₂ with ⟨cfg, h₂, h₃⟩
  exact ⟨cfg, zSt h₁ h₂, h₃⟩

abbrev W0 : zF := [0]
abbrev W1 : zF := [1]

lemma shift_C (n : Nat) (l r : zB) :
    (l {{C}}> ((W1 ^ n) +> r)) [target_tm]⊢* (((W1 ^ n) +> l) {{C}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{C}}> (W1 +> ((W1 ^ n) +> r))) [target_tm]⊢*
        ((W1 +> l) {{C}}> ((W1 ^ n) +> r)) := by
      dsimp [W1]; execute
    have h2 := ih (W1 +> l) r
    have heq : (W1 ^ n) +> (W1 +> l) = (W1 ^ (n + 1)) +> l := by
      rw [← append_assoc, z0l]
    rw [heq] at h2
    exact zSt h1 h2

lemma shift_E (n : Nat) (l r : zB) :
    (((W1 ^ n) +> l) <{{E}} r) [target_tm]⊢* (l <{{E}} ((W1 ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : ((W1 +> ((W1 ^ n) +> l)) <{{E}} r) [target_tm]⊢*
        (((W1 ^ n) +> l) <{{E}} (W1 +> r)) := by
      dsimp [W1]; execute
    have h2 := ih l (W1 +> r)
    have heq : (W1 ^ n) +> (W1 +> r) = (W1 ^ (n + 1)) +> r := by
      rw [← append_assoc, z0l]
    rw [heq] at h2
    exact zSt h1 h2

lemma bounce_C (n : Nat) (l r : zB) :
    ((W1 +> l) {{C}}> ((W1 ^ n) +> (([0] : zF) +> r))) [target_tm]⊢*
    (l <{{E}} ((W1 ^ n) +> (([0, 1] : zF) +> r))) := by
  have h1 := shift_C n (W1 +> l) (([0] : zF) +> r)
  have heq1 : (W1 ^ n) +> (W1 +> l) = W1 +> ((W1 ^ n) +> l) := by
    rw [← append_assoc, z0l, z0j, append_assoc]
  rw [heq1] at h1
  have h2 : ((W1 +> ((W1 ^ n) +> l)) {{C}}> (([0] : zF) +> r)) [target_tm]⊢*
      (((W1 ^ n) +> l) <{{E}} (([0, 1] : zF) +> r)) := by
    dsimp [W1]; execute
  exact zSt h1 (zSt h2 (shift_E n l (([0, 1] : zF) +> r)))

@[simp]
def LC : List Nat → zB
  | [] => default
  | n :: l => ([0] : zF) +> ((W1 ^ n) +> LC l)

@[simp]
def RC : List Nat → zB
  | [] => default
  | n :: r => ([0, 0, 0] : zF) +> ((W1 ^ n) +> RC r)

def S (l : List Nat) (a b : Nat) (r : List Nat) : Cfg (Fin 2) (Fin 6) :=
  (([0, 0] : zF) +> ((W1 ^ b) +> RC r)) {{B}}> ((W1 ^ a) +> LC l)

lemma Spos (a b : Nat) (l r : List Nat) :
    (S l (a + 2) b r) [target_tm]⊢* (S (a :: l) 0 (b + 1) r) := by
  dsimp only [S, LC, W1, zPz, z0j, List.cons_append, List.nil_append]
  execute

lemma S12 (a b : Nat) (l r : List Nat) :
    (S ((a + 2) :: l) 1 b r) [target_tm]⊢* (S l a 1 (b :: r)) := by
  dsimp only [S, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]
  execute

lemma HS10 (b : Nat) (l r : List Nat) :
    IsHaltFrom (S (0 :: l) 1 b r) := by
  cases l with
  | nil =>
    dsimp only [S, LC, W1, zPz, z0j, List.cons_append, List.nil_append]
    refine ⟨(([1, 0, 0, 0] : zF) +> ((W1 ^ b) +> RC r)) {{F}}> default, ?_, by simp [step, target_tm, F]⟩
    execute
  | cons x0 l1 =>
    dsimp only [S, LC, W1, zPz, z0j, List.cons_append, List.nil_append]
    refine ⟨(([1, 0, 0, 0] : zF) +> ((W1 ^ b) +> RC r)) {{F}}> (([0] : zF) +> ((W1 ^ x0) +> LC l1)), ?_, by simp [step, target_tm, F]⟩
    execute

lemma S112 (a b : Nat) (l r : List Nat) :
    (S (1 :: (a + 2) :: l) 1 b r) [target_tm]⊢* (S ((a + 2) :: l) 2 (b + 1) r) := by
  dsimp only [S, LC, W1, zPz, z0j, List.cons_append, List.nil_append]
  execute

lemma S110 (a b c : Nat) (l r : List Nat) :
    (S (1 :: 0 :: a :: b :: l) 1 c r) [target_tm]⊢* (S ((b + 2) :: l) (a + 2) (c + 1) r) := by
  dsimp only [S, LC]
  have h1 : ((([0, 0] : zF) +> ((W1 ^ c) +> RC r)) {{B}}>
      ((W1 ^ 1) +> (([0] : zF) +> ((W1 ^ 1) +> (([0] : zF) +> ((W1 ^ 0) +>
      (([0] : zF) +> ((W1 ^ a) +> (([0] : zF) +> ((W1 ^ b) +> LC l)))))))))) [target_tm]⊢*
      ((W1 +> (([1, 0, 1, 0, 0, 0] : zF) +> ((W1 ^ c) +> RC r))) {{C}}>
      ((W1 ^ a) +> (([0] : zF) +> ((W1 ^ b) +> LC l)))) := by
    dsimp [W1, list_nat_repeat]; execute
  have h2 := bounce_C a (([1, 0, 1, 0, 0, 0] : zF) +> ((W1 ^ c) +> RC r)) ((W1 ^ b) +> LC l)
  have h3 : ((([1, 0, 1, 0, 0, 0] : zF) +> ((W1 ^ c) +> RC r)) <{{E}}
      ((W1 ^ a) +> (([0, 1] : zF) +> ((W1 ^ b) +> LC l)))) [target_tm]⊢*
      ((W1 +> (([1, 1, 0, 0, 0] : zF) +> ((W1 ^ c) +> RC r))) {{C}}>
      ((W1 ^ a) +> (([0] : zF) +> (([1] : zF) +> ((W1 ^ b) +> LC l))))) := by
    dsimp [W1]; execute
  have h4 := bounce_C a (([1, 1, 0, 0, 0] : zF) +> ((W1 ^ c) +> RC r)) (([1] : zF) +> ((W1 ^ b) +> LC l))
  have h5 : ((([1, 1, 0, 0, 0] : zF) +> ((W1 ^ c) +> RC r)) <{{E}}
      ((W1 ^ a) +> (([0, 1] : zF) +> (([1] : zF) +> ((W1 ^ b) +> LC l))))) [target_tm]⊢*
      ((([0, 0] : zF) +> ((W1 ^ (c + 1)) +> RC r)) {{B}}>
      ((W1 ^ (a + 2)) +> (([0] : zF) +> ((W1 ^ (b + 2)) +> LC l)))) := by
    dsimp [W1, list_nat_repeat]; execute
  exact zSt h1 (zSt h2 (zSt h3 (zSt h4 h5)))

lemma start_S0 (a b m : Nat) (l : List Nat) (r : zB) :
    ((([0, 0] : zF) +> ((W1 ^ m) +> r)) {{B}}> (([0] : zF) +> ((W1 ^ a) +> (([0] : zF) +> ((W1 ^ b) +> LC l))))) [target_tm]⊢*
    (((W1 ^ m) +> r) <{{D}} ((W1 ^ (a + 2)) +> (([0] : zF) +> ((W1 ^ (b + 1)) +> LC l)))) := by
  have h1 : ((([0, 0] : zF) +> ((W1 ^ m) +> r)) {{B}}> (([0] : zF) +> ((W1 ^ a) +> (([0] : zF) +> ((W1 ^ b) +> LC l))))) [target_tm]⊢*
      ((W1 +> (([0, 0] : zF) +> ((W1 ^ m) +> r))) {{C}}> ((W1 ^ a) +> (([0] : zF) +> ((W1 ^ b) +> LC l)))) := by
    dsimp [W1]; execute
  have h2 := bounce_C a (([0, 0] : zF) +> ((W1 ^ m) +> r)) ((W1 ^ b) +> LC l)
  have h3 : ((([0, 0] : zF) +> ((W1 ^ m) +> r)) <{{E}} ((W1 ^ a) +> (([0, 1] : zF) +> ((W1 ^ b) +> LC l)))) [target_tm]⊢*
      (((W1 ^ m) +> r) <{{D}} ((W1 ^ (a + 2)) +> (([0] : zF) +> ((W1 ^ (b + 1)) +> LC l)))) := by
    dsimp [W1, list_nat_repeat]; execute
  exact zSt h1 (zSt h2 h3)

lemma S01 (a b c : Nat) (l r : List Nat) :
    (S (a :: b :: l) 0 1 (c :: r)) [target_tm]⊢* (S ((a + 2) :: (b + 1) :: l) 0 (c + 1) r) := by
  dsimp only [S, LC, RC]
  refine zSt (start_S0 a b 1 l (([0, 0, 0] : zF) +> ((W1 ^ c) +> RC r))) ?_
  dsimp only [W1, zPz, z0j, List.cons_append, List.nil_append]
  execute

lemma S02 (a b c : Nat) (l r : List Nat) :
    (S (a :: b :: l) 0 2 (c :: r)) [target_tm]⊢* (S ((b + 1) :: l) a 1 ((c + 1) :: r)) := by
  dsimp only [S, LC, RC]
  refine zSt (start_S0 a b 2 l (([0, 0, 0] : zF) +> ((W1 ^ c) +> RC r))) ?_
  dsimp only [W1, zPz, z0j, List.cons_append, List.nil_append]
  execute

lemma S03 (a b c d : Nat) (l r : List Nat) :
    (S (a :: b :: l) 0 (c + 3) (d :: r)) [target_tm]⊢* (S (c :: (a + 2) :: (b + 1) :: l) 0 (d + 2) r) := by
  have h_mid : (S (a :: b :: l) 0 (c + 3) (d :: r)) [target_tm]⊢*
      (S ((a + 2) :: (b + 1) :: l) (c + 2) (d + 1) r) := by
    dsimp only [S, LC, RC]
    refine zSt (start_S0 a b (c + 3) l (([0, 0, 0] : zF) +> ((W1 ^ d) +> RC r))) ?_
    have h1 : (((W1 ^ (c + 3)) +> (([0, 0, 0] : zF) +> ((W1 ^ d) +> RC r))) <{{D}}
        ((W1 ^ (a + 2)) +> (([0] : zF) +> ((W1 ^ (b + 1)) +> LC l)))) [target_tm]⊢*
        (((W1 ^ (c + 2)) +> (([0, 0, 0] : zF) +> ((W1 ^ d) +> RC r))) <{{E}}
        (([0] : zF) +> ((W1 ^ (a + 2)) +> (([0] : zF) +> ((W1 ^ (b + 1)) +> LC l))))) := by
      rw [show c + 3 = (c + 2) + 1 from rfl, z0j, append_assoc]
      dsimp only [W1, zPz, z0j, List.cons_append, List.nil_append]
      execute
    refine zSt h1 (zSt (shift_E (c + 2) _ _) ?_)
    dsimp only [W1, zPz, z0j, List.cons_append, List.nil_append]
    execute
  exact zSt h_mid (Spos c (d + 1) ((a + 2) :: (b + 1) :: l) r)

lemma Inc (a b c : Nat) (l r : List Nat) :
    (S ((a + 2) :: b :: l) 0 2 (c :: r)) [target_tm]⊢* (S (a :: (b + 1) :: l) 0 2 ((c + 1) :: r)) :=
  zSt (S02 (a + 2) b c l r) (Spos a 1 ((b + 1) :: l) ((c + 1) :: r))

lemma Incs (n a b c : Nat) (l r : List Nat) :
    (S ((a + n * 2) :: b :: l) 0 2 (c :: r)) [target_tm]⊢* (S (a :: (b + n) :: l) 0 2 ((c + n) :: r)) := by
  induction n generalizing a b c with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 := Inc (a + n * 2) b c l r
    have h2 := ih a (b + 1) (c + 1)
    have heq1 : (a + n * 2) + 2 = a + (n + 1) * 2 := by omega
    have heq2 : (b + 1) + n = b + (n + 1) := by omega
    have heq3 : (c + 1) + n = c + (n + 1) := by omega
    rw [heq1] at h1
    rw [heq2, heq3] at h2
    exact zSt h1 h2

lemma Incs_S02 (x0 x1 c : Nat) (l r : List Nat) :
    (S (x0 :: x1 :: l) 0 2 (c :: r)) [target_tm]⊢*
    (S (((x1 + x0 / 2) + 1) :: l) (x0 % 2) 1 (((c + x0 / 2) + 1) :: r)) := by
  have h1 := Incs (x0 / 2) (x0 % 2) x1 c l r
  have hx0 : x0 % 2 + (x0 / 2) * 2 = x0 := by omega
  rw [hx0] at h1
  exact zSt h1 (S02 (x0 % 2) (x1 + x0 / 2) (c + x0 / 2) l r)

lemma Even_S02_S01 (x0 x1 x2 c : Nat) (l r : List Nat)
    (h_even : Nat.beq (x0 % 2) 0 = true) :
    (S (x0 :: x1 :: x2 :: l) 0 2 (c :: r)) [target_tm]⊢*
    (S (((x1 + x0 / 2) + 3) :: (x2 + 1) :: l) 0 ((c + x0 / 2) + 2) r) := by
  have hrem : x0 % 2 = 0 := Nat.eq_of_beq_eq_true h_even
  have h1 := Incs_S02 x0 x1 c (x2 :: l) r
  rw [hrem] at h1
  exact zSt h1 (S01 ((x1 + x0 / 2) + 1) x2 ((c + x0 / 2) + 1) l r)

lemma Odd_Incs_S02 (x0 x1 c : Nat) (l r : List Nat)
    (h_odd : Nat.beq (x0 % 2) 0 = false) :
    (S (x0 :: x1 :: l) 0 2 (c :: r)) [target_tm]⊢*
    (S (((x1 + x0 / 2) + 1) :: l) 1 1 (((c + x0 / 2) + 1) :: r)) := by
  have hne : x0 % 2 ≠ 0 := Nat.ne_of_beq_eq_false h_odd
  have hrem : x0 % 2 = 1 := by omega
  have h1 := Incs_S02 x0 x1 c l r
  rw [hrem] at h1
  exact h1

lemma Odd_S02_S12_Spos (x0 x1 c : Nat) (l r : List Nat)
    (h_odd : Nat.beq (x0 % 2) 0 = false)
    (h_ge3 : Nat.ble 3 (x1 + x0 / 2) = true) :
    (S (x0 :: x1 :: l) 0 2 (c :: r)) [target_tm]⊢*
    (S ((x1 + x0 / 2 - 3) :: l) 0 2 (1 :: ((c + x0 / 2) + 1) :: r)) := by
  have hle : 3 ≤ x1 + x0 / 2 := Nat.le_of_ble_eq_true h_ge3
  have h1 := Odd_Incs_S02 x0 x1 c l r h_odd
  have h_split : (x1 + x0 / 2) + 1 = ((x1 + x0 / 2 - 3) + 2) + 2 := by omega
  rw [h_split] at h1
  have h2 := S12 ((x1 + x0 / 2 - 3) + 2) 1 l (((c + x0 / 2) + 1) :: r)
  have h3 := Spos (x1 + x0 / 2 - 3) 1 l (1 :: ((c + x0 / 2) + 1) :: r)
  exact zSt h1 (zSt h2 h3)

lemma init_to_S :
    (init []) [target_tm]⊢* (S [1] 1 1 []) := by
  dsimp only [init, Tape.mk₁, S, LC, RC, W1, zPz, z0j, List.cons_append, List.nil_append]
  execute

-- ============================================================================
-- Section 6: Fast Kernel Evaluator
-- ============================================================================

noncomputable section

inductive NList where
  | nil : NList
  | cons (head : Nat) (tail : NList) : NList
deriving DecidableEq, Repr

inductive StepRes where
  | halted : StepRes
  | running (l : NList) (a : Nat) (b : Nat) (r : NList) : StepRes
deriving DecidableEq, Repr

def bindNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  (Nat.rec (fun _ => k 0) (fun m _ k => k m) (Nat.add 1 n) : (Nat → α) → α) k

def forceNList (rest : NList) (k : NList → NList) : NList :=
  k rest

def mkCons (n : Nat) (rest : NList) : NList :=
  bindNat n (fun n' => forceNList rest (NList.cons n'))

def forceNListS (xs : NList) (k : NList → StepRes) : StepRes :=
  k xs

def mkRunning (l : NList) (a b : Nat) (r : NList) : StepRes :=
  forceNListS l (fun l' => forceNListS r (fun r' => bindNat a (fun a' => bindNat b (fun b' => StepRes.running l' a' b' r'))))

def popNList {α : Type} (xs : NList) (k : Nat → NList → α) : α :=
  (NList.rec (fun k => k 0 NList.nil) (fun h t _ k => k h t) xs : (Nat → NList → α) → α) k

def sweep_r_nil (l : NList) (c : Nat) : StepRes :=
  popNList l (fun x0 l1 =>
    popNList l1 (fun x1 l2 =>
      mkRunning (mkCons c (mkCons (Nat.add x0 2) (mkCons (Nat.add x1 1) l2))) 0 2 NList.nil))

def sweep_r_cons_branch (is0 : Bool) : (NList → Nat → StepRes) → NList → Nat → NList → StepRes :=
  Bool.rec
    (fun ih l_next d _ => bindNat (Nat.sub d 1) (fun d' => ih l_next d'))
    (fun _ l_next _ r1 => mkRunning l_next 0 2 r1)
    is0

def sweep_r_cons (d : Nat) (r1 : NList) (ih : NList → Nat → StepRes) (l : NList) (c : Nat) : StepRes :=
  popNList l (fun x0 l1 =>
    popNList l1 (fun x1 l2 =>
      forceNListS (mkCons c (mkCons (Nat.add x0 2) (mkCons (Nat.add x1 1) l2))) (fun l_next =>
        sweep_r_cons_branch (Nat.beq d 0) ih l_next d r1)))

def sweep_r (r : NList) (l : NList) (c : Nat) : StepRes :=
  (NList.rec sweep_r_nil sweep_r_cons r : NList → Nat → StepRes) l c

def finish_even_branch (is0 : Bool) : NList → Nat → NList → StepRes :=
  Bool.rec
    (fun l_new cn r1 => bindNat (Nat.sub cn 1) (fun cn' => sweep_r r1 l_new cn'))
    (fun l_new _ r1 => mkRunning l_new 0 2 r1)
    is0

def finish_even (l_new : NList) (cn : Nat) (r1 : NList) : StepRes :=
  forceNListS l_new (fun l_new' => finish_even_branch (Nat.beq cn 0) l_new' cn r1)

def sweep_l_odd_nil_branch (ge3 : Bool) : Nat → Nat → NList → StepRes :=
  Bool.rec
    (fun n cn r1 => mkRunning (mkCons (Nat.add n 1) NList.nil) 1 1 (mkCons (Nat.add cn 1) r1))
    (fun n cn r1 => mkRunning (mkCons (Nat.sub n 3) NList.nil) 0 2 (mkCons 1 (mkCons (Nat.add cn 1) r1)))
    ge3

def sweep_l_nil_branch (is_even : Bool) : Nat → Nat → NList → StepRes :=
  Bool.rec
    (fun n cn r1 => sweep_l_odd_nil_branch (Nat.ble 3 n) n cn r1)
    (fun n cn r1 => finish_even (mkCons (Nat.add n 3) (mkCons 1 NList.nil)) cn r1)
    is_even

def sweep_l_nil (x0 : Nat) (r : NList) : StepRes :=
  popNList r (fun c r1 =>
    bindNat (Nat.div x0 2) (fun n =>
    bindNat (Nat.mod x0 2) (fun rem =>
    bindNat (Nat.add c n) (fun cn =>
    sweep_l_nil_branch (Nat.beq rem 0) n cn r1))))

def sweep_l_odd_cons_branch (ge3 : Bool) : (Nat → NList → StepRes) → NList → Nat → Nat → NList → StepRes :=
  Bool.rec
    (fun _ l2 x1n cn r1 => mkRunning (mkCons (Nat.add x1n 1) l2) 1 1 (mkCons (Nat.add cn 1) r1))
    (fun ih _ x1n cn r1 =>
      bindNat (Nat.sub x1n 3) (fun x0_next =>
      forceNListS (mkCons 1 (mkCons (Nat.add cn 1) r1)) (fun r_next =>
      ih x0_next r_next)))
    ge3

def sweep_l_cons_branch (is_even : Bool) : (Nat → NList → StepRes) → NList → Nat → Nat → NList → StepRes :=
  Bool.rec
    (fun ih l2 x1n cn r1 => sweep_l_odd_cons_branch (Nat.ble 3 x1n) ih l2 x1n cn r1)
    (fun _ l2 x1n cn r1 =>
      popNList l2 (fun x2 l3 =>
        finish_even (mkCons (Nat.add x1n 3) (mkCons (Nat.add x2 1) l3)) cn r1))
    is_even

def sweep_l_cons (x1 : Nat) (l2 : NList) (ih : Nat → NList → StepRes) (x0 : Nat) (r : NList) : StepRes :=
  popNList r (fun c r1 =>
    bindNat (Nat.div x0 2) (fun n =>
    bindNat (Nat.mod x0 2) (fun rem =>
    bindNat (Nat.add c n) (fun cn =>
    bindNat (Nat.add x1 n) (fun x1n =>
    sweep_l_cons_branch (Nat.beq rem 0) ih l2 x1n cn r1)))))

def sweep_l (l1 : NList) (x0 : Nat) (r : NList) : StepRes :=
  (NList.rec sweep_l_nil sweep_l_cons l1 : Nat → NList → StepRes) x0 r

def step_a1_x1_ge2_branch (ge2 : Bool) : Nat → NList → Nat → NList → StepRes :=
  Bool.rec
    (fun x1 l2 b r => mkRunning (mkCons 1 (mkCons x1 l2)) 1 b r)
    (fun x1 l2 b r => mkRunning (mkCons x1 l2) 2 (Nat.add b 1) r)
    ge2

def step_a1_x1_0_branch (is0 : Bool) : Nat → NList → Nat → NList → StepRes :=
  Bool.rec
    (fun x1 l2 b r => step_a1_x1_ge2_branch (Nat.ble 2 x1) x1 l2 b r)
    (fun _ l2 b r =>
      popNList l2 (fun x2 l3 =>
        popNList l3 (fun x3 l4 =>
          mkRunning (mkCons (Nat.add x3 2) l4) (Nat.add x2 2) (Nat.add b 1) r)))
    is0

def step_a1_x0_ge2_branch (ge2 : Bool) : Nat → NList → Nat → NList → StepRes :=
  Bool.rec
    (fun _ l1 b r =>
      popNList l1 (fun x1 l2 =>
        step_a1_x1_0_branch (Nat.beq x1 0) x1 l2 b r))
    (fun x0 l1 b r => mkRunning l1 (Nat.sub x0 2) 1 (mkCons b r))
    ge2

def step_a1_x0_0_branch (is0 : Bool) : Nat → NList → Nat → NList → StepRes :=
  Bool.rec
    (fun x0 l1 b r => step_a1_x0_ge2_branch (Nat.ble 2 x0) x0 l1 b r)
    (fun _ _ _ _ => StepRes.halted)
    is0

def step_a0_b_ge3_branch (ge3 : Bool) : NList → Nat → NList → StepRes :=
  Bool.rec
    (fun l b r => mkRunning l 0 b r)
    (fun l b r => bindNat (Nat.sub b 3) (fun b' => sweep_r r l b'))
    ge3

def step_a0_b1_branch (is1 : Bool) : NList → Nat → NList → StepRes :=
  Bool.rec
    (fun l b r => step_a0_b_ge3_branch (Nat.ble 3 b) l b r)
    (fun l _ r =>
      popNList l (fun x0 l1 =>
        popNList l1 (fun x1 l2 =>
          popNList r (fun c r1 =>
            mkRunning (mkCons (Nat.add x0 2) (mkCons (Nat.add x1 1) l2)) 0 (Nat.add c 1) r1))))
    is1

def step_a0_b2_branch (is2 : Bool) : NList → Nat → NList → StepRes :=
  Bool.rec
    (fun l b r => step_a0_b1_branch (Nat.beq b 1) l b r)
    (fun l _ r => popNList l (fun x0 l1 => sweep_l l1 x0 r))
    is2

def step_a1_branch (is1 : Bool) : NList → Nat → Nat → NList → StepRes :=
  Bool.rec
    (fun l _ b r => step_a0_b2_branch (Nat.beq b 2) l b r)
    (fun l _ b r => popNList l (fun x0 l1 => step_a1_x0_0_branch (Nat.beq x0 0) x0 l1 b r))
    is1

def step_a_ge2_branch (ge2 : Bool) : NList → Nat → Nat → NList → StepRes :=
  Bool.rec
    (fun l a b r => step_a1_branch (Nat.beq a 1) l a b r)
    (fun l a b r => mkRunning (mkCons (Nat.sub a 2) l) 0 (Nat.add b 1) r)
    ge2

def step_cfg (l : NList) (a b : Nat) (r : NList) : StepRes :=
  step_a_ge2_branch (Nat.ble 2 a) l a b r

def forceListCPS {α : Type} : NList → (NList → α) → α
  | NList.nil, k => k NList.nil
  | NList.cons h t, k =>
    bindNat h (fun h' =>
      forceListCPS t (fun t' =>
        k (NList.cons h' t')))

def forceRes (s : StepRes) : StepRes :=
  StepRes.rec StepRes.halted
    (fun l a b r =>
      forceListCPS l (fun l' =>
        forceListCPS r (fun r' =>
          bindNat a (fun a' =>
            bindNat b (fun b' =>
              StepRes.running l' a' b' r')))))
    s

def rp_step (k : Nat) (ih : NList → Nat → Nat → NList → StepRes) (l : NList) (a b : Nat) (r : NList) : StepRes :=
  StepRes.rec StepRes.halted ih (Bool.rec (ih l a b r) (forceRes (ih l a b r)) (Nat.beq k 5))

def run_pow (k : Nat) (l : NList) (a b : Nat) (r : NList) : StepRes :=
  (Nat.rec step_cfg rp_step k : NList → Nat → Nat → NList → StepRes) l a b r

-- ============================================================================
-- Section 7: Soundness Proof of Fast Kernel Evaluator
-- ============================================================================

@[simp]
lemma bindNat_eq {α : Type} (n : Nat) (k : Nat → α) :
    bindNat n k = k n := by
  unfold bindNat
  rw [show Nat.add 1 n = n + 1 from Nat.add_comm 1 n]

@[simp]
lemma forceNList_eq (rest : NList) (k : NList → NList) :
    forceNList rest k = k rest := by
  cases rest <;> rfl

@[simp]
lemma mkCons_eq (n : Nat) (rest : NList) :
    mkCons n rest = NList.cons n rest := by
  rw [mkCons, bindNat_eq, forceNList_eq]

@[simp]
lemma forceNListS_eq (xs : NList) (k : NList → StepRes) :
    forceNListS xs k = k xs := by
  cases xs <;> rfl

@[simp]
lemma mkRunning_eq (l : NList) (a b : Nat) (r : NList) :
    mkRunning l a b r = StepRes.running l a b r := by
  rw [mkRunning, forceNListS_eq, forceNListS_eq, bindNat_eq, bindNat_eq]

lemma nat_not_le_of_ble_eq_false {a b : Nat} (h : Nat.ble a b = false) : ¬ (a ≤ b) := by
  intro hle
  have h1 : Nat.ble a b = true := Nat.ble_eq_true_of_le hle
  rw [h] at h1
  contradiction

@[simp]
def denote_list : NList → List Nat
  | .nil => []
  | .cons h t => h :: denote_list t

def StepSpec (c : Cfg (Fin 2) (Fin 6)) : StepRes → Prop
  | .halted => IsHaltFrom c
  | .running l a b r => c [target_tm]⊢* S (denote_list l) a b (denote_list r)

lemma step_spec_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : StepRes}
    (h₁₂ : c₁ [target_tm]⊢* c₂) (h₂ : StepSpec c₂ res) :
    StepSpec c₁ res := by
  cases res with
  | halted => exact halt_from_trans h₁₂ h₂
  | running l a b r => exact zSt h₁₂ h₂

lemma S_nil_l (a b : Nat) (r : List Nat) :
    S [] a b r = S [0] a b r := by
  simp [S, LC, W1, z0i]

lemma S_nil_l1 (x0 a b : Nat) (r : List Nat) :
    S [x0] a b r = S [x0, 0] a b r := by
  simp [S, LC, W1, z0i]

lemma S_nil_l2 (x0 x1 a b : Nat) (r : List Nat) :
    S [x0, x1] a b r = S [x0, x1, 0] a b r := by
  simp [S, LC, W1, z0i]

lemma S_nil_l3 (x0 x1 x2 a b : Nat) (r : List Nat) :
    S [x0, x1, x2] a b r = S [x0, x1, x2, 0] a b r := by
  simp [S, LC, W1, z0i]

lemma S_nil_r (l : List Nat) (a b : Nat) :
    S l a b [] = S l a b [0] := by
  simp [S, RC, W1, z0i]

lemma pop_l_spec {a b : Nat} {r : List Nat} {k : Nat → NList → StepRes} (l : NList)
    (hk : ∀ x0 l1, StepSpec (S (x0 :: denote_list l1) a b r) (k x0 l1)) :
    StepSpec (S (denote_list l) a b r) (popNList l k) := by
  cases l with
  | nil =>
    change StepSpec (S [] a b r) (k 0 NList.nil)
    rw [S_nil_l]
    exact hk 0 NList.nil
  | cons x0 l1 =>
    exact hk x0 l1

lemma pop_l1_spec {a b : Nat} {r : List Nat} {k : Nat → NList → StepRes} (x0 : Nat) (l1 : NList)
    (hk : ∀ x1 l2, StepSpec (S (x0 :: x1 :: denote_list l2) a b r) (k x1 l2)) :
    StepSpec (S (x0 :: denote_list l1) a b r) (popNList l1 k) := by
  cases l1 with
  | nil =>
    change StepSpec (S [x0] a b r) (k 0 NList.nil)
    rw [S_nil_l1]
    exact hk 0 NList.nil
  | cons x1 l2 =>
    exact hk x1 l2

lemma pop_l2_spec {a b : Nat} {r : List Nat} {k : Nat → NList → StepRes} (x0 x1 : Nat) (l2 : NList)
    (hk : ∀ x2 l3, StepSpec (S (x0 :: x1 :: x2 :: denote_list l3) a b r) (k x2 l3)) :
    StepSpec (S (x0 :: x1 :: denote_list l2) a b r) (popNList l2 k) := by
  cases l2 with
  | nil =>
    change StepSpec (S [x0, x1] a b r) (k 0 NList.nil)
    rw [S_nil_l2]
    exact hk 0 NList.nil
  | cons x2 l3 =>
    exact hk x2 l3

lemma pop_l3_spec {a b : Nat} {r : List Nat} {k : Nat → NList → StepRes} (x0 x1 x2 : Nat) (l3 : NList)
    (hk : ∀ x3 l4, StepSpec (S (x0 :: x1 :: x2 :: x3 :: denote_list l4) a b r) (k x3 l4)) :
    StepSpec (S (x0 :: x1 :: x2 :: denote_list l3) a b r) (popNList l3 k) := by
  cases l3 with
  | nil =>
    change StepSpec (S [x0, x1, x2] a b r) (k 0 NList.nil)
    rw [S_nil_l3]
    exact hk 0 NList.nil
  | cons x3 l4 =>
    exact hk x3 l4

lemma pop_r_spec {l : List Nat} {a b : Nat} {k : Nat → NList → StepRes} (r : NList)
    (hk : ∀ c r1, StepSpec (S l a b (c :: denote_list r1)) (k c r1)) :
    StepSpec (S l a b (denote_list r)) (popNList r k) := by
  cases r with
  | nil =>
    change StepSpec (S l a b []) (k 0 NList.nil)
    rw [S_nil_r]
    exact hk 0 NList.nil
  | cons c r1 =>
    exact hk c r1

lemma sweep_r_spec (r l : NList) (c : Nat) :
    StepSpec (S (denote_list l) 0 (c + 3) (denote_list r)) (sweep_r r l c) := by
  induction r generalizing l c with
  | nil =>
    change StepSpec (S (denote_list l) 0 (c + 3) []) (sweep_r_nil l c)
    rw [S_nil_r]
    unfold sweep_r_nil
    refine pop_l_spec l (fun x0 l1 => ?_)
    refine pop_l1_spec x0 l1 (fun x1 l2 => ?_)
    simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
    exact S03 x0 x1 c 0 (denote_list l2) []
  | cons d r1 ih =>
    change StepSpec (S (denote_list l) 0 (c + 3) (d :: denote_list r1)) (sweep_r_cons d r1 (sweep_r r1) l c)
    unfold sweep_r_cons
    refine pop_l_spec l (fun x0 l1 => ?_)
    refine pop_l1_spec x0 l1 (fun x1 l2 => ?_)
    simp only [forceNListS_eq]
    have hstep := S03 x0 x1 c d (denote_list l2) (denote_list r1)
    let l_next := mkCons c (mkCons (x0 + 2) (mkCons (x1 + 1) l2))
    have h_lnext : denote_list l_next = c :: (x0 + 2) :: (x1 + 1) :: denote_list l2 := by
      simp [l_next, denote_list]
    cases hd : Nat.beq d 0 with
    | true =>
      have hd0 : d = 0 := Nat.eq_of_beq_eq_true hd
      subst hd0
      change StepSpec _ (mkRunning l_next 0 2 r1)
      rw [mkRunning_eq]
      dsimp [StepSpec]
      rw [h_lnext]
      exact hstep
    | false =>
      have hd_ne : d ≠ 0 := Nat.ne_of_beq_eq_false hd
      change StepSpec _ (bindNat (d - 1) (fun d' => sweep_r r1 l_next d'))
      rw [bindNat_eq]
      have h_b : d + 2 = (d - 1) + 3 := by omega
      rw [h_b, ← h_lnext] at hstep
      exact step_spec_trans hstep (ih l_next (d - 1))

lemma finish_even_spec (l_new : NList) (cn : Nat) (r1 : NList) :
    StepSpec (S (denote_list l_new) 0 (cn + 2) (denote_list r1)) (finish_even l_new cn r1) := by
  unfold finish_even
  rw [forceNListS_eq]
  cases hcn : Nat.beq cn 0 with
  | true =>
    have h0 : cn = 0 := Nat.eq_of_beq_eq_true hcn
    subst h0
    change StepSpec _ (mkRunning l_new 0 2 r1)
    rw [mkRunning_eq]
    exact ⟨0, rfl⟩
  | false =>
    have hne : cn ≠ 0 := Nat.ne_of_beq_eq_false hcn
    change StepSpec _ (bindNat (cn - 1) (fun cn' => sweep_r r1 l_new cn'))
    rw [bindNat_eq]
    have hb : cn + 2 = (cn - 1) + 3 := by omega
    rw [hb]
    exact sweep_r_spec r1 l_new (cn - 1)

lemma sweep_l_spec (l1 : NList) (x0 : Nat) (r : NList) :
    StepSpec (S (x0 :: denote_list l1) 0 2 (denote_list r)) (sweep_l l1 x0 r) := by
  induction l1 generalizing x0 r with
  | nil =>
    change StepSpec (S [x0] 0 2 (denote_list r)) (sweep_l_nil x0 r)
    rw [S_nil_l1]
    unfold sweep_l_nil
    refine pop_r_spec r (fun c r1 => ?_)
    simp only [bindNat_eq]
    cases heven : Nat.beq (x0 % 2) 0 with
    | true =>
      change StepSpec _ (finish_even (mkCons (x0 / 2 + 3) (mkCons 1 NList.nil)) (c + x0 / 2) r1)
      rw [S_nil_l2]
      have h1 := Even_S02_S01 x0 0 0 c [] (denote_list r1) heven
      have h2 := finish_even_spec (mkCons (x0 / 2 + 3) (mkCons 1 NList.nil)) (c + x0 / 2) r1
      simp only [mkCons_eq, denote_list, Nat.zero_add] at h1 h2 ⊢
      exact step_spec_trans h1 h2
    | false =>
      dsimp only [sweep_l_nil_branch]
      cases hge3 : Nat.ble 3 (x0 / 2) with
      | true =>
        change StepSpec _ (mkRunning (mkCons (x0 / 2 - 3) NList.nil) 0 2 (mkCons 1 (mkCons ((c + x0 / 2) + 1) r1)))
        have hge3' : Nat.ble 3 (0 + x0 / 2) = true := by
          simpa [Nat.zero_add] using! hge3
        have h1 := Odd_S02_S12_Spos x0 0 c [] (denote_list r1) heven hge3'
        simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list, Nat.zero_add] at h1 ⊢
        exact h1
      | false =>
        change StepSpec _ (mkRunning (mkCons (x0 / 2 + 1) NList.nil) 1 1 (mkCons ((c + x0 / 2) + 1) r1))
        have h1 := Odd_Incs_S02 x0 0 c [] (denote_list r1) heven
        simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list, Nat.zero_add] at h1 ⊢
        exact h1
  | cons x1 l2 ih =>
    change StepSpec (S (x0 :: x1 :: denote_list l2) 0 2 (denote_list r)) (sweep_l_cons x1 l2 (sweep_l l2) x0 r)
    unfold sweep_l_cons
    refine pop_r_spec r (fun c r1 => ?_)
    simp only [bindNat_eq]
    cases heven : Nat.beq (x0 % 2) 0 with
    | true =>
      change StepSpec _ (popNList l2 (fun x2 l3 => finish_even (mkCons ((x1 + x0 / 2) + 3) (mkCons (x2 + 1) l3)) (c + x0 / 2) r1))
      refine pop_l2_spec x0 x1 l2 (fun x2 l3 => ?_)
      have h1 := Even_S02_S01 x0 x1 x2 c (denote_list l3) (denote_list r1) heven
      have h2 := finish_even_spec (mkCons ((x1 + x0 / 2) + 3) (mkCons (x2 + 1) l3)) (c + x0 / 2) r1
      simp only [mkCons_eq, denote_list] at h2 ⊢
      exact step_spec_trans h1 h2
    | false =>
      dsimp only [sweep_l_cons_branch]
      cases hge3 : Nat.ble 3 (x1 + x0 / 2) with
      | true =>
        change StepSpec _ (bindNat ((x1 + x0 / 2) - 3) (fun x0_next => forceNListS (mkCons 1 (mkCons ((c + x0 / 2) + 1) r1)) (fun r_next => sweep_l l2 x0_next r_next)))
        simp only [bindNat_eq, forceNListS_eq]
        have h1 := Odd_S02_S12_Spos x0 x1 c (denote_list l2) (denote_list r1) heven hge3
        have h2 := ih ((x1 + x0 / 2) - 3) (mkCons 1 (mkCons ((c + x0 / 2) + 1) r1))
        simp only [mkCons_eq, denote_list] at h2 ⊢
        exact step_spec_trans h1 h2
      | false =>
        change StepSpec _ (mkRunning (mkCons ((x1 + x0 / 2) + 1) l2) 1 1 (mkCons ((c + x0 / 2) + 1) r1))
        have h1 := Odd_Incs_S02 x0 x1 c (denote_list l2) (denote_list r1) heven
        simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
        exact h1

lemma step_cfg_spec (l : NList) (a b : Nat) (r : NList) :
    StepSpec (S (denote_list l) a b (denote_list r)) (step_cfg l a b r) := by
  unfold step_cfg
  cases ha2 : Nat.ble 2 a with
  | true =>
    have hle : 2 ≤ a := Nat.le_of_ble_eq_true ha2
    change StepSpec _ (mkRunning (mkCons (a - 2) l) 0 (b + 1) r)
    simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
    have ha : a = (a - 2) + 2 := by omega
    rw [ha]
    exact Spos (a - 2) b (denote_list l) (denote_list r)
  | false =>
    have hlt2 : ¬ (2 ≤ a) := nat_not_le_of_ble_eq_false ha2
    dsimp only [step_a_ge2_branch]
    cases ha1 : Nat.beq a 1 with
    | true =>
      have ha_eq : a = 1 := Nat.eq_of_beq_eq_true ha1
      subst ha_eq
      change StepSpec _ (popNList l (fun x0 l1 => step_a1_x0_0_branch (Nat.beq x0 0) x0 l1 b r))
      refine pop_l_spec l (fun x0 l1 => ?_)
      cases hx0_0 : Nat.beq x0 0 with
      | true =>
        have hx0 : x0 = 0 := Nat.eq_of_beq_eq_true hx0_0
        subst hx0
        exact HS10 b (denote_list l1) (denote_list r)
      | false =>
        have hx0_ne : x0 ≠ 0 := Nat.ne_of_beq_eq_false hx0_0
        dsimp only [step_a1_x0_0_branch]
        cases hx0_2 : Nat.ble 2 x0 with
        | true =>
          have hx0_le : 2 ≤ x0 := Nat.le_of_ble_eq_true hx0_2
          change StepSpec _ (mkRunning l1 (x0 - 2) 1 (mkCons b r))
          simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
          have hx0_eq : x0 = (x0 - 2) + 2 := by omega
          rw [hx0_eq]
          exact S12 (x0 - 2) b (denote_list l1) (denote_list r)
        | false =>
          have hx0_lt2 : ¬ (2 ≤ x0) := nat_not_le_of_ble_eq_false hx0_2
          have hx0_1 : x0 = 1 := by omega
          subst hx0_1
          change StepSpec _ (popNList l1 (fun x1 l2 => step_a1_x1_0_branch (Nat.beq x1 0) x1 l2 b r))
          refine pop_l1_spec 1 l1 (fun x1 l2 => ?_)
          cases hx1_0 : Nat.beq x1 0 with
          | true =>
            have hx1 : x1 = 0 := Nat.eq_of_beq_eq_true hx1_0
            subst hx1
            change StepSpec _ (popNList l2 (fun x2 l3 => popNList l3 (fun x3 l4 => mkRunning (mkCons (x3 + 2) l4) (x2 + 2) (b + 1) r)))
            refine pop_l2_spec 1 0 l2 (fun x2 l3 => ?_)
            refine pop_l3_spec 1 0 x2 l3 (fun x3 l4 => ?_)
            simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
            exact S110 x2 x3 b (denote_list l4) (denote_list r)
          | false =>
            dsimp only [step_a1_x1_0_branch]
            cases hx1_2 : Nat.ble 2 x1 with
            | true =>
              have hx1_le : 2 ≤ x1 := Nat.le_of_ble_eq_true hx1_2
              change StepSpec _ (mkRunning (mkCons x1 l2) 2 (b + 1) r)
              simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
              have hx1_eq : x1 = (x1 - 2) + 2 := by omega
              have hstep := S112 (x1 - 2) b (denote_list l2) (denote_list r)
              rw [← hx1_eq] at hstep
              exact hstep
            | false =>
              change StepSpec _ (mkRunning (mkCons 1 (mkCons x1 l2)) 1 b r)
              simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
              exact ⟨0, rfl⟩
    | false =>
      have ha_ne1 : a ≠ 1 := Nat.ne_of_beq_eq_false ha1
      have ha0 : a = 0 := by omega
      subst ha0
      change StepSpec _ (step_a0_b2_branch (Nat.beq b 2) l b r)
      cases hb2 : Nat.beq b 2 with
      | true =>
        have hb_eq : b = 2 := Nat.eq_of_beq_eq_true hb2
        subst hb_eq
        change StepSpec _ (popNList l (fun x0 l1 => sweep_l l1 x0 r))
        exact pop_l_spec l (fun x0 l1 => sweep_l_spec l1 x0 r)
      | false =>
        change StepSpec _ (step_a0_b1_branch (Nat.beq b 1) l b r)
        cases hb1 : Nat.beq b 1 with
        | true =>
          have hb_eq : b = 1 := Nat.eq_of_beq_eq_true hb1
          subst hb_eq
          change StepSpec _ (popNList l (fun x0 l1 => popNList l1 (fun x1 l2 => popNList r (fun c r1 => mkRunning (mkCons (x0 + 2) (mkCons (x1 + 1) l2)) 0 (c + 1) r1))))
          refine pop_l_spec l (fun x0 l1 => ?_)
          refine pop_l1_spec x0 l1 (fun x1 l2 => ?_)
          refine pop_r_spec r (fun c r1 => ?_)
          simp only [mkRunning_eq, mkCons_eq, StepSpec, denote_list]
          exact S01 x0 x1 c (denote_list l2) (denote_list r1)
        | false =>
          change StepSpec _ (step_a0_b_ge3_branch (Nat.ble 3 b) l b r)
          cases hb3 : Nat.ble 3 b with
          | true =>
            have hb_le : 3 ≤ b := Nat.le_of_ble_eq_true hb3
            change StepSpec _ (bindNat (b - 3) (fun b' => sweep_r r l b'))
            rw [bindNat_eq]
            have hb_eq : b = (b - 3) + 3 := by omega
            rw [hb_eq]
            exact sweep_r_spec r l (b - 3)
          | false =>
            change StepSpec _ (mkRunning l 0 b r)
            rw [mkRunning_eq]
            exact ⟨0, rfl⟩

@[simp]
lemma forceListCPS_eq {α : Type} (xs : NList) (k : NList → α) : forceListCPS xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons h t ih => simp only [forceListCPS, bindNat_eq, ih]

@[simp]
lemma forceRes_eq (s : StepRes) : forceRes s = s := by
  cases s with
  | halted => rfl
  | running l a b r => simp only [forceRes, forceListCPS_eq, bindNat_eq]

lemma run_pow_spec (k : Nat) (l : NList) (a b : Nat) (r : NList) :
    StepSpec (S (denote_list l) a b (denote_list r)) (run_pow k l a b r) := by
  induction k generalizing l a b r with
  | zero => exact step_cfg_spec l a b r
  | succ k ih =>
    have hnorm : Bool.rec (run_pow k l a b r) (forceRes (run_pow k l a b r)) (Nat.beq k 5) = run_pow k l a b r := by
      cases Nat.beq k 5 <;> simp [forceRes_eq]
    change StepSpec _ (StepRes.rec StepRes.halted (run_pow k) (Bool.rec (run_pow k l a b r) (forceRes (run_pow k l a b r)) (Nat.beq k 5)))
    rw [hnorm]
    have h1 := ih l a b r
    cases hc : run_pow k l a b r with
    | halted => rw [hc] at h1; exact h1
    | running l' a' b' r' =>
      rw [hc] at h1
      exact step_spec_trans h1 (ih l' a' b' r')

lemma chain_pow (k : Nat) {l l' : NList} {a a' b b' : Nat} {r r' : NList}
    (h_step : run_pow k l a b r = StepRes.running l' a' b' r')
    (h_next : IsHaltFrom (S (denote_list l') a' b' (denote_list r'))) :
    IsHaltFrom (S (denote_list l) a b (denote_list r)) := by
  have h1 := run_pow_spec k l a b r
  rw [h_step] at h1
  exact halt_from_trans h1 h_next

lemma finish_pow (k : Nat) {l : NList} {a b : Nat} {r : NList}
    (h_halt : run_pow k l a b r = StepRes.halted) :
    IsHaltFrom (S (denote_list l) a b (denote_list r)) := by
  have h1 := run_pow_spec k l a b r
  rw [h_halt] at h1
  exact h1



-- ============================================================================
-- Section 8: Ultra-Fast Closed-Form Kernel Evaluator (`step_combo`) & Soundness
-- ============================================================================

inductive StateL where
  | bad : StateL
  | ok (h0 h1 : Nat) (tail : NList) : StateL
deriving DecidableEq

def strictNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  (Nat.rec (fun _ => k 0) (fun m _ k => k m) (n + 1) : (Nat → α) → α) k

@[simp]
lemma strictNat_eq {α : Type} (n : Nat) (k : Nat → α) :
    strictNat n k = k n := rfl

def rec_zero (_ _ : Nat) (_ : NList) : StateL := StateL.bad

def rec_even (n x1n : Nat) (rest : NList) : StateL :=
  popNList rest (fun x2 rest1 =>
    strictNat (x1n + 5) (fun b1 =>
    strictNat (x2 + 2) (fun b2 =>
      StateL.ok n b1 (.cons b2 rest1))))

def rec_step (_ : Nat) (ih : Nat → Nat → NList → StateL) (x0 x1 : Nat) (rest : NList) : StateL :=
  let n := Nat.shiftRight x0 1
  let x1n := x1 + n
  @Bool.rec (fun _ => StateL)
    (@Bool.rec (fun _ => StateL)
      StateL.bad
      (popNList rest (fun x2 rest1 =>
        StateL.rec StateL.bad
          (fun y0 y1 rest' =>
            strictNat (n + 1) (fun b0 =>
            strictNat (y0 + 2) (fun b1 =>
            strictNat (y1 + 1) (fun b2 =>
              StateL.ok b0 b1 (.cons b2 rest')))))
          (ih (x1n - 3) x2 rest1)))
      (Nat.ble 3 x1n))
    (rec_even n x1n rest)
    (Nat.beq (Nat.land x0 1) 0)

def step_rec_fuel (fuel : Nat) : Nat → Nat → NList → StateL :=
  (Nat.rec rec_zero rec_step fuel : Nat → Nat → NList → StateL)

def step_rec : Nat → Nat → NList → StateL :=
  step_rec_fuel 21

def do_odd_step (x0 x1 x2 : Nat) (rest1 : NList) : StateL :=
  let n := Nat.shiftRight x0 1
  let x1n := x1 + n
  @Bool.rec (fun _ => StateL)
    StateL.bad
    (let u := x1n - 3
     @Bool.rec (fun _ => StateL)
       (StateL.rec StateL.bad
         (fun y0 y1 rest' =>
           strictNat (y0 + 2) (fun b1 =>
           strictNat (y1 + 1) (fun b2 =>
             StateL.ok n b1 (.cons b2 rest'))))
         (step_rec u x2 rest1))
       (popNList rest1 (fun x3 rest2 =>
         let m := Nat.shiftRight u 1
         strictNat (m + 2) (fun b1 =>
         strictNat (x2 + m + 6) (fun b2 =>
         strictNat (x3 + 2) (fun b3 =>
           StateL.ok n b1 (.cons b2 (.cons b3 rest2)))))))
       (Nat.beq (Nat.land u 1) 0))
    (Nat.ble 3 x1n)

lemma shr1_eq_div2 (x : Nat) : Nat.shiftRight x 1 = x / 2 := rfl

lemma land1_eq_mod2 (x : Nat) : Nat.land x 1 = x % 2 :=
  Nat.and_one_is_mod x

lemma S_pad_rest (x0 x1 a b : Nat) (rest : NList) (r : List Nat) :
    S (x0 :: x1 :: denote_list rest) a b r =
      S (x0 :: x1 :: (popNList rest (fun x2 _ => x2)) :: denote_list (popNList rest (fun _ rest1 => rest1))) a b r := by
  cases rest with
  | nil =>
    change S [x0, x1] a b r = S [x0, x1, 0] a b r
    exact S_nil_l2 x0 x1 a b r
  | cons x2 rest1 => rfl

lemma rec_step_fuel_sound (fuel : Nat) :
    ∀ (x0 x1 : Nat) (rest : NList) (y0 y1 : Nat) (rest' : NList) (d : Nat) (r_tail : List Nat),
      step_rec_fuel fuel x0 x1 rest = StateL.ok y0 y1 rest' →
      (S (x0 :: x1 :: denote_list rest) 0 2 (1 :: d :: r_tail)) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 (d + 2) r_tail) := by
  induction fuel with
  | zero =>
    intro _ _ _ _ _ _ _ _ h
    contradiction
  | succ fuel ih =>
    intro x0 x1 rest y0 y1 rest' d r_tail h
    change rec_step fuel (step_rec_fuel fuel) x0 x1 rest = StateL.ok y0 y1 rest' at h
    unfold rec_step at h
    dsimp only at h
    rw [shr1_eq_div2, land1_eq_mod2] at h
    rw [S_pad_rest x0 x1 0 2 rest]
    cases rest with
    | nil =>
      cases hev : Nat.beq (x0 % 2) 0 with
      | true =>
        rw [hev] at h
        change rec_even (x0 / 2) (x1 + x0 / 2) NList.nil = StateL.ok y0 y1 rest' at h
        unfold rec_even popNList at h
        simp only [strictNat_eq, StateL.ok.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have h1 := Even_S02_S01 x0 x1 0 1 [] (d :: r_tail) hev
        have h2 := S03 (x1 + x0 / 2 + 3) 1 (x0 / 2) d [] r_tail
        simp only [denote_list]
        exact zSt h1 (by simpa [Nat.add_comm 1 (x0 / 2), Nat.add_assoc] using! h2)
      | false =>
        rw [hev] at h
        cases hge : Nat.ble 3 (x1 + x0 / 2) with
        | false => rw [hge] at h; contradiction
        | true =>
          rw [hge] at h
          dsimp only [popNList] at h
          cases hrec : step_rec_fuel fuel (x1 + x0 / 2 - 3) 0 NList.nil with
          | bad => rw [hrec] at h; contradiction
          | ok z0 z1 zrest =>
            rw [hrec] at h
            simp only [strictNat_eq, StateL.ok.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            have h1 := Odd_S02_S12_Spos x0 x1 1 [0] (d :: r_tail) hev hge
            have h2 := ih (x1 + x0 / 2 - 3) 0 NList.nil z0 z1 zrest (x0 / 2 + 2) (d :: r_tail) hrec
            have h3 := S03 z0 z1 (x0 / 2 + 1) d (denote_list zrest) r_tail
            exact zSt (by simpa [Nat.add_comm 1 (x0 / 2), Nat.add_assoc] using! h1) (zSt h2 h3)
    | cons x2 rest1 =>
      cases hev : Nat.beq (x0 % 2) 0 with
      | true =>
        rw [hev] at h
        change rec_even (x0 / 2) (x1 + x0 / 2) (NList.cons x2 rest1) = StateL.ok y0 y1 rest' at h
        unfold rec_even popNList at h
        simp only [strictNat_eq, StateL.ok.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have h1 := Even_S02_S01 x0 x1 x2 1 (denote_list rest1) (d :: r_tail) hev
        have h2 := S03 (x1 + x0 / 2 + 3) (x2 + 1) (x0 / 2) d (denote_list rest1) r_tail
        simp only [denote_list]
        exact zSt h1 (by simpa [Nat.add_comm 1 (x0 / 2), Nat.add_assoc] using! h2)
      | false =>
        rw [hev] at h
        cases hge : Nat.ble 3 (x1 + x0 / 2) with
        | false => rw [hge] at h; contradiction
        | true =>
          rw [hge] at h
          dsimp only [popNList] at h
          cases hrec : step_rec_fuel fuel (x1 + x0 / 2 - 3) x2 rest1 with
          | bad => rw [hrec] at h; contradiction
          | ok z0 z1 zrest =>
            rw [hrec] at h
            simp only [strictNat_eq, StateL.ok.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            have h1 := Odd_S02_S12_Spos x0 x1 1 (x2 :: denote_list rest1) (d :: r_tail) hev hge
            have h2 := ih (x1 + x0 / 2 - 3) x2 rest1 z0 z1 zrest (x0 / 2 + 2) (d :: r_tail) hrec
            have h3 := S03 z0 z1 (x0 / 2 + 1) d (denote_list zrest) r_tail
            exact zSt (by simpa [Nat.add_comm 1 (x0 / 2), Nat.add_assoc] using! h1) (zSt h2 h3)

lemma even_step_pos (k x1 x2 : Nat) (rest1 : List Nat) :
    (S ((2 * k + 2) :: x1 :: x2 :: rest1) 0 2 []) [target_tm]⊢*
      (S (k :: (x1 + k + 6) :: (x2 + 2) :: rest1) 0 2 []) := by
  have hev : Nat.beq ((2 * k + 2) % 2) 0 = true := by
    have : (2 * k + 2) % 2 = 0 := by omega
    simp [this]
  have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
  rw [S_nil_r]
  have h1 := Even_S02_S01 (2 * k + 2) x1 x2 0 rest1 [] hev
  rw [hdiv, Nat.zero_add] at h1
  have h2 : S ((x1 + (k + 1) + 3) :: (x2 + 1) :: rest1) 0 ((k + 1) + 2) [] =
            S ((x1 + k + 4) :: (x2 + 1) :: rest1) 0 (k + 3) [0] := by
    rw [S_nil_r]
    have : x1 + (k + 1) + 3 = x1 + k + 4 := by omega
    rw [this]
  exact zSt h1 (by rw [h2]; exact S03 (x1 + k + 4) (x2 + 1) k 0 rest1 [])

lemma even_pow_steps (t q x1 x2 : Nat) (rest1 : List Nat) (hq : 1 ≤ q) :
    (S ((q * 2 ^ (t + 1) - 2) :: x1 :: x2 :: rest1) 0 2 []) [target_tm]⊢*
      (if q = 1 then
        S ((x1 + 2 ^ (t + 1) + 4 * (t + 1) - 3) :: (x2 + 2 * (t + 1) - 1) :: rest1) 0 2 []
      else
        S ((q - 2) :: (x1 + q * 2 ^ (t + 1) - q + 4 * (t + 1)) :: (x2 + 2 * (t + 1)) :: rest1) 0 2 []) := by
  induction t generalizing x1 x2 with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_one]
    split_ifs with hq1
    · subst hq1
      rw [S_nil_r]
      simpa using! Even_S02_S01 0 x1 x2 0 rest1 [] rfl
    · have hq2 : 2 ≤ q := by omega
      have e0 : q * 2 - 2 = 2 * (q - 2) + 2 := by omega
      have e1 : x1 + (q - 2) + 6 = x1 + q * 2 - q + 4 * 1 := by omega
      rw [e0, ← e1]
      exact even_step_pos (q - 2) x1 x2 rest1
  | succ t ih =>
    have hpow : 2 ≤ 2 ^ (t + 1) := by
      have h0 : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by decide)
      have : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; ring
      omega
    have hq2 : 2 ≤ q * 2 ^ (t + 1) := by nlinarith
    have hexp : q * 2 ^ (t + 2) - 2 = 2 * (q * 2 ^ (t + 1) - 2) + 2 := by
      have : q * 2 ^ (t + 2) = 2 * (q * 2 ^ (t + 1)) := by
        rw [show t + 2 = (t + 1) + 1 from rfl, Nat.pow_succ]; ring
      omega
    rw [hexp]
    have h1 := even_step_pos (q * 2 ^ (t + 1) - 2) x1 x2 rest1
    have h2 := ih (x1 + (q * 2 ^ (t + 1) - 2) + 6) (x2 + 2)
    refine zSt h1 ?_
    split_ifs at h2 ⊢ with hq1
    · subst hq1
      simp only [Nat.one_mul] at h2 ⊢
      have e1 : x1 + (2 ^ (t + 1) - 2) + 6 + 2 ^ (t + 1) + 4 * (t + 1) - 3 = x1 + 2 ^ (t + 2) + 4 * (t + 2) - 3 := by
        have : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [show t + 2 = (t + 1) + 1 from rfl, Nat.pow_succ]; ring
        omega
      have e2 : x2 + 2 + 2 * (t + 1) - 1 = x2 + 2 * (t + 2) - 1 := by omega
      rw [e1, e2] at h2; exact h2
    · have e1 : x1 + (q * 2 ^ (t + 1) - 2) + 6 + q * 2 ^ (t + 1) - q + 4 * (t + 1) =
                x1 + q * 2 ^ (t + 2) - q + 4 * (t + 2) := by
        have : q * 2 ^ (t + 2) = 2 * (q * 2 ^ (t + 1)) := by
          rw [show t + 2 = (t + 1) + 1 from rfl, Nat.pow_succ]; ring
        have hq_le : q ≤ q * 2 ^ (t + 1) := by nlinarith
        omega
      have e2 : x2 + 2 + 2 * (t + 1) = x2 + 2 * (t + 2) := by omega
      rw [e1, e2] at h2; exact h2

lemma do_odd_step_sound (x0 x1 x2 : Nat) (rest1 : NList) (y0 y1 : Nat) (rest' : NList)
    (hodd : Nat.beq (x0 % 2) 0 = false)
    (h : do_odd_step x0 x1 x2 rest1 = StateL.ok y0 y1 rest') :
    (S (x0 :: x1 :: x2 :: denote_list rest1) 0 2 []) [target_tm]⊢*
      (S (y0 :: y1 :: denote_list rest') 0 2 []) := by
  unfold do_odd_step at h
  dsimp only at h
  rw [shr1_eq_div2, land1_eq_mod2] at h
  cases hge : Nat.ble 3 (x1 + x0 / 2) with
  | false => rw [hge] at h; contradiction
  | true =>
    rw [hge] at h
    dsimp only at h
    cases hu : Nat.beq ((x1 + x0 / 2 - 3) % 2) 0 with
    | true =>
      rw [hu] at h
      cases rest1 with
      | nil =>
        dsimp only [popNList] at h
        rw [shr1_eq_div2] at h
        simp only [strictNat_eq, StateL.ok.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        rw [S_nil_r]
        have h1 := Odd_S02_S12_Spos x0 x1 0 [x2, 0] [] hodd hge
        have h1' : S (x0 :: x1 :: [x2]) 0 2 [0] = S (x0 :: x1 :: x2 :: [0]) 0 2 [0] := by
          simp [S, LC, W1, z0i]
        have h2 := Even_S02_S01 (x1 + x0 / 2 - 3) x2 0 1 [] [x0 / 2 + 1] hu
        have h3 := S03 (x2 + (x1 + x0 / 2 - 3) / 2 + 3) 1 ((x1 + x0 / 2 - 3) / 2) (x0 / 2 + 1) [] []
        have h4 := S03 ((x1 + x0 / 2 - 3) / 2) (x2 + (x1 + x0 / 2 - 3) / 2 + 5) (x0 / 2) 0 [2] []
        simp only [denote_list, Nat.zero_add] at *
        rw [h1']
        exact zSt h1 (zSt (by simpa [Nat.add_comm 1, Nat.add_assoc] using! h2) (zSt h3 (by simpa [← S_nil_r, Nat.add_assoc] using! h4)))
      | cons x3 rest2 =>
        dsimp only [popNList] at h
        rw [shr1_eq_div2] at h
        simp only [strictNat_eq, StateL.ok.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        rw [S_nil_r]
        have h1 := Odd_S02_S12_Spos x0 x1 0 (x2 :: x3 :: denote_list rest2) [] hodd hge
        have h2 := Even_S02_S01 (x1 + x0 / 2 - 3) x2 x3 1 (denote_list rest2) [x0 / 2 + 1] hu
        have h3 := S03 (x2 + (x1 + x0 / 2 - 3) / 2 + 3) (x3 + 1) ((x1 + x0 / 2 - 3) / 2) (x0 / 2 + 1) (denote_list rest2) []
        have h4 := S03 ((x1 + x0 / 2 - 3) / 2) (x2 + (x1 + x0 / 2 - 3) / 2 + 5) (x0 / 2) 0 ((x3 + 2) :: denote_list rest2) []
        simp only [denote_list, Nat.zero_add] at *
        exact zSt h1 (zSt (by simpa [Nat.add_comm 1, Nat.add_assoc] using! h2) (zSt h3 (by simpa [← S_nil_r, Nat.add_assoc] using! h4)))
    | false =>
      rw [hu] at h
      cases hrec : step_rec (x1 + x0 / 2 - 3) x2 rest1 with
      | bad => rw [hrec] at h; contradiction
      | ok z0 z1 zrest =>
        rw [hrec] at h
        simp only [strictNat_eq, StateL.ok.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        rw [S_nil_r]
        have h1 := Odd_S02_S12_Spos x0 x1 0 (x2 :: denote_list rest1) [] hodd hge
        have h2 := rec_step_fuel_sound 21 (x1 + x0 / 2 - 3) x2 rest1 z0 z1 zrest (x0 / 2 + 1) [] hrec
        have h3 := S03 z0 z1 (x0 / 2) 0 (denote_list zrest) []
        simp only [denote_list, Nat.zero_add] at *
        exact zSt h1 (zSt h2 (by simpa [← S_nil_r, Nat.add_assoc] using! h3))

noncomputable section
def normNListCPS : NList → (NList → StateL) → StateL :=
  NList.rec
    (fun k => k NList.nil)
    (fun h _ ih k =>
      @Nat.rec (fun _ => StateL) StateL.bad (fun vh _ => ih (fun t' => k (NList.cons vh t'))) (Nat.add 1 h))

lemma normNListCPS_eq (xs : NList) (k : NList → StateL) : normNListCPS xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons h t ih =>
    change @Nat.rec (fun _ => StateL) StateL.bad (fun vh _ => normNListCPS t (fun t' => k (NList.cons vh t'))) (Nat.add 1 h) = k (NList.cons h t)
    have h1 : Nat.add 1 h = Nat.succ h := Nat.add_comm 1 h
    rw [h1]
    dsimp only
    exact ih (fun t' => k (NList.cons h t'))

def normStateL (s : StateL) : StateL :=
  StateL.rec StateL.bad (fun h0 h1 tail =>
    @Nat.rec (fun _ => StateL) StateL.bad (fun v0 _ =>
      @Nat.rec (fun _ => StateL) StateL.bad (fun v1 _ =>
        normNListCPS tail (fun tail' => StateL.ok v0 v1 tail'))
        (Nat.add 1 h1))
      (Nat.add 1 h0)) s

lemma normStateL_eq (s : StateL) : normStateL s = s := by
  cases s with
  | bad => rfl
  | ok h0 h1 tail =>
    unfold normStateL
    dsimp only
    have e0 : Nat.add 1 h0 = Nat.succ h0 := Nat.add_comm 1 h0
    have e1 : Nat.add 1 h1 = Nat.succ h1 := Nat.add_comm 1 h1
    rw [e0, e1]
    dsimp only
    exact normNListCPS_eq tail (fun tail' => StateL.ok h0 h1 tail')


@[simp] lemma nat_add_eq (x y : Nat) : x.add y = x + y := rfl
@[simp] lemma nat_sub_eq (x y : Nat) : x.sub y = x - y := rfl

noncomputable def popNList_fast : NList → (Nat → NList → StateL) → StateL :=
  fun xs f => (NList.rec (fun f => f 0 NList.nil) (fun h t _ f => f h t) xs : (Nat → NList → StateL) → StateL) f

lemma popNList_fast_eq : popNList_fast = popNList := by
  funext xs f
  cases xs <;> rfl

noncomputable def rec_step_f (_ : Nat) (ih : Nat → Nat → NList → StateL) (x0 x1 : Nat) (rest : NList) : StateL :=
  let n := Nat.shiftRight x0 1
  let x1n := Nat.add x1 n
  @Bool.rec (fun _ => StateL)
    (@Bool.rec (fun _ => StateL)
      StateL.bad
      (popNList_fast rest (fun x2 rest1 =>
        StateL.rec StateL.bad
          (fun y0 y1 rest' =>
            StateL.ok (Nat.add n 1) (Nat.add y0 2) (NList.cons (Nat.add y1 1) rest'))
          (ih (Nat.sub x1n 3) x2 rest1)))
      (Nat.ble 3 x1n))
    (popNList_fast rest (fun x2 rest1 =>
      StateL.ok n (Nat.add x1n 5) (NList.cons (Nat.add x2 2) rest1)))
    (Nat.beq (Nat.land x0 1) 0)

noncomputable def step_rec_f_fuel (fuel : Nat) : Nat → Nat → NList → StateL :=
  @Nat.rec (fun _ => Nat → Nat → NList → StateL) (fun _ _ _ => StateL.bad) rec_step_f fuel

lemma rec_step_f_eq (f : Nat) (ih : Nat → Nat → NList → StateL) (x0 x1 : Nat) (rest : NList) :
    rec_step_f f ih x0 x1 rest = rec_step f ih x0 x1 rest := by
  unfold rec_step_f rec_step rec_even
  simp only [popNList_fast_eq, nat_add_eq, nat_sub_eq, strictNat_eq]

lemma step_rec_f_fuel_eq (fuel : Nat) : step_rec_f_fuel fuel = step_rec_fuel fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext x0 x1 rest
    change rec_step_f fuel (step_rec_f_fuel fuel) x0 x1 rest = rec_step fuel (step_rec_fuel fuel) x0 x1 rest
    rw [ih]
    exact rec_step_f_eq fuel (step_rec_fuel fuel) x0 x1 rest

noncomputable def ctz_run (fuel : Nat) (k : Nat → Nat → StateL) : Nat → Nat → StateL :=
  @Nat.rec (fun _ => Nat → Nat → StateL) k
    (fun _ ih_c t q => @Bool.rec (fun _ => StateL) (ih_c (Nat.add t 1) (Nat.shiftRight q 1)) (k t q) (Nat.beq (Nat.land q 1) 1))
    fuel

lemma nat_rec_ctz_exists (fuel : Nat) (k : Nat → Nat → StateL) (t0 q0 : Nat) :
    ∃ t q, ctz_run fuel k t0 q0 = k t q := by
  unfold ctz_run
  induction fuel generalizing t0 q0 with
  | zero => exact ⟨t0, q0, rfl⟩
  | succ fuel ih =>
    dsimp only
    cases Nat.beq (Nat.land q0 1) 1
    · exact ih (Nat.add t0 1) (Nat.shiftRight q0 1)
    · exact ⟨t0, q0, rfl⟩

set_option linter.unusedSimpArgs false

lemma shiftLeft_eq_mul_pow : ∀ (q t : Nat), Nat.shiftLeft q t = q * 2 ^ t
  | q, 0 => by simp [Nat.shiftLeft]
  | q, t + 1 => by
    change Nat.shiftLeft (2 * q) t = q * 2 ^ (t + 1)
    rw [shiftLeft_eq_mul_pow (2 * q) t, Nat.pow_succ]
    ring

abbrev ContL := Nat → Nat → Nat → NList → StateL

def CPS_Sound (F : ContL → ContL) : Prop :=
  ∀ (cont : ContL) (y0 y1 : Nat) (rest' : NList),
    (∀ v0 v1 v2 tail, cont v0 v1 v2 tail = StateL.ok y0 y1 rest' →
      (S (v0 :: v1 :: v2 :: denote_list tail) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 [])) →
    ∀ x0 x1 x2 rest1,
      F cont x0 x1 x2 rest1 = StateL.ok y0 y1 rest' →
      (S (x0 :: x1 :: x2 :: denote_list rest1) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 [])

noncomputable def compCPS (F G : ContL → ContL) : ContL → ContL := fun k => F (G k)
noncomputable def apply2 (F : ContL → ContL) : ContL → ContL := fun k => F (F k)

lemma cps_comp {F G : ContL → ContL} (hF : CPS_Sound F) (hG : CPS_Sound G) :
    CPS_Sound (compCPS F G) :=
  fun cont y0 y1 rest' hcont => hF (G cont) y0 y1 rest' (hG cont y0 y1 rest' hcont)

lemma cps_apply2 {F : ContL → ContL} (hF : CPS_Sound F) : CPS_Sound (apply2 F) :=
  cps_comp hF hF

noncomputable def do_odd_k_def
    (popNList_f : NList → (Nat → NList → StateL) → StateL)
    (step_rec_f : Nat → Nat → NList → StateL)
    (cont : ContL)
    (x0 x1 x2 : Nat) (rest1 : NList) : StateL :=
  let n := Nat.shiftRight x0 1
  let x1n := Nat.add x1 n
  @Bool.rec (fun _ => StateL)
    StateL.bad
    (let u := Nat.sub x1n 3
     @Bool.rec (fun _ => StateL)
       (StateL.rec StateL.bad
         (fun y0 y1 rest' =>
           cont n (Nat.add y0 2) (Nat.add y1 1) rest')
         (step_rec_f u x2 rest1))
       (popNList_f rest1 (fun x3 rest2 =>
         let m := Nat.shiftRight u 1
         cont n (Nat.add m 2) (Nat.add (Nat.add x2 m) 6) (NList.cons (Nat.add x3 2) rest2)))
       (Nat.beq (Nat.land u 1) 0))
    (Nat.ble 3 x1n)

lemma do_odd_k_sound
    {popNList_f : NList → (Nat → NList → StateL) → StateL}
    (hpop : popNList_f = popNList)
    {step_rec_f : Nat → Nat → NList → StateL}
    (hsr : step_rec_f = step_rec_fuel 20)
    (cont : ContL) {y0 y1 : Nat} {rest' : NList}
    (hcont : ∀ v0 v1 v2 tail, cont v0 v1 v2 tail = StateL.ok y0 y1 rest' →
      (S (v0 :: v1 :: v2 :: denote_list tail) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 []))
    (x0 x1 x2 : Nat) (rest1 : NList)
    (hodd : Nat.beq (x0 % 2) 0 = false)
    (h : do_odd_k_def popNList_f step_rec_f cont x0 x1 x2 rest1 = StateL.ok y0 y1 rest') :
    (S (x0 :: x1 :: x2 :: denote_list rest1) 0 2 []) [target_tm]⊢*
      (S (y0 :: y1 :: denote_list rest') 0 2 []) := by
  subst hpop; subst hsr
  unfold do_odd_k_def at h
  simp only [nat_add_eq, nat_sub_eq, shr1_eq_div2, land1_eq_mod2] at h
  cases hge : Nat.ble 3 (x1 + x0 / 2) with
  | false => rw [hge] at h; contradiction
  | true =>
    rw [hge] at h
    dsimp only at h
    cases hu : Nat.beq ((x1 + x0 / 2 - 3) % 2) 0 with
    | true =>
      rw [hu] at h
      dsimp only at h
      let x3 := popNList rest1 (fun x3 _ => x3)
      let rest2 := popNList rest1 (fun _ rest2 => rest2)
      have hpop1 : ∀ {f : Nat → NList → StateL}, popNList rest1 f = f x3 rest2 := by
        intro f; cases rest1 <;> rfl
      rw [hpop1] at h
      have hdo : do_odd_step x0 x1 x2 rest1 =
          StateL.ok (x0 / 2) ((x1 + x0 / 2 - 3) / 2 + 2)
            (.cons (x2 + (x1 + x0 / 2 - 3) / 2 + 6) (.cons (x3 + 2) rest2)) := by
        unfold do_odd_step
        simp only [shr1_eq_div2, land1_eq_mod2, hge, hu, hpop1, strictNat_eq]
      exact zSt (do_odd_step_sound x0 x1 x2 rest1 _ _ _ hodd hdo) (hcont _ _ _ _ h)
    | false =>
      rw [hu] at h
      dsimp only at h
      cases hrec : step_rec_fuel 20 (x1 + x0 / 2 - 3) x2 rest1 with
      | bad => rw [hrec] at h; contradiction
      | ok z0 z1 zrest =>
        rw [hrec] at h
        dsimp only at h
        have hstep1 : (S (x0 :: x1 :: x2 :: denote_list rest1) 0 2 []) [target_tm]⊢*
            (S ((x0 / 2) :: (z0 + 2) :: (z1 + 1) :: denote_list zrest) 0 2 []) := by
          rw [S_nil_r]
          have h1 := Odd_S02_S12_Spos x0 x1 0 (x2 :: denote_list rest1) [] hodd hge
          have h2 := rec_step_fuel_sound 20 (x1 + x0 / 2 - 3) x2 rest1 z0 z1 zrest (x0 / 2 + 1) [] hrec
          have h3 := S03 z0 z1 (x0 / 2) 0 (denote_list zrest) []
          simp only [denote_list, Nat.zero_add] at *
          exact zSt h1 (zSt h2 (by simpa [← S_nil_r, Nat.add_assoc] using! h3))
        exact zSt hstep1 (hcont _ _ _ _ h)

noncomputable def step1_k_fuel (fuel : Nat)
    (popNList_f : NList → (Nat → NList → StateL) → StateL)
    (do_odd_k : ContL → ContL)
    (cont : ContL)
    (x0 x1 x2 : Nat) (rest1 : NList) : StateL :=
  @Bool.rec (fun _ => StateL)
    (do_odd_k cont x0 x1 x2 rest1)
    (let h := Nat.add (Nat.shiftRight x0 1) 1
     @Bool.rec (fun _ => StateL)
       (let z := Nat.add x0 2
(ctz_run fuel
         (fun t q =>
           @Bool.rec (fun _ => StateL)
             StateL.bad
             (@Bool.rec (fun _ => StateL)
               (do_odd_k cont (Nat.sub q 2)
                 (Nat.add (Nat.sub (Nat.add x1 z) q) (Nat.mul 4 t))
                 (Nat.add x2 (Nat.mul 2 t))
                 rest1)
               (popNList_f rest1 (fun x3 rest2 =>
                 cont
                   (Nat.sub (Nat.add (Nat.add x1 z) (Nat.mul 4 t)) 3)
                   (Nat.sub (Nat.add x2 (Nat.mul 2 t)) 1)
                   x3 rest2))
               (Nat.beq q 1))
             (Bool.and (Nat.beq z (Nat.shiftLeft q t)) (Bool.and (Nat.beq (Nat.land q 1) 1) (Nat.ble 1 t))))) 2 (Nat.shiftRight h 1))
       (@Bool.rec (fun _ => StateL)
         (do_odd_k cont (Nat.sub h 2) (Nat.add (Nat.add x1 h) 4) (Nat.add x2 2) rest1)
         (popNList_f rest1 (fun x3 rest2 => cont (Nat.add x1 3) (Nat.add x2 1) x3 rest2))
         (Nat.beq h 1))
       (Nat.beq (Nat.land h 1) 1))
    (Nat.beq (Nat.land x0 1) 0)

noncomputable def step1_k_def
    (popNList_f : NList → (Nat → NList → StateL) → StateL)
    (do_odd_k : ContL → ContL) : ContL → ContL :=
  step1_k_fuel 13 popNList_f do_odd_k

lemma step1_k_sound
    {popNList_f : NList → (Nat → NList → StateL) → StateL}
    (hpop : popNList_f = popNList)
    {do_odd_k : ContL → ContL}
    (hdo : ∀ (cont : ContL) {y0 y1 rest'},
      (∀ v0 v1 v2 tail, cont v0 v1 v2 tail = StateL.ok y0 y1 rest' →
        (S (v0 :: v1 :: v2 :: denote_list tail) 0 2 []) [target_tm]⊢*
          (S (y0 :: y1 :: denote_list rest') 0 2 [])) →
      ∀ x0 x1 x2 rest1, Nat.beq (x0 % 2) 0 = false →
        do_odd_k cont x0 x1 x2 rest1 = StateL.ok y0 y1 rest' →
        (S (x0 :: x1 :: x2 :: denote_list rest1) 0 2 []) [target_tm]⊢*
          (S (y0 :: y1 :: denote_list rest') 0 2 [])) :
    CPS_Sound (step1_k_def popNList_f do_odd_k) := by
  subst hpop
  intro cont y0 y1 rest' hcont x0 x1 x2 rest1 h
  unfold step1_k_def step1_k_fuel at h
  simp only [nat_add_eq, nat_sub_eq, shr1_eq_div2, land1_eq_mod2] at h
  cases hev : Nat.beq (x0 % 2) 0 with
  | false =>
    rw [hev] at h
    exact hdo cont hcont x0 x1 x2 rest1 hev h
  | true =>
    rw [hev] at h
    dsimp only at h
    let hv := x0 / 2 + 1
    cases hh : Nat.beq (hv % 2) 1 with
    | true =>
      rw [hh] at h
      dsimp only at h
      have hhv_ge1 : 1 ≤ hv := by dsimp [hv]; omega
      have h_run := even_pow_steps 0 hv x1 x2 (denote_list rest1) hhv_ge1
      have hx0_hv : hv * 2 ^ 1 - 2 = x0 := by
        have hx0_mod : x0 % 2 = 0 := Nat.eq_of_beq_eq_true hev
        dsimp [hv]; omega
      rw [hx0_hv] at h_run
      cases hh1 : Nat.beq hv 1 with
      | true =>
        rw [hh1] at h
        dsimp only at h
        let x3 := popNList rest1 (fun x3 _ => x3)
        let rest2 := popNList rest1 (fun _ rest2 => rest2)
        have hpop1 : ∀ {f : Nat → NList → StateL}, popNList rest1 f = f x3 rest2 := by
          intro f; cases rest1 <;> rfl
        rw [hpop1] at h
        have hhv1 : hv = 1 := Nat.eq_of_beq_eq_true hh1
        simp only [hhv1, ↓reduceIte] at h_run
        have h_run' : (S (x0 :: x1 :: x2 :: denote_list rest1) 0 2 []) [target_tm]⊢*
            (S ((x1 + 3) :: (x2 + 1) :: denote_list rest1) 0 2 []) := by
          simpa using! h_run
        rw [S_pad_rest (x1 + 3) (x2 + 1) 0 2 rest1 []] at h_run'
        exact zSt h_run' (hcont _ _ _ _ h)
      | false =>
        rw [hh1] at h
        dsimp only at h
        have hhv_mod1 : hv % 2 = 1 := Nat.eq_of_beq_eq_true hh
        have hhv_ne1 : hv ≠ 1 := Nat.ne_of_beq_eq_false hh1
        simp only [hhv_ne1, ↓reduceIte] at h_run
        have hh_sub2_odd : Nat.beq ((hv - 2) % 2) 0 = false := by
          have : (hv - 2) % 2 = 1 := by omega
          rw [this]; rfl
        have h1_arith : x1 + hv * 2 ^ (0 + 1) - hv + 4 * (0 + 1) = x1 + hv + 4 := by dsimp [hv]; omega
        have h2_arith : x2 + 2 * (0 + 1) = x2 + 2 := rfl
        rw [h1_arith, h2_arith] at h_run
        exact zSt h_run (hdo cont hcont (hv - 2) (x1 + hv + 4) (x2 + 2) rest1 hh_sub2_odd h)
    | false =>
      rw [hh] at h
      dsimp only at h
      let z := x0 + 2
      rcases nat_rec_ctz_exists 13 _ 2 (hv / 2) with ⟨t, q, h_tq⟩
      rw [h_tq] at h
      simp only [show ∀ a b, Nat.mul a b = a * b from fun _ _ => rfl] at h
      cases hchk : Bool.and (Nat.beq z (Nat.shiftLeft q t)) (Bool.and (Nat.beq (q % 2) 1) (Nat.ble 1 t)) with
      | false => rw [hchk] at h; dsimp only at h; contradiction
      | true =>
        rw [hchk] at h
        dsimp only at h
        simp only [Bool.and_eq_true] at hchk
        rcases hchk with ⟨hz_eq, hq_odd, ht_ge1⟩
        have hz : z = q * 2 ^ t := by rw [← shiftLeft_eq_mul_pow q t]; exact Nat.eq_of_beq_eq_true hz_eq
        have hq_mod : q % 2 = 1 := Nat.eq_of_beq_eq_true hq_odd
        have ht1 : 1 ≤ t := Nat.le_of_ble_eq_true ht_ge1
        have hq1 : 1 ≤ q := by omega
        have h_even_run := even_pow_steps (t - 1) q x1 x2 (denote_list rest1) hq1
        have ht_eq : (t - 1) + 1 = t := by omega
        rw [ht_eq] at h_even_run
        have hx0_eq : q * 2 ^ t - 2 = x0 := by dsimp [z] at hz; omega
        rw [hx0_eq, ← hz] at h_even_run
        cases hq_one : Nat.beq q 1 with
        | true =>
          rw [hq_one] at h
          dsimp only at h
          let x3 := popNList rest1 (fun x3 _ => x3)
          let rest2 := popNList rest1 (fun _ rest2 => rest2)
          have hpop1 : ∀ {f : Nat → NList → StateL}, popNList rest1 f = f x3 rest2 := by
            intro f; cases rest1 <;> rfl
          rw [hpop1] at h
          have hq_is1 : q = 1 := Nat.eq_of_beq_eq_true hq_one
          have hz_1 : 2 ^ t = z := by rw [hz, hq_is1, Nat.one_mul]
          simp only [hq_is1, ↓reduceIte, hz_1] at h_even_run
          rw [S_pad_rest (x1 + z + 4 * t - 3) (x2 + 2 * t - 1) 0 2 rest1 []] at h_even_run
          exact zSt h_even_run (hcont _ _ _ _ h)
        | false =>
          rw [hq_one] at h
          dsimp only at h
          have hq_ne1 : q ≠ 1 := Nat.ne_of_beq_eq_false hq_one
          simp only [hq_ne1, ↓reduceIte] at h_even_run
          have hq_sub2_odd : Nat.beq ((q - 2) % 2) 0 = false := by
            have hmod1 : (q - 2) % 2 = 1 := by omega
            rw [hmod1]; rfl
          exact zSt h_even_run (hdo cont hcont (q - 2) (x1 + z - q + 4 * t) (x2 + 2 * t) rest1 hq_sub2_odd h)

noncomputable def run_tree_16
    (normState_f : StateL → StateL)
    (leaf : Nat → Nat → NList → StateL) :
    Nat → Nat → Nat → NList → StateL :=
  @Nat.rec (fun _ => Nat → Nat → NList → StateL) leaf
    (fun j ih x0 x1 rest =>
      (@Bool.rec (fun _ => StateL → StateL) (fun s => s) normState_f (Nat.beq j 0))
      (StateL.rec StateL.bad ih (ih x0 x1 rest)))

lemma run_tree_16_sound
    {normState_f : StateL → StateL}
    (hnorm : normState_f = normStateL)
    {leaf : Nat → Nat → NList → StateL}
    (hleaf : ∀ x0 x1 rest y0 y1 rest',
      leaf x0 x1 rest = StateL.ok y0 y1 rest' →
      (S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 []))
    (k : Nat) :
    ∀ (x0 x1 : Nat) (rest : NList) (y0 y1 : Nat) (rest' : NList),
      run_tree_16 normState_f leaf k x0 x1 rest = StateL.ok y0 y1 rest' →
      (S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 []) := by
  subst hnorm
  induction k with
  | zero => exact hleaf
  | succ j ih =>
    intro x0 x1 rest y0 y1 rest' h
    let step_j := run_tree_16 normStateL leaf j
    change (@Bool.rec (fun _ => StateL → StateL) (fun s => s) normStateL (Nat.beq j 0))
      (StateL.rec StateL.bad step_j (step_j x0 x1 rest)) = StateL.ok y0 y1 rest' at h
    cases hb0 : Nat.beq j 0 with
    | true =>
      rw [hb0] at h; dsimp only at h; rw [normStateL_eq] at h
      cases hc : step_j x0 x1 rest with
      | bad => rw [hc] at h; contradiction
      | ok m0 m1 mrest =>
        rw [hc] at h
        exact zSt (ih x0 x1 rest m0 m1 mrest hc) (ih m0 m1 mrest y0 y1 rest' h)
    | false =>
      rw [hb0] at h; dsimp only at h
      cases hc : step_j x0 x1 rest with
      | bad => rw [hc] at h; contradiction
      | ok m0 m1 mrest =>
        rw [hc] at h
        exact zSt (ih x0 x1 rest m0 m1 mrest hc) (ih m0 m1 mrest y0 y1 rest' h)

noncomputable def plain_finish_def (v0 v1 v2 : Nat) (tail : NList) : StateL :=
  StateL.ok v0 v1 (NList.cons v2 tail)

noncomputable def run_C_fast_fuel (fuel_rec fuel k : Nat) : Nat → Nat → NList → StateL :=
  ((fun (popNList_f : NList → (Nat → NList → StateL) → StateL) =>
  ((fun (normState_f : StateL → StateL) =>
  ((fun (plain_finish : ContL) =>
  ((fun (step_rec_f : Nat → Nat → NList → StateL) =>
  ((fun (do_odd_k : ContL → ContL) =>
  ((fun (step1_k : ContL → ContL) =>
  ((fun (s2 : ContL → ContL) =>
  ((fun (s4 : ContL → ContL) =>
  ((fun (s8 : ContL → ContL) =>
  ((fun (leaf : Nat → Nat → NList → StateL) =>
    @Nat.rec (fun _ => Nat → Nat → NList → StateL) leaf
      (fun j ih x0 x1 rest =>
        (@Bool.rec (fun _ => StateL → StateL) (fun s => s) normState_f (Nat.beq j 0))
        (StateL.rec StateL.bad ih (ih x0 x1 rest)))
      k)
  (fun x0 x1 rest => popNList_f rest (fun x2 rest1 => apply2 s8 plain_finish x0 x1 x2 rest1))))
  (apply2 s4)))
  (apply2 s2)))
  (apply2 step1_k)))
  (step1_k_fuel fuel popNList_f do_odd_k)))
  (do_odd_k_def popNList_f step_rec_f)))
  (step_rec_f_fuel fuel_rec)))
  plain_finish_def))
  normStateL))
  popNList_fast)

noncomputable def run_C_fast (k : Nat) : Nat → Nat → NList → StateL :=
  run_C_fast_fuel 20 13 k

noncomputable def run_tail13_fuel (fuel_rec fuel : Nat) : Nat → Nat → NList → StateL :=
  ((fun (popNList_f : NList → (Nat → NList → StateL) → StateL) =>
  ((fun (plain_finish : ContL) =>
  ((fun (step_rec_f : Nat → Nat → NList → StateL) =>
  ((fun (do_odd_k : ContL → ContL) =>
  ((fun (step1_k : ContL → ContL) =>
  ((fun (s2 : ContL → ContL) =>
  ((fun (s4 : ContL → ContL) =>
  ((fun (s8 : ContL → ContL) =>
    fun x0 x1 rest => popNList_f rest (fun x2 rest1 => compCPS s8 (compCPS s4 step1_k) plain_finish x0 x1 x2 rest1))
  (apply2 s4)))
  (apply2 s2)))
  (apply2 step1_k)))
  (step1_k_fuel fuel popNList_f do_odd_k)))
  (do_odd_k_def popNList_f step_rec_f)))
  (step_rec_f_fuel fuel_rec)))
  plain_finish_def))
  popNList_fast)

noncomputable def run_tail13 : Nat → Nat → NList → StateL :=
  run_tail13_fuel 20 13

lemma plain_finish_sound (v0 v1 v2 : Nat) (tail : NList) (y0 y1 : Nat) (rest' : NList)
    (h : plain_finish_def v0 v1 v2 tail = StateL.ok y0 y1 rest') :
    (S (v0 :: v1 :: v2 :: denote_list tail) 0 2 []) [target_tm]⊢*
      (S (y0 :: y1 :: denote_list rest') 0 2 []) := by
  unfold plain_finish_def at h
  simp only [StateL.ok.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  dsimp only [denote_list]
  exact ⟨0, rfl⟩

lemma step_rec_f_17_plus_3 : step_rec_f_fuel 20 = step_rec_fuel 20 := step_rec_f_fuel_eq 20

lemma run_leaf_cps_sound
    {popNList_f : NList → (Nat → NList → StateL) → StateL}
    (hpop : popNList_f = popNList)
    {F : ContL → ContL}
    (hF : CPS_Sound F)
    (x0 x1 : Nat) (rest : NList) (y0 y1 : Nat) (rest' : NList)
    (h : popNList_f rest (fun x2 rest1 => F plain_finish_def x0 x1 x2 rest1) = StateL.ok y0 y1 rest') :
    (S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
      (S (y0 :: y1 :: denote_list rest') 0 2 []) := by
  subst hpop
  rw [S_pad_rest x0 x1 0 2 rest []]
  let x2 := popNList rest (fun x2 _ => x2)
  let rest1 := popNList rest (fun _ rest1 => rest1)
  have hpop1 : ∀ {f : Nat → NList → StateL}, popNList rest f = f x2 rest1 := by
    intro f; cases rest <;> rfl
  rw [hpop1] at h
  exact hF plain_finish_def y0 y1 rest' (fun v0 v1 v2 tail => plain_finish_sound v0 v1 v2 tail y0 y1 rest') x0 x1 x2 rest1 h

lemma run_C_fast_sound (k : Nat) :
    ∀ (x0 x1 : Nat) (rest : NList) (y0 y1 : Nat) (rest' : NList),
      run_C_fast k x0 x1 rest = StateL.ok y0 y1 rest' →
      (S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 []) :=
  have hs1 := step1_k_sound popNList_fast_eq (fun cont {_ _ _} hcont => do_odd_k_sound popNList_fast_eq step_rec_f_17_plus_3 cont hcont)
  have hs16 := cps_apply2 (cps_apply2 (cps_apply2 (cps_apply2 hs1)))
  run_tree_16_sound rfl (run_leaf_cps_sound popNList_fast_eq hs16) k

lemma run_tail13_sound :
    ∀ (x0 x1 : Nat) (rest : NList) (y0 y1 : Nat) (rest' : NList),
      run_tail13 x0 x1 rest = StateL.ok y0 y1 rest' →
      (S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 []) :=
  have hs1 := step1_k_sound popNList_fast_eq (fun cont {_ _ _} hcont => do_odd_k_sound popNList_fast_eq step_rec_f_17_plus_3 cont hcont)
  have hs4 := cps_apply2 (cps_apply2 hs1)
  have hs8 := cps_apply2 hs4
  run_leaf_cps_sound popNList_fast_eq (cps_comp hs8 (cps_comp hs4 hs1))

noncomputable def beqNList : NList → NList → Bool :=
  NList.rec
    (fun b => NList.rec true (fun _ _ _ => false) b)
    (fun h1 _ ih b =>
      NList.rec false (fun h2 t2 _ => @Bool.rec (fun _ => Bool) false (ih t2) (Nat.beq h1 h2)) b)

lemma beqNList_sound : ∀ (a b : NList), beqNList a b = true → a = b
  | .nil, .nil, _ => rfl
  | .cons _ _, .nil, h => by simp [beqNList] at h
  | .nil, .cons _ _, h => by simp [beqNList] at h
  | .cons h1 t1, .cons h2 t2, h => by
    simp only [beqNList] at h
    cases heq : Nat.beq h1 h2
    · rw [heq] at h; simp at h
    · rw [heq] at h; dsimp at h
      rw [Nat.eq_of_beq_eq_true heq, beqNList_sound t1 t2 h]

noncomputable def checkStateL (s : StateL) (e0 e1 : Nat) (erest : NList) : Bool :=
  StateL.rec false
    (fun h0 h1 tail =>
      @Bool.rec (fun _ => Bool) false
        (@Bool.rec (fun _ => Bool) false (beqNList tail erest) (Nat.beq h1 e1))
        (Nat.beq h0 e0))
    s

lemma checkStateL_sound {s : StateL} {e0 e1 : Nat} {erest : NList}
    (h : checkStateL s e0 e1 erest = true) :
    s = StateL.ok e0 e1 erest := by
  cases s with
  | bad => simp [checkStateL] at h
  | ok h0 h1 tail =>
    simp only [checkStateL] at h
    cases h0_eq : Nat.beq h0 e0
    · rw [h0_eq] at h; simp at h
    · rw [h0_eq] at h; dsimp at h
      cases h1_eq : Nat.beq h1 e1
      · rw [h1_eq] at h; simp at h
      · rw [h1_eq] at h; dsimp at h
        rw [Nat.eq_of_beq_eq_true h0_eq, Nat.eq_of_beq_eq_true h1_eq, beqNList_sound tail erest h]

lemma chain_C_fast {x0 x1 y0 y1 : Nat} {rest rest' : NList}
    (h_step : checkStateL (run_C_fast 12 x0 x1 rest) y0 y1 rest' = true)
    (h_next : IsHaltFrom (S (y0 :: y1 :: denote_list rest') 0 2 [])) :
    IsHaltFrom (S (x0 :: x1 :: denote_list rest) 0 2 []) :=
  halt_from_trans (run_C_fast_sound 12 x0 x1 rest y0 y1 rest' (checkStateL_sound h_step)) h_next

noncomputable def run_rem_fast (x0 x1 : Nat) (rest : NList) : StateL :=
  let s := run_C_fast 11 x0 x1 rest
  let s := StateL.rec StateL.bad (run_C_fast 10) s
  let s := StateL.rec StateL.bad (run_C_fast 8) s
  let s := StateL.rec StateL.bad (run_C_fast 7) s
  let s := StateL.rec StateL.bad (run_C_fast 6) s
  let s := StateL.rec StateL.bad (run_C_fast 5) s
  let s := StateL.rec StateL.bad (run_C_fast 4) s
  let s := StateL.rec StateL.bad (run_C_fast 0) s
  StateL.rec StateL.bad run_tail13 s

lemma stepL_fast_step (k : Nat) {s : StateL} {y0 y1 : Nat} {rest' : NList}
    (h : StateL.rec StateL.bad (run_C_fast k) s = StateL.ok y0 y1 rest') :
    ∃ x0 x1 rest, s = StateL.ok x0 x1 rest ∧
      ((S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 [])) := by
  cases s with
  | bad => contradiction
  | ok x0 x1 rest => exact ⟨x0, x1, rest, rfl, run_C_fast_sound k x0 x1 rest y0 y1 rest' h⟩

lemma stepL_tail13_step {s : StateL} {y0 y1 : Nat} {rest' : NList}
    (h : StateL.rec StateL.bad run_tail13 s = StateL.ok y0 y1 rest') :
    ∃ x0 x1 rest, s = StateL.ok x0 x1 rest ∧
      ((S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
        (S (y0 :: y1 :: denote_list rest') 0 2 [])) := by
  cases s with
  | bad => contradiction
  | ok x0 x1 rest => exact ⟨x0, x1, rest, rfl, run_tail13_sound x0 x1 rest y0 y1 rest' h⟩

lemma run_rem_fast_sound {x0 x1 y0 y1 : Nat} {rest rest' : NList}
    (h_step : checkStateL (run_rem_fast x0 x1 rest) y0 y1 rest' = true) :
    (S (x0 :: x1 :: denote_list rest) 0 2 []) [target_tm]⊢*
      (S (y0 :: y1 :: denote_list rest') 0 2 []) := by
  have h := checkStateL_sound h_step
  unfold run_rem_fast at h
  rcases stepL_tail13_step h with ⟨a1, b1, r1, h1, s1⟩
  rcases stepL_fast_step 0 h1 with ⟨a2, b2, r2, h2, s2⟩
  rcases stepL_fast_step 4 h2 with ⟨a3, b3, r3, h3, s3⟩
  rcases stepL_fast_step 5 h3 with ⟨a4, b4, r4, h4, s4⟩
  rcases stepL_fast_step 6 h4 with ⟨a5, b5, r5, h5, s5⟩
  rcases stepL_fast_step 7 h5 with ⟨a6, b6, r6, h6, s6⟩
  rcases stepL_fast_step 8 h6 with ⟨a7, b7, r7, h7, s7⟩
  rcases stepL_fast_step 10 h7 with ⟨a8, b8, r8, h8, s8⟩
  have s9 := run_C_fast_sound 11 x0 x1 rest a8 b8 r8 h8
  exact zSt s9 (zSt s8 (zSt s7 (zSt s6 (zSt s5 (zSt s4 (zSt s3 (zSt s2 s1)))))))

lemma chain_rem_fast {x0 x1 y0 y1 : Nat} {rest rest' : NList}
    (h_step : checkStateL (run_rem_fast x0 x1 rest) y0 y1 rest' = true)
    (h_next : IsHaltFrom (S (y0 :: y1 :: denote_list rest') 0 2 [])) :
    IsHaltFrom (S (x0 :: x1 :: denote_list rest) 0 2 []) :=
  halt_from_trans (run_rem_fast_sound h_step) h_next

noncomputable def rec_step_comb (ih : Nat → Nat → NList → StateL) (x0 x1 : Nat) (rest : NList) : StateL :=
  let n := Nat.shiftRight x0 1
  let x1n := Nat.add x1 n
  @Bool.rec (fun _ => Nat → Nat → NList → StateL)
    (fun n x1n rest =>
      @Bool.rec (fun _ => StateL)
        StateL.bad
        (popNList_fast rest (fun x2 rest1 =>
          StateL.rec StateL.bad
            (fun y0 y1 rest' =>
              StateL.ok (Nat.add n 1) (Nat.add y0 2) (NList.cons (Nat.add y1 1) rest'))
            (ih (Nat.sub x1n 3) x2 rest1)))
        (Nat.ble 3 x1n))
    (fun n x1n rest =>
      popNList_fast rest (fun x2 rest1 =>
        StateL.ok n (Nat.add x1n 5) (NList.cons (Nat.add x2 2) rest1)))
    (Nat.beq (Nat.land x0 1) 0)
    n x1n rest

lemma rec_step_comb_eq (ih : Nat → Nat → NList → StateL) :
    rec_step_comb ih = rec_step_f 0 ih := by
  funext x0 x1 rest
  unfold rec_step_comb rec_step_f
  cases Nat.beq (Nat.land x0 1) 0 <;> rfl

noncomputable def step_rec_comb_fuel : Nat → Nat → Nat → NList → StateL :=
  @Nat.rec (fun _ => Nat → Nat → NList → StateL)
    (fun _ _ _ => StateL.bad)
    (fun _ ih => rec_step_comb ih)

lemma step_rec_comb_eq (fuel : Nat) :
    step_rec_comb_fuel fuel = step_rec_f_fuel fuel := by
  induction fuel with
  | zero => rfl
  | succ f ih =>
    change rec_step_comb (step_rec_comb_fuel f) = rec_step_f f (step_rec_f_fuel f)
    rw [ih]
    exact rec_step_comb_eq (step_rec_f_fuel f)

noncomputable def do_odd_comb (step_rec_f : Nat → Nat → NList → StateL) : ContL → ContL :=
  fun cont x0 x1 x2 rest1 =>
    let n := Nat.shiftRight x0 1
    let x1n := Nat.add x1 n
    @Bool.rec (fun _ => StateL)
      StateL.bad
      (let u := Nat.sub x1n 3
       @Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
         (fun cont n u x2 rest1 =>
           StateL.rec StateL.bad
             (fun y0 y1 rest' => cont n (Nat.add y0 2) (Nat.add y1 1) rest')
             (step_rec_f u x2 rest1))
         (fun cont n u x2 rest1 =>
           popNList_fast rest1 (fun x3 rest2 =>
             let m := Nat.shiftRight u 1
             cont n (Nat.add m 2) (Nat.add (Nat.add x2 m) 6) (NList.cons (Nat.add x3 2) rest2)))
         (Nat.beq (Nat.land u 1) 0)
         cont n u x2 rest1)
      (Nat.ble 3 x1n)

lemma do_odd_comb_eq (step_rec_f : Nat → Nat → NList → StateL) :
    do_odd_comb step_rec_f = do_odd_k_def popNList_fast step_rec_f := by
  funext cont x0 x1 x2 rest1
  unfold do_odd_comb do_odd_k_def
  dsimp only
  cases Nat.ble 3 (Nat.add x1 (Nat.shiftRight x0 1)) <;>
    cases Nat.beq (Nat.land (Nat.sub (Nat.add x1 (Nat.shiftRight x0 1)) 3) 1) 0 <;> rfl

noncomputable def step1_comb_fuel (fuel : Nat) (do_odd_k : ContL → ContL) : ContL → ContL :=
  fun cont x0 =>
    @Bool.rec (fun _ => Nat → Nat → NList → StateL)
      (do_odd_k cont x0)
      (fun x1 x2 rest1 =>
        let h := Nat.add (Nat.shiftRight x0 1) 1
        @Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
          (fun c h x1 x2 rest1 =>
            let z := Nat.add x0 2
            ctz_run fuel
              (fun t q =>
                @Bool.rec (fun _ => StateL)
                  StateL.bad
                  (@Bool.rec (fun _ => StateL)
                    (do_odd_k c (Nat.sub q 2)
                      (Nat.add (Nat.sub (Nat.add x1 z) q) (Nat.mul 4 t))
                      (Nat.add x2 (Nat.mul 2 t))
                      rest1)
                    (popNList_fast rest1 (fun x3 rest2 =>
                      c
                        (Nat.sub (Nat.add (Nat.add x1 z) (Nat.mul 4 t)) 3)
                        (Nat.sub (Nat.add x2 (Nat.mul 2 t)) 1)
                        x3 rest2))
                    (Nat.beq q 1))
                  (Bool.and (Nat.beq z (Nat.shiftLeft q t)) (Bool.and (Nat.beq (Nat.land q 1) 1) (Nat.ble 1 t)))) 2 (Nat.shiftRight h 1))
          (@Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
            (fun c h x1 x2 rest1 =>
              do_odd_k c (Nat.sub h 2) (Nat.add (Nat.add x1 h) 4) (Nat.add x2 2) rest1)
            (fun c _ x1 x2 rest1 =>
              popNList_fast rest1 (fun x3 rest2 => c (Nat.add x1 3) (Nat.add x2 1) x3 rest2))
            (Nat.beq h 1))
          (Nat.beq (Nat.land h 1) 1)
          cont h x1 x2 rest1)
      (Nat.beq (Nat.land x0 1) 0)

lemma step1_comb_fuel_eq (fuel : Nat) (do_odd_k : ContL → ContL) :
    step1_comb_fuel fuel do_odd_k = step1_k_fuel fuel popNList_fast do_odd_k := by
  funext cont x0 x1 x2 rest1
  unfold step1_comb_fuel step1_k_fuel
  dsimp only
  cases Nat.beq (Nat.land x0 1) 0 with
  | false => rfl
  | true =>
    cases Nat.beq (Nat.land (Nat.add (Nat.shiftRight x0 1) 1) 1) 1 with
    | false => rfl
    | true => cases Nat.beq (Nat.add (Nat.shiftRight x0 1) 1) 1 <;> rfl

lemma step1_comb_eq (do_odd_k : ContL → ContL) :
    step1_comb_fuel 13 do_odd_k = step1_k_def popNList_fast do_odd_k :=
  step1_comb_fuel_eq 13 do_odd_k

noncomputable def run_C_fast_comb_fuel (fuel_rec fuel k : Nat) : Nat → Nat → NList → StateL :=
  ((fun (popNList_f : NList → (Nat → NList → StateL) → StateL) =>
  ((fun (normState_f : StateL → StateL) =>
  ((fun (plain_finish : ContL) =>
  ((fun (rec_even_br : Nat → Nat → NList → StateL) =>
  ((fun (rec_odd_br : (Nat → Nat → NList → StateL) → Nat → Nat → NList → StateL) =>
  ((fun (step_rec_f : Nat → Nat → NList → StateL) =>
  ((fun (odd_even_br : ContL → Nat → Nat → Nat → NList → StateL) =>
  ((fun (odd_odd_br : ContL → Nat → Nat → Nat → NList → StateL) =>
  ((fun (do_odd_k : ContL → ContL) =>
  ((fun (ev_h1_one : ContL → Nat → Nat → NList → StateL) =>
  ((fun (ev_h1_gt1 : ContL → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_ctz_q1 : ContL → Nat → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_ctz_qgt1 : ContL → Nat → Nat → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_h_even : ContL → Nat → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_branch : ContL → ContL) =>
  ((fun (step1_k : ContL → ContL) =>
  ((fun (s2 : ContL → ContL) =>
  ((fun (s4 : ContL → ContL) =>
  ((fun (s8 : ContL → ContL) =>
  ((fun (leaf : Nat → Nat → NList → StateL) =>
    @Nat.rec (fun _ => Nat → Nat → NList → StateL) leaf
      (fun j ih x0 x1 rest =>
        (@Bool.rec (fun _ => StateL → StateL) (fun s => s) normState_f (Nat.beq j 0))
        (StateL.rec StateL.bad ih (ih x0 x1 rest)))
      k)
  (fun x0 x1 rest => popNList_f rest (fun x2 rest1 => s8 (s8 plain_finish) x0 x1 x2 rest1))))
  (fun cont => s4 (s4 cont))))
  (fun cont => s2 (s2 cont))))
  (fun cont => step1_k (step1_k cont))))
  (fun cont x0 =>
    @Bool.rec (fun _ => Nat → Nat → NList → StateL)
      (do_odd_k cont x0)
      (ev_branch cont x0)
      (Nat.beq (Nat.land x0 1) 0))))
  (fun cont x0 x1 x2 rest1 =>
    let h := Nat.add (Nat.shiftRight x0 1) 1
    @Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
      (fun c => ev_h_even c x0)
      (@Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
        ev_h1_gt1
        (fun c _ => ev_h1_one c)
        (Nat.beq h 1))
      (Nat.beq (Nat.land h 1) 1)
      cont h x1 x2 rest1)))
  (fun cont x0 h x1 x2 rest1 =>
    let z := Nat.add x0 2
    ctz_run fuel
      (fun t q =>
        @Bool.rec (fun _ => StateL)
          StateL.bad
          (@Bool.rec (fun _ => StateL)
            (ev_ctz_qgt1 cont x1 z q t x2 rest1)
            (ev_ctz_q1 cont x1 z t x2 rest1)
            (Nat.beq q 1))
          (Bool.and (Nat.beq z (Nat.shiftLeft q t)) (Bool.and (Nat.beq (Nat.land q 1) 1) (Nat.ble 1 t)))) 2 (Nat.shiftRight h 1))))
  (fun cont x1 z q t x2 rest1 =>
    do_odd_k cont (Nat.sub q 2) (Nat.add (Nat.sub (Nat.add x1 z) q) (Nat.mul 4 t)) (Nat.add x2 (Nat.mul 2 t)) rest1)))
  (fun cont x1 z t x2 rest1 =>
    popNList_f rest1 (fun x3 rest2 =>
      cont (Nat.sub (Nat.add (Nat.add x1 z) (Nat.mul 4 t)) 3) (Nat.sub (Nat.add x2 (Nat.mul 2 t)) 1) x3 rest2))))
  (fun cont h x1 x2 rest1 =>
    do_odd_k cont (Nat.sub h 2) (Nat.add (Nat.add x1 h) 4) (Nat.add x2 2) rest1)))
  (fun cont x1 x2 rest1 =>
    popNList_f rest1 (fun x3 rest2 => cont (Nat.add x1 3) (Nat.add x2 1) x3 rest2))))
  (fun cont x0 x1 x2 rest1 =>
    let n := Nat.shiftRight x0 1
    let x1n := Nat.add x1 n
    @Bool.rec (fun _ => StateL)
      StateL.bad
      (let u := Nat.sub x1n 3
       @Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
         odd_odd_br
         odd_even_br
         (Nat.beq (Nat.land u 1) 0)
         cont n u x2 rest1)
      (Nat.ble 3 x1n))))
  (fun cont n u x2 rest1 =>
    StateL.rec StateL.bad
      (fun y0 y1 rest' => cont n (Nat.add y0 2) (Nat.add y1 1) rest')
      (step_rec_f u x2 rest1))))
  (fun cont n u x2 rest1 =>
    popNList_f rest1 (fun x3 rest2 =>
      let m := Nat.shiftRight u 1
      cont n (Nat.add m 2) (Nat.add (Nat.add x2 m) 6) (NList.cons (Nat.add x3 2) rest2)))))
  (@Nat.rec (fun _ => Nat → Nat → NList → StateL)
    (fun _ _ _ => StateL.bad)
    (fun _ ih x0 x1 rest =>
      let n := Nat.shiftRight x0 1
      let x1n := Nat.add x1 n
      @Bool.rec (fun _ => Nat → Nat → NList → StateL)
        (rec_odd_br ih)
        rec_even_br
        (Nat.beq (Nat.land x0 1) 0)
        n x1n rest)
    fuel_rec)))
  (fun ih n x1n rest =>
    @Bool.rec (fun _ => StateL)
      StateL.bad
      (popNList_f rest (fun x2 rest1 =>
        StateL.rec StateL.bad
          (fun y0 y1 rest' =>
            StateL.ok (Nat.add n 1) (Nat.add y0 2) (NList.cons (Nat.add y1 1) rest'))
          (ih (Nat.sub x1n 3) x2 rest1)))
      (Nat.ble 3 x1n))))
  (fun n x1n rest =>
    popNList_f rest (fun x2 rest1 =>
      StateL.ok n (Nat.add x1n 5) (NList.cons (Nat.add x2 2) rest1)))))
  (fun v0 v1 v2 tail => StateL.ok v0 v1 (NList.cons v2 tail))))
  normStateL))
  popNList_fast)

noncomputable def run_C_fast_comb (k : Nat) : Nat → Nat → NList → StateL :=
  run_C_fast_comb_fuel 20 13 k

noncomputable def run_tail13_comb_fuel (fuel_rec fuel : Nat) : Nat → Nat → NList → StateL :=
  ((fun (popNList_f : NList → (Nat → NList → StateL) → StateL) =>
  ((fun (plain_finish : ContL) =>
  ((fun (rec_even_br : Nat → Nat → NList → StateL) =>
  ((fun (rec_odd_br : (Nat → Nat → NList → StateL) → Nat → Nat → NList → StateL) =>
  ((fun (step_rec_f : Nat → Nat → NList → StateL) =>
  ((fun (odd_even_br : ContL → Nat → Nat → Nat → NList → StateL) =>
  ((fun (odd_odd_br : ContL → Nat → Nat → Nat → NList → StateL) =>
  ((fun (do_odd_k : ContL → ContL) =>
  ((fun (ev_h1_one : ContL → Nat → Nat → NList → StateL) =>
  ((fun (ev_h1_gt1 : ContL → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_ctz_q1 : ContL → Nat → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_ctz_qgt1 : ContL → Nat → Nat → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_h_even : ContL → Nat → Nat → Nat → Nat → NList → StateL) =>
  ((fun (ev_branch : ContL → ContL) =>
  ((fun (step1_k : ContL → ContL) =>
  ((fun (s2 : ContL → ContL) =>
  ((fun (s4 : ContL → ContL) =>
  ((fun (s8 : ContL → ContL) =>
    fun x0 x1 rest => popNList_f rest (fun x2 rest1 => s8 (s4 (step1_k plain_finish)) x0 x1 x2 rest1))
  (fun cont => s4 (s4 cont))))
  (fun cont => s2 (s2 cont))))
  (fun cont => step1_k (step1_k cont))))
  (fun cont x0 =>
    @Bool.rec (fun _ => Nat → Nat → NList → StateL)
      (do_odd_k cont x0)
      (ev_branch cont x0)
      (Nat.beq (Nat.land x0 1) 0))))
  (fun cont x0 x1 x2 rest1 =>
    let h := Nat.add (Nat.shiftRight x0 1) 1
    @Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
      (fun c => ev_h_even c x0)
      (@Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
        ev_h1_gt1
        (fun c _ => ev_h1_one c)
        (Nat.beq h 1))
      (Nat.beq (Nat.land h 1) 1)
      cont h x1 x2 rest1)))
  (fun cont x0 h x1 x2 rest1 =>
    let z := Nat.add x0 2
    ctz_run fuel
      (fun t q =>
        @Bool.rec (fun _ => StateL)
          StateL.bad
          (@Bool.rec (fun _ => StateL)
            (ev_ctz_qgt1 cont x1 z q t x2 rest1)
            (ev_ctz_q1 cont x1 z t x2 rest1)
            (Nat.beq q 1))
          (Bool.and (Nat.beq z (Nat.shiftLeft q t)) (Bool.and (Nat.beq (Nat.land q 1) 1) (Nat.ble 1 t)))) 2 (Nat.shiftRight h 1))))
  (fun cont x1 z q t x2 rest1 =>
    do_odd_k cont (Nat.sub q 2) (Nat.add (Nat.sub (Nat.add x1 z) q) (Nat.mul 4 t)) (Nat.add x2 (Nat.mul 2 t)) rest1)))
  (fun cont x1 z t x2 rest1 =>
    popNList_f rest1 (fun x3 rest2 =>
      cont (Nat.sub (Nat.add (Nat.add x1 z) (Nat.mul 4 t)) 3) (Nat.sub (Nat.add x2 (Nat.mul 2 t)) 1) x3 rest2))))
  (fun cont h x1 x2 rest1 =>
    do_odd_k cont (Nat.sub h 2) (Nat.add (Nat.add x1 h) 4) (Nat.add x2 2) rest1)))
  (fun cont x1 x2 rest1 =>
    popNList_f rest1 (fun x3 rest2 => cont (Nat.add x1 3) (Nat.add x2 1) x3 rest2))))
  (fun cont x0 x1 x2 rest1 =>
    let n := Nat.shiftRight x0 1
    let x1n := Nat.add x1 n
    @Bool.rec (fun _ => StateL)
      StateL.bad
      (let u := Nat.sub x1n 3
       @Bool.rec (fun _ => ContL → Nat → Nat → Nat → NList → StateL)
         odd_odd_br
         odd_even_br
         (Nat.beq (Nat.land u 1) 0)
         cont n u x2 rest1)
      (Nat.ble 3 x1n))))
  (fun cont n u x2 rest1 =>
    StateL.rec StateL.bad
      (fun y0 y1 rest' => cont n (Nat.add y0 2) (Nat.add y1 1) rest')
      (step_rec_f u x2 rest1))))
  (fun cont n u x2 rest1 =>
    popNList_f rest1 (fun x3 rest2 =>
      let m := Nat.shiftRight u 1
      cont n (Nat.add m 2) (Nat.add (Nat.add x2 m) 6) (NList.cons (Nat.add x3 2) rest2)))))
  (@Nat.rec (fun _ => Nat → Nat → NList → StateL)
    (fun _ _ _ => StateL.bad)
    (fun _ ih x0 x1 rest =>
      let n := Nat.shiftRight x0 1
      let x1n := Nat.add x1 n
      @Bool.rec (fun _ => Nat → Nat → NList → StateL)
        (rec_odd_br ih)
        rec_even_br
        (Nat.beq (Nat.land x0 1) 0)
        n x1n rest)
    fuel_rec)))
  (fun ih n x1n rest =>
    @Bool.rec (fun _ => StateL)
      StateL.bad
      (popNList_f rest (fun x2 rest1 =>
        StateL.rec StateL.bad
          (fun y0 y1 rest' =>
            StateL.ok (Nat.add n 1) (Nat.add y0 2) (NList.cons (Nat.add y1 1) rest'))
          (ih (Nat.sub x1n 3) x2 rest1)))
      (Nat.ble 3 x1n))))
  (fun n x1n rest =>
    popNList_f rest (fun x2 rest1 =>
      StateL.ok n (Nat.add x1n 5) (NList.cons (Nat.add x2 2) rest1)))))
  (fun v0 v1 v2 tail => StateL.ok v0 v1 (NList.cons v2 tail))))
  popNList_fast)

noncomputable def run_tail13_comb : Nat → Nat → NList → StateL :=
  run_tail13_comb_fuel 20 13

noncomputable def run_comb_wrap (step_rec_f : Nat → Nat → NList → StateL)
    (do_odd_f : (Nat → Nat → NList → StateL) → ContL → ContL)
    (step1_f : (ContL → ContL) → ContL → ContL)
    (s2_f : (ContL → ContL) → ContL → ContL)
    (k : Nat) : Nat → Nat → NList → StateL :=
  let do_odd_k := do_odd_f step_rec_f
  let step1_k := step1_f do_odd_k
  let s2 : ContL → ContL := s2_f step1_k
  let s4 : ContL → ContL := s2_f s2
  let s8 : ContL → ContL := s2_f s4
  let leaf : Nat → Nat → NList → StateL :=
    fun x0 x1 rest => popNList_fast rest (fun x2 rest1 => s2_f s8 plain_finish_def x0 x1 x2 rest1)
  @Nat.rec (fun _ => Nat → Nat → NList → StateL) leaf
    (fun j ih x0 x1 rest =>
      (@Bool.rec (fun _ => StateL → StateL) (fun s => s) normStateL (Nat.beq j 0))
      (StateL.rec StateL.bad ih (ih x0 x1 rest)))
    k

lemma run_C_fast_comb_fuel_eq (fuel_rec fuel k : Nat) :
    run_C_fast_comb_fuel fuel_rec fuel k = run_C_fast_fuel fuel_rec fuel k := by
  have h1 : run_C_fast_comb_fuel fuel_rec fuel k = run_comb_wrap (step_rec_comb_fuel fuel_rec) do_odd_comb (step1_comb_fuel fuel) (fun F cont => F (F cont)) k := rfl
  have h2 : run_C_fast_fuel fuel_rec fuel k = run_comb_wrap (step_rec_f_fuel fuel_rec) (do_odd_k_def popNList_fast) (step1_k_fuel fuel popNList_fast) apply2 k := rfl
  rw [h1, h2, step_rec_comb_eq fuel_rec]
  have hd : do_odd_comb = do_odd_k_def popNList_fast := funext do_odd_comb_eq
  have hs : step1_comb_fuel fuel = step1_k_fuel fuel popNList_fast := funext (step1_comb_fuel_eq fuel)
  have ha : (fun (F : ContL → ContL) cont => F (F cont)) = apply2 := rfl
  rw [hd, hs, ha]

lemma run_C_fast_comb_eq (k : Nat) : run_C_fast_comb k = run_C_fast k :=
  run_C_fast_comb_fuel_eq 20 13 k

noncomputable def run_tail13_wrap (step_rec_f : Nat → Nat → NList → StateL)
    (do_odd_f : (Nat → Nat → NList → StateL) → ContL → ContL)
    (step1_f : (ContL → ContL) → ContL → ContL)
    (s2_f : (ContL → ContL) → ContL → ContL)
    (comp_f : (ContL → ContL) → (ContL → ContL) → ContL → ContL) : Nat → Nat → NList → StateL :=
  let do_odd_k := do_odd_f step_rec_f
  let step1_k := step1_f do_odd_k
  let s2 : ContL → ContL := s2_f step1_k
  let s4 : ContL → ContL := s2_f s2
  let s8 : ContL → ContL := s2_f s4
  fun x0 x1 rest => popNList_fast rest (fun x2 rest1 => comp_f s8 (comp_f s4 step1_k) plain_finish_def x0 x1 x2 rest1)

lemma run_tail13_comb_fuel_eq (fuel_rec fuel : Nat) :
    run_tail13_comb_fuel fuel_rec fuel = run_tail13_fuel fuel_rec fuel := by
  have h1 : run_tail13_comb_fuel fuel_rec fuel = run_tail13_wrap (step_rec_comb_fuel fuel_rec) do_odd_comb (step1_comb_fuel fuel) (fun F cont => F (F cont)) (fun F G cont => F (G cont)) := rfl
  have h2 : run_tail13_fuel fuel_rec fuel = run_tail13_wrap (step_rec_f_fuel fuel_rec) (do_odd_k_def popNList_fast) (step1_k_fuel fuel popNList_fast) apply2 compCPS := rfl
  rw [h1, h2, step_rec_comb_eq fuel_rec]
  have hd : do_odd_comb = do_odd_k_def popNList_fast := funext do_odd_comb_eq
  have hs : step1_comb_fuel fuel = step1_k_fuel fuel popNList_fast := funext (step1_comb_fuel_eq fuel)
  have ha : (fun (F : ContL → ContL) cont => F (F cont)) = apply2 := rfl
  have hc : (fun (F G : ContL → ContL) cont => F (G cont)) = compCPS := rfl
  rw [hd, hs, ha, hc]

lemma run_tail13_comb_eq : run_tail13_comb = run_tail13 :=
  run_tail13_comb_fuel_eq 20 13

noncomputable def run_rem_fast_comb (x0 x1 : Nat) (rest : NList) : StateL :=
  let s := run_C_fast_comb 11 x0 x1 rest
  let s := StateL.rec StateL.bad (run_C_fast_comb 10) s
  let s := StateL.rec StateL.bad (run_C_fast_comb 8) s
  let s := StateL.rec StateL.bad (run_C_fast_comb 7) s
  let s := StateL.rec StateL.bad (run_C_fast_comb 6) s
  let s := StateL.rec StateL.bad (run_C_fast_comb 5) s
  let s := StateL.rec StateL.bad (run_C_fast_comb 4) s
  let s := StateL.rec StateL.bad (run_C_fast_comb 0) s
  StateL.rec StateL.bad run_tail13_comb s

lemma run_rem_fast_comb_eq : run_rem_fast_comb = run_rem_fast := by
  funext x0 x1 rest
  unfold run_rem_fast_comb run_rem_fast
  simp only [run_C_fast_comb_eq, run_tail13_comb_eq]

lemma chain_C_comb {x0 x1 y0 y1 : Nat} {rest rest' : NList}
    (h_step : checkStateL (run_C_fast_comb 12 x0 x1 rest) y0 y1 rest' = true)
    (h_next : IsHaltFrom (S (y0 :: y1 :: denote_list rest') 0 2 [])) :
    IsHaltFrom (S (x0 :: x1 :: denote_list rest) 0 2 []) := by
  rw [run_C_fast_comb_eq 12] at h_step
  exact chain_C_fast h_step h_next

lemma chain_rem_comb {x0 x1 y0 y1 : Nat} {rest rest' : NList}
    (h_step : checkStateL (run_rem_fast_comb x0 x1 rest) y0 y1 rest' = true)
    (h_next : IsHaltFrom (S (y0 :: y1 :: denote_list rest') 0 2 [])) :
    IsHaltFrom (S (x0 :: x1 :: denote_list rest) 0 2 []) := by
  rw [run_rem_fast_comb_eq] at h_step
  exact chain_rem_fast h_step h_next

abbrev st0_l : NList := NList.cons 1 NList.nil

abbrev c0_x0 : Nat := 2
abbrev c0_x1 : Nat := 5
abbrev c0_rest : NList := (NList.cons 8 (NList.cons 2 NList.nil))
abbrev c0_l : NList := NList.cons c0_x0 (NList.cons c0_x1 c0_rest)

abbrev c1_x0 : Nat := 92
abbrev c1_x1 : Nat := 2404
abbrev c1_rest : NList := (NList.cons 30819 (NList.cons 169721 (NList.cons 421294 (NList.cons 24741 (NList.cons 24740 (NList.cons 2 NList.nil))))))

abbrev c2_x0 : Nat := 37
abbrev c2_x1 : Nat := 25995
abbrev c2_rest : NList := (NList.cons 224964 (NList.cons 224151 (NList.cons 275785 (NList.cons 301606 (NList.cons 301611 (NList.cons 2 NList.nil))))))

abbrev c3_x0 : Nat := 3913
abbrev c3_x1 : Nat := 127277
abbrev c3_rest : NList := (NList.cons 691798 (NList.cons 609442 (NList.cons 609447 (NList.cons 2 NList.nil))))

abbrev c4_x0 : Nat := 21
abbrev c4_x1 : Nat := 7551
abbrev c4_rest : NList := (NList.cons 88180 (NList.cons 1008051 (NList.cons 811801 (NList.cons 405900 (NList.cons 405903 (NList.cons 2 NList.nil))))))

abbrev c5_x0 : Nat := 595
abbrev c5_x1 : Nat := 15419
abbrev c5_rest : NList := (NList.cons 103581 (NList.cons 1283779 (NList.cons 846047 (NList.cons 502393 (NList.cons 330569 (NList.cons 330574 (NList.cons 2 NList.nil)))))))

abbrev c6_x0 : Nat := 423
abbrev c6_x1 : Nat := 169488
abbrev c6_rest : NList := (NList.cons 1036044 (NList.cons 1614596 (NList.cons 1011586 (NList.cons 134856 (NList.cons 67427 (NList.cons 33713 (NList.cons 33716 (NList.cons 2 NList.nil))))))))

abbrev c7_x0 : Nat := 58
abbrev c7_x1 : Nat := 31646
abbrev c7_rest : NList := (NList.cons 485369 (NList.cons 2378055 (NList.cons 946344 (NList.cons 946345 (NList.cons 2 NList.nil)))))

abbrev c8_x0 : Nat := 375
abbrev c8_x1 : Nat := 41379
abbrev c8_rest : NList := (NList.cons 606043 (NList.cons 4829972 (NList.cons 8 NList.nil)))

abbrev c9_x0 : Nat := 3234
abbrev c9_x1 : Nat := 115455
abbrev c9_rest : NList := (NList.cons 1542883 (NList.cons 2142766 (NList.cons 2255004 (NList.cons 56119 (NList.cons 56120 (NList.cons 2 NList.nil))))))

abbrev c10_x0 : Nat := 77
abbrev c10_x1 : Nat := 2421
abbrev c10_rest : NList := (NList.cons 74793 (NList.cons 1546693 (NList.cons 2620621 (NList.cons 2620628 (NList.cons 2 NList.nil)))))

abbrev c11_x0 : Nat := 40556
abbrev c11_x1 : Nat := 1525633
abbrev c11_rest : NList := (NList.cons 2951211 (NList.cons 1475607 (NList.cons 1475610 (NList.cons 2 NList.nil))))
abbrev c11_l : NList := NList.cons c11_x0 (NList.cons c11_x1 c11_rest)

macro "fast_rfl" : tactic => `(tactic| decide +kernel)

theorem step_init : run_pow 3 st0_l 1 1 NList.nil = StepRes.running c0_l 0 2 NList.nil := by fast_rfl
theorem step_c0 : checkStateL (run_C_fast_comb 12 c0_x0 c0_x1 c0_rest) c1_x0 c1_x1 c1_rest = true := by fast_rfl
theorem step_c1 : checkStateL (run_C_fast_comb 12 c1_x0 c1_x1 c1_rest) c2_x0 c2_x1 c2_rest = true := by fast_rfl
theorem step_c2 : checkStateL (run_C_fast_comb 12 c2_x0 c2_x1 c2_rest) c3_x0 c3_x1 c3_rest = true := by fast_rfl
theorem step_c3 : checkStateL (run_C_fast_comb 12 c3_x0 c3_x1 c3_rest) c4_x0 c4_x1 c4_rest = true := by fast_rfl
theorem step_c4 : checkStateL (run_C_fast_comb 12 c4_x0 c4_x1 c4_rest) c5_x0 c5_x1 c5_rest = true := by fast_rfl
theorem step_c5 : checkStateL (run_C_fast_comb 12 c5_x0 c5_x1 c5_rest) c6_x0 c6_x1 c6_rest = true := by fast_rfl
theorem step_c6 : checkStateL (run_C_fast_comb 12 c6_x0 c6_x1 c6_rest) c7_x0 c7_x1 c7_rest = true := by fast_rfl
theorem step_c7 : checkStateL (run_C_fast_comb 12 c7_x0 c7_x1 c7_rest) c8_x0 c8_x1 c8_rest = true := by fast_rfl
theorem step_c8 : checkStateL (run_C_fast_comb 12 c8_x0 c8_x1 c8_rest) c9_x0 c9_x1 c9_rest = true := by fast_rfl
theorem step_c9 : checkStateL (run_C_fast_comb 12 c9_x0 c9_x1 c9_rest) c10_x0 c10_x1 c10_rest = true := by fast_rfl
theorem step_c10 : checkStateL (run_rem_fast_comb c10_x0 c10_x1 c10_rest) c11_x0 c11_x1 c11_rest = true := by fast_rfl
theorem step_exit : run_pow 5 c11_l 0 2 NList.nil = StepRes.halted := by fast_rfl

lemma halt_c11 : IsHaltFrom (S (c11_x0 :: c11_x1 :: denote_list c11_rest) 0 2 []) := by
  simpa [c11_l, denote_list] using! finish_pow 5 step_exit
lemma halt_c10 : IsHaltFrom (S (c10_x0 :: c10_x1 :: denote_list c10_rest) 0 2 []) := chain_rem_comb step_c10 halt_c11
lemma halt_c9 : IsHaltFrom (S (c9_x0 :: c9_x1 :: denote_list c9_rest) 0 2 []) := chain_C_comb step_c9 halt_c10
lemma halt_c8 : IsHaltFrom (S (c8_x0 :: c8_x1 :: denote_list c8_rest) 0 2 []) := chain_C_comb step_c8 halt_c9
lemma halt_c7 : IsHaltFrom (S (c7_x0 :: c7_x1 :: denote_list c7_rest) 0 2 []) := chain_C_comb step_c7 halt_c8
lemma halt_c6 : IsHaltFrom (S (c6_x0 :: c6_x1 :: denote_list c6_rest) 0 2 []) := chain_C_comb step_c6 halt_c7
lemma halt_c5 : IsHaltFrom (S (c5_x0 :: c5_x1 :: denote_list c5_rest) 0 2 []) := chain_C_comb step_c5 halt_c6
lemma halt_c4 : IsHaltFrom (S (c4_x0 :: c4_x1 :: denote_list c4_rest) 0 2 []) := chain_C_comb step_c4 halt_c5
lemma halt_c3 : IsHaltFrom (S (c3_x0 :: c3_x1 :: denote_list c3_rest) 0 2 []) := chain_C_comb step_c3 halt_c4
lemma halt_c2 : IsHaltFrom (S (c2_x0 :: c2_x1 :: denote_list c2_rest) 0 2 []) := chain_C_comb step_c2 halt_c3
lemma halt_c1 : IsHaltFrom (S (c1_x0 :: c1_x1 :: denote_list c1_rest) 0 2 []) := chain_C_comb step_c1 halt_c2
lemma halt_c0 : IsHaltFrom (S (c0_x0 :: c0_x1 :: denote_list c0_rest) 0 2 []) := chain_C_comb step_c0 halt_c1

lemma halt_0 : IsHaltFrom (S (denote_list st0_l) 1 1 (denote_list NList.nil)) := by
  refine chain_pow 3 step_init ?_
  simpa [c0_l, denote_list] using! halt_c0

end

end

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  exact halt_from_trans init_to_S halt_0

end BusyBeaver.M_1RB0RB_1RC0RD_1LD1RC_1RF0LE_1LC1LE_HHH0RA
