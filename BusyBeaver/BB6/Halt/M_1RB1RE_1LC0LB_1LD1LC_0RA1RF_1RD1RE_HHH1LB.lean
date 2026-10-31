/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RE_1LC0LB_1LD1LC_0RA1RF_1RD1RE_---1LB` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RE_1LC0LB_1LD1LC_0RA1RF_1RD1RE_---1LB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RE_1LC0LB_1LD1LC_0RA1RF_1RD1RE_HHH1LB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RE_1LC0LB_1LD1LC_0RA1RF_1RD1RE_---1LB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 1, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5



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
@[simp] lemma zPz {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z0j {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
lemma z0k {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [z0j, Nat.succ_add, ih, List.append_assoc]
lemma z0l {α : Type*} (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) := by
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
  `(tactic| (try dsimp only [append_cons, append_nil]) <;> exists 0 <;> fail)
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

@[simp] lemma zero_pow_default (n : Nat) : (W0 ^ n) +> (default : zB) = default := by
  induction n with
  | zero => rfl
  | succ n ih => rw [z0j, append_assoc, append_cons, append_nil, ih, z0i]

lemma start_sweep (r : zB) :
    (default <{{C}} r) [target_tm]⊢* ((default << 1) {{E}}> r) := by
  execute

lemma sweep_ones (n : Nat) (l r : zB) :
    (l {{E}}> ((W1 ^ n) +> r)) [target_tm]⊢* ((l <+ (W1 ^ n)) {{E}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{E}}> (W1 +> (W1 ^ n) +> r)) [target_tm]⊢*
        ((l << 1) {{E}}> ((W1 ^ n) +> r)) := by
      dsimp [W1]; execute
    have h2 := ih (l << 1) r
    have heq : (l << 1) <+ (W1 ^ n) = l <+ (W1 ^ (n + 1)) := by
      rw [← z0l, append_assoc]; rfl
    rw [heq] at h2
    exact zSt h1 h2

lemma sweep_011 (l r : zB) :
    (l {{E}}> (([0, 1, 1] : zF) +> r)) [target_tm]⊢* (l <{{B}} (([0, 0, 1] : zF) +> r)) := by
  execute

lemma sweep_010_halt (l r : zB) :
    IsHaltFrom (l {{E}}> (([0, 1, 0] : zF) +> r)) := by
  refine ⟨((l << 1 << 1) {{F}}> (([0] : zF) +> r)), ?_, by simp [step, target_tm, F]⟩
  execute

lemma sweep_001 (l r : zB) :
    (l {{E}}> (([0, 0, 1] : zF) +> r)) [target_tm]⊢* ((l << 1 << 0 << 1) {{E}}> r) := by
  execute

lemma sweep_0001 (l r : zB) :
    (l {{E}}> (([0, 0, 0, 1] : zF) +> r)) [target_tm]⊢* (l <{{C}} (([1, 1, 0, 0] : zF) +> r)) := by
  execute

lemma sweep_0000 (l r : zB) :
    (l {{E}}> (([0, 0, 0, 0] : zF) +> r)) [target_tm]⊢* (l <{{B}} (([0, 1, 1, 1] : zF) +> r)) := by
  execute

lemma back_some_C (n : Nat) (l r : zB) :
    ((l <+ (W1 ^ n)) <{{C}} r) [target_tm]⊢* (l <{{C}} ((W1 ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (((l <+ (W1 ^ n)) << 1) <{{C}} r) [target_tm]⊢*
        ((l <+ (W1 ^ n)) <{{C}} (W1 +> r)) := by
      dsimp [W1]; execute
    have h2 := ih l (W1 +> r)
    have heq : (W1 ^ n) +> (W1 +> r) = (W1 ^ (n + 1)) +> r := by
      rw [← z0l, append_assoc]
    rw [heq] at h2
    exact zSt h1 h2

lemma back_some_B (n : Nat) (l r : zB) :
    ((l <+ (W1 ^ n)) <{{B}} r) [target_tm]⊢* (l <{{B}} ((W0 ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (((l <+ (W1 ^ n)) << 1) <{{B}} r) [target_tm]⊢*
        ((l <+ (W1 ^ n)) <{{B}} (W0 +> r)) := by
      dsimp [W0]; execute
    have h2 := ih l (W0 +> r)
    have heq : (W0 ^ n) +> (W0 +> r) = (W0 ^ (n + 1)) +> r := by
      rw [← z0l, append_assoc]
    rw [heq] at h2
    exact zSt h1 h2

lemma back_none_C (l r : zB) :
    ((l << 1 << 0 << 1) <{{C}} r) [target_tm]⊢* (l <{{B}} (([0, 1, 1] : zF) +> r)) := by
  execute

lemma back_none_B (l r : zB) :
    ((l << 1 << 0 << 1) <{{B}} r) [target_tm]⊢* (l <{{C}} (([1, 1, 0] : zF) +> r)) := by
  execute

lemma back_nil_C (r : zB) :
    ((default << 1) <{{C}} r) [target_tm]⊢* (default <{{C}} (W1 +> r)) := by
  dsimp [W1]; execute

lemma back_nil_B (r : zB) :
    ((default << 1) <{{B}} r) [target_tm]⊢* (default <{{C}} (([1, 0] : zF) +> r)) := by
  execute

lemma ff_entry (s : zB) :
    (default <{{C}} (([1, 0, 0, 0, 0] : zF) +> s)) [target_tm]⊢*
    (default <{{C}} ((W1 ^ 4) +> (([0, 0, 1, 1] : zF) +> s))) := by
  dsimp [W1]; execute

lemma sweep_a_3 (a : Nat) (s : zB) :
    (default <{{C}} ((W1 ^ a) +> (([0, 0, 0, 1] : zF) +> s))) [target_tm]⊢*
    (default <{{C}} ((W1 ^ (a + 3)) +> (([0, 0] : zF) +> s))) := by
  refine zSt (start_sweep _) ?_
  refine zSt (sweep_ones a _ _) ?_
  refine zSt (sweep_0001 _ _) ?_
  refine zSt (back_some_C a _ _) ?_
  have h1 := back_nil_C ((W1 ^ a) +> (([1, 1, 0, 0] : zF) +> s))
  have heq : W1 +> ((W1 ^ a) +> (([1, 1, 0, 0] : zF) +> s)) = (W1 ^ (a + 3)) +> (([0, 0] : zF) +> s) := by
    rw [show a + 3 = 1 + (a + 2) by omega, z0k, z0k W1 a 2, append_assoc, append_assoc]
    rfl
  rw [heq] at h1
  exact h1

lemma sweep_a_ge4 (a : Nat) (s : zB) :
    (default <{{C}} ((W1 ^ a) +> (([0, 0, 0, 0] : zF) +> s))) [target_tm]⊢*
    (default <{{C}} (W1 +> ((W0 ^ (a + 2)) +> (([1, 1, 1] : zF) +> s)))) := by
  refine zSt (start_sweep _) ?_
  refine zSt (sweep_ones a _ _) ?_
  refine zSt (sweep_0000 _ _) ?_
  refine zSt (back_some_B a _ _) ?_
  have h1 := back_nil_B ((W0 ^ a) +> (([0, 1, 1, 1] : zF) +> s))
  have heq : ([1, 0] : zF) +> ((W0 ^ a) +> (([0, 1, 1, 1] : zF) +> s)) =
      W1 +> ((W0 ^ (a + 2)) +> (([1, 1, 1] : zF) +> s)) := by
    rw [show a + 2 = 1 + (a + 1) by omega, z0k, z0k W0 a 1, append_assoc, append_assoc]
    rfl
  rw [heq] at h1
  exact h1

lemma ff_one (a : Nat) (s : zB) :
    (default <{{C}} ((W1 ^ a) +> (([0, 0, 1, 1, 0, 0, 0, 0] : zF) +> s))) [target_tm]⊢*
    (default <{{C}} ((W1 ^ (a + 6)) +> (([0, 0, 1, 1] : zF) +> s))) := by
  refine zSt (start_sweep _) ?_
  refine zSt (sweep_ones a _ _) ?_
  have h_split : (([0, 0, 1, 1, 0, 0, 0, 0] : zF) +> s) = ([0, 0, 1] : zF) +> (([1, 0, 0, 0, 0] : zF) +> s) := rfl
  rw [h_split]
  refine zSt (sweep_001 _ _) ?_
  have h_mid : (((default << 1 <+ (W1 ^ a)) << 1 << 0 << 1) {{E}}> (([1, 0, 0, 0, 0] : zF) +> s)) [target_tm]⊢*
      ((default << 1 <+ (W1 ^ a)) <{{C}} (([1, 1, 0, 0, 0, 1, 1, 1] : zF) +> s)) := by
    execute
  refine zSt h_mid ?_
  refine zSt (back_some_C a _ _) ?_
  have h_back := back_nil_C ((W1 ^ a) +> (([1, 1, 0, 0, 0, 1, 1, 1] : zF) +> s))
  have heq1 : W1 +> ((W1 ^ a) +> (([1, 1, 0, 0, 0, 1, 1, 1] : zF) +> s)) =
      (W1 ^ (a + 3)) +> (([0, 0, 0, 1] : zF) +> (([1, 1] : zF) +> s)) := by
    rw [show a + 3 = 1 + (a + 2) by omega, z0k, z0k W1 a 2, append_assoc, append_assoc]
    rfl
  rw [heq1] at h_back
  refine zSt h_back ?_
  have h2 := sweep_a_3 (a + 3) (([1, 1] : zF) +> s)
  have heq2 : (a + 3) + 3 = a + 6 := by omega
  rw [heq2] at h2
  exact h2

lemma ff_loop (q a : Nat) (s : zB) :
    (default <{{C}} ((W1 ^ a) +> (([0, 0, 1, 1] : zF) +> ((W0 ^ (4 * q)) +> s)))) [target_tm]⊢*
    (default <{{C}} ((W1 ^ (a + 6 * q)) +> (([0, 0, 1, 1] : zF) +> s))) := by
  induction q generalizing a with
  | zero => simp; exact ⟨0, rfl⟩
  | succ q ih =>
    have hq : 4 * (q + 1) = 4 + 4 * q := by omega
    rw [hq, z0k W0 4 (4 * q), append_assoc]
    have h1 : (([0, 0, 1, 1] : zF) +> ((W0 ^ 4) +> ((W0 ^ (4 * q)) +> s))) =
        (([0, 0, 1, 1, 0, 0, 0, 0] : zF) +> ((W0 ^ (4 * q)) +> s)) := rfl
    rw [h1]
    refine zSt (ff_one a ((W0 ^ (4 * q)) +> s)) ?_
    have h2 := ih (a + 6)
    have ha : a + 6 + 6 * q = a + 6 * (q + 1) := by omega
    rw [ha] at h2
    exact h2

lemma init_to_seed :
    (init []) [target_tm]⊢*
    (default <{{C}} ((W1 ^ 4) +> ((W0 ^ 2) +> ((W1 ^ 5) +> default)))) := by
  dsimp [init, Tape.mk₁, W0, W1]
  execute

-- ============================================================================
-- Section 6: Fast Kernel RLE Evaluator
-- ============================================================================

noncomputable section

inductive RTape where
  | nil : RTape
  | cons (b : Bool) (n : Nat) (rest : RTape) : RTape

inductive AccList where
  | nil : AccList
  | some (n : Nat) (rest : AccList) : AccList
  | none (rest : AccList) : AccList

inductive SweepRes where
  | halted : SweepRes
  | done (phase : Bool) (t : RTape) : SweepRes
  | failed : SweepRes

inductive StepRes where
  | halted : StepRes
  | running (t : RTape) : StepRes
  | failed : StepRes

def bindNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k m) (Nat.add n 1)

def forceRTape {α : Type} (t : RTape) (k : RTape → α) : α :=
  (RTape.rec (fun k => k RTape.nil) (fun b n rest _ k => k (RTape.cons b n rest)) t : (RTape → α) → α) k

def bool_eq (b b0 : Bool) : Bool :=
  Bool.rec (Bool.rec true false b0) b0 b

def push1_nil (b : Bool) (n : Nat) : RTape :=
  bindNat n (fun n' => RTape.cons b n' RTape.nil)

def push1_cons_diff (b : Bool) (n : Nat) (b0 : Bool) (n0 : Nat) (rest : RTape) : RTape :=
  bindNat n (fun n' => RTape.cons b n' (RTape.cons b0 n0 rest))

def push1_cons_same (b : Bool) (n : Nat) (b0 : Bool) (n0 : Nat) (rest : RTape) : RTape :=
  bindNat (Nat.add n n0) (fun s => RTape.cons b0 s rest)

def push1_branch (eq : Bool) : Bool → Nat → Bool → Nat → RTape → RTape :=
  Bool.rec push1_cons_diff push1_cons_same eq

def push1_cons (b0 : Bool) (n0 : Nat) (rest : RTape) (_ : Nat → Bool → RTape) (n : Nat) (b : Bool) : RTape :=
  push1_branch (bool_eq b b0) b n b0 n0 rest

def push1 (b : Bool) (n : Nat) (t : RTape) : RTape :=
  (RTape.rec (fun n b => push1_nil b n) push1_cons t : Nat → Bool → RTape) n b

def push_branch (is0 : Bool) : Bool → Nat → RTape → RTape :=
  Bool.rec push1 (fun _ _ t => t) is0

def push (b : Bool) (n : Nat) (t : RTape) : RTape :=
  push_branch (Nat.beq n 0) b n t

def back_rel_some (n : Nat) (_ : AccList) (ih : Bool → RTape → SweepRes) (phase : Bool) (t : RTape) : SweepRes :=
  forceRTape (push1 phase n t) (ih phase)

def back_rel_none_false (ih : Bool → RTape → SweepRes) (t : RTape) : SweepRes :=
  forceRTape (push1 false 1 t) (fun t' => ih true (RTape.cons true 2 t'))

def back_rel_none_true (ih : Bool → RTape → SweepRes) (t : RTape) : SweepRes :=
  forceRTape (push1 true 2 t) (fun t' => ih false (RTape.cons false 1 t'))

def back_rel_none_branch (phase : Bool) : (Bool → RTape → SweepRes) → RTape → SweepRes :=
  Bool.rec back_rel_none_false back_rel_none_true phase

def back_rel_none (_ : AccList) (ih : Bool → RTape → SweepRes) (phase : Bool) (t : RTape) : SweepRes :=
  back_rel_none_branch phase ih t

def back_rel (acc : AccList) (phase : Bool) (t : RTape) : SweepRes :=
  (AccList.rec SweepRes.done back_rel_some back_rel_none acc : Bool → RTape → SweepRes) phase t

def sf_nil (_ : AccList) : SweepRes :=
  SweepRes.failed

def sf_n0_1_true_ge2 (acc : AccList) (r2 : RTape) (n1 : Nat) : SweepRes :=
  bindNat (Nat.sub n1 1) (fun n1' => back_rel acc false (RTape.cons false 2 (RTape.cons true n1' r2)))

def sf_n0_1_true_branch (ge2 : Bool) : AccList → RTape → Nat → SweepRes :=
  Bool.rec (fun _ _ _ => SweepRes.halted) sf_n0_1_true_ge2 ge2

def sf_n0_1_true (n1 : Nat) (r2 : RTape) (acc : AccList) : SweepRes :=
  sf_n0_1_true_branch (Nat.ble 2 n1) acc r2 n1

def sf_n0_1_branch (b1 : Bool) : Nat → RTape → AccList → SweepRes :=
  Bool.rec (fun _ _ _ => SweepRes.failed) sf_n0_1_true b1

def sf_n0_1_cons (b1 : Bool) (n1 : Nat) (r2 : RTape) (_ : AccList → SweepRes) (acc : AccList) : SweepRes :=
  sf_n0_1_branch b1 n1 r2 acc

def sf_n0_1 (rest : RTape) (acc : AccList) : SweepRes :=
  (RTape.rec (fun _ => SweepRes.failed) sf_n0_1_cons rest : AccList → SweepRes) acc

def sf_n0_2_true (ih : AccList → RTape → SweepRes) (acc : AccList) (n1 : Nat) (r2 : RTape) : SweepRes :=
  bindNat (Nat.sub n1 1) (fun n1' => forceRTape (push true n1' r2) (ih (AccList.none acc)))

def sf_n0_2_branch (b1 : Bool) : (AccList → RTape → SweepRes) → AccList → Nat → RTape → SweepRes :=
  Bool.rec (fun _ _ _ _ => SweepRes.failed) sf_n0_2_true b1

def sf_n0_2_cons (b1 : Bool) (n1 : Nat) (r2 : RTape) (_ : (AccList → RTape → SweepRes) → AccList → SweepRes)
    (ih : AccList → RTape → SweepRes) (acc : AccList) : SweepRes :=
  sf_n0_2_branch b1 ih acc n1 r2

def sf_n0_2 (rest : RTape) (ih : AccList → RTape → SweepRes) (acc : AccList) : SweepRes :=
  (RTape.rec (fun _ acc => sf_nil acc) sf_n0_2_cons rest : (AccList → RTape → SweepRes) → AccList → SweepRes) ih acc

def sf_n0_3_true (acc : AccList) (n1 : Nat) (r2 : RTape) : SweepRes :=
  bindNat (Nat.sub n1 1) (fun n1' =>
  forceRTape (push true n1' r2) (fun r3 =>
  forceRTape (push1 false 2 r3) (fun r4 =>
  back_rel acc true (RTape.cons true 2 r4))))

def sf_n0_3_branch (b1 : Bool) : AccList → Nat → RTape → SweepRes :=
  Bool.rec (fun _ _ _ => SweepRes.failed) sf_n0_3_true b1

def sf_n0_3_cons (b1 : Bool) (n1 : Nat) (r2 : RTape) (_ : AccList → SweepRes) (acc : AccList) : SweepRes :=
  sf_n0_3_branch b1 acc n1 r2

def sf_n0_3 (rest : RTape) (acc : AccList) : SweepRes :=
  (RTape.rec sf_nil sf_n0_3_cons rest : AccList → SweepRes) acc

def sf_n0_ge4 (n0 : Nat) (rest : RTape) (acc : AccList) : SweepRes :=
  bindNat (Nat.sub n0 4) (fun n0' =>
  forceRTape (push false n0' rest) (fun r3 =>
  forceRTape (push1 true 3 r3) (fun r4 =>
  back_rel acc false (RTape.cons false 1 r4))))

def sf_b3 (c : Bool) : Nat → RTape → AccList → SweepRes :=
  Bool.rec sf_n0_ge4 (fun _ rest acc => sf_n0_3 rest acc) c

def sf_b2 (c : Bool) : Nat → RTape → (AccList → RTape → SweepRes) → AccList → SweepRes :=
  Bool.rec (fun n0 rest _ acc => sf_b3 (Nat.beq n0 3) n0 rest acc) (fun _ rest ih acc => sf_n0_2 rest ih acc) c

def sf_b1 (c : Bool) : Nat → RTape → (AccList → RTape → SweepRes) → AccList → SweepRes :=
  Bool.rec (fun n0 rest ih acc => sf_b2 (Nat.beq n0 2) n0 rest ih acc) (fun _ rest _ acc => sf_n0_1 rest acc) c

def sf_false_branch (n0 : Nat) (rest : RTape) (ih : AccList → RTape → SweepRes) (acc : AccList) : SweepRes :=
  sf_b1 (Nat.beq n0 1) n0 rest ih acc

def sf_cons_branch (b0 : Bool) : Nat → RTape → (AccList → RTape → SweepRes) → AccList → SweepRes :=
  Bool.rec sf_false_branch (fun _ _ _ _ => SweepRes.failed) b0

def sf_cons (b0 : Bool) (n0 : Nat) (rest : RTape) (_ : (AccList → RTape → SweepRes) → AccList → SweepRes)
    (ih : AccList → RTape → SweepRes) (acc : AccList) : SweepRes :=
  sf_cons_branch b0 n0 rest ih acc

def sweep_false_rel (ih : AccList → RTape → SweepRes) (acc : AccList) (t : RTape) : SweepRes :=
  (RTape.rec (fun _ acc => sf_nil acc) sf_cons t : (AccList → RTape → SweepRes) → AccList → SweepRes) ih acc

def sl_cons_branch (b0 : Bool) : (AccList → RTape → SweepRes) → AccList → Nat → RTape → SweepRes :=
  Bool.rec
    (fun ih acc n0 r1 => sweep_false_rel ih acc (RTape.cons false n0 r1))
    (fun ih acc n0 r1 => sweep_false_rel ih (AccList.some n0 acc) r1)
    b0

def sl_cons (b0 : Bool) (n0 : Nat) (r1 : RTape) (_ : (AccList → RTape → SweepRes) → AccList → SweepRes)
    (ih : AccList → RTape → SweepRes) (acc : AccList) : SweepRes :=
  sl_cons_branch b0 ih acc n0 r1

def sl_step (_ : Nat) (ih : AccList → RTape → SweepRes) (acc : AccList) (t : RTape) : SweepRes :=
  (RTape.rec (fun ih acc => sweep_false_rel ih acc RTape.nil) sl_cons t : (AccList → RTape → SweepRes) → AccList → SweepRes) ih acc

def run_sweep_rel (fuel : Nat) (acc : AccList) (t : RTape) : SweepRes :=
  (Nat.rec (fun _ _ => SweepRes.failed) sl_step fuel : AccList → RTape → SweepRes) acc t

def fsn_false_b3_true (val : Nat) (c' : Nat) (r'' : RTape) : StepRes :=
  bindNat (Nat.add val 4) (fun v4 =>
  bindNat (Nat.sub c' 1) (fun c1 =>
  forceRTape (push true c1 r'') (fun r3 =>
  StepRes.running (RTape.cons true v4 (RTape.cons false 2 r3)))))

def fsn_false_b3_branch (ok : Bool) : Nat → Nat → RTape → StepRes :=
  Bool.rec (fun _ _ _ => StepRes.failed) fsn_false_b3_true ok

def fsn_false_b3_cons (b2 : Bool) (c' : Nat) (r'' : RTape) (_ : Nat → StepRes) (val : Nat) : StepRes :=
  fsn_false_b3_branch (Bool.rec false (Nat.ble 2 c') b2) val c' r''

def fsn_false_b3 (r' : RTape) (val : Nat) : StepRes :=
  (RTape.rec (fun _ => StepRes.failed) fsn_false_b3_cons r' : Nat → StepRes) val

def fsn_false_b_ge4 (val : Nat) (b' : Nat) (r' : RTape) : StepRes :=
  bindNat (Nat.add val 3) (fun v3 =>
  bindNat (Nat.sub b' 4) (fun b4 =>
  forceRTape (push false b4 r') (fun r2 =>
  forceRTape (push1 true 3 r2) (fun r3 =>
  StepRes.running (RTape.cons true 1 (RTape.cons false v3 r3))))))

def fsn_false_branch2 (is3 : Bool) : Nat → RTape → StepRes :=
  Bool.rec (fun _ _ => StepRes.failed) (fun val r' => fsn_false_b3 r' val) is3

def fsn_false_branch1 (ge4 : Bool) : Nat → Nat → RTape → StepRes :=
  Bool.rec (fun val b' r' => fsn_false_branch2 (Nat.beq b' 3) val r') fsn_false_b_ge4 ge4

def fsn_false_cons (b1 : Bool) (b' : Nat) (r' : RTape) (_ : Nat → StepRes) (val : Nat) : StepRes :=
  (Bool.rec (fun val b' r' => fsn_false_branch1 (Nat.ble 4 b') val b' r') (fun _ _ _ => StepRes.failed) b1 : Nat → Nat → RTape → StepRes) val b' r'

def fsn_false (t : RTape) (val : Nat) : StepRes :=
  (RTape.rec (fun _ => StepRes.failed) fsn_false_cons (push1 false 1 t) : Nat → StepRes) val

def fsn_true (t : RTape) (val : Nat) : StepRes :=
  bindNat val (fun v =>
  forceRTape (push1 true 2 t) (fun r2 =>
  StepRes.running (RTape.cons true 1 (RTape.cons false v r2))))

def fsn_done (phase : Bool) : RTape → Nat → StepRes :=
  Bool.rec fsn_false fsn_true phase

def finish_some_none_fused (sr : SweepRes) (val : Nat) : StepRes :=
  (SweepRes.rec (fun _ => StepRes.halted) (fun phase t val => fsn_done phase t val) (fun _ => StepRes.failed) sr : Nat → StepRes) val

def step_case1 (b : Nat) (r2 : RTape) : StepRes :=
  bindNat (Nat.div b 4) (fun q1 =>
  bindNat (Nat.mod b 4) (fun rem =>
  bindNat (Nat.mul 6 q1) (fun p6 =>
  forceRTape (push false rem r2) (fun r3 =>
  forceRTape (push1 true 1 r3) (fun r4 =>
  finish_some_none_fused (run_sweep_rel 16 AccList.nil r4) p6)))))

def step_case2_cons (b2 : Bool) (c : Nat) (r3 : RTape) (_ : Nat → StepRes) (a : Nat) : StepRes :=
  (Bool.rec
    (fun _ _ _ => StepRes.failed)
    (fun a c r3 =>
      bindNat (Nat.sub c 1) (fun c1 =>
      bindNat (Nat.add a 2) (fun a2 =>
      forceRTape (push true c1 r3) (fun r4 =>
      finish_some_none_fused (run_sweep_rel 16 AccList.nil r4) a2))))
    b2 : Nat → Nat → RTape → StepRes) a c r3

def step_case2 (a : Nat) (r2 : RTape) : StepRes :=
  (RTape.rec (fun _ => StepRes.failed) step_case2_cons r2 : Nat → StepRes) a

def step_dispatch_b2 (is_b2 : Bool) : Nat → RTape → StepRes :=
  Bool.rec (fun _ _ => StepRes.failed) step_case2 is_b2

def step_dispatch_ff (is_ff : Bool) : Nat → Nat → RTape → StepRes :=
  Bool.rec (fun a b r2 => step_dispatch_b2 (Nat.beq b 2) a r2) (fun _ b r2 => step_case1 b r2) is_ff

def step_r1_false (a : Nat) (b : Nat) (r2 : RTape) : StepRes :=
  step_dispatch_ff (Bool.rec false (Nat.ble 4 b) (Nat.beq a 1)) a b r2

def step_r1_cons (b1 : Bool) (b : Nat) (r2 : RTape) (_ : Nat → StepRes) (a : Nat) : StepRes :=
  (Bool.rec step_r1_false (fun _ _ _ => StepRes.failed) b1 : Nat → Nat → RTape → StepRes) a b r2

def step_r0_true (a : Nat) (r1 : RTape) : StepRes :=
  (RTape.rec (fun _ => StepRes.failed) step_r1_cons r1 : Nat → StepRes) a

def step_r0_cons (b0 : Bool) (a : Nat) (r1 : RTape) (_ : StepRes) : StepRes :=
  (Bool.rec (fun _ _ => StepRes.failed) step_r0_true b0 : Nat → RTape → StepRes) a r1

def rle_step (t : RTape) : StepRes :=
  RTape.rec StepRes.failed step_r0_cons t

def rp_step (_ : Nat) (ih : RTape → StepRes) (t : RTape) : StepRes :=
  StepRes.rec StepRes.halted ih StepRes.failed (ih t)

def run_pow (k : Nat) (t : RTape) : StepRes :=
  (Nat.rec rle_step rp_step k : RTape → StepRes) t

def is_halted (sr : StepRes) : Bool :=
  StepRes.rec true (fun _ => false) false sr

def seed : RTape := RTape.cons true 4 (RTape.cons false 2 (RTape.cons true 5 RTape.nil))

-- ============================================================================

def trunc_zero_cons (b : Bool) (n : Nat) (rest : RTape) (_ : RTape) : RTape :=
  Bool.rec RTape.nil (RTape.cons true n rest) b

def trunc_zero (t : RTape) : RTape :=
  RTape.rec RTape.nil trunc_zero_cons t

def trunc_step (_ : Nat) (ih : RTape → RTape) (t : RTape) : RTape :=
  RTape.rec RTape.nil (fun b n rest _ => forceRTape (ih rest) (RTape.cons b n)) t

def trunc (k : Nat) (t : RTape) : RTape :=
  (Nat.rec trunc_zero trunc_step k : RTape → RTape) t

def trunc_res (k : Nat) (sr : StepRes) : StepRes :=
  StepRes.rec StepRes.halted (fun t => StepRes.running (trunc k t)) StepRes.failed sr

def run_64 (t : RTape) : StepRes :=
  trunc_res 25 (run_pow 6 t)

def run_chunk (k : Nat) (t : RTape) : StepRes :=
  (Nat.rec run_64 rp_step k : RTape → StepRes) t

def bool_beq (b1 b2 : Bool) : Bool :=
  Bool.rec (Bool.rec true false b2) (Bool.rec false true b2) b1

def rtape_beq (t1 t2 : RTape) : Bool :=
  (RTape.rec
    (fun t2 => RTape.rec true (fun _ _ _ _ => false) t2)
    (fun b1 n1 _ ih t2 =>
      RTape.rec false (fun b2 n2 r2 _ =>
        Bool.rec false (Bool.rec false (ih r2) (Nat.beq n1 n2)) (bool_beq b1 b2)) t2)
    t1 : RTape → Bool) t2

def is_running_eq (sr : StepRes) (target : RTape) : Bool :=
  StepRes.rec false (fun t => rtape_beq t target) false sr

-- Section 7: Soundness Proof of RLE Evaluator
-- ============================================================================

@[simp]
lemma bindNat_eq {α : Type} (n : Nat) (k : Nat → α) :
    bindNat n k = k n := rfl

@[simp]
lemma forceRTape_eq {α : Type} (t : RTape) (k : RTape → α) :
    forceRTape t k = k t := by
  cases t <;> rfl


@[simp]
def denote_tape_tail (tail : zB) : RTape → zB
  | .nil => tail
  | .cons b n rest => ((if b then W1 else W0) ^ n) +> denote_tape_tail tail rest

section Tail
variable {tail : zB}
local notation "denote_tape" => denote_tape_tail tail

@[simp]
def denote_acc_rel (l0 : zB) : AccList → zB
  | .nil => l0
  | .some n rest => denote_acc_rel l0 rest <+ (W1 ^ n)
  | .none rest => denote_acc_rel l0 rest << 1 << 0 << 1

@[simp]
lemma denote_push1 (b : Bool) (n : Nat) (t : RTape) :
    denote_tape (push1 b n t) = ((if b then W1 else W0) ^ n) +> denote_tape t := by
  cases t with
  | nil =>
    cases b <;> simp [push1, push1_nil]
  | cons b0 n0 rest =>
    cases b <;> cases b0 <;>
      simp [push1, push1_cons, bool_eq, push1_branch, push1_cons_same, push1_cons_diff, z0k, append_assoc]

@[simp]
lemma denote_push (b : Bool) (n : Nat) (t : RTape) :
    denote_tape (push b n t) = ((if b then W1 else W0) ^ n) +> denote_tape t := by
  unfold push
  cases h : Nat.beq n 0 with
  | true =>
    have hn : n = 0 := Nat.eq_of_beq_eq_true h
    subst hn
    simp [push_branch]
  | false =>
    simp [push_branch, denote_push1]

lemma split_W0_1 {n : Nat} (hn : 1 ≤ n) (s : zB) :
    (W0 ^ n) +> s = ([0] : zF) +> ((W0 ^ (n - 1)) +> s) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [show 1 + m - 1 = m by omega, z0k W0 1 m, append_assoc]
  rfl

lemma split_W0_4 {n : Nat} (hn : 4 ≤ n) (s : zB) :
    (W0 ^ n) +> s = ([0, 0, 0, 0] : zF) +> ((W0 ^ (n - 4)) +> s) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  rw [show 4 + m - 4 = m by omega, z0k W0 4 m, append_assoc]
  rfl

lemma split_W1_1 {n : Nat} (hn : 1 ≤ n) (s : zB) :
    (W1 ^ n) +> s = ([1] : zF) +> ((W1 ^ (n - 1)) +> s) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [show 1 + m - 1 = m by omega, z0k W1 1 m, append_assoc]
  rfl

lemma split_W1_2 {n : Nat} (hn : 2 ≤ n) (s : zB) :
    (W1 ^ n) +> s = ([1, 1] : zF) +> ((W1 ^ (n - 2)) +> s) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  rw [show 2 + m - 2 = m by omega, z0k W1 2 m, append_assoc]
  rfl

def head_zero_tail (tail : zB) (t : RTape) : Prop :=
  ∃ r, denote_tape_tail tail t = ([0] : zF) +> r
local notation "head_zero" => head_zero_tail tail

lemma head_zero_of_W0 (n : Nat) (hn : 1 ≤ n) (s : zB) :
    ∃ r, (W0 ^ n) +> s = ([0] : zF) +> r :=
  ⟨(W0 ^ (n - 1)) +> s, split_W0_1 hn s⟩

lemma head_zero_nil : head_zero_tail default RTape.nil :=
  ⟨default, z0i.symm⟩

lemma head_zero_cons_false {n : Nat} (hn : 1 ≤ n) (rest : RTape) :
    head_zero (RTape.cons false n rest) :=
  head_zero_of_W0 n hn (denote_tape rest)

lemma head_zero_push1_false {n : Nat} (hn : 1 ≤ n) (rest : RTape) :
    head_zero (push1 false n rest) := by
  unfold head_zero_tail
  rw [denote_push1]
  exact head_zero_of_W0 n hn (denote_tape rest)

def Valid_tail (tail : zB) : RTape → Prop
  | .nil => ∃ r, tail = ([0] : zF) +> r
  | .cons b n rest => 1 ≤ n ∧ (b = true → head_zero_tail tail rest) ∧ Valid_tail tail rest
local notation "Valid" => Valid_tail tail

def ValidAcc : AccList → Prop
  | .nil => True
  | .some n rest => 1 ≤ n ∧ ValidAcc rest
  | .none rest => ValidAcc rest

lemma valid_cons_false {n : Nat} {t : RTape} (hn : 1 ≤ n) (ht : Valid t) :
    Valid (RTape.cons false n t) :=
  ⟨hn, fun h => Bool.noConfusion h, ht⟩

lemma valid_cons_true {n : Nat} {t : RTape} (hn : 1 ≤ n) (hz : head_zero t) (ht : Valid t) :
    Valid (RTape.cons true n t) :=
  ⟨hn, fun _ => hz, ht⟩

lemma valid_push1 {b : Bool} {n : Nat} {t : RTape} (hn : 1 ≤ n) (ht : Valid t) :
    Valid (push1 b n t) := by
  cases t with
  | nil =>
    cases b with
    | false => exact ⟨hn, fun h => Bool.noConfusion h, ht⟩
    | true => exact ⟨hn, fun _ => ht, ht⟩
  | cons b0 n0 rest =>
    rcases ht with ⟨hn0, hz0, hrest⟩
    cases b <;> cases b0
    · exact ⟨by change 1 ≤ n + n0; omega, fun h => Bool.noConfusion h, hrest⟩
    · exact ⟨hn, fun h => Bool.noConfusion h, hn0, hz0, hrest⟩
    · exact ⟨hn, fun _ => head_zero_cons_false hn0 rest, hn0, hz0, hrest⟩
    · exact ⟨by change 1 ≤ n + n0; omega, hz0, hrest⟩

lemma valid_push {b : Bool} {n : Nat} {t : RTape} (ht : Valid t) :
    Valid (push b n t) := by
  unfold push
  cases h : Nat.beq n 0 with
  | true => exact ht
  | false =>
    have hn : 1 ≤ n := by
      cases n with
      | zero => cases h
      | succ m => omega
    exact valid_push1 hn ht

def SweepSpec_tail (tail : zB) (l0 : zB) (c : Cfg (Fin 2) (Fin 6)) : SweepRes → Prop
  | .halted => IsHaltFrom c
  | .done ph' t' => Valid_tail tail t' ∧ (c [target_tm]⊢* (l0 <{{if ph' then C else B}} denote_tape_tail tail t'))
  | .failed => True
local notation "SweepSpec" => SweepSpec_tail tail

lemma sweep_spec_trans {l0 : zB} {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {sr : SweepRes}
    (h₁₂ : c₁ [target_tm]⊢* c₂) (h₂ : SweepSpec l0 c₂ sr) :
    SweepSpec l0 c₁ sr := by
  cases sr with
  | halted => exact halt_from_trans h₁₂ h₂
  | done ph' t' => exact ⟨h₂.1, zSt h₁₂ h₂.2⟩
  | failed => trivial

lemma back_rel_spec (l0 : zB) (acc : AccList) (phase : Bool) (t : RTape)
    (hacc : ValidAcc acc) (ht : Valid t) :
    SweepSpec l0 (denote_acc_rel l0 acc <{{if phase then C else B}} denote_tape t) (back_rel acc phase t) := by
  induction acc generalizing phase t with
  | nil =>
    exact ⟨ht, ⟨0, rfl⟩⟩
  | some n rest ih =>
    rcases hacc with ⟨hn, hrest⟩
    change SweepSpec l0 _ (forceRTape (push1 phase n t) (back_rel rest phase))
    rw [forceRTape_eq]
    refine sweep_spec_trans ?_ (ih phase (push1 phase n t) hrest (valid_push1 hn ht))
    cases phase
    · rw [denote_push1]; exact back_some_B n (denote_acc_rel l0 rest) (denote_tape t)
    · rw [denote_push1]; exact back_some_C n (denote_acc_rel l0 rest) (denote_tape t)
  | none rest ih =>
    cases phase
    · change SweepSpec l0 _ (forceRTape (push1 false 1 t) (fun t' => back_rel rest true (RTape.cons true 2 t')))
      rw [forceRTape_eq]
      have hu : Valid (RTape.cons true 2 (push1 false 1 t)) :=
        valid_cons_true (by decide) (head_zero_push1_false (by decide) t) (valid_push1 (by decide) ht)
      refine sweep_spec_trans ?_ (ih true (RTape.cons true 2 (push1 false 1 t)) hacc hu)
      have h1 := back_none_B (denote_acc_rel l0 rest) (denote_tape t)
      have heq : denote_tape (RTape.cons true 2 (push1 false 1 t)) = ([1, 1, 0] : zF) +> denote_tape t := by
        simp [denote_push1, W1, W0]
      rw [heq]
      exact h1
    · change SweepSpec l0 _ (forceRTape (push1 true 2 t) (fun t' => back_rel rest false (RTape.cons false 1 t')))
      rw [forceRTape_eq]
      have hu : Valid (RTape.cons false 1 (push1 true 2 t)) :=
        valid_cons_false (by decide) (valid_push1 (by decide) ht)
      refine sweep_spec_trans ?_ (ih false (RTape.cons false 1 (push1 true 2 t)) hacc hu)
      have h1 := back_none_C (denote_acc_rel l0 rest) (denote_tape t)
      have heq : denote_tape (RTape.cons false 1 (push1 true 2 t)) = ([0, 1, 1] : zF) +> denote_tape t := by
        simp [denote_push1, W1, W0]
      rw [heq]
      exact h1



lemma sweep_false_rel_spec (l0 : zB) (ih : AccList → RTape → SweepRes)
    (h_ih : ∀ acc' t', ValidAcc acc' → Valid t' →
      SweepSpec l0 (denote_acc_rel l0 acc' {{E}}> denote_tape t') (ih acc' t'))
    (acc : AccList) (t : RTape) (hacc : ValidAcc acc) (ht : Valid t) :
    SweepSpec l0 (denote_acc_rel l0 acc {{E}}> denote_tape t) (sweep_false_rel ih acc t) := by
  cases t with
  | nil => trivial
  | cons b0 n0 rest =>
    cases b0 with
    | true => trivial
    | false =>
      rcases ht with ⟨hn0, _, hrest⟩
      change SweepSpec l0 _ (sf_b1 (Nat.beq n0 1) n0 rest ih acc)
      cases h1 : Nat.beq n0 1 with
      | true =>
        have hn0_eq : n0 = 1 := Nat.eq_of_beq_eq_true h1
        subst hn0_eq
        change SweepSpec l0 _ (sf_n0_1 rest acc)
        cases rest with
        | nil => trivial
        | cons b1 n1 r2 =>
          cases b1 with
          | false => trivial
          | true =>
            rcases hrest with ⟨hn1, hz2, hr2⟩
            change SweepSpec l0 _ (sf_n0_1_true_branch (Nat.ble 2 n1) acc r2 n1)
            cases hge2 : Nat.ble 2 n1 with
            | false =>
              have hn1_eq : n1 = 1 := by
                have hnot : ¬ (2 ≤ n1) := by rw [← Nat.ble_eq, hge2]; decide
                omega
              subst hn1_eq
              rcases hz2 rfl with ⟨r', hr'⟩
              change IsHaltFrom (denote_acc_rel l0 acc {{E}}> ((W0 ^ 1) +> ((W1 ^ 1) +> denote_tape r2)))
              rw [hr']
              exact sweep_010_halt (denote_acc_rel l0 acc) r'
            | true =>
              have hn1_ge : 2 ≤ n1 := Nat.ble_eq.mp hge2
              change SweepSpec l0 _ (back_rel acc false (RTape.cons false 2 (RTape.cons true (n1 - 1) r2)))
              have hu : Valid (RTape.cons false 2 (RTape.cons true (n1 - 1) r2)) :=
                valid_cons_false (by decide) (valid_cons_true (by omega) (hz2 rfl) hr2)
              refine sweep_spec_trans ?_ (back_rel_spec l0 acc false _ hacc hu)
              have hstep := sweep_011 (denote_acc_rel l0 acc) ((W1 ^ (n1 - 2)) +> denote_tape r2)
              have heq_in : denote_tape (RTape.cons false 1 (RTape.cons true n1 r2)) =
                  ([0, 1, 1] : zF) +> ((W1 ^ (n1 - 2)) +> denote_tape r2) := by
                change (W0 ^ 1) +> ((W1 ^ n1) +> denote_tape r2) = _
                rw [split_W1_2 hn1_ge]; rfl
              have heq_out : denote_tape (RTape.cons false 2 (RTape.cons true (n1 - 1) r2)) =
                  ([0, 0, 1] : zF) +> ((W1 ^ (n1 - 2)) +> denote_tape r2) := by
                change (W0 ^ 2) +> ((W1 ^ (n1 - 1)) +> denote_tape r2) = _
                rw [split_W1_1 (by omega), show n1 - 1 - 1 = n1 - 2 by omega]; rfl
              rw [heq_in, heq_out]
              exact hstep
      | false =>
        change SweepSpec l0 _ (sf_b2 (Nat.beq n0 2) n0 rest ih acc)
        cases h2 : Nat.beq n0 2 with
        | true =>
          have hn0_eq : n0 = 2 := Nat.eq_of_beq_eq_true h2
          subst hn0_eq
          change SweepSpec l0 _ (sf_n0_2 rest ih acc)
          cases rest with
          | nil => trivial
          | cons b1 n1 r2 =>
            cases b1 with
            | false => trivial
            | true =>
              rcases hrest with ⟨hn1, _, hr2⟩
              change SweepSpec l0 _ (forceRTape (push true (n1 - 1) r2) (ih (AccList.none acc)))
              rw [forceRTape_eq]
              refine sweep_spec_trans ?_ (h_ih (AccList.none acc) (push true (n1 - 1) r2) hacc (valid_push hr2))
              have hstep := sweep_001 (denote_acc_rel l0 acc) ((W1 ^ (n1 - 1)) +> denote_tape r2)
              have heq_in : denote_tape (RTape.cons false 2 (RTape.cons true n1 r2)) =
                  ([0, 0, 1] : zF) +> ((W1 ^ (n1 - 1)) +> denote_tape r2) := by
                change (W0 ^ 2) +> ((W1 ^ n1) +> denote_tape r2) = _
                rw [split_W1_1 hn1]; rfl
              rw [heq_in, denote_push]
              exact hstep
        | false =>
          change SweepSpec l0 _ (sf_b3 (Nat.beq n0 3) n0 rest acc)
          cases h3 : Nat.beq n0 3 with
          | true =>
            have hn0_eq : n0 = 3 := Nat.eq_of_beq_eq_true h3
            subst hn0_eq
            change SweepSpec l0 _ (sf_n0_3 rest acc)
            cases rest with
            | nil => trivial
            | cons b1 n1 r2 =>
              cases b1 with
              | false => trivial
              | true =>
                rcases hrest with ⟨hn1, _, hr2⟩
                change SweepSpec l0 _ (forceRTape (push true (n1 - 1) r2) (fun r3 => forceRTape (push1 false 2 r3) (fun r4 => back_rel acc true (RTape.cons true 2 r4))))
                rw [forceRTape_eq, forceRTape_eq]
                have hu : Valid (RTape.cons true 2 (push1 false 2 (push true (n1 - 1) r2))) :=
                  valid_cons_true (by decide) (head_zero_push1_false (by decide) _) (valid_push1 (by decide) (valid_push hr2))
                refine sweep_spec_trans ?_ (back_rel_spec l0 acc true _ hacc hu)
                have hstep := sweep_0001 (denote_acc_rel l0 acc) ((W1 ^ (n1 - 1)) +> denote_tape r2)
                have heq_in : denote_tape (RTape.cons false 3 (RTape.cons true n1 r2)) =
                    ([0, 0, 0, 1] : zF) +> ((W1 ^ (n1 - 1)) +> denote_tape r2) := by
                  change (W0 ^ 3) +> ((W1 ^ n1) +> denote_tape r2) = _
                  rw [split_W1_1 hn1]; rfl
                have heq_out : denote_tape (RTape.cons true 2 (push1 false 2 (push true (n1 - 1) r2))) =
                    ([1, 1, 0, 0] : zF) +> ((W1 ^ (n1 - 1)) +> denote_tape r2) := by
                  simp [denote_push1, denote_push, W1, W0]
                rw [heq_in, heq_out]
                exact hstep
          | false =>
            have hn0_ge4 : 4 ≤ n0 := by
              have hne1 : n0 ≠ 1 := Nat.ne_of_beq_eq_false h1
              have hne2 : n0 ≠ 2 := Nat.ne_of_beq_eq_false h2
              have hne3 : n0 ≠ 3 := Nat.ne_of_beq_eq_false h3
              omega
            change SweepSpec l0 _ (forceRTape (push false (n0 - 4) rest) (fun r3 => forceRTape (push1 true 3 r3) (fun r4 => back_rel acc false (RTape.cons false 1 r4))))
            rw [forceRTape_eq, forceRTape_eq]
            have hu : Valid (RTape.cons false 1 (push1 true 3 (push false (n0 - 4) rest))) :=
              valid_cons_false (by decide) (valid_push1 (by decide) (valid_push hrest))
            refine sweep_spec_trans ?_ (back_rel_spec l0 acc false _ hacc hu)
            have hstep := sweep_0000 (denote_acc_rel l0 acc) ((W0 ^ (n0 - 4)) +> denote_tape rest)
            have heq_in : denote_tape (RTape.cons false n0 rest) =
                ([0, 0, 0, 0] : zF) +> ((W0 ^ (n0 - 4)) +> denote_tape rest) := by
              change (W0 ^ n0) +> denote_tape rest = _
              exact split_W0_4 hn0_ge4 (denote_tape rest)
            have heq_out : denote_tape (RTape.cons false 1 (push1 true 3 (push false (n0 - 4) rest))) =
                ([0, 1, 1, 1] : zF) +> ((W0 ^ (n0 - 4)) +> denote_tape rest) := by
              simp [denote_push1, denote_push, W1, W0]
            rw [heq_in, heq_out]
            exact hstep

lemma run_sweep_rel_spec (l0 : zB) (fuel : Nat) (acc : AccList) (t : RTape)
    (hacc : ValidAcc acc) (ht : Valid t) :
    SweepSpec l0 (denote_acc_rel l0 acc {{E}}> denote_tape t) (run_sweep_rel fuel acc t) := by
  induction fuel generalizing acc t with
  | zero => trivial
  | succ fuel ih =>
    cases t with
    | nil => exact sweep_false_rel_spec l0 (run_sweep_rel fuel) ih acc RTape.nil hacc ht
    | cons b0 n0 r1 =>
      cases b0 with
      | false => exact sweep_false_rel_spec l0 (run_sweep_rel fuel) ih acc (RTape.cons false n0 r1) hacc ht
      | true =>
        rcases ht with ⟨hn0, _, hr1⟩
        change SweepSpec l0 _ (sweep_false_rel (run_sweep_rel fuel) (AccList.some n0 acc) r1)
        refine sweep_spec_trans (sweep_ones n0 (denote_acc_rel l0 acc) (denote_tape r1)) ?_
        exact sweep_false_rel_spec l0 (run_sweep_rel fuel) ih (AccList.some n0 acc) r1 ⟨hn0, hacc⟩ hr1

def StepSpec_tail (tail : zB) (c : Cfg (Fin 2) (Fin 6)) : StepRes → Prop
  | .halted => IsHaltFrom c
  | .running t' => Valid_tail tail t' ∧ (c [target_tm]⊢* (default <{{C}} denote_tape_tail tail t'))
  | .failed => True
local notation "StepSpec" => StepSpec_tail tail

lemma step_spec_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : StepRes}
    (h₁₂ : c₁ [target_tm]⊢* c₂) (h₂ : StepSpec c₂ res) :
    StepSpec c₁ res := by
  cases res with
  | halted => exact halt_from_trans h₁₂ h₂
  | running t' => exact ⟨h₂.1, zSt h₁₂ h₂.2⟩
  | failed => trivial

lemma finish_some_none_fused_spec (a : Nat) (c : Cfg (Fin 2) (Fin 6)) (sr : SweepRes)
    (hsr : SweepSpec ((default << 1 <+ (W1 ^ a)) << 1 << 0 << 1) c sr) :
    StepSpec c (finish_some_none_fused sr (a + 2)) := by
  cases sr with
  | halted => exact hsr
  | failed => trivial
  | done phase t =>
    rcases hsr with ⟨ht, hstep_c⟩
    refine step_spec_trans hstep_c ?_
    cases phase with
    | true =>
      change StepSpec _ (forceRTape (push1 true 2 t) (fun r2 => StepRes.running (RTape.cons true 1 (RTape.cons false (a + 2) r2))))
      rw [forceRTape_eq]
      refine ⟨valid_cons_true (by decide) (head_zero_cons_false (by omega) _) (valid_cons_false (by omega) (valid_push1 (by decide) ht)), ?_⟩
      refine zSt (back_none_C _ _) ?_
      refine zSt (back_some_B a _ _) ?_
      have h1 := back_nil_B ((W0 ^ a) +> (([0, 1, 1] : zF) +> denote_tape t))
      have heq : (([1, 0] : zF) +> ((W0 ^ a) +> (([0, 1, 1] : zF) +> denote_tape t))) =
          denote_tape (RTape.cons true 1 (RTape.cons false (a + 2) (push1 true 2 t))) := by
        change W1 +> (W0 +> ((W0 ^ a) +> (W0 +> ((W1 ^ 2) +> denote_tape t)))) =
          (W1 ^ 1) +> ((W0 ^ (a + 2)) +> denote_tape (push1 true 2 t))
        rw [denote_push1, show a + 2 = 1 + (a + 1) by omega, z0k W0 1 (a + 1), z0k W0 a 1, append_assoc, append_assoc]
        rfl
      rw [heq] at h1
      exact h1
    | false =>
      change StepSpec _ (fsn_false t (a + 2))
      have h_unwind : (((default << 1 <+ (W1 ^ a)) << 1 << 0 << 1) <{{B}} denote_tape t) [target_tm]⊢*
          (default <{{C}} ((W1 ^ (a + 3)) +> denote_tape (push1 false 1 t))) := by
        refine zSt (back_none_B _ _) ?_
        refine zSt (back_some_C a _ _) ?_
        have h1 := back_nil_C ((W1 ^ a) +> (([1, 1, 0] : zF) +> denote_tape t))
        have heq : W1 +> ((W1 ^ a) +> (([1, 1, 0] : zF) +> denote_tape t)) =
            (W1 ^ (a + 3)) +> denote_tape (push1 false 1 t) := by
          rw [denote_push1, show a + 3 = 1 + (a + 2) by omega, z0k W1 1 (a + 2), z0k W1 a 2, append_assoc, append_assoc]
          rfl
        rw [heq] at h1
        exact h1
      refine step_spec_trans h_unwind ?_
      have hvp : Valid (push1 false 1 t) := valid_push1 (by decide) ht
      unfold fsn_false
      cases hp : push1 false 1 t with
      | nil => trivial
      | cons b1 b' r' =>
        rw [hp] at hvp
        rcases hvp with ⟨hb', _, hr'⟩
        cases b1 with
        | true => trivial
        | false =>
          change StepSpec _ (fsn_false_branch1 (Nat.ble 4 b') (a + 2) b' r')
          cases hge4 : Nat.ble 4 b' with
          | true =>
            have hb_ge4 : 4 ≤ b' := Nat.ble_eq.mp hge4
            change StepSpec _ (forceRTape (push false (b' - 4) r') (fun r2 => forceRTape (push1 true 3 r2) (fun r3 => StepRes.running (RTape.cons true 1 (RTape.cons false ((a + 2) + 3) r3)))))
            rw [forceRTape_eq, forceRTape_eq]
            refine ⟨valid_cons_true (by decide) (head_zero_cons_false (by omega) _) (valid_cons_false (by omega) (valid_push1 (by decide) (valid_push hr'))), ?_⟩
            have hstep := sweep_a_ge4 (a + 3) ((W0 ^ (b' - 4)) +> denote_tape r')
            have heq_in : denote_tape (RTape.cons false b' r') =
                ([0, 0, 0, 0] : zF) +> ((W0 ^ (b' - 4)) +> denote_tape r') :=
              split_W0_4 hb_ge4 (denote_tape r')
            have heq_out : W1 +> ((W0 ^ ((a + 3) + 2)) +> (([1, 1, 1] : zF) +> ((W0 ^ (b' - 4)) +> denote_tape r'))) =
                denote_tape (RTape.cons true 1 (RTape.cons false ((a + 2) + 3) (push1 true 3 (push false (b' - 4) r')))) := by
              simp [denote_tape_tail, denote_push1, denote_push, W1, W0]
            rw [heq_in]
            rw [heq_out] at hstep
            exact hstep
          | false =>
            change StepSpec _ (fsn_false_branch2 (Nat.beq b' 3) (a + 2) r')
            cases his3 : Nat.beq b' 3 with
            | false => trivial
            | true =>
              have hb_eq3 : b' = 3 := Nat.eq_of_beq_eq_true his3
              subst hb_eq3
              change StepSpec _ (fsn_false_b3 r' (a + 2))
              cases r' with
              | nil => trivial
              | cons b2 c' r'' =>
                rcases hr' with ⟨hc', _, hr''⟩
                cases b2 with
                | false => trivial
                | true =>
                  change StepSpec _ (fsn_false_b3_branch (Nat.ble 2 c') (a + 2) c' r'')
                  cases hge2 : Nat.ble 2 c' with
                  | false => trivial
                  | true =>
                    have hc_ge2 : 2 ≤ c' := Nat.ble_eq.mp hge2
                    change StepSpec _ (forceRTape (push true (c' - 1) r'') (fun r3 => StepRes.running (RTape.cons true ((a + 2) + 4) (RTape.cons false 2 r3))))
                    rw [forceRTape_eq]
                    refine ⟨valid_cons_true (by omega) (head_zero_cons_false (by decide) _) (valid_cons_false (by decide) (valid_push hr'')), ?_⟩
                    have hstep := sweep_a_3 (a + 3) ((W1 ^ (c' - 1)) +> denote_tape r'')
                    have heq_in : denote_tape (RTape.cons false 3 (RTape.cons true c' r'')) =
                        ([0, 0, 0, 1] : zF) +> ((W1 ^ (c' - 1)) +> denote_tape r'') := by
                      change (W0 ^ 3) +> ((W1 ^ c') +> denote_tape r'') = _
                      rw [split_W1_1 hc']; rfl
                    have heq_out : (W1 ^ ((a + 3) + 3)) +> (([0, 0] : zF) +> ((W1 ^ (c' - 1)) +> denote_tape r'')) =
                        denote_tape (RTape.cons true ((a + 2) + 4) (RTape.cons false 2 (push true (c' - 1) r''))) := by
                      simp [denote_tape_tail, denote_push, W1, W0]
                    rw [heq_in]
                    rw [heq_out] at hstep
                    exact hstep

lemma rle_step_spec (t : RTape) (ht : Valid t) :
    StepSpec (default <{{C}} denote_tape t) (rle_step t) := by
  cases t with
  | nil => trivial
  | cons b0 a r1 =>
    rcases ht with ⟨ha, _, hr1⟩
    cases b0 with
    | false => trivial
    | true =>
      cases r1 with
      | nil => trivial
      | cons b1 b r2 =>
        rcases hr1 with ⟨hb, _, hr2⟩
        cases b1 with
        | true => trivial
        | false =>
          change StepSpec _ (step_dispatch_ff (Bool.rec false (Nat.ble 4 b) (Nat.beq a 1)) a b r2)
          cases ha1 : Nat.beq a 1 with
          | false =>
            change StepSpec _ (step_dispatch_b2 (Nat.beq b 2) a r2)
            cases hb2 : Nat.beq b 2 with
            | false => trivial
            | true =>
              have hb_eq2 : b = 2 := Nat.eq_of_beq_eq_true hb2
              subst hb_eq2
              change StepSpec _ (step_case2 a r2)
              cases r2 with
              | nil => trivial
              | cons b2 c r3 =>
                rcases hr2 with ⟨hc, _, hr3⟩
                cases b2 with
                | false => trivial
                | true =>
                  change StepSpec _ (forceRTape (push true (c - 1) r3) (fun r4 => finish_some_none_fused (run_sweep_rel 16 AccList.nil r4) (a + 2)))
                  rw [forceRTape_eq]
                  refine finish_some_none_fused_spec a _ _ ?_
                  have h_init : (default <{{C}} denote_tape (RTape.cons true a (RTape.cons false 2 (RTape.cons true c r3)))) [target_tm]⊢*
                      (((default << 1 <+ (W1 ^ a)) << 1 << 0 << 1) {{E}}> denote_tape (push true (c - 1) r3)) := by
                    refine zSt (start_sweep _) ?_
                    refine zSt (sweep_ones a _ _) ?_
                    have heq : denote_tape (RTape.cons false 2 (RTape.cons true c r3)) =
                        ([0, 0, 1] : zF) +> denote_tape (push true (c - 1) r3) := by
                      change (W0 ^ 2) +> ((W1 ^ c) +> denote_tape r3) = _
                      rw [denote_push, split_W1_1 hc]; rfl
                    rw [heq]
                    exact sweep_001 _ _
                  exact sweep_spec_trans h_init (run_sweep_rel_spec ((default << 1 <+ (W1 ^ a)) << 1 << 0 << 1) 16 AccList.nil (push true (c - 1) r3) trivial (valid_push hr3))
          | true =>
            have ha_eq1 : a = 1 := Nat.eq_of_beq_eq_true ha1
            subst ha_eq1
            cases hb4 : Nat.ble 4 b with
            | false =>
              change StepSpec _ (step_dispatch_b2 (Nat.beq b 2) 1 r2)
              cases hb2 : Nat.beq b 2 with
              | false => trivial
              | true =>
                have hb_eq2 : b = 2 := Nat.eq_of_beq_eq_true hb2
                subst hb_eq2
                change StepSpec _ (step_case2 1 r2)
                cases r2 with
                | nil => trivial
                | cons b2 c r3 =>
                  rcases hr2 with ⟨hc, _, hr3⟩
                  cases b2 with
                  | false => trivial
                  | true =>
                    change StepSpec _ (forceRTape (push true (c - 1) r3) (fun r4 => finish_some_none_fused (run_sweep_rel 16 AccList.nil r4) (1 + 2)))
                    rw [forceRTape_eq]
                    refine finish_some_none_fused_spec 1 _ _ ?_
                    have h_init : (default <{{C}} denote_tape (RTape.cons true 1 (RTape.cons false 2 (RTape.cons true c r3)))) [target_tm]⊢*
                        (((default << 1 <+ (W1 ^ 1)) << 1 << 0 << 1) {{E}}> denote_tape (push true (c - 1) r3)) := by
                      refine zSt (start_sweep _) ?_
                      refine zSt (sweep_ones 1 _ _) ?_
                      have heq : denote_tape (RTape.cons false 2 (RTape.cons true c r3)) =
                          ([0, 0, 1] : zF) +> denote_tape (push true (c - 1) r3) := by
                        change (W0 ^ 2) +> ((W1 ^ c) +> denote_tape r3) = _
                        rw [denote_push, split_W1_1 hc]; rfl
                      rw [heq]
                      exact sweep_001 _ _
                    exact sweep_spec_trans h_init (run_sweep_rel_spec ((default << 1 <+ (W1 ^ 1)) << 1 << 0 << 1) 16 AccList.nil (push true (c - 1) r3) trivial (valid_push hr3))
            | true =>
              have hb_ge4 : 4 ≤ b := Nat.ble_eq.mp hb4
              change StepSpec _ (forceRTape (push false (b % 4) r2) (fun r3 => forceRTape (push1 true 1 r3) (fun r4 => finish_some_none_fused (run_sweep_rel 16 AccList.nil r4) (6 * (b / 4)))))
              rw [forceRTape_eq, forceRTape_eq]
              let q := (b - 4) / 4
              have hp6 : 6 * (b / 4) = (4 + 6 * q) + 2 := by omega
              rw [hp6]
              refine finish_some_none_fused_spec (4 + 6 * q) _ _ ?_
              have h_init : (default <{{C}} denote_tape (RTape.cons true 1 (RTape.cons false b r2))) [target_tm]⊢*
                  (((default << 1 <+ (W1 ^ (4 + 6 * q))) << 1 << 0 << 1) {{E}}> denote_tape (push1 true 1 (push false (b % 4) r2))) := by
                have heq_b : denote_tape (RTape.cons true 1 (RTape.cons false b r2)) =
                    ([1, 0, 0, 0, 0] : zF) +> ((W0 ^ (4 * q)) +> ((W0 ^ (b % 4)) +> denote_tape r2)) := by
                  change (W1 ^ 1) +> ((W0 ^ b) +> denote_tape r2) = _
                  have hb_split : W0 ^ b = W0 ^ (4 + (4 * q + b % 4)) := congrArg (W0 ^ ·) (by omega)
                  rw [hb_split, z0k W0 4 (4 * q + b % 4), z0k W0 (4 * q) (b % 4), append_assoc, append_assoc]
                  rfl
                rw [heq_b]
                refine zSt (ff_entry _) ?_
                refine zSt (ff_loop q 4 ((W0 ^ (b % 4)) +> denote_tape r2)) ?_
                refine zSt (start_sweep _) ?_
                refine zSt (sweep_ones (4 + 6 * q) _ _) ?_
                have h_s001 := sweep_001 (default << 1 <+ (W1 ^ (4 + 6 * q))) (denote_tape (push1 true 1 (push false (b % 4) r2)))
                have heq_tail : (([0, 0, 1] : zF) +> denote_tape (push1 true 1 (push false (b % 4) r2))) =
                    (([0, 0, 1, 1] : zF) +> ((W0 ^ (b % 4)) +> denote_tape r2)) := by
                  simp [denote_push1, denote_push, W1, W0]
                rw [heq_tail] at h_s001
                exact h_s001
              exact sweep_spec_trans h_init (run_sweep_rel_spec ((default << 1 <+ (W1 ^ (4 + 6 * q))) << 1 << 0 << 1) 16 AccList.nil (push1 true 1 (push false (b % 4) r2)) trivial (valid_push1 (by decide) (valid_push hr2)))

lemma run_pow_spec (k : Nat) (t : RTape) (ht : Valid t) :
    StepSpec (default <{{C}} denote_tape t) (run_pow k t) := by
  induction k generalizing t with
  | zero => exact rle_step_spec t ht
  | succ k ih =>
    change StepSpec _ (StepRes.rec StepRes.halted (run_pow k) StepRes.failed (run_pow k t))
    have h1 := ih t ht
    cases hc : run_pow k t with
    | halted => rw [hc] at h1; exact h1
    | running t' =>
      rw [hc] at h1
      exact step_spec_trans h1.2 (ih t' h1.1)
    | failed => trivial

end Tail

abbrev head_zero {tail : zB} := head_zero_tail tail
abbrev Valid {tail : zB} := Valid_tail tail

def trunc_tail (tail : zB) : Nat → RTape → zB
  | 0, .nil => tail
  | 0, .cons b n rest => Bool.rec (denote_tape_tail tail (.cons false n rest)) tail b
  | _ + 1, .nil => tail
  | k + 1, .cons _ _ rest => trunc_tail tail k rest

lemma denote_trunc (tail : zB) (k : Nat) (t : RTape) :
    denote_tape_tail (trunc_tail tail k t) (trunc k t) = denote_tape_tail tail t := by
  induction k generalizing t with
  | zero =>
    cases t with
    | nil => rfl
    | cons b n rest => cases b <;> rfl
  | succ k ih =>
    cases t with
    | nil => rfl
    | cons b n rest =>
      change denote_tape_tail (trunc_tail tail k rest) (forceRTape (trunc k rest) (RTape.cons b n)) = _
      rw [forceRTape_eq]
      change ((if b then W1 else W0) ^ n) +> denote_tape_tail (trunc_tail tail k rest) (trunc k rest) = _
      rw [ih rest]
      rfl

lemma head_zero_trunc {tail : zB} (k : Nat) {t : RTape} (hz : @head_zero tail t) :
    @head_zero (trunc_tail tail k t) (trunc k t) := by
  unfold head_zero head_zero_tail at hz ⊢
  rwa [denote_trunc]

lemma valid_trunc {tail : zB} (k : Nat) {t : RTape} (ht : @Valid tail t) :
    @Valid (trunc_tail tail k t) (trunc k t) := by
  induction k generalizing t with
  | zero =>
    cases t with
    | nil => exact ht
    | cons b n rest =>
      cases b with
      | false =>
        rcases ht with ⟨hn, _, _⟩
        exact head_zero_of_W0 n hn (denote_tape_tail tail rest)
      | true => exact ht
  | succ k ih =>
    cases t with
    | nil => exact ht
    | cons b n rest =>
      rcases ht with ⟨hn, hz, hrest⟩
      change @Valid (trunc_tail tail k rest) (forceRTape (trunc k rest) (RTape.cons b n))
      rw [forceRTape_eq]
      exact ⟨hn, fun hb => head_zero_trunc k (hz hb), ih hrest⟩

def StepSpecEx (c : Cfg (Fin 2) (Fin 6)) : StepRes → Prop
  | .halted => IsHaltFrom c
  | .running t' => ∃ tail', @Valid tail' t' ∧ (c [target_tm]⊢* (default <{{C}} denote_tape_tail tail' t'))
  | .failed => True

lemma step_spec_ex_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : StepRes}
    (h₁₂ : c₁ [target_tm]⊢* c₂) (h₂ : StepSpecEx c₂ res) :
    StepSpecEx c₁ res := by
  cases res with
  | halted => exact halt_from_trans h₁₂ h₂
  | running t' =>
    rcases h₂ with ⟨tail', ht', hstep⟩
    exact ⟨tail', ht', zSt h₁₂ hstep⟩
  | failed => trivial

lemma run_64_spec {tail : zB} (t : RTape) (ht : @Valid tail t) :
    StepSpecEx (default <{{C}} denote_tape_tail tail t) (run_64 t) := by
  unfold run_64
  have h1 := @run_pow_spec tail 6 t ht
  cases hc : run_pow 6 t with
  | halted => rw [hc] at h1; exact h1
  | running t' =>
    rw [hc] at h1
    rcases h1 with ⟨ht', hstep⟩
    refine ⟨trunc_tail tail 25 t', valid_trunc 25 ht', ?_⟩
    rw [denote_trunc]
    exact hstep
  | failed => trivial

lemma run_chunk_spec (k : Nat) {tail : zB} (t : RTape) (ht : @Valid tail t) :
    StepSpecEx (default <{{C}} denote_tape_tail tail t) (run_chunk k t) := by
  induction k generalizing tail t with
  | zero => exact run_64_spec t ht
  | succ k ih =>
    change StepSpecEx _ (StepRes.rec StepRes.halted (run_chunk k) StepRes.failed (run_chunk k t))
    have h1 := ih t ht
    cases hc : run_chunk k t with
    | halted => rw [hc] at h1; exact h1
    | running t' =>
      rw [hc] at h1
      rcases h1 with ⟨tail', ht', hstep⟩
      exact step_spec_ex_trans hstep (ih t' ht')
    | failed => trivial

lemma bool_beq_eq {b1 b2 : Bool} (h : bool_beq b1 b2 = true) : b1 = b2 := by
  cases b1 <;> cases b2 <;> first | rfl | cases h

lemma rtape_beq_eq {t1 t2 : RTape} (h : rtape_beq t1 t2 = true) : t1 = t2 := by
  induction t1 generalizing t2 with
  | nil =>
    cases t2 with
    | nil => rfl
    | cons _ _ _ => cases h
  | cons b1 n1 r1 ih =>
    cases t2 with
    | nil => cases h
    | cons b2 n2 r2 =>
      change Bool.rec false (Bool.rec false (rtape_beq r1 r2) (Nat.beq n1 n2)) (bool_beq b1 b2) = true at h
      cases hb : bool_beq b1 b2
      · rw [hb] at h; cases h
      · rw [hb] at h
        dsimp at h
        cases hn : Nat.beq n1 n2
        · rw [hn] at h; cases h
        · rw [hn] at h
          dsimp at h
          rw [bool_beq_eq hb, Nat.eq_of_beq_eq_true hn, ih h]

lemma chain_chunk {t t' : RTape}
    (h_eq : is_running_eq (run_chunk 8 t) t' = true)
    (h_next : ∀ {tail' : zB}, @Valid tail' t' → IsHaltFrom (default <{{C}} denote_tape_tail tail' t'))
    {tail : zB} (ht : @Valid tail t) :
    IsHaltFrom (default <{{C}} denote_tape_tail tail t) := by
  have h1 := run_chunk_spec 8 t ht
  revert h1 h_eq
  generalize run_chunk 8 t = res
  intro h_eq h1
  cases res with
  | halted => cases h_eq
  | failed => cases h_eq
  | running t_out =>
    have h_t : t_out = t' := rtape_beq_eq h_eq
    subst h_t
    rcases h1 with ⟨tail', ht', hstep⟩
    exact halt_from_trans hstep (h_next ht')

lemma finish_chunk {t : RTape}
    (h_halt : is_halted (run_chunk 8 t) = true)
    {tail : zB} (ht : @Valid tail t) :
    IsHaltFrom (default <{{C}} denote_tape_tail tail t) := by
  have h1 := run_chunk_spec 8 t ht
  revert h1 h_halt
  generalize run_chunk 8 t = res
  intro h_halt h1
  cases res with
  | halted => exact h1
  | running _ => cases h_halt
  | failed => cases h_halt

def st_0 : RTape := (RTape.cons true 4 (RTape.cons false 2 (RTape.cons true 5 (RTape.cons false 100 RTape.nil))))
def st_1 : RTape := (RTape.cons true 1 (RTape.cons false 61355888903510261716329430401428410789094962784795687908770234312467309066395736343665893284816352404093840432451576395537331409230326811531718870620242311802074364327874318624733879635552067585115945897587558453669234766484464185136407372925931825853402780799067252490426967888626247650263793602105465442096177200110758385019408240224363040284308942146524983474898997588762250280542045240517803465486407619271046431943756245124635673464869324359559586392939128449102683916063082456703678436472468173383380728718752933557860034041732801011279566098001559958126060572360102565731352155194839334755792702959501191122428633720483279607777911232863825583656403799308998834913781769811938831664575378802386817665730253513215136764633895174461257456355206511971662000792406617620410703869086947214327732507597350888794432767955481642932015418221615422871314473172110795098686688369395526010499851335014314568618892485423799967619844092653206915405078219569431449246366122672505271946114358848646262951467491829957959133522928116749850768736740758986247053224820694690307035110011710085314538571725922224832195216215096326180058145218503118724804287242602284783399121165133885483982216437664550644338844208194971465614071714734103124104239774814135947184204155839020147326743476648931162310793970334764559802057325130939523357357755641060544169245482840784782785855917017116114102926743488571660870512242581772687069311985164671517642120582644677346842597621862568835519472856340044115446768406290064183662804973235395905364845027200481914255950807388434515329718058233084697298771764054634684126250788437286979067906753361851251530858263302280125733896041109800827317186984802062134511845372280987600805389187922921874977560235619419023953203173412902975141839704243899402023463259101730866819760787395705769672159296010267513985844154263233213044316427149280536864835266160576766045824669104856874424340028542434138952040606392804205649724927186620379326359657829969142135175687734223083023051792028865635718996839906575307892086875404488982164478013318115353242999078517811690154564569860059865558838157605330175066261233789554884650132053339347190907691001543126941021654247103834625707109940586054212900129285983947724604168684161586909523990078647035155254020289763983300156946636378028743766598587585906596400078986873520862138836249321961692567608141224671973073 (RTape.cons true 5 (RTape.cons false 9 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 7 (RTape.cons true 6 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 22 (RTape.cons true 5 (RTape.cons false 5 (RTape.cons true 6 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 5 (RTape.cons true 3 (RTape.cons false 5 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 6 RTape.nil)))))))))))))))))))))))))
def st_2 : RTape := (RTape.cons true 1 (RTape.cons false 1617491306905454944625181198296747611084420324065908406892681465814248338562833576543354127244862933355139949387736720371697295375036380588298471727786488966295434594471373768888592054733114544752754188445092550310005217854077965956156478414287669584632288782078964146027800251403706059203206774088121311042951153404412868409922014126845254378712945978096504138966535119630655831279736320774381828482271153762113076009242221926174448236161390335827288341658146572401346646197192720825948390799729059768801371787318545209360154056033998988560413863956335976761521953171549639162901134029536528569408116938483176393180866148635920526690789327724325710752693962258159167240321947455078161822867482775436260999594093471122986419609503726008404164952820290247263696827450963132150380809798035195247329946193244912716318232154880747683737232611103522382589002556045348135452854850471942519728931821389022607057522251582155868597280961672918226775824719192145629176689590015146644644501729020680095902295290195743100623216177957043009495894007824337719566430482866494779080666042280671522435711388012089786223147811086710030025162009200513512217558339518386577115140133698679594603495642339309344259341182569122609251235237609891869687994016364026315966401161407409257369278403794403062957633812605955633035307692848543256490001089013484903281763940867758288974200313250433275621518870695849819891102438870406210480573353565793532591536333488734825811308445145390711314858338780578469946541151355003710172724824508464997111391146881098582307879530264752905373600903822556528574691313497671719845006563899103267221239889386152472574313032172455507221680634770990363854737912138853701230529076666135595222540381021002752334702705890216584743843441721295676772597840808252299778107791842508851251225612284868687187079240766509721967105572986034482063181562805991887324385273529870802465490138176245570289626366548425667145603911058171712421320791876176996871059868951072185142942456640545132006597746334122025418510541229230564830196849036028054115267279877543343181656900067198958760758834956048305462953279600493012202429200660789840657352420443771291670406940593732919175109444582670830229439418045517688030992395425209911906924270227824773285099563794690231272421475650469027067530435428832342223474220720693054278386122587616236084764200464068566997163773307434815457674909392143464379319055734701676903811452506508953620485791862431865914951145835328822792363580002493821948963432545226151374455469045061326039616473449359260397419161759700167533003734674432728700387109101595833004403744235329350497019037259453788686334528936145043351670275542471105228337042354827755216646495410065440046005141306861034910783041090841212858780377266004791085186602065691088087052016509747160432556953438936780745430155340763141690112628365723993817691817765556707813023407142913106107584067794277005697169949039451930144480529607741847590033080281582356281164734797116698155358036812609635273904862319826666267302816815868221503832645110844271934969532744769403922111699648740371663395230402511959246297087966044765773125602187971967082859286252887221585924323281778096553664455954504869606870203890574442674526381233750195840218924441364430464807488214045170918642926288783553417772037008491085242494438518262248937287319564593729652071377614337176993733527487192565776064141325223364264598936017316335968162097360929235068408968317197301297613456376229418029558745283928392413635281888240929921549591187800349034508086159176746744567499591800790499147320348364445436816853649691642040952329161670569531459504958778138470163559466786859569078332345754521986858445893775648505384030881689161643668573730936345720772304030161695030161393644482710091073160625391948197726566999479768047636943141381249923206172597204385831510266811497001597426441901166312211824571250118541916637037770308151056421463094266190480192280273258586723022099306729097555188160645258578013469392622424130123051996666034665263186327216366424894093433696672086157779466893838996505912789871142251153751784709881422985094453425207553835712910385916457581129878665372662826104385336495828108456749697633627684562163452162094014231365101505386599564975391020903894860106887481178808824141504003015456220631869112084235451522302046709233497982339118963724609143066085792464118007763138395260968773576277539364560632158276651231241046768356954001664459185904154656994697874628416244329262390804009213769897919672745294166746807362722086430512035125599381302474364484742634765112262633811867193756129787013186378187206111544499879787752948533166571318172851940063340526796263217178971869149523912487340137473234292149719931045777803013255854321339351343743482406799432656873088015779076 (RTape.cons true 25 (RTape.cons false 2 (RTape.cons true 2 (RTape.cons false 27 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 6 (RTape.cons false 3 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 5 (RTape.cons true 3 RTape.nil)))))))))))))))))))))))))
def st_3 : RTape := (RTape.cons true 1 (RTape.cons false 6514143529604139024321326760061967124710310351313426088778294077754167198158265573428423004390006674261080243567414399411602165067568262980561123307272839850140500910524921811087806112140082430363177826009374848553212544564456728891005630875353508153758010095168784633092890276403034695450079142055819703457241803492116809158580765447752019166739203201587897595122463982665646736749287539327506355904359613591617926022384916514252677761288700426756057463908643507101672035780885496883380684674049650645327713403624964241473166176207515592898783912011946697134440530794205265145587899218243912397822177578302834594782858891661843170747715874103901127354562707056236307020325756795186642574559997690383931760925513227991995053354536994434832547675110614883814605435712907963684546653644468247595741873259592728998665897232380550187377253642761808718761941683496162456916463997166947229988122328627782562235179493521589418204716682946588645123993144555868827828023151166566228515928968946470958308073580037243837948522362547604821870240681760496447317336171419076930005491875767706575571137958421880128378703796909606329387496221970662398793363608147661492708688290509182417794060877714353802865008820163488621593454377614590759225654913464227986588288947691285157897001385008979519737925755829801063143240933380781687090730262782907121624785112425320196985726090228059150135475522939335692670079444506451846269673136976687012457691701903199221930966630017644510432448185452221712469914242510998222499786102111246872663534684534107558273810670521773720236746095626402329796718055683653097752571462766735806264144477710120297236831311443832138267831496080351363497689785660866602923188520350312456047358324541288275696187572584034424094386144761827357187509134392689787678306114732128532398875868858388117953427469087315921135892329896679683360749508148309930709269075756347727243176175560970025946143291433001884012488419467679348630607432500720259148362507359397581844784204648350047652822676451825021503069792402817193333325436759092882558959896101785054791866253880407808341112049297926386796053964677131170616073133202842921855464952086181459637948807249455154217760368564455440896507283016804023189707223426614253944558261183554435848367986917077589452405830052789341736352067637478828252113880691323588299852934364453687699740257759288405115344100966747002521070198447830812808286405216461397941865132848010742603004255094270385186780566976564091574453517300420479023897534452575793171244562519922901943921917397656334351578692798826167510074530816553837840387277194086069793377482623520250218398914598193397556857325893976092143313038425678286153761026362559046518022309384902773347003512360666378408678871922031777083603453178162551882940691372134344912509271410399675865894107668668918172830437948056856387541732806462852038169279341487082598962686756532228537086788159314146975818983163018849293542772727621271258658493690168156157119495294047013682792605784893032496282389238736350542312796983850195269101849500601830395665426095971237577156246889280079810746460353035953510070742009995156282519822166036487745211162677218015331853911621531496258578860563465605705920419404542407209805384686440053199171547501951667430606542472517461799333964175506162247851006212416617545676457052897952034370729230800273093351872300293389221927670311971636617590566830328034898169088117597036584075771980789979527196128639427237375501135067973483767511671904021001132234266725318358116706024602037597176762896390539552530388025011451170528729078156504436637049822146947180795433575187809382089416396556249459165497164609895519683922008258403731460604552203792213484120691841224799465075717757156330698762155109797533987285557141603460490721435281421680699233020590970040263329707346837273125940820661049633628762376497027943958082769760926820197631667977568000872136893791941310638175083390930952036531822172879188895069538134768080520724364507121459934136657452011313997382347374547161134672342356399141250600596874759654831566672564920326027897666384032539322261567233969247035075325321253189821267422012322620340143567820531628995964528874483598423055262016328955020699319423234388133124369015417761430714411809172448843238816367550816241296534843386998762491974573826423563045573616642976259540036004604026731823714357291031728094486533748604629057646583151199307514652875784024603731524014304357670950082127907649277813695974044602006170538910007329983102482932260661613716666657262473633659582782810235479735601805419341429867266613705015185825076207136041450382507966304804834004223631373035716000982228294967977789939893272631223129938225590224688433333331913294012838608534234967997428030550244021225090486371119684060955516426436094307051214711995992414172148991609585551564143681920248945562616613029964364429680607409134914519952053981578829552085569172731737867964884993943087234646773833569305090935385949732990091732507587765184142657288130628895493106606201385205649620860745302307827044498666889991006949432142931307644422041882374278191599361371497401791578240311084984407559287154207595463603138687064205589819730315407224202475912923838589413495754344424871892513171842311549067221229560597351327726688915733344798277541660421662019970703229445824414966406766392540112259180782480512597925427108051977906516976922238883535978932771468262841186543111661474233280339558498625478773693180222176730920485996629061827721980175716848133713125370473804484662253403786086044493272696537875008767752215729207298371297348814420676594265417296693343738405225038419950153354006211104043777199541086555427991751380642740943372221077218939929438769658795353554477293438960834507165827724877277027685669250409536624593675330245995183987193145339318987819994908810685947671861107308462437857131469059381777521109701009112034911553020737004866618570565938138480224955268772849107591418954892249951590746676442528932576788343627076328636613125665006002356123502082205341547441352576478640577345637221705436807622380936938604289494229063327680109155315178220289145421350833358273203210463203040060609672885358604190272687372970371482845083721087852370364274576815779981327317378164723839278894448691159811441522246377304791173940963526254720441841942449490275016071715539611732617225372345779376540438594915711677744642316918925509431847230352320301938236056422784757051144722167538408132899601949572277098269548955740066793937109746815334327277822430493661463862342409892642424014886427910492772860698204413582383476997470909924173056104371724991578400179070880491261601601795767316335170592734955775838348871419032072543306673031497000054086426774203605868895617192719340167059505293271474225691945304184338040975289546856324299620706726495697833599649568697134120869025293412983146761215085474786647517130179631634000183239717904557028512313913220500247840890924352318913585839993644820119791299889092070728841019492676704342188249697932036428581911871284272774292879022639807510474419087141000508320583335255678498007568541206405214616336427522966805559814342349201783808083150 (RTape.cons true 5 (RTape.cons false 6 (RTape.cons true 3 (RTape.cons false 17 (RTape.cons true 5 (RTape.cons false 9 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 15 (RTape.cons true 5 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 8 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 5 RTape.nil)))))))))))))))))))))))))
def st_4 : RTape := (RTape.cons true 4670544162206590055427276984015956032405324322743701909742583236614744500795877407428344192345850702236692612575130533203302293443207491592222409261742961441273398986040024130911541192427016154995310027634713798823280474848969835446025328038678942014728359345985090695558624609573511888469120910574679116960229534441645709374982392486568470950453935532816726414519813338504267505414101650444205606864885562237261087516485628138559695307262913645648794223860587582199113238718204481110057542745902426441324038926539510504894483514365945154466755585741076247079164638897551579635644876515057407114266984879556950533079746931583983707325675073428224868007890769635484976477735786688664104907976754624906429678550334345340538278450844687007424535658618026566865972642599714044578860513624276113633413028926734885556475458435852127785298149848643843268087625775529512210550949702279302380319252686715543912812547358277525707308944663551575200818343143820925731923228852713112693191626694338206476970073733442704005271196454283532152256638063598834458288549859636151323952245383142293720704212653646929765790793824113179066895633687119317713828118820239431526395833958343344864754056071012366542241626193993562724358639175502907441954343708629824934907015387239187799419280217875750883571367660364201711340428380789198346536795710441717390085708528910246196524419087806672819275292696512294153830503873292389266102683091107232521071115870887695167982806404235636241903196794128393660371940502958401787801309102880375252310685331097362099442650063070237526250176183377393017779214762473039864767491430837683028282148029438343978024981330041480946610371227037027711244634052508058884966079045972359298349348412221046173822221080509651087150502553758880764739708896909313581137602601876813733007642564325238983871668514509139512073954063524722760228725110307161067236350963354460641729473086699032804075605958573091231357986888264391102118411734394552279701607492793180847401158384085497664764617079437788298676889901549497401452890128009307593527874272612805218092852224155230302812665985121517878511747139837163317104495960242608233065334772172901564530649409781399759788179395216752326536819960325078632939743770024482314468738726458603314949530016226728797398621691028264029489024079224365537772089218000122670038690777339699805531987100642589424956956981329831419736447040953123184720053370458589551992608953416504342916065893578002313911669738005246030920435865487448901455176864933227721681282675376068960022889500059544798621136270369511614229887870881885639845000402948688130604172760889613482486959174043862190182732034409576579951691741688334648874180809064397068981323200739813326554685281198485472734689728655692647396468114901940277029507600925442392398025856782572777406461372844614186675982476758576471406961258885020047756192501916989406889963559287275241646078425822831980155834748471749156817930041820791929221721938951618363213328920380005305243170001879054971783182877065518365224173528143472844584203486147868073863427324285540538824304410979677630945711622432036786593810433932993303702033925205352106154258976998494486283042011418250748599877294813967035446508634999629333911697674573705273131157206230122804733852667828279526259631556892155032654416777662933191046990457693318204797676063119197491256703485791178836258721252411288420733054673815788915276275586534697303263455161092949881994568129494837400282342137003033468167596467127477805599419969985998108945706840364786671020678430221886264034817857866159806890333346464548528814182540314167326865287127304878346921635813118258599348818163832500372475373101675744926395069338250573817704617978953822222926383445795900341337490544822530561402851191171845766366017892774836169620004968916672540737744171537376650229282182104821352617208112359874009328843921302285956979171829237633426777966537956788829520821101266039619005377783171939277394735910777427688782373556042767910348851524983246005020051884785262679812546956465166427502754037580483961256774299240073159325622385910307482746468508134943468560276247972926562739093017342575234778335586287514343873129837182011094107669146412587167297036277673341859206712912449487721329835187551487537508933419132764049799562105051631334403498427608994946936831231698126532379078854289836490875575074656774746431801825402722723526819686931866989146925463248422905274784870378487210594707107572707332147717970457425856606539926017489417114289469514860038508073440769182305508216499152580612776679122950829142880554134439467740924739291558683977927992174716597289366696015794174333618125636971607342829217630503475155401882351596073113473098646411022002285302700174413783153049441548217214514676084011116811188941625368780335304843711781427855926746474523871920751136626667683073183234937918146333913629050784044467181500002160617993000558359406227260599719061542033556736417691174497374978869328035358722469552597013428923286165673921762756415297568796419797623103987402031529542282505438812571600719972144994009606312407570184071631538311760694119610865493879339367763402969590261502457245360896760262741568989214483455343661699612299315633337819076406404967854714639554970050140852714805930697580200440528761137000785379397481627163308333457453980534983601695395840022452276468611420044174511736544725102974101411478246906365063078318636834304730001369018865876796930408821111481324127984452752561762655814321719632141130584509983845843716572398023179824656323798154753826906030690379743564416354528273937661511685880991848084475389013421887673644077436876744812621599872277077882464341026164833179724297113778827240194450801561671146015744729321199492927924530049931931519599922787470253746763589016927920507383928168862722937895557203010484692318037164990610341897759401525033438563230267095074121878954405666553230446704298938291112422656618279062356455859387392555815981540640978703077911617940937132759346120030635983272005013517204110868625668794438903706507301903846130628850062265525206686505783418495625950245171006155136748778043812651486696581459664634434447719747698989126530731918443337531884100754649521450096530248013162276514173759559167127026120605670918906364070852653481789383046132966463597854080310044227777281897293620144990805706893287028007998432771517742861360500769224740655174017671686976861055526966673945094447426130463131926537549938131242743241557051280931345711424955237757496929526289240137239560882766391013650583965206736315006927956321826876753753834664561045869594516496371214410122920770909779195658308477789312857838257998928420445760255849823142962097384230938933954781847538542538710116210141578872232020956662334092589249763413554122854806517256571497795837436003783381920631345168192104868401522110626088589915914066387991367464785719532907386349317616146343128862915915789592558881108032618870146757430947079885384984771612864684366685649705931496777635708934724456729674023127442512982190059197991412139590495280468693140307047711713626591054961318339216327337212409159152496732788151960931202965912000731048955110054241557397473055590249215844360260860042572440483669764065420294981570025691569339874389161711100423295960768583504647195971049741694655806964314220689300611865653723733913776303636257041229866309751614830922804286385657143404641793680070716343468924176972964509221057695502401911963030965921060818799373546958764980159612363759578669635148054431467253119628024696551879696460837197618918746133294380984650346461647065125477511867435286827043539711019787625760697568489340153005791134780334146185101736912911120593513253272353150292701077250547378408954686308328046357158994607284832398669965992079589001301461180339049983812100517034275171272383109538797609565084801646724314144955512719884971870626804100875699426783234718602024198722567993027099547249318993551081362179086361167140452663465711076381840982619328994190290094054801913055713364077886406254371859212325962546700437932815322697896816312822589885626323964546331894652392234152111960183223558791812796503403866671363854454091696700156781293369832600933714744875179360769890074998086701189211714986938077570834941499713411328715027462428471066206640524910592670076298129009511135509629125980975634277453059708956437809394086739257311134180639390934757662529695238132993091054331777137976589266366411934140823042582407298582169674363678388113981856219994122966661277748036340620704287012608427459022757070107519764654161091637938481822575999233207395826339081498564713588339348844249891447340472677299954128124341463331976940082960318565673932641739248994500381626319291367122898005662466798590729991950698178932678962709448644833335966138759967126955051170577667649671439681274098504821712530368420501959736135952689465748664472958783737122817562961894039783006230139657046457884895121086741917073127745948850676574798921810075321559331697306731135021032058618678870748621013812017792043188624420452987355221884381744562232168054716452123907063150784134034601501908510576086156910590957519399552711184648843793800074459770900191658692539198269381628279494807815447751270455614421694602781812609863236965297822423435416580365290442399638520454230318092640123614081068233401013037454647651762527690936646332815330364573168720900276339232820469284300532272257879703651404593888099838109363675921551462545986004167588209829720451034025167619745444799080509474415400997774911252029666794760911643490728922 (RTape.cons false 2 (RTape.cons true 12 (RTape.cons false 2 (RTape.cons true 5 (RTape.cons false 9 (RTape.cons true 6 (RTape.cons false 12 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 15 (RTape.cons true 5 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 3 RTape.nil)))))))))))))))))))))))))
def st_5 : RTape := (RTape.cons true 1 (RTape.cons false 1022118049092391463710601509831703761350422023222199949173597924385778723008448312297693776963204178564418972991901142737923346316310746403122489318261650058183021397470426527000098257649705505008677372188624384040548321438746372783799837352839093029117740966287061937888538581106060735291029889474593862959601787902105318399875968924246773045715117536595887727499978556096876086060504838981779235082992737090653886947933075596239754673917312230313203531848269795492340607583001710549410643479047494179323650098096972264858059964064099404389904058217944999489737612622627742879681472541428117602849073737849858100872040488337926310118590950341612491600241019345753968836722798368380744195606660089175082536534152249117268229073845873933476630892176314591593642440268233743396714634206401526069130486966734334234008259606889811708285567440103330602529019869268078233173921470822561700816869175271541981553283738564887641581643626362589404614752658894299584892491652084516382044806728462699006478810474114506691884634692539872649264238678973387083052731514503349844511798943712789128675399225831795493254377793073709777893621707512211205947020114142639031989986488657209483954918645118689696436209341135607685053885721437363900927833704056528037096107089324783115690001453497278658552537342159752195105059239544986334611017253803121805651659919965026903434776057645756489443273615030393254205411682783182529650693202877910546152885426256777146321318990549652110401743191647339979378601387692831038297725246800174180730223521811287953807064401854721379897799001057754353628100001872934887635038314855452997017196590083411072354709085050110983932235381877578319645201428540225403015674695789370869467597911017105918194814285767097582059901807156342569654167734036635730035484142205934143719365421009809300137451793973593193997321304215125326817692805627301417554907162852342140340893656800942509785574269998476469182474959739817178291154206151785150202427654812114267370965303764243293616090176940761796945730794362953234218839999460383154020190884526096527068017368678923002084448726534153205338527044589114977262183652433862067941315249641490184698280874288792694880228688676887621317870120766226296624120082699851140700879608072849999603349859070359339024927394706023573158206002770107382631098087142629691072516935685859303445023776986513378390340849509064690922562193999479831625927983182616819818631715760049476213438790308626481048875854051545282695835879527631203006174185322150989579235252903962716495060883016600732284980936913316214090131487633442844742137712650541978924269115011007336964903648734865363140896141886983462892561684234977495747433219007710795312743076511706174650218619201758864815872300937446190368806614643604891374456687025969244924973065232795375760521744950925976341964301455081238299973561228199213543668395109941861298170839529478107853924895852325583558354412227687213614786987249403203072153539827358318858105550954795582302276493294309192622534948277681139417633553545990367087991476280825335355517704727838800355213682652494289576450750548768826359230152413263154353924835080782880485080897008903137906238795563994387999198976999199707424225089429888669200350980202034276533745131310141222843185090813809479829504046553320032722732625712578380723934103918447121759542775814448330380128408922858872366794332135391733036006488789656103486124288422670679802750290702496433073187128065922579149344318639547476053844076285329059016698520689339783996151919095833805850193786618446397727200502768871023662675508565771025779411337291363710337204451512587083838605027428870287623743446474999721893799007960552291926760309780126526292653208690750706666907055287980819982492178535377988767519395597344826233865631442890561208647918758527757237377024927730911692557183789112453301151770974238324828574276112773754954938278223088404892737141195621869738621293445712545920467860240205110217334705703894050179406856452976430591884958953110819064689035378484786071398223482206740382057681702852176990527456905293836522722811220352069195844624499404352205313443341252941156737624690241903686027520025324263180327572210766897696503405885222518138898397097516179575480836589146568971586823798412027877679607100580267507097437010096707242989819911505724981761071147750563332229493670706532443062119841245520745442435018570666743122793136273931460264337632434338077076943511103405874259081989722578096893561511263932921489599934225083930207485178944663359927379156090388135817781217240460971152178499852821797569598083746929992001321785559181207051881702538716646781007215377348873891901619341917924068293545514415733825443458276180820575353655781546585754878709739044548165343313710213012656576341305481320009126017453580107248556114618633081948153465469332389901033086278481670943249673056888721580648985556055418044390654780097201874766999845810079836778751305072321232054997177524808912825201872733054135786861311878784123787622043595855166919939008466640920370167433417551946761222795519267142120995725562201464739716337382996434383951663086681777454922568897405233916804592931698342278064166501819207058620671372918558880673553180358797486840063123361186548148976807469875318978894056474313699551297165810615069763643499610719812197863600445202754943296915160371248500736120114137260443754581492038438537696768952845776434518704938826613577927836844256132853013316182216712843172597386422042460186699638024146767228140399705209438832362334196964092379979116660356874769907666080293675554825880748059829258655293230958079709184553175163456023274079631079099532105503009983568229337636047524066103309767923378039992541035722642042224817802493079774236178478768991266659528522341662641103607020353469057591503946545347755825731671272038093926561446415663634245939294345828621187316416429888952397026796572432866197179492135432250474076441130206930644084363718849185868688348379316285386857835691125054792859922442844727013253943431937051876192301284777979451355307177402803837517306331781264817898255406048514115745888200471495597981288871144456198301316832992915819675515457163320515947367822400268386497517457751269265484891863599940167667442083733331929937659705653468117253829603859547100808416167925030155637562692799955269367437740078347998834062316660467757420817222634432555061386424130406831134738060464400585101563471194825647629511483586091710348430951532808491385931885679704979151356840924622077680270030187343678624906073527776205387831548855367751545215017454118602188927443813136538061957901303530002972671144535690005297657359848276828456251904114891828299804724068410297826874850486603449592639701036029977252308393043332147410441054728648840248427060187170507714373743127715908627009234891924302904189012271414547655930313552422814428271647113644957360304624670370568444151759483911977326453010371231071284166673778832240137737720452379002219498842292343850733313811324964500670127184203727803218641557634192841565425738880962989034443389053344846951287479886417695969701534267339151052796850043411815667639918493806967763340839312436844095880828539069298133969263332215475862180342710863695593003653531784100972477597183388389492663781867929417293163302909274444937759735293777089986064227381389939574656211943685012768428237039732763675759883452316727465404524710717030304496370486968281911500765672053710971553843569216337955543175197404466726160768685940843444895850497474962736765589447902455352609529708344586139952149345625122341694912762819103545474124328671539314333054758193346979705770456320225167975181406056322740343564259712084315325913275218218110371479272456373452318029534850955465121364705056692597645288744984777641103037303205411333142832480523523440358566130722547126346711999001156235411660493930195613244299113670496101260741521563511228111762793325967198664420463904421366751585146614158691103770309814082066539910803392814026512062333760642465286463947624029045468193266308229350339275999090875688065484560539132329220988818067292166040123967258744027680563701944662575403778585209377429165448747768033679611939395125335926456543951302955249281376334581327011403893771547688492530993127572765087142711925504232103459945270470905303753739517476367509908164541617850164045324581798792275921349054566955262129607198456181131809358668950495366898260690771891852641488297065264542924652084450687176382787784609339999112970295171913284183293133254407444721212316437689781333827036172213491828436580237637721137784861163780877001771644249940261810189410067231569538109707425017220230757143182499525651874237657296140561847174847267452088216046799677872743241606399000984792076877682851534238456936126770946970905784465708928788682858589023120739978141206404613924836375493896701044416020396417992806197121230321831973465605944399785331247530338608062316694534611414246318473964997460876560621736906613214818587010514694238674422003533647635993393559858327476634050359680328390874311588803596017594644572478991989087411500433419266480705577448413999783191401762126783694520865616944282975276249280637130065746483200650544435599603530257422690441761729864049295380930851587864341921033417742515614081317499694609311134674797789322017758665069939820494658152043418851475974774885558757462064513997817921540258311974603625187517218884810208541440310534960783624296362097344950708236917542815926590655047089107904915034061161795166646733168938142096584791119854843182346100928135956362448166974084146078068528425626683289532002486176817306070673820767498342351339878636806083945366343702322929241738787794023286120330769980126596902491079098865631387388541812742573890045971050683150340829013358600782133033885339388899941398734500353079727666898720809066855508196544063920484786121350154226822688946044551039302011400112720327930657149617645361428385706976774291152656432586967251625269989718777378492378636105571216676218670429686438384092501581323817901870724553733671736182312411360665285717461076190516704689483229142603044677813671129441509305138509022042909979225658031780676295003256929907885722429838909345245317737734268134708041318442160090242724083252595171148458943562657112716762317303893691181886220402086994898925700183719412982806103923864837501849818407873476530830728984156536141315838212964931330409242617408672120322299791817591443011709593644915762876570742376991485381115399571864931549989462241773846016414139294840435376872973797088473815832409731618605083478848858437169725992369677056152285057605914373224345938720991453528605204903879084797077550467861720285726962756774862404715828588472507785846925417098761950063498005305839200791411482074251282709339026655760920895014495152435631952835653523180413606679289152498754566239447693820800151577260732471383421508588513036770294984399714748626009924033880899251009968398129311828918668930975866972686645267231778068251915305129782426537983111945893283801446807887556076844919155266304828415485155180411082850925335952689742245329499242433334821609254362656732171846803393696430498687102069268416212879698224699131424765333459872016794425090596040535360786621643100907801194271536440726192499646499839901406334325477794757181540008096674486226325437913534636945640096049051318634645202682564101222984546096977282302252381396359307274082111594569814820805330103334582101894888723025785862248840037964789006780186942457266965034587736950673703459848368440029152653902216711724092572950204072283587822824225229568543523038359291919655974817697205621842474891171128037403225882830565016861490135990283888997626798051722142827573129016170782532032782206187829842855952509380208396819553243903294300909278939401822001922345213771349295314330357094568067008599489241029375889458019723328082622660456204322448547580378798917933509307873044260397656877953783598079810488737086 (RTape.cons true 15 (RTape.cons false 7 (RTape.cons true 5 (RTape.cons false 27 (RTape.cons true 5 (RTape.cons false 2 (RTape.cons true 4 (RTape.cons false 15 (RTape.cons true 6 (RTape.cons false 3 (RTape.cons true 6 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 15 (RTape.cons true 10 (RTape.cons false 2 (RTape.cons true 5 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 2 (RTape.cons true 3 RTape.nil)))))))))))))))))))))))))
def st_6 : RTape := (RTape.cons true 1 (RTape.cons false 19637539765207783451446490488320436861016437924279911546808424086738153059960181660166994567612476255590288438388125952157177573901064126758479719306484326070875352665003855000796217126864213487916272418485174981514678201049113457962430444420951222431974927473620315631920344054543279102697858803040600222755351185322485334406546009325903138302944324783577301296403187660073055643206648814731940462960114996337352610704302299866677416985188072626612574455569816075726769710303111075821583926581717077724989790860910185227346636552362823519396704681355640283872486202605821423470013437471864141469273298404531460924316448434159048445145374848904545562981510083508894725245203064989034480932933913772673404576229828509657491352466164603259891795644148730031260611876856848500320019313829762731717688249857230230143743060952579989232712351227389135139515831055721658035068437248261956137083142396859892258575242783020291764202151986553332621195192817676458543038536014338085058568483493543067671388095841500894698173541638388706417293416674156264009307256733072245364555495371215838296309178634820123869168130897805007844475085024954109677284741806956846170958401125920299936186479407759001266588275412885308352282516865203929266213183321681153955124265083961530845792504949984082851296307815859730247297950572017626406804170746600217712970276425111372065839267534049319257962519714838676890012457900413908514572613601041154408127294247302056476243141497295173222564659333731539082368679355708910847503403189495385374972050606138505743896743594004228328152709234047502434342581384968020267252134975071565054318826880324483200759951902875837279688362377605288997120915573219281398214626909859971669412359459176230060701181670908153161880059782529934066975024666501795224225470383189384672796863354784163293547215324824813573623292093067338090645953801174956173027976712012724194327048691239264861086354339874461784647427595820044288993451435715641349163311733463251567182678936150803096601385987558735805641137186192695063428135791516119437634679195401971211108164712726581955505390662693596733032037707326256188096271685304968848540491749737763884496111554549751818269064166009734531043648708068231981268911183355698396985769443799316970009248430151933808335428572548403205568016403967829665402046535769184698495509710526246941940694001327886982351616935767131974295156060363878104302444878361107515618442562405311060991718850393775553069769216488743117105684271979944733894283248446837267169050773474453563903230621934373615158788291592124269251524590840148827350125760299944307211735864544644371499759536802349963389280193209877567318026883391812300057536356339003012597517441905178949285337533836252912969785381264632798128622321726863417360573946870901108598730433572295289657133974570895911657891008945927615999962293505852589016115682895228058113144549324583308746363361127517918604407123359618259425274113266678856757083999757300368796658297987043866908086678352699400836088765486138729789535219283401543548336619998609519808149416117735025058898844872070997005102235541866369566081936231402424075301573231253313115325453293751855613347699893539267383272757536895697558158966330969599449659788210156733640405724245572921777009578821074144458310726150528913156271174336773905914218393134348351118322637267991422192813233045200241928066732841550709433472816842766839102253772838330376350619940168858200044833272210003707539209625448687834796584495001012234872213302754204506157356829801825451183640202333997576807864059304834749564516034108336917539767730962973371348488853806574820196124319713849023902781819291434279231223761092492641761321137549613056792756047936635868493566162828450341892287629954366873025655346087398945060334850343457496002963826344423446859379289169024311259085939146124019887525113151357154106540071156604924234773153572481526898695334679191320608868461253833916182435904838645519862324867238352570895505151909369114902706143977433553255544016955641047899885111126245151810990024815157820125723916034737680513713782187723993858524984598056472097865161654623403863514434925942172963944122389229292734692638378797501146594118799470029148763467381318383442862732652817804888181040237378093873776071097051367876052244336965885655801850286418057659787605993740802851486250933794822116058144397690532622794332798350745099724126165474135284051748502948270264781193400776200534139962198946332116613058673500005359295253632760129986787349287803429402177673761582483008879570785787318970919070033408163672642470350408036398055370528780289085817368666082227655519557026318678260839669508560815178031130515753310801476417055844293322607693683626116885054717729515805254961384625867659586199460975938388164373016542180876607680301367158841735816467528934070815972551741769664716359761211634749451177857794459072515730024727965330188271738906169556555645863013579312965257261386014730292959139790135131635614129212010833729804821821051383854428394863777126409817917945122248505880573914498859592995194093185350999149342763359988189705497643480532213022906980856290810516165763078172325636486552454788404855862304235645259071026582015280987514901601250535084970015691468445630674510940586915228462052689195531902422685131211463279912176616292184215958473667761804275292365532852266398640724969249094826198611598195512289106369734127709349444276495579511235267660388039282135348542504558018441775678164618230634992549780947544720256312709039049413239675110920253427814179870899006872135304196924112645341467180874929433005930556030397884153191618443126513515786217713073673902904004343740123949843714131571236698675075570025887170231511573437943154681728910189364229610983859834327177488055821965450600211902975845795675439192202320399655511835619679845055738454711133839568700249457609047380011115584328401973359015741546363980031724423458740949024826250934880835807143855718477940484760154200851798952627107514470070018168463573126999723616438651607678957645442979623963246640856227160666154508797801771062623311845722336634709453961660357816811328200594626449312239015199117580442322162138213276405845283921111723418276382300245835446143264849640197797623639656479062991052883695101184416238851036263608481873068626831551396977555786392543407673628287331641673591319176234230333417008431107653552672263397595098137588032928505226818268781600595141322440568247028247168139451765729469069369723977506183221747732562768500212128077066459770452238830863323796911639252248183070993280839262746275928421056239983120338826688665028687114536318588394833483078102394192077456338778033405974666495438610692752137039264390414621139599826507180042016390757047962626022217704753566836990614191450356730999017424069147630996373011578840798939539842557760468970495175846951383669137160030541772462215497646992385331502803030529106362266826874599110988017852446810606959489732521186163645865450600600549927407026388349214778585235585280297115880160936585800168813885567120935363418164946050248094885888582274159335261938117783677242727337936097605939566114235176523210517807482896576470030309678369609059873019907738599633919574822444565055386912629770827807479719627704156898711944506324808869492128772891027326645134204881883537613599693455328603287392807691056856308425797674834637238351716421412299060254599923518668945823296794400532367650902072364100813787904490177020832297819904231236649507317822880579812514651391155728409771742258518702827784657724100770635744871713982487178140260382831810418972592309813223821743818241501891805450248784025917361290951760005554260213441376126282830204141400620958546655165994701459274992630898643039892321639548741419391360180692215984938012404549044702340206809435934281131482406271084759424461764428809389345647935107803522088094901630459723077276824829579583757192371139966212686613103436547999581575930057597815891681540193074833489254224588550454228795137787428729633403370839997999466218943740816019404448762239252070307217579306144957297926958727229362022874027356514530693800295397568722386523519093240948871705749471431206263554975292382016951762575712264637929428712982375565168288307107779315806379949102750865918096559675962162024340483889705238599010345515377432997851481660848716878419565371737074158252903065228694731896877497629494169416110182452021486187077767457020216065358216920327663610627891090732777103118353775818465376963469928587865551825794806169655352523432882387851730112928427539570766649741577253061497143762537848972926302978987242008851300160826634676080858442497866512275475323810554228847937028265629657526058351950498950172633444352221830176920133311515792271676425873351794271721085662904749523748389083880939246263733467963455467949144002289298260393532104016133438176950526934129512563583537760517693973911136807003283373575334069858989822986830959296477502289156142354033061275443547342754728596906568276561585618896431704793589943256842203608341974467168155479840660766152579338015716460367792967553654186124269370662929560986481615673630207052113152355854033129502122847687536050418685622527562293904608673596317734840235049737065179975583782113982887421012820375035607334935683672600629064889508869020800712635918833641832128411273111550171703310397036070124828613192297495288057875372088828189558362608788118074461560591726425679049963649735997286879012787349275524653649926483782841595408280075035980289297147769770391965987118468681827943007182092860778477941342876155224631418327233379803973838575356222772762804353769001889489889753528242602091473826856869123276226164007254953218107035183959274334788856272796240754129575699191839377609121277517500986825161203490068899414895893534088873701382797678889337358417245410189821798581969897778135802959499820415713101616743166260705163390111495647876970967656593531867965438731348634409723796523033436821814566313527648294864724732775885234999062854072868426657774230358154503712432034742983816698212080262987373023199961374236500460900260536159135367037174668401213557428283698567831085607553173629291601259666101518761308594374202034944766379595696250409773154690135857408895896567500918373986332399012076761567812881407862641220677653375924599409144340823635920753356629497864461367092695407413679231529096787444616975503486301476590746307235931730596977469067102179965817574712116660365369482887030545080955068175549537382282769149770878937130718700546288792245672021594829086554718478303191660334403152330797366590641933806403605206150353491236427447461030641289923339279367118384109977835707992237199874247878292314079347811130705819667771766838001185866879790904911085217567725720651244019927488313371261095575403218204067086110996580367125536005374226621453409897721124674604225648490829945981229077794478579875265316651999089693249615350291580599274491749397521794621560252065118875343550366714520583269318726744439921146178843582700517877199929492330752995416964097987454628018326143388288308802090818043848694958953260093881194627572302796124237800240484906661969287913233732837657862573648789427359319266346422148411571611637689609968052638365901563441613931626085810611263500347379711414400966973854188869748625567949102675264296974232405064682561243839895249631434288473730106010533328057370610832971992075692327654347246740661890619571775394313737390576024890996225284466269026516113687562276170575611035798373329932288571521625902375225232246626915703872346436326357495562302004700102832984975027429089919749620761207801026608435784332902130424793681951863840209904490419231216077272309085365418358566980523774834568419131299487701780915513692222259421274292524348519141376922990230457337078262439152979564681469905243856656104511955826777736281349206695814777888774873199724240142821825055161685890455307200837333760517578214522629481435933822417771321506818171412584548404630612473902078753734914016318485278145292673457437367816594146220051306290385366657292686298502543417217288577534714055357226589326462919345979746278113112498767568593572899108277257506952033347012092306444842876082543150966562402988173220869551376047959580737300409174077953647453533157364423685900004037045322591904064582411562931719232851616446145247204961538501562021931537927330317279032887765348114416443274208888017352360597694290878071006907933964719251016886511881300351653509204011696901240926964828790061860663856318347023518265689590831801581619158419625703160545130040634301881620262441646809223497104316508856577814692055444485766331374447260037376335099216001052673802011334224819368250874761881857907141615493774706754173362701698395761765388205849528806439608012673921210836149798896266626695075443773089487288523356568984401827053676501501982971523536152280472593823431617208154599166742674495250860475378846463152168842916520945943993750119819925273203069837767286865820240125299180785479210496130513243201781324484146261139606349758272315950438742855981605149913574073580715271969772686122063024420386377067530444719209592090516054751807065699448926975093755344696305082343123677762137159474151535705508691358615340731676357531341486025289758179980815227985274682512878452490814990979932641058762831519353291545532967130148719049605956979868266533851819711765058689948961581329585343367937192070429695792903030004476589834455509689272060066519992942540145468702938421229100219008539564518313933381464242207425893081868736606571367153345410904929667343984839841305613809540750409545665928228680370600864054075455543274362748761225440987802955896477315538835182346545793758717394891274816947240388083461671636109245146002282541022740666020997099939882188566499321570647133405463694368873058375225795522833874122279677444488098187217946759062783789350770545403822518610459133100546225072227551973501196457203338118379759794447403219874824603990238580411089247945968591041874404197453259880847853443638875353586383465586165741202335348168837803336674728775785921543440732387954398774707643230872052027435248048587194455571455805641559147905997155152912885072997773626182703019108955975745719785925667716991553565809729407768159478106990678589142737946810599445410348198237523377668411019547362086860 (RTape.cons true 35 (RTape.cons false 2 (RTape.cons true 2 (RTape.cons false 43 (RTape.cons true 18 (RTape.cons false 2 (RTape.cons true 2 (RTape.cons false 22 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 3 RTape.nil)))))))))))))))))))))))))
def st_7 : RTape := (RTape.cons true 18477836993901974680627662260541480290816276984268865645453776283606601666829254862494123422065037614635581511407902023231452028015451399538904700593705473656806485035245336656165785571743892537176986185600651014798782666690031325135863969334570494260409870666824300063168618024043553329430991028567711094428637296490325078040827570895384263324759198780301979171009751460720413404524145173437886678243805483221655320459282897224394005467980961227751021527317628922017466090821958234907397323328411264294915306872874767417848035987887091222566715682237349828900469817368514581008568436318695672743054022861602505729288278845167817257242096753300157300235194720339051533262639016998699396583530878581340159552602968731651334738533871273774024360281416631564204965069873619212555475173531458732764367026616317416216339331366324362687283618633239474329849937119917770777533133721942413568925906602760378670567193395337467807871167113176478157808486275914360774083075415785472721532408722995043226597106032467240328713510830242834203023238606670833265775868190985388329154702259534839002906499496628516937457728245741513905692411169782321447349717872141267054604014479033356184625117205300086697913788309925341922692753756046081191825711603442311818196967192932747715642493684831674133322787558570689868250256754286571616253787544674121251608881317930795841913542411802320413099957606512967693253391476419559735603213578695675507002417413195152453235395189887976767198181183036683131484348819386876967363325830822413577629934613665756625387681980692359845876886526723380316667813435705692693773798956855717006436995317782932003093114955232264918450575064420614239209112218391393930562109379762307946464426655228972066758545076014997680104360767655032383242588522936178369794619327107520072463329775318395083558018139312223107625539889648296199814259603887808833837176672101722224492446629853906639838453069286388942452022687359202246367909988863401300787904912635174488656753226000951546521648083877851146288317198142752516441778815205638343015452257261070447208199730320929480579554835994447904205305087819480794090682936178559262797026649521178108853468330005823290076938423284880780593349402900844027165114429596004767580186821303072263697117100841023562030523687018767046954577675218843632279066135629201001567045069520516825175463644634582493435384160313701461742011952841829744968558461174646074585631494594754582131087945489028935319095650006595228214036393332333300018312673620854774557030974468228310456828063478565648458587842876864441037407258407680881032811092893475816423201586745516705624995691370771509821071229678783262312824750669062462378911425897459406835352661238052481367228718368364088905631401017424817692306424971475390183328692331194016703746318031617540076249330962647107349352453348038184159926994428285275043154517827284265852116844679208495690428817717408171248749802986514513475932078193233963157486654469374465481911052252057610469689363311442282572582642065554382796396026852524748486439138817494123336031853230998589013278180114079074020339704618975478783632036365144802042501655555722131656397894069229694337703916950090634548053232250512497179137829673583630363049392578154668930532647693956564393927104410494006338229790294783979216860467235214182564278265669294364384508404831079274392467869134727315746588369542092482188856504055746750175105920153687600837278003664323266355252124965899874399746236545897392963360257985000739151082755048686807877426218969189596435176741069953678357678297442492218874324082047185093733236867525036255153057869449560088966127577919517899280200970885971428726390460060484316665113996954543301266263252345925600061880081261574096635863493197116115228065994553978194777381089800110295706131071562696355630520859126593595291857137094655973930753465043585628783685490293418196824316630546730400993541706103102387656831514576272587194736604218348698839559108674044391799439902044003424495764541824038140578705279575087262402799019251211295648924436278294110737004192567322600540244333507828182407383659852470935467032545815240802790057625510213537937500409759049106948174232546283139231773116222281251659003788928882323554063041571758537997812541137254454826761908528778139796770492783064831434247690058517489495202116035465157623419378046290926153610110017024855756807155701788921171560176045359819182858004762938448386924764038172184361047281601792396517091360999963083214638321873894258178163566871859084268715029259257496230404762745205157777109376652792885392407194289397913069509100875646853773361183505043063102610128813303344606268522967390938128383150274735677522557237621082654565068912703598268342029950827124982238760649977569399461474119247544357812152719165115055855337406271224564999415496713924396006061746828895213434053377153776904070778434965614312295269336741409046741594342905274462091312526982441253236048742115979112079992498926292233984400701265640945483424041090205054125158474488713137558911377523251948068816006488237429265153520201866701783698376397870593070644768353012784761978228054379372092153364161852441839094744413687992909451327214715369512858639537887065997308047935039254820199692857944421852386710829470925128143753924847750707660581609713020106476077389843952836636923713032713689629805607368420416183304903194971234230569872925311979985319687577229391677940833816074468250212613666504901900498049038966039025961420855128963744169715401352806474891317428293006088102421661477206561358908560069651119630666573667691544080496794900563120968678763573176469901782882094294601860481394634921881777697098455780852421353588179500287697690421173789083767559048843826857105861017218511852505263045003605505643336817849290668269027839224609114887683371446564228695011447496396000772284828862336231808823529196330449227877939379409994571968723733759215879526969641057101127484569408942365223226104228820995450711956628889690871933546043632646705028430634490019633724477733269331825431520588091121112415198139085473694889007909649288030719446508534753990264563129939926251612920156415113667397906257439971254404042771297215863180091549127141669737656876085293946306144922728280371173024966818830798924524611215383014003349851513592210432934124762715898771835854810990337389115730307985416934561544628289248911614723401571749169006821603742140445219336361307593234700784204581674795444322052918477940954604964679005553059457800306183343646013556595173644605497630807659034890109684451048200465652661032385754544628832212871848750276010694209777108800284830403420779534555414284858381589461925653971586674846303025393783205204328169246751473068257400308410433098069069155102386588578059161333696894163539505246063090364441240395936246872304163414260536524940336050398900447311808299216969908754359363182681397060017809920060123531765437567861800113755619300531741297476504669751383958885049710682422200831179748736614760784420528499739835138323831132095358265831905996235860987368627485696479537583724868911913382389695005937273629997579132676699329158510429244670235264596348016666323511148708130722349009061751610148203612418787105709712268281474400099031775798901683142585292873233603451133280744093271775692792807421349775167795325746046973270470538110696384581233898666145689498205437629260713963139117716879912557544657223278629560913550793185509194410527697600547334716594463663773927252023987897652109474381543216821503789121388344847753595914974431660834164500400140013108262307052390662311285886559916202684243678592692387883238011834913409082256209361782774403806612798036623012439328047176037001711243429107932930992109345199542442945144275677796603174655012540256737884992042011356874271818063302396286174514028109128632687573082531827542729173557610656966944232676265888911837074652178200499655281993890263000079808608476136280093537876164926802121916906174030472670860839112408245820406060448517142810733706514234435561885255936881471807010710670198355086193326454287144011247062875228398373995982227453448246390442628006685306084721254205225598887319726647306224582018410591276719152153275437082104471114694807885098999244230334845403378226586000546748748901558519126705196982431593307435570411585611469330414182975883164651386683746457684227949323625888785848908946968090047822301997927160904088651434258974189120640849838426973495594942406809160847603707495104742130634573302377386752961352886241314666501135217135180972207388587802548938634269129482341942157680088801312654694005388572349188798040005714311512539659652419214468600375624978431681933257346571594690785965336097708652223812171017097455587806156003159233530236064989105226541562366912868438208229368551375103432730993508485879187104994287965100172755168528985706838295520159248447951956684300228792908895807214582713150575721253739624691177530203362092464819449252473245143851491279946030854883388395253056919377868661469626437727281909167924725883321012514654369320918598252394037691349131789945437803621728755018540567875730403873982288230130342162630988953218107333501355213380414564599162211686022650595463986161188778102523033123884316374486896047001366019413473104305754912116205073318277870458330344498531089106532756334028182180037461821750887576940607233227977100903552595850925529767155273023679222904040407587748985956298929067452386724761200916582209322000625118074542878626980865748874569312073157082840907335759858238425847266296493108110905410781334283224224378171621962257172704810967201058506500250326596552999398109139870497523980969702739863333795491451863070549307585673976538454820050688251809153353777279701032426342647080562873662514871270935157903937469894513998018547055247918625267758112033062883637495189681405968002273459844107366922404262256768914250890365094058939182014472654350793563544156842255488284836809433255351036109593168860530358696213888519695761321599026380024833261633960365604922215190892777673698273130626675041360773216890865978580886396542309660425087939991828975463694210362543598074835944845069270772693029060369995112940724497337415809276686207863838061769052425129381945337978833244633783922695938641928964769673241708685547465847902705027188053739099794123094129250745211164701732788024032357744446760390485374851270332174969165582979769447271361676652659058569132165234295168245463567205892405188931685170303299414722288257126211474338265203740674648763027582180362005296136855100496065365214490557233178139691835636304387549787468963604326274033159429167730997136896067026281856868637753587946241380507794800894511168926368862064261180976941944692415009371166752248178755983079064717533492622642861582280409701193551818006235756645123640065020348767636017186170230264076119555809987152965022271414301582870440419160563477908331239517411039692218698816207590339613179880206068042269794766605430705260393769898866810540356371748434508702154900244674352592969287823952231894796740682352529106583440183247081514968253408620599721347781047937524832042477264913683168369539485605909906394341537495182223879285194479981007648706627294238249185252590910833065342680334572423580892298327844396304927841010179877925597227893672775892630585454829880002021309878199068077479932422207113969746266413473008106254240369283235384597136714241451325649705607153831149796526331416262629266513933754670703344639726431096653485103302349577409377758790049182253661530925657741003062200528836653339107975379390102208528893376239352457240324172704510528326352447557196661155293347188012076635224397760746493978319346517868565001392677922538231269716076996100168038935278296605798879637400521138073273681710238948674700788114697152359857645464009219802139343713024212148538170045428597931426674697595833043645856420025695121888890237489412355133782517012889363993486313357870743213859887326866464663453525816593007885829047760566518620731985057266211184308404127835167742596339816640206323221087856241003686740095706500060763307202804316679098024311988481172264970479681557066717739948079350532737035458017719740101931215640136380765007014566776566678936063082012397717754912696631567838722551647037178846603637747684087925992052436605467339589048976767814786598348674263009082364096238748767570178663316036275823350332750793837660360086779692869702595977959700094612587510580709680841918759046015651745039005422653688014958977663503866215417967268531545119293307388271837088633243123039171314592809860233617714580625627929794831115019679564733797156881689521069007943846511723203715637401475341942694164702053189622637543285112878184896223124495230505968384000909214434869411185567662686548302039196030500135704662261091697871194146659376520252632625291742737595569273396288633405428144770716118776717909276641738806006243132958530521719148904253987696834605081564912324313973783838855410334455846031874267193710614825441800892343386535214384979458740338169620843095690863915181979250831069251164266747181594338377356911229907335079553554419248730412871510322772419240959877599788029229250661063187531557568120764447389620516678748468302168343810346002199416492476963245158977078403796498331462467276116532277820341363345597405889341457753846110344000592827119929551963437926067996481442029312844334258563421170480693511882236672269160483760447876265737997940131830566083163045084829382728631998448022357458512522347050058656914771719873640770024609312963576122361228656292129878251710008163553077540119140430560259345069826831540625140429603464630613783567787961457645736491161493756952377914525332143605301610531573181255596656749456121863985026686989556888253332109030811889712468066817253989406856709038055444608593905277324561058660060707364024733433461570097082283402360400101843996815920451047384006064654809905946759674217980974283675240755535881536580121853656139028439629355593107697863211626464059515534183357971187402293396466437663891086467925749907751263821095243219924018024581678624191566378725425459217084766227389982249657449827233218612937316280048158247740977980411346627943690140104869128099334810936221642515535733125187554998532891414688667995657648134882749007997201040980628728159108801296279790432212783833283817557307953426925762490442528124007535271046653225946327090834684115091576616465292040303380449969952602486087469978447476635506469008318276993807353861181356779283286554318068895492779435832965500752716365165659080074705482414588524985919843509547170333133176304856604853359640937701444918953715366443175041858513642170383563277351718035516162793794503214310783230002009003796667203416801753140486820686530868514939137069125168622042798672729710581978569923916963651313282715527773573197308928619524154083215071252111547263719915105466880530659436999132874103517694522646867401716881804672277369171705743824065035494664714046964664305587066998556244386561279079240771038400112270558153545466721139878994220402181481621104899078867248580578123754091499868169178218821897530290413410310172043743779130841282644999072500974608709691250710295416695389329629697372042653352864203514873524450200180515534794087518870570248256686285059629498948048446208055041139868183852199990789338306498439518173713443774661406972936400342981417219447798822535026618964101528569364201567495206156940665024458187873313569228080835894348425969471748711127673553515042979754879502028683936963657211330016974466496055152927035019917959372989478528889470876057787575759028697075742063307719374603135438548583650513860668849316812836050131720172525336711916934862065505866581812860029917244789414290063489817520946006141293326279634227904462333993465203756756888025415960517096298431401066821023656901291763339432536040434023654933173880014096545052881480926750658791063192664842060093691096236429088174709065730421617614025013634435878499126595978719364840203022595525428031114739472266397429354234245323534552984760282762598922220804725192605253443541880010032680058170116020216998383811579046912112183877281870079182400205932455919403373353607336769740033635799923458464362658229348053835208066342205359972212733221279079642581581522114427814499779575608530658418649356631906824244368606441176721433162413256093852842094290255860203580837039432828298903794931620002366478154366038775903654644535406552270244451338100883534364539985914421049987398092649864686115629488751867513942086739452194594756016196434884181577530180930883610560617515984256397102839032820397806793419431053850668749880550474374434532041391538555844342072728799691842999335616056875630963790892820521577946349288277644064534952093456878724833531700594 (RTape.cons false 2 (RTape.cons true 7 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 5 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 25 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 6 (RTape.cons false 14 (RTape.cons true 10 (RTape.cons false 2 (RTape.cons true 5 (RTape.cons false 17 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 2 (RTape.cons false 5 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 6 RTape.nil)))))))))))))))))))))))))
def st_8 : RTape := (RTape.cons true 1 (RTape.cons false 334535928885317273852364375031626099303433316083566645109793572731065219395407023823441761514930348591107885700005791310292533435004198086581945091672172052256331279485786955574979450328432929661752155164506433163246910910790693585117074472555912403155211500780916053013106589361715591407320871736788502713612385605683236559117267305058990266255324519028033855544216417873163399402624128331335483072061237365378511586474732261030781412027833236328740197158903194110157232433195688927017221414247719101925553602193206443548599095652659501255841563220236742122526270471364091694340600393855903537994780604857802740100114973305567728636076772483259795290408237990950579558087991146551959345254902225134497678333813225630660974449058415287911614332800632944059292835345816427985686777691134935509034176251903015228399009527454164399333750721136822152927696162974426653789279836163674869684610932175889289864469070923910268814253343268370663363669799447742364897281271498429770873654498539964720707969593822360157358744675846799102967260088991629674059105580240049625080490720972475062483359640853520896343997767823097555263844975527206466308601430981922117225805049870941714762875371417597818922488082333412875971303509209581250024356338383828739533019759319606810635666833334546535894898306946194306875155371862278202682315123990095049443693915552551843329326741423280121623092690044777192071676008502247826198603284876947194473473837140031560157607193654976970124035469241091590503167995354883332438992259512766072632676270273092364086074065571215353124216377841678798112848626671032550951229329003029359132070011211713047577332056181778794261533003610429579044947926199518235685053600179758485060199300378488310183017281451588396486330351187990421259909378725144985315689874696176196146002666000021050097733822031029771522447013052160018232892947555273207678566348066476508879742511138645834127400428512069907761711113150573378972665468561164996733094026686259822335446756872307314615910242579610431013862079930793934867419111446581391739545840523647594596331023602321229554659066338444946579695767873048016309021304342981098618900849325220343337243067054032126981881102981333830561176583438336324396714582192078783191161407861846928359140455452992587661881488998924614875681327358936369295568976230997199825347580844113419249492487750024492778373779136712476389256953239168344255611800265019181246772223690016942840783099211651996331533204878680327209635514605860346592668486408973098429329688702672663466837339363251599463332649706789896919426207264526518018678474348760635695128750292904670379589650009401098265218188014699860397935749160920552019753365449165776613885431630699717832257225447840720352643656813720595942375988133105120843906936298743126552808624838664281479083022352472096517129087099101392492689495985245933744695822705663243819689829534586335798187984804465778191592916865429540592736609283526005359937212306778599661001237975924256962082407179244738435953159396716838932951405173764218692126556013448916645968395208963015619660240805602085617109867918740821445889689620690383570733220416490873746299217607734931898684936456226168019311100305135844091354580873204775226638277962055019886956287727934888906399186054835011590562983905992642721632870200442664745835738686016202116440450403499724324264119546937357147123338912215285373538252078743645352667335700544233939387723398571413073412355263046226074637054392034997512903706627349120089859423224727515712089278184745571170609252170892956994680660539412169290222924644389973164495781528191209337926456652628214858585617487519432324418228680762850681360967906986267859606963899707639299639809146046912723912742731596648387071365779698926531361113798707650184714221107325001117523733510086507586392910078565288176383220089981476206774733863178646231702091153102416381704439942747494675135163607140033860844414202611939979951158620494018564357246948542384112905425048854105255711024556307309952505550057325192769455122606976319721049464121370135580823874014134579122805852688538911494588479087981334940091406472670156555552164720998594954898723773855542855457479013279554165897772800364439392654993991917019412851001217681660724763230766818400822083162974791036683350183440080289257270900830639591121430459183340660411434054031555545828854447370545026339026946579512999703828807294910050855948367652645970894424767611102868130596814414696687640016614479412093047825313513647569757385100502456516133644987062098798914525328604046649845619624873458419730658318396026198565352624003294803216450355276432500564000155120564841008669563516630077560729130552165175807445493510188669847077273927239182389897337513990340352632583579164650798662018816685939772780520989230238214696932437712175217440061829583180449851313709129783128042315684533205273545544056151259674273756624147591159874539988798863806608196698031867684765590966862786875962975687302810590038631284400989128789019929361058799435743654309403806484976878491774761116251286065567679555412272355914821500434597773519909607579403243469462125511803497340994995563736240425634163959839626806791586504669231360629979697071461529114836770289293792064947482086336644807081104799661357625053525778922652984142748953365861018756168498202781935999776448802636869238680499133766785300630580503087910034118822762412295170769420223736057656576053557490278005562097021356375360018341237532730856555838437266855123583491552416356465423186366480120209038669717071613285120200144144936356157124446861164246814474575616266691061167111016386526474327038383312429013554972854809599933024332182108748811700026249837632784932809949068848322379206059510275431087886762748308953977083909447793549726469482781117944494577927675675427348111668086407469550453968286796783960683457670974888684594737227637423424588748019627127799949001826405373800561967341724254890054477876653432694233792188389886070468427686357630651782735224422155886484316719871388389826468775431420920093327623794171326509338903921026687644160473866164764031337516199654575525747041410869117530362649716541042201430686475507300186295883528537411807355951244418050820441838095849301626515866220731171708190378052353068055002392461052445153868849102633236265052616368492771386321138594190156311137611382693846338864792617788896794087104695437030805210777314644999674367767184528180576888479703286127649673746951663303305539233245889754299262623948160058735309101429917569960293331874437230117036907244083819189863383922266576986775990947990434344160258906618938020890362685800609852970576461266477463039967486144004969740505139971474053638228261308706714027317806782396004113246423910334023160443158936083152437776798422086541563753597596913638429483313957365580052022851450759016609853829879416547792484838392586767018089115821319958873245403194948200312131576643654814979333773994712071232113561759381795025863895040799442876859190024185503339425661445848055716416961422441626323001040493490582159966761686810822044615851744907102068731751075895967260001620664733335830405038796794747548487717906420930041838132185638071862427429047485051787152806269394291795450458647306749980313664549475443504497534079291124231439235121205916860600471727744556137705104569785327830433699351660437972783842210712092478072073715113567661657955354380581953187589318036156304557427851903313168341168052608127013156440066143051657690401670431252935990365853355072861156393349074339098656568431297695662676152396938186692915775346935611847561476337318719929661561541515544655874469385396128238684431823346615715475888714990834199742344707740933101272855614539054538789219819783755807664588826471642527148174551524616285452141544884158517588134284482454594510356274824231134249016346263068510283068140092914447696765319307110571114840566241384289626035935252747200285933663946237970176692421404256073445821320269937236429498762846595879413741201233740477239107063299837772773330711794381072693819560282468741645751157793156058198759042705191167111443382616452582081732142650754362718301361703664031161310713429576324800945641309897728388881827030324195900754827018170452628873123884875148367180976034288712046364636292941935764377722904033231949965756657460846180566872161246878585829699309980188399798308463349612397173045695777264079050580433703717076157960436260145943608986030344365781395383014984316726467126598703412002763572344861344744141560734423154592514562356210382789302296236844675670852130843205341400502586229108435727161485293914553766124707167965991646811527527140853094057536239749928921172884192907423978945473069497379108076940264476571555695298026820342433559324598639235766269365487759970553650250128137915564792166881970519736037326794154862753772410349657284658663537816031209345520275311983647791463760379563305275886630600295309192117712828852904677040557970259839531339907987923936968545732417291653511461048701201090475178971619532423365009326478454213459826794841770663733777582209533227528649144249847940743947105317657451831190509158030585453762152854455539494912185868349133259607636139256781651237430171528078945247971807395019763362879563130049052256341633557493617149644683193661156203883009151028545742567190021293131497152743845610289546332161937555430871140228005969723858194842533606728370284055139271343707726061825557344189856462788185701276271690980761785523917307141930636501415044665278040764442930105133861040792653509870134625049044019122221888027826440048646142178541531314438044079248498878938932274308248641243013293804745083550247297135391402095652580391688229532130927136893165929490120659947332974869822268764002920265589364416350908340695468486340361280148977915129365034860004533352870919798636785602870286685188708618607711569429034674060225922114822708174524388194519694623520787995658534212930078180281856966294905857432623216106617294968183061819021124871077993428943163603070586946688060625071715338902859463322466170923569783125611538781011934515612076955102041077007001116360338437851614132867295461463120061693228820869817597046937883567449392379102944723360059988171635629697409257405480959691779197295669656677648761830734586417189468633432894912232947765791265173854358662243839128496324246563346399646033505617331068163911246069702035316966933422682406064501095288599080849982762250481625954987720067245843402197743827962246906554979786503837452119902130404763844846959913525081722215127722897800460272016797874074998155947305755910437707334668204655444775908880236435476091328248488900720724929046757821085792177732225423451972236067216843134871202647515324752067780075606292705325005400529467460093329893207137361215155908720915748696358709922695829404596931823254445976503582926583542482734225354109517588126251578817229742020298922352983226927803783008519398090666612310477129803126945981466900628438505473702039976196671011987612646536786272771984223190160692418476325256465716304031890765985587958659239686452944637567769576718616638808664590329548122532372870608804664126510731420844049264949140762396603485703673340604021483902574287720249999036760576706478796429141694105677880063424486644036649724983917110232088272663088749927837222699906768326188235018226766381703288127189659216070046311693011852493705367857565720511843086308575464685863792100949991955468765531422848090707925708484430191181413634103348135306535810023560965114969719920374284790471663138127613739813197603440818237131452548241959362521763452597391696120796137860223620002712090057765651086336466600407531290030166867140075757295006206396380893820926706250796977767844991087968870113975533960796435096786881640727165912977292385749363359849126876207360699496431820589039743121829783935383092015856726097346843762493866236862476526614013822955573597419701657606871341759277499177203255562213944774898205026612037142135561340941023086853658610205434319156302687486984374299778556250756297267275824876333180745312893848044988825996540345802866669070941299990355533228234952125183996026966956017611395534473551110846948079919298162817007630712352965497648159232138184115764888428409504889058266424757077912746544884507123636414566307759870706569047935328129981178814148723166305598395986874544134975437309680168535996330407337347260257832944399481423329256726847788240350453008550836970855983042770096116532462159228815117060057396448795836970549181113934553240496696999181995580372540765855199082928532805327822853593325340756043118819209450464182929514138720806900828605770040430905152645380353937226129106374404964526172445972350638944830577969817060543580031653193477158061643874846596244405320199677203326985095118071493810217473845063272488568901829197732017956926038371841641775960234919705180467885309654090533770603465263184654454139833720788249871501133878546110380500259480187902927825529857677426029342574789553215423114170839470605598757180606091950453363455484384672163031283997517334477810427775529768195309238147842311429907099979708269949485584510013368658921916897269927335278635254988886808628073932007888309346710981418817018715761160536712955079675103687837860628212873317135139615352340060157766586178520534278032763872925446026115597893800158765452340961086124158794216636124049153885844104420803625433740286847651319456851788785122625074773746245999673107423543711236009977001274086917428613830924543710251578340644360516747615537330389489167197431531336063902694894425317717436360494681042145779393425118969173508272992397799540990525098395732360663558478544623601030058088861795226277370509513463518440528597851092555703156621889851424273972272845094239740332817315381600613148639386101524443990147697075572491299423922403000403705071699212044684548598098653831563456964258545937231140505017315385678873203831809241760424749164272659929002589532351330869331515694165223806070908152842433590753859363937031500851787465330618719990386910597235535302829492529889613990836364513824385527720584866930617964179492102368806221510334013479907118023220554872377736675953806477230131623376989487937110698028480000724817934360000220250102833187961881640003346935285755253753092045935890601047780918296940194246566931663977046527130382957129490019802576865808066896123682896900923825565054837785235787499921557017124156961513698085114967571063965027448949893646527386342314292078566838760478053628491548972276464222321641601249778900013358917548766952683453157128328359463486819191383184303556003770574989861594431795012456082677214717252478696835501355532968657949616135275331645098194661072403516827779245253055326287607922734399382318341976640456043251615831216693267554282529956141000454979782434213654609068612360764882951603928532399603804915063480487481156224808902122065435225311690885116902911541869857498815972369241278828250688557229132995350745371175503963422606740564808386820418134401972342326645792717462113736572835134584557869946147789674554623245088820247657607192769510617409863409155960394905118853067750396490530302433457100669785052115278822813104718552222824755631033650833316013711580782199739614135553329897304365649149399642075127388825971152541256241462028266787625862601361197624272384106908118921139749655993036287837157006181201236160316982295215785329539394127949059071419589991114138518710796547659445570440098987250379946410524300713601824079743591869878562114934889391219325880706409498571296851322505638312724135164963425400596733924365115193000552843085660965737417924333596214040415560297781804249100171753076168461885728717701855201684163622926817298468578840611053027730142019890203545189642530091504696000243336056820669268235244447634752217662816000165665579560633904060280073646894347794973992035624382203872884100556062812999930673863150747049103360078387375041959030548360904637862765395109858316388395494497988708283658937752358539253730374976051333780949726377899312032146980275165952493944009501040350627442527291054957529538813092686269662664187310204829480698290432891246671239288917472803543813379947546705922805207099580541440772834985571942962237349480620580427584649352082449502805011402909493148465868185899084817502565103493871050891901683199780818015422347987833763033333321139850442985480907770506173395020252837314255352502425621766980405259267750612194138168690067427429861141937513601839533894779556765863251083308473103475991940871757607492213621476530591900162868874312618303307868677374096904807918248150722713312184832462588069125877800227015982893122085282600965923640945556337329593693625461926242307666471339717560322989651741539766458311374363902783620203105374982826452657540146552931873145793573076502099516402968696780051309368953077757940900727676708958526208797569127030490786716168953520976417486648900030956427853742888362196695426837735852449863022879021879869407144168261493538897099447736820586748524728255794096806848204176304504495361201153937457829364075341421507666910398313044308902717864528649637516502904602917648115158671232560697800209960285587847230568443270911951201513008855420375759957988854135909608819340045939628715727796702735102743846495380092379111479315302359891811019929650771384482758956486447553705778738509268316301541351096310905937356592175487328387084441886467584199791779015292273067948844415301368786197641894138424752393196073124811671770220079034393765293901241544259228363221045182566144956949295858065948767923773026664109957062395330477385064623420556622952954362640902056307883494028330388067488138811699857816714684149929186049791781311123965798526728693301277552055919100141572922503044062715593178052620752431145895770507666336384784869492322309203226083305985506145998674980081262758549226412295708556545837542034283147454974016269331875317161632999765030732817691960068887009544587502353241751609256011250414279929912857887058593190037366555576573723241616167948789853458073469301530520177819382604683664537495566032695403649825056169015997278068370396754043235193708859188876482738266554458057859545141515459832547882655307781558203869959256613172367334958996666559568121494722317494308255406475723427687491237749203827343299741309856542952594256224301850018690119470833037039535990032606561452873906750597485495363696676118584757772021415766175779567517036996024757001560235561049669894978791550496577963461131217319043902349062135328821677134280173439081162817571284199462690547615961864776066618965240536539843196559388570590688026714246893039567292386177986301963271847375032295382663519062661567589836313183836900715022609542407963568605905840748289419999164034501051458550710817266870298277059965615407920869142789950550252388364117826441244200076312191599596474632733370874927774688857569287333404082750835510368293975365472066446082031761135973574796784560827874039484612852987138422625087982757850869028580364976790887420242943580572778082778604057437343952995029434536468200903674833161531457070616965397653264729182078216768046583565660757239839898050348044530147 (RTape.cons true 3 (RTape.cons false 19 (RTape.cons true 10 (RTape.cons false 4 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 22 (RTape.cons true 5 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 6 (RTape.cons false 1 (RTape.cons true 3 RTape.nil)))))))))))))))))))))))))
def st_9 : RTape := (RTape.cons true 16776341816159063278694288489714205205405748535569817000891132867860650018823025061079248693726076573757424025918401450443689475789883485231934575564528205908430273279180661510633513879566761690272270010150848172470887375367998228799475605395453391133884796988584404404046142012707818995250501837836228304218395632457613353581406499398890652442406515949835977243370273157262195688558963998648022778975682216054354547972507087246024520177593455176930083461233861378095152553771616214115677697513348933359624253452854312776493946201235835038141247646297529148640684767712243973642920975833133045390739599932296864116970959682789573014807919253925493226179943117630735778802883559968609877487530313687386703091979222326785494985561943172943584657482914544876645356426009515476339655209398587488358537646798825207631915259440320027505243801602170655485586606176229221478301843620722379625984456694411466070478132807589725059164798260333268027279447339774975645691789604132669987845302545446072048362598519218941317651847746537306584449145014777537692941196452201787292986509753361170939114023089595558997558726738454567745893722619075778626587968652273850078110048204689353383407470368817102697511484106219955516712447916524762352694529979105976947864902551496131376744183305859328229668726837055681741220641230074444615757496142880579866552174148007655947089487711022723935416341517263148520233016119813316512230361104519402502667682096024098883684110869199520074191466798030218329186946965233430206500463608219569094519628470059586612861789024533615651909224059121342494454626914325501076507877501261856191146084823686130129660536493779664253567508336322810804416298929024072314708270261612873491433127755106671816858019439836335662077717308560193197756782650282602448649873672495455908957330974072651875691293057925731461711242290018384761259261406821087390657150418727746566304937244668768020836742218457585506205568019129642777999068790853566504667232882178441400769888640658436796712764195568633917370416464540908343937522781634685337336101774287042484955792801954629538998185699309758048288495582201727186623318239284542891973765413577377643559851111572267418404029461993232187962084228771378709416801129201188752409744255240486652064669968424117659464793023065219004950058701986559991417741080398130531706701611175138028625959541086754010092669322749720390005993158718799071699227968521735729032570536995724215982527405655154199876502410212255481451299551388523707582826669878625719545099182957900741934797621888693187286312879409477087958260746452657454041732861346358515085282743332249046440224610403423629282790775661195099051353706457475534921796615059925639115025431912980054210815063817807756837992999399097459945283899921757201151863017683312267892577996523100969226330404966329233757369713545312152571809608890491835535774515924742199641917301125614289980431690319396833115272083715304902639421732249348316984455759619768706640133227556635807214416668072356560458494854636064239931872312462469467700609144080291820814781939371847000571315224307060246780705071421645294073436664659696142476475492623196854345236533972260228928779080686999336265468966025764532071394619769247463663010963546535919329211996696776231946371041254366334397114214571023888434766809753742916717396329073670468575677553688140545817058788036611540039568710891785617532814405505904295722064357725093093957758987474861443006518258736056051057033072687143450459860376442726701130024546473962468469421006880206513546545067254336966078800994949121046036000143286061029053877288128462841550485142947734507905809630249339769326604657735633890138261082150665561404003336876719384188925385224920881011754090268867240496238178260942204022127405957150158802183402684897272074604009018871143002595575796951493351373842155530932281568497985535723027879645075108717782051230545241988511643616251097491254884742697405207484855439044879032194822005627868559964869476691667512168554325054119806296677149868340343492259166312894636149076675993326362159312657462083338831170059666472135908945985860512501626965179413406751132692053515455277265857729996887778361513970790392033653204305243096698996814879025482597059975669229281745313977224603874740903584645189647710157966460561778839563702666688296462159753750250894842994012542917457831501213796364453556132497869574187297941814534650112483817254098213121324253109763514874224821004478087488745077879133051173247700100404301841914865478387979263933140655612615371824664986396577361033443151499531689732654115763209382426560935764225363042126493607713564427044531972761655975060119168233301663122992231343552742633334456748557866767208777267234718570346680479663267716201672731667959426439639347160369998048248844671965199640859816107873284253325068970633706434062280580645605974167233525708902453874187814982378786094642633201690271888355707445713237488601288484966526749722422556279575723519301752411710109033165535909508049688210551969659526885795214274107105622645518700707339569148779605657670544624992941386215812971217797978264087398248580183808048318657897760217850173897389354206290889250891809701646346463800586253911823988651490924874149298129789805989790411541257549141859344457784890455524562331166995130313991514525977239013588610889708674451347875376099040769988586467785471963064107161066031699506720575056371841685171786168096318020703984554766779757344186515292621529530603722854802824067971534617850083329245129297725590919022929292291440062894557812609573106559717548078041759589737257519406736595666447548065642930354455203250476266080261987409828140852830121934010720905698624704864990580237714034206677155851832213459759085317424550247768108520882076225707140408356812815475995411831119378439213040395519678406127045018616091160608720719343488194708942989409100539116277552809801896152705515954470349362504852925958827745618370846788887624831527008147505517466651317349907022760901344784667064096999980662755547558460988634334851060631485968244434529263137421313891247738288422872360973411807191624515832312221054794399600642531208578855739236892117110324402116275137362871174846221028278294721160986869424779258773364866985217821365950207270048898815112411328236274102065430783579045146876621903671007946097681044475975019960013705254867853307354671514788860919164052628741566074360950611158248947515555450277987314641515789249015125439531260940189949927955865246255998903303658607911403911226941465670120445953792468844683789339492679558026708051037632144283144580376134354004437509644513141927332956595750475321549214449116950489450652936963243757247593965171308059711461241488044319676832605137125141467023799398633426294397575237765630613059319956053487807523826807349627036035553710489732978207550502499567929823879190808335123948106383242646394012920098138994732481645859896614492836028627480232961434201589825028078391089890080928614601896912292431138994200154802983162293784930649873278678507951718868049633829407147666070601807580241187652300109921798325719002102078562499746642187006621246495785493815971319409269834584520295669144511048767169188477110712102341367859716832085220217185662262406998857634714964765657058673384477048274504883903777387316451656432988760103645443645587617039244271736112056945765443775777134458005291237866719728519803735064849075145158502524208144204840442804398312401886330677011387316088170854653411258220008227458930926585162487619989744453167858915784845422122506354126364659262239304772541767881530749847531515113044958587450900470000957769256453928302005667364634216198614443112831591813667329677625312683563085960874277007975813214981509700936001355357378258286299813854752644564060416127986464914203191551215906279139506644371294637763656252788494693915771041143713641217879572817499750140158975238254655321909850669357078317351736643381386931742782472920426515559792092407401046494263141710155041200575335861646940364239736363558541873297332854472631826123240847837010212777856933146667434899123285051955452518015357225482399153373656556737161746582745714214343155414382080537250382714511785385962045205768712432414607373653697952691026832184923916478766513056132662967348339035727458735218895480917253928194894141475681183021222455360287467733121964269240497290154469279759740698161818701131173771906903231969541197998623806936531808448448703570274111553048763061894806769507223061384156717169548209509821456098046734678954560598169279987808597215357049638802009385371834812775168133984589811436739019537481941901423731409637787305228188473861690327513365707746663833771033343627403082368121643488613371572896252543169542238397370062578975901399461813165199480174307759102536652654043966141695972019803420575613683021489220065796778512830531671670578934263218967623105130921548105060714058280005293781422083214385092908460221174220566610345077489794678719687192940445981311667707287438321812410388915727245005580158761247291765408735865376489537694221193445401267102794790327264889881697424351566135630698469355673177897911400974234348710744496722450329949407720660904177990673644407060722306902571512431076923528364559986469752207623954582795288650511415782007385766684105902378902318831395364811959571136186315435913900673642330572869369391491087422553506946387638882543406433034082565419690521891700121646551430049225579010659362803967707430136246608299486284359963142366586054442768376736464986957785605245663922003069007373519837089759109275562542248892400771900053535901557938156169431949298093239029490466511506328810478695360616681594480368261073876352700426796621423262907755848800997654728913814951835678005060654096893439416938554178446269730229368470835762550367880965237188078289648867167945997509092492477010324229677163937802601012389396683503784733832267563477763673755780371395079992509324187530025408785247098410514724386614824398444261547006439489621501110619351785490935617183598833041459880451418770193159920455344396131548508171094176311644401816541627298564085921530617425783574819593008496108358646697075889585087807619824308838220094143133390573889959666626164089258344902943692040522680241330361618350492359764546216062303334198175330264176156470243553830267150795907222213778145265701473809818011997615513043024292250246219312155594191433393381548381140444919941624575752862103977125418082986148672377657670016900477779804129064687264309280396225462020632389503866738646278881160302802795351528501224729715737485723314430304032747481239091519290617540447891871331058883534752158431758600638272186752541116565923911421303183309681644947748981823911199144080772918388493437182005276479340832517133032402668631686927257026524996794479248270075866509994252157465135460297547166239046239096217440788776204943282813426893473582526569708896392595829940132268661729813593499821569740257114305013873750273731983185435850709893680688508224014233347221539749996991612112283660393440277286141649828403652472583380412860015162894091421055371078370746419411591137062477234843309004420311771899873809630125660634295018833615340860670093976349578134247606626205846045225753071800305938102747695377752491766843260430000638600438427663946364998002841819914604109065799584588974899198653485556488642138431485409392358772746761110770287836400549522363153599963543597581546375759209643875812557491642635804629668440917498752686365026069595742316102959218041072866302278183360124671563227359620249553935290310389090428944829325273348408948492963607473950931291378573823858638128215331629286078223144359051143073707508200084311289061755942593728807653599711056616719563787814501597294560043229361834514558079793097110104446193212500293655451560364189275763073811527233913459946536485636379563768389393927827852195539594034475217742963644777269031500817276562408781166154563483650797583583726782581287482970713451201133481526960337387109946157775030852050248333906394774874765911486651596959097246631456850192561582923069668610450709724544041622961309819852513284998871791238367012359070015780871888955192731097919961817672137901333670863226744307348867333071756640915446343451450846498637560966422239915252425073832222273855937331204929590951121391898074583101866315322683181168116712868159104534550176524890346469991232861156323327243306631455117100270453680291116610219187762887791351436578542797031841786664534755983176317741120905834764506229018615577992667434544006240930012852199012804486739950404225547894829998906955614993642546469351863134425236928218909738165883546079915304325905234801272503005212830635546007676137236583419190401232646636984538637345916607350131200161964967285757341420852526843919610611690634307077059255663321684039604112249572964443007242101076714075027693251443040382779247003881154024748358516988657752464787804239168199247394370637877308172057996021785657927471635927340879201130710107850612594024040941068092901115142084403967108130198240807435616036304161334470857587762644856276433152971742537297862142784069249788494997970662762321376629319724671415269678078360900724076424773533582017827488165812600054134074566338345717066682623707442988850247551955136233902987268304368951457121174458735729745197650615293718271383795329246964888599742670134307916673395255293175883087707120625989914335632377221810285758909003924968643970093306842476247866524430525228824049137853753814640989279378744757259952130123056499763162172172980500696154184068830484138656919262973875685764036597161944818192025498108822300995323260166581557803848409516873837891026041198145488355915569075776157981545394867658360502206104920328006551423906187972742302225963363307402864194292928070995103463778131431681271767750996498865625716028446615575606851706420454559201291088863484122156350502348848355576821755552073012013046844974852448188710501672642551175305521487808161597345136778590435600685853946169508049165520902125518698044696134994433236853275942892011337823659763936073230336736005982779907044348640507059495796732744672563939994774817272792206568811873596558109889395645020206109119558865261823070365634809283514072424047975587587586693375748490127432853073894366386362107882341507850936563354612806009058897097046049944253888282713446224363817709893608227147461852853156136741907959199424501014434108683364102173286391247285077323705637575437345093057892703539827050696370476627372591326685422040774441953294605178701586810996388581564911877689872956299794978057084989994269183848909892597141470255076974943167746484310310745645089807301432616938642256022053870789015771797675769347732020731494854418524763149403760772998215624968200245721253665395260681108508930947330713467992042365318083293494473157028666447295491872588283146600870186929284554988492050116016052150146157738757871429055535672168878777970839947040872417840219370167097013425242142157585908884104881750417631441477719693119451842367886415503346108957018477244585737491835078741875132521449685738676166302187234789145074783894277622023443101542434227034321983471137794400688729669492082949986250943546731430451434306730203730772096758224884557411715736610236937154276271679088840431527654757888164969572228801420702135600637843497445408519713229059729289267168126067134715368020630559216555683758748177646417750192349803816748643245562547919889094050781356950380758733091927048160628041963069016145816386471125635131275194677702492300092365786912528715899836473829524734921585469166305194927992654516889862815532219342740104572989647907023647419563265813065517352517361175503378560197063503507871905547884225286018529067857465684892642472100737658839505793078761066498107783566947242280395809341444777134381947294617254885564888684898038497457169235933263290037831087722468483978978701975685027490347869603306416490651251435389986726741777464007848533799646115881897521495445158149427104302966271120760832272322510153004889414033582614642767239237999058784343072339846133602262508904534923221152941567412615965217404703871829023480690383475229214543908772998655469130332393084062829185463806411528066722403953901227722625226639418423292660632819394860361082731160499110778186659095265605452186351192879615026341223612448867830599757758532808113689167491516369382132630970112623924732712581431213515420911772012703766919636701990925937307466437329517060760692559079219582079143264480517000202956338980861802074215214316515858799195133870389191729874497659367766408384512766185012581902667022364623979497179881591775287633557752215169668178796596496745074981928233025992979565378961984163148793209640875223034098400280234190628010412325059084614887318345124811868624046188240411746823290331907114512737891736425071861016360155021579200690012290084630373006244151189436437281857956962428680709814666491268975642704778875383773762353687093053926107604592886863665870303114129865310156432071132877758905331165273891192815831943692679153194867299607433607002533098322825447093432364156663945334912565468870479089018215323447566707720093922855295262192996906165468501551548041691410590723988602071072537624284827075601645008911536100782178405204749645369423312609335840305261914998746668842115285584563516554031384641405784953848199898481200155188247544687297616991943341406658943669192306061829188078574854249910841356176119593527025417754761460175046570576264220897916015560724786823845102243855979630169073297788315404497825691482851315286206589527631573558130781019208757200876363116707922446433651776092369621326142989794122226113003490741187404849997459969084020087033050531210576668266184699998148348840711175708153610265866056770197075279600573940335350900041612707081831467681137281008835065355835765517837332659348251977537942774328095168806866899287661289640497751983056725407240805256204945169228187637124953624200341895422678005717007757625150799397379319373444954787739626762564051603939573632665435903025725571027968243131965822835114562637455509069672711710255863606169727774641844899943665699890628121490687481978216719482661846582295767623149884999835422210765730447522147247070529595642848260968306314598111658727384235254929025440317627409251140223199913963783328279181270564147835234007290120160001169139888232179035375615411314475272971728410558300220482659925454392822269770971355732276528404455285353898344609111092517995612108233849239514330758081480518969385565992456835495989984741150348939856534843803803400970109582644982293566402228642861644576262624003357559466752728451154963013307671898939042284234039531962070140764481464468571118925571640121449393183894444934497970753123364838794555572274482629155691108217201592825630240150090516311362383508133834143197082791188038937404245164576047335768232675317998608943555265485738607637409927489451435549601803127754374811674728933779018126358910640614225893408881088642833330924573359519918209791353995407664231095832507880985408818092483923343178226797037717114477212100080417219518779788900604398685590585593340209135674243339625569458628960337674017066345267965110534762993290367898881166997454739257827931022547633182974050014084641552202264955789838098528505957716189957691258198332806062190445934149113538771830663813491559205592335623677567054216700600739843859515260603445266746758562602435712748620836126076774634719639349837786349797596427541685985853846497849344126012175118841692970768238840776058471757836704874453680749845501251892257795977185092391048737507445487094088754079177381069434716892045530006097959883538684939406706279109547380968223429065913468990038343640847941704203608497159132564777363398545482697415656962078609311347967307385223636090565453125885839072736485112248327513606421275229969584147345940534248260577703683508817549513953962151585265408766644289733336733082239830041217460984149191865957670033579366603492361737915067494862782362653918917920795238739644321223725285353798428341545227142311020804253806097370843870120342030066252835921944705519813162801439710628325698552035821013211139950292132346390530682667664192095540120805262979783426658871665781444023655685564622399813337966122116182349531304393600874568762115672918160633614583133658879537077598061125296598176409426695879838894481951940891533084658236651513628024235022525979929588952134930522916258680185137634731719843032724928867099539567592675972111574771520304368968169852219810704199727224815075367681075111888968774777396902399857214974282054055450827387013817048779925341879278694220163318385617671596145325587257265310328653969975799646816899914109491209602840727245418375511678211943031046153308172367245903988534132809912339759737628022180472173102434572400058682213184035661242541119833180027208146112377465512977234925240095792511334503688376815147734208711167673882315855295464007823731405752122342366060652504372878434944650273012687259247434168704084624929144333950087916494265781949834588378309462266351132240873442771131754418935998602890629814358439390638848949106448855898889354490601546120333018174634792194126917139447078677288953939984893606715347241442818610254504068387585345740600553967225182495812206533860194041982317599808345725355744487455008307465086553916746330483568480230821883455731561819191478450451504593665222751827190916914867323979123198061765547045674645776652993319303184853219778835213193928453592641529184823302143986264 (RTape.cons false 2 (RTape.cons true 212 (RTape.cons false 2 (RTape.cons true 2 (RTape.cons false 57 (RTape.cons true 10 (RTape.cons false 2 (RTape.cons true 5 (RTape.cons false 2 (RTape.cons true 5 (RTape.cons false 3 (RTape.cons true 5 (RTape.cons false 2 (RTape.cons true 3 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 10 (RTape.cons true 3 (RTape.cons false 3 (RTape.cons true 2 (RTape.cons false 15 (RTape.cons true 10 RTape.nil)))))))))))))))))))))))))
def st_10 : RTape := (RTape.cons true 1 (RTape.cons false 4177236263720042510692459195910769287152494841244238719031716522500259202099147094525540774865801612492881855040068102622182819354272099323434465656525684482582165385751043023173315953194773557618250252424670113520937247097784454073569709612321502036869441567498428152093058406593992085007822867329301751054315088048726439745919153992287234673721229487526031179006548070635583838054600425423722450710357156258682836102499914625870333604778051196479924327817921566296991148715080262825351290863041315453766763968574019037349313799176448843394809434954343477410592555793533038600385781425956697944659487515457115503631864612057949857451115308610461462568779974158514524450926633470237211484173203545874789035997378344543630500555275586236932837672325083264490566968137440691293743943973398994798183258372383780226905280706041445444405521656075141624480773629838434283419024563342362600558758770995817696324107581151361135649592412380213151431670024435506983094103679794848450931203906372377581463893288295464677288703429682943625580986184577279033588789430145481246140703640315203454443055434824964933427266875804646239935373424727239068269893942211914727325282950399875669369620463273563391570169482764544726931593653955065105374786696422013440033935616072702181626454062599765003530888241932477853356841500189029295604722473348266281141669000475713043805452853391599633700069777508154412673447562233913887067755674409641781058599772674122063378635837143785194105546658057386743887885042151559849750664967023944871755761303026368560356979395266062687718823749212981304105864474361969308809392325542555887882026133047621564663018657372627912760870025660917534137015035135004081415462332056141302925553261439730039571174188011414399624250019945812366518885236921582668739030467944285964733870413545857940831910850754790144488026317263486356024766858866228971251630006344621720232554297802904844101874664475406310839903217414869064809761456250777984144469712174065592528357166008836663239668959892197837229743086221655219662391954084329645814539521086799519307430373721072900055450390879004339746080974068122955818424240043183932553325836708011149802322024710783304919363433899837482561901466622578058100181657965774013580689069979497052154916675394662929803717967718829549842445624669309914771455486644905533722070467749270789537940589077300018947836373433620284912187020680311933005263643050354948921109511512389799524567633633512529167989243233577821918174397296237399075334918840372304017854092406176057980278044963325146349298246048545926661619478129699330181525145157402890936284889117737024817487369970195242720154969560834643556425253722820953340135520663891243188040320990560164304924227347735828811314456562856011592274015401721157914709705929421443404722779822771632610469419155257882186322501327507740063389674042366238702191187905001776553742240972624200645967658879961703471369268290622121072814457407505396535800212576644089619925878107775569984529285211796006411827058039828656472076860083696358664782070034801204816795391363646396976004351792079540555515074815205714419912415682464502471027627332361472016375600712118363856778916988282018346068963880203950667393725725400697117418862975414994392339740922028741305421957839674041306161735064987762803446423484647785477620495607190156903227049421103346519600047045872718101585266624863516531337410897692480742688256238868118865068056452710473466946093721760132082534766838697104358506951485692190111017172085675764933992158506777566572135061689147272583862923236625824037949193800057320927641806125868328218073954549080421817528295519710582850446058190299808453523691483067825657379420370317943876136653659657484853138685336666084485850645816190097710261139408704492747501238879386871806045446071494067146906156346831069023337640305190489602653631826980655272548011739351348469848927174548167528763133824848566942794743708700522171964199673444905923890792351165719111266511844352406886612893702733843635889421717424789040887381388399216847671580814307136489988161843074111439107140765565928333117036365096140858532722534294043297007814059826363954357906358998597275548017381322633305502933658789829616429841786409883922627049581676335727838850827901438183559627078863573614332937720755043243231827451218312796933419980223991540806130421309298186638067489691287095415141542250776070234208756492510059875061236225787731837271843610543696712676632318667460528127270384921915541089875446077006698733924708980833492553444222729326299947514931394455942425029408186449661465132844229015043004795467149002424097835247240524534243987401265566792407930184861499413259763286439804878866464220394762463788645594834032086569296934212100930248300031483347062834049116403668076894347829761414898339208466824525523753073922524504208808856639886062806350569538663519293199988399462140555653546750000820451334671573467371505037249716236058635121349549198768931120395009595365255282551889787699292680519225949834215450681678833427241281860417535952413831097561601037811482950196880613173055966866157509472841936255736026748587059800506799850169274333319595595029045977614854933504377893276293162023442479254320103022691078014527062641920557334659957368019518108603600117006765830035735094891973820586331787729713408972995003231954306017684937379815605244297572304907910012378228415478161956587271617490614478223865093027162497514240169661466506919909744319061973925083406653745449562590856631209375987186004671493228078329050012808381539216561854106986760103446001405549267426757667557890929424094816081356702253306267421561222516362725849130139920015621857697632889777294460163343402607881767531097987980712579022375772128603997172847251791372070183708351259924091687548998887782077491843623631307355492519124022626102405513897813764137328082571068762083797209812289774230998371140372967268513526323742714707712486324222623671478726081298379833000588472132760961567122395057095917769376796035482625545591295690942717472955385758074259427379116628089050778999029203741849164170891673740340060292552226457049162779370418904269174979208740734471021418024956739392170445114665300174631329796407057007436062609653165031112219935494921154332935862288414375277984744608323524940287158537240172677710516991212881546763972332318035360569836015478906280494753077691228858502268941171149225713330105585964330662481423138200756854729300548016724255236246391065306797354290407087310534332589630532046966373859194954561773567638404753050754411094924598809601196551518789114446110071401356173115928788570646896492222615236449856160859832536367980965844390536532009547155098348542902214249445801743688309759690778729582984677053484465773925230624922118087227307528208486542992946546657339550837984174790865160191374466291929599772323597111289344219350057708173881685631880165220779271454735650699671480942822474668657002140405666814892673284924803039693143571254521642351576987404258983060703761851451459531256178857673944818598586519497928584409213783604327841390215056139766280096095382135244346004198867082020099792923498535494006533838275262196415410170035943186081392573935198558022850107346198046161505303922302550659929788719570372976343921816135680309241567457882791093443562291609638671588911461029019782797468981419564453758480317588042662279512681253976461680516531776071426578217392200995456905490125016743869427311761687803696661089599864400800910407712685923190555838539818797725386010662806724956092958199504248073256922933803509360609311448295628311094984897313735389382709655170539396724773367387413128435640431992766808983421809421062748008921955864992807521553248372025794228394127058291876102108027226063155238143952432982725623163842126445900209024044059568470834316260366880272646003733932087364032402841349910137513934018556759719089472164754258898307996707879368849333455603445841651104993232189875489056099470368447846322899740154653232454036996099303435864494672158439589784829359598138195427416772554673836901395045848243179575089759995913411734689591786932377269914350152052389543917404349425352302712085377922140403464859951565613497321845059800367381664418615758648172687268638214651888691916835146760963230586604011096233817201266052078268947339636940212757893764371246257306302914420349291273064967742040225804592729523589048480744566359302330644420271582272324996547594779118702091531375803237346937129526600568456001698655886837564108285492871899778536269956437899915905637851098404495912406874038545504225267483132627707908573163585364336900964812700180129983103490659758979322612338957390808313288670127371326113024531444280869959846710731514749810575193885164849300660855439381153198219450601746462904383312735936520296919598668552156562117013041582054643026695313041038434315546421160447368724304524101858335596002668043545189665775850639352346702688532540505160191973597954397281675028634723982878895888466388057576762984728243968103842627420626108425380626802844474179314698998166419524871481817692489130538059511928460644753034336426768693748110015985141916181536939027271506815319647358590451900550637624491797245442270551483825153827482678625191973853893969735196654620411442491850208393204702832675943357376643476214934889480255750621650349701628437720855587753509947005019231427544408945312959654837694799035212486802773472997425034625510036594077553957852828606230573179322383410329504996597449702744425406426313965204518184761409912402498509497799536530660629035549653811301753947074589381637325494425965240934238658833116819216054975350567341410508371768575306929697079927187902813031440400276735970113857346349427890269832265409068970124282908057956274693530976058484563530478266279975858815402912176780131980821439899937023978525720573617856604350156388903425178954377988841135670448998506513854623324016372075795095285906610618407369194947589816872399960130672896175644578503539700968618128936905414067235306746958334378494796014763499402009474958097466412795162696617950550420910534411445347963784653962041186360243491060336758990502713602324765283313461132038698349542055000718476258633849176517405735674391426758633039624293467347390105522745407376185318437009727057903744037922760976252083783275209105459874181534609348555328785083959394776834268357568052364829304914221270154508105146239884759180665405566021546714550494370363612981964639662138149972855608757258185521960074292391295226697248873229576984999477062661934991954313192876199687940071814564430170580492138241385535453631531836071214245693889774153935143870815466215465261009381068370070314825144850531798793159256579151216017076019452185458471514723140979072548028516731281438597540160135583132638783372357097734380508845145945341351527463964010204781701932092787470185024684965030623978688335974267443185424940097199070806927647149270690553180163391318718757535457841197925472356388924756853773919565322832816668583964720926699921211846229887272592302932882932492317071122480141737357598358428447570968861593610480841029506814767325898975917400660574681542718238549082576168528245564908634757239330475715028072485475886545752632609738730029583043686759249746841087813821539637979804208359921457181371728461168565492978256035335217104780071128688294088212721871476824187406065812216556664842551362480083693321476597670743327413494801919895255649990161759398652351241563943406794124607999591524433356614139930696028992684400177997921239104359989551034824738139759054617081745170097818345526503906310222245639612025420164184435482130343862335006254805172262588476251070645179856425285299091501823765545853076666175577631505416506852086777298167449810112994869511949827007133202363641043161271091940116512845778720345146337909138482178882013209391216972670593077691460777716423971965525772302765072884959638196154353644445760489713158236858689431280003572286655240644496915460389279499790527301982211750172311653282218832619712864978998244043123981827781768456546401301257883645643255805304805886142751997760270434252860968148904771501767188229748332589382122956163348229055118513723922702858859626812659274796727302880486772289743584956843564669729326734999164002030214383817083890743697116860537057399610385902327584073073177630812590233438195582374932376794489676968826897693835782258475400459674746280859751513086579872164269406511799713741791127635877323690713616283102302020967867539484522089249095812098794153300684318734968173268113198292257051599395220109390943989360188564406874692295741673424751124917277274068383586246409857167395956807597379686817413427395107140888757953708587388891519122622419874534078366708397461369978332959461158693592565633208602035885371491116413017654824378794888214568431996452313613658249557137113113381546853053924560795139536852801167718411415413015303488495265439973692841301135603347496570686419383935575967559269314397140976916816681742475551329809746282203548626925794108993704263580142962658996031999817632817556276854238267715475426030708402988138050478284086352431928795387256979299101962912768252117931988652053874397703768179776290194002196259155588540260681600916306765836291703802025392847264968458980226944276242236874756548877256097496023386161718797895814323231045239469018725022024107489503728754509892242244825332635854473735575556174560145328939988913555236305483580103884702261862515810648655677501112209711977566417767495053961513727538906046313895826112103086011717728175371894550767935647080111264901971946764399460952450533861930457229525338563319195289028759557032444086402507438000567158455795936046406339684479483458271707934994743516256371974856984321047340321178516546094664369708813955419448688154852032022320876567205540677303441591848551805999605196543455425266510302034469096272612653019662984215508825230358021357938103681882131773890377629454778925962881763079582047165235253369381119502944430442567248929054894960650250913436277498358111655474699626186589396978757913014406184643263222968527249553116209812249069813629900826955218749921403317618402058256089998412468718174171357416407395149928941552601020101945925534330874458116916225354480109819957184444219961194295346691752279985859541631255442559929340581217530363599318243218466361890428824970958240927768522288699774299803338388097893480768573681093558724225741706141096596026678385879048167853200366139758823066775260624543763842608933324530255036398180546061648848088518136263094925217359509923880231942342686740886385892207380618892037212937087609566390691427676231471578362738964943884495807022862163632394301429660505813168909945482485929505073158442232020714738901902817303199964196768941354846370063270178577283165847823426641359139188433379725821585359233841714191002956656183016780028313859334440669532916516567548125617824234491178145428137393903245594885798382986272693875043732024741056923763855038412130354780737772399639993349440577044907987612120303596204872559748530472136839076979588912796133197309553792832374462118393977230985942396157658059870177170774004554702040897530966184194236960527531179446734968430945885647036904465294656091530005551986950352484515967717905315187766302067346029125344363850882451625880801969750758982518172042722895016331804875458846361596315799484724123277641443090529746098337837916952314155857522311125153944024168354436385785752359526285065255279169546107155004666896187138831673621705475692647561259078177947447742326686227537301567497739909356912942342988413293548284664802957649184158411955956338183522563175841801322258247040395856644455451962061282311106203333441374129768726559514090281038740405366207729574730513160633074298908457540986930304652871131837132150713247549162921458874939025808477669781619305193954236100768371173956977855108971907586648558853249104169009954425041195402101827032126853701303338692536695130876278385803827330292171032055412621724128854593910451933364787258298164892225950002777531691987729563986831557254315134795093305510339361200339366055729656415295772825334171491240578058481236141326471783612890111168226635052847023581097739951878323515368830068979922794628023764930333013843730529458664151210299489929233689404710973109973170196468834447508655165491778887854482508305278037774868358524216930002297965882251353089093367457177817738134843352558469044889463115052670273120969043654070984054875143997087218310206195765312479939420552114870374866550025521191149711404001150330434310830683602367514461981296135530281138975870414541795184890485281890063741369285084159299069622357840310707041571505776433074126911967961083982526158984550479477885504600424717674847495341481712780206791592378762489657970494550903087729964054074612584157727896572019341395205278740670625824654688965370903088480533519192316524270519100619974041838195401969229648765141014234512057116225650653292155254836845394081780409450902990731784087758722829238195393516328236012205719569453867145690592908531958975089987443903910329147810504168091116573879397984439150046975644986151295991304451511587711478909579889032178643373952469593400295709247060615101865647431448106177884016313849294113218723112705142427728955026124347000209493453868190759668829757815486223409157373565000378263630308173024892290924227255475309681161923370711667620313102462569436754408035030266420325664734889839392405731770911065710929901096580893844376175075039994429385209898069808647098890794465146036526986699794919669952713603001669924467044891965697515702207041018447570575702913807779036828361139459079212218333008454618897552960390056541597878987389403011158307955953521998239958376911300428169963184615145789063185996239433398321376016910385583993181275415429283740069262766316649409065260369275185240753882585541699151053863598405075833790776802088269040181428513160433072269540808113742282899638887977686782274039967271681902750092527741471639150631278526556254063855053019394061837068379875093624529014277237406705882472710045338600720277068415126710856787787150194608975028707268221461156040476649014109337532044519620757262015810788004160566588386393527123594461910786155561611661428448553542929810466369617477167737281553018205352211520739057001026421188975537215798888787236900978390148264884764995802744377845635355412619758997853967673206670572369529734099631709613347565895173281277237946386977930679629068754607601548760702035717864687769862829153664440337462804041344714513662197006604981730038479275982006220101809586047050248975965279999075452987525727323023254633193630809691479646507215998744010996207219283014219554621137951183855048222323816765651816479973851625305701687869505056792972420337624956276294031041206130187752083723305762465705925052179792228153934370858717911944920736212256997261839528525939992210988157404133068170717420186289274350572625601770320931696491928086457328257030155287781323367834505336753272218895271455194084027469644719897750972392396210890094580010900205997644826711720953614399826293900312046200379026263519208730439889600939948347424467238187261251716145145982007636514504205092190049804927763129320357067478941634683029347475498356955442533216808598728166857196160415209977187980075474400339317450960104718562972435831789077960669900868103437086502204000798472734695592550613122564204902674907470305194390005414565739264115231005394598627312715995144703970221081697137249086983277129573937328792156818531172855578823093959734417909794068748524945730290241554592187104471443133491262866825399140917595546908514264432577088901349669577735496897007175372352891296689386885502045913932718799550485143071533835638368114139710133194231997047636042767079811935737403075374848926948607440028152973112964218721395783602322817188311121812120656550340207985973118091932344509822811970942902877580763965972105180758174968199343712174686609694267145977153870664678350205265183778199347121354641639860935980119689532877548639969538849556709872491846972490435238952520551402205963403589057033052120619654011493896150351992608880758550676227735744440086879886833422029722633606977122081090529508187420787456773419465022422374028226487695814975661677417020578623109181553458949278741376496005064073982645894044223660685751013509034722172856186858958511369641877654964963164456676467220167530021562290152287423569524438490061156472652164028776878761252688683975883403591875975243982805432693194397989318329479325926641977546617267614102945018002845329859501339060346884798178824086996810706540394438974660850402694271666900069920311928074730034189737963997950152432098456204430145359004857724590688028186447899483399403695861726694285099835120401628687558310148301677496413023005465167584018687987313414587299193088008074941749746628210483611890075608723952366954062502289274105196924971126630313364428893250527805883500897971898728464301396532195209974926860656947855817656326610659220113919722823911446255215159024069658820923903917274773574191131171638828997423978306013552715947222963498471578957733120030637955468813765636636966008745731028987960928910174620530711330555184663726634233506019916199373890397966318076319248858755814885191078166320090490815950330120006149226428121702174567954231198264405770744676061159863385973822535001489517413751376244080918674818643952699619707105561712347614678759369103501900865569934415332507688810813050433362553798862324139902010781529798249086513019940875356248093608714847356421616122738557779607879732111409161458167084063911277917232777147987773913631422722607498656003154973509003352072707625863287947231069705454646313077938809898219883502932874639284825425030712894665120346332813854404634372066544010410789172303466039403157655049809261791048793171089721268499605672340175107110280112416148329943059194631816643028662889405499024895081862010533294869678287465780731706153630260566605142363024839063184597727600096046421818708832812862845798579735738318426207207830567745527699187895569583810364858398592760605326201678564977640456621608014638106367301804445557043850385700319902491020710897783444627236497506461245363904925581488770718522792418511742965912543835753203609925753307543718374807351737482215004775365039037166648798140678341352525967009325817140846990151064391336189593102469137304504366705228845876648723250877327833045712301006187721747999254976173291195029265155641063813948774115335697689564997821741499479578601286002850421807252981561682558783688126948634026350470401621252005184101118775434738187843540487913744896046025926918109180431035150765042417029249367865637471260036221230182251006499383465314785117789198801167218069319250148820238529281704900074087053181885000737730978831966536649918748490041307067369020322129313147049572909031757683652575186679027843968042842216928609698754934979784685753100207467194625468603475949270919331207253147404110277254304780790083444260525419565222101968063621488110842413518120600859323518772269809906736260888383237705765507787418693326418234086720034364467133770240244813183371930337512244801368828359916387724921267640965827309495292095741903639854715333041439183543764134826707985228808427874596476358716799144534234159211716344449034750513366616792783474485504587304513420847756145951292064877903806754017209493223027877192798530995481129263186921072543043316724572959652948994200786983558335397376752139385924863680388984592104567284453180337584946483655931324375469579347105584243374357771478603952418103156017257131326778310892216880670859670983066430685640439350008269428311540098884117014028418240041181989041412727693610870081615569719115371186014034925810375670281316835484245106318944 (RTape.cons true 5 (RTape.cons false 2 (RTape.cons true 4 (RTape.cons false 4 (RTape.cons true 3 (RTape.cons false 7 (RTape.cons true 3 (RTape.cons false 1 (RTape.cons true 3 (RTape.cons false 5 (RTape.cons true 8 (RTape.cons false 4 (RTape.cons true 3 (RTape.cons false 8 (RTape.cons true 3 (RTape.cons false 2 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 6 (RTape.cons false 4 (RTape.cons true 6 RTape.nil)))))))))))))))))))))))))

set_option Elab.async false

set_option maxHeartbeats 10000000
macro "fast_rfl" : tactic => `(tactic| decide +kernel)

theorem step_0 : is_running_eq (run_chunk 8 st_0) st_1 = true := by fast_rfl
theorem step_1 : is_running_eq (run_chunk 8 st_1) st_2 = true := by fast_rfl
theorem step_2 : is_running_eq (run_chunk 8 st_2) st_3 = true := by fast_rfl
theorem step_3 : is_running_eq (run_chunk 8 st_3) st_4 = true := by fast_rfl
theorem step_4 : is_running_eq (run_chunk 8 st_4) st_5 = true := by fast_rfl
theorem step_5 : is_running_eq (run_chunk 8 st_5) st_6 = true := by fast_rfl
theorem step_6 : is_running_eq (run_chunk 8 st_6) st_7 = true := by fast_rfl
theorem step_7 : is_running_eq (run_chunk 8 st_7) st_8 = true := by fast_rfl
theorem step_8 : is_running_eq (run_chunk 8 st_8) st_9 = true := by fast_rfl
theorem step_9 : is_running_eq (run_chunk 8 st_9) st_10 = true := by fast_rfl
theorem step_10 : is_halted (run_chunk 8 st_10) = true := by fast_rfl

lemma halt_10 {tail : zB} (ht : @Valid tail st_10) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_10) := finish_chunk step_10 ht
lemma halt_9 {tail : zB} (ht : @Valid tail st_9) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_9) := chain_chunk step_9 halt_10 ht
lemma halt_8 {tail : zB} (ht : @Valid tail st_8) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_8) := chain_chunk step_8 halt_9 ht
lemma halt_7 {tail : zB} (ht : @Valid tail st_7) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_7) := chain_chunk step_7 halt_8 ht
lemma halt_6 {tail : zB} (ht : @Valid tail st_6) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_6) := chain_chunk step_6 halt_7 ht
lemma halt_5 {tail : zB} (ht : @Valid tail st_5) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_5) := chain_chunk step_5 halt_6 ht
lemma halt_4 {tail : zB} (ht : @Valid tail st_4) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_4) := chain_chunk step_4 halt_5 ht
lemma halt_3 {tail : zB} (ht : @Valid tail st_3) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_3) := chain_chunk step_3 halt_4 ht
lemma halt_2 {tail : zB} (ht : @Valid tail st_2) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_2) := chain_chunk step_2 halt_3 ht
lemma halt_1 {tail : zB} (ht : @Valid tail st_1) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_1) := chain_chunk step_1 halt_2 ht
lemma halt_0 {tail : zB} (ht : @Valid tail st_0) : IsHaltFrom (default <{{C}} denote_tape_tail tail st_0) := chain_chunk step_0 halt_1 ht

end

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  have h_seed_pad_eq : denote_tape_tail default st_0 = denote_tape_tail default seed := by
    simp [st_0, seed, denote_tape_tail]
  have h_valid_0 : @Valid default st_0 := by
    refine valid_cons_true (by decide) (head_zero_cons_false (by decide) _) ?_
    refine valid_cons_false (by decide) ?_
    refine valid_cons_true (by decide) (head_zero_cons_false (by decide) _) ?_
    exact valid_cons_false (by decide) head_zero_nil
  have h_halt_0 : IsHaltFrom (default <{{C}} denote_tape_tail default st_0) := halt_0 h_valid_0
  rw [h_seed_pad_eq] at h_halt_0
  exact halt_from_trans init_to_seed h_halt_0

end BusyBeaver.M_1RB1RE_1LC0LB_1LD1LC_0RA1RF_1RD1RE_HHH1LB
