/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RC_1LC1RF_1RA1LD_1RD0LE_1LD1LC_0RE---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RC_1LC1RF_1RA1LD_1RD0LE_1LD1LC_0RE---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1LC1RF_1RA1LD_1RD0LE_1LD1LC_0REHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RC_1LC1RF_1RA1LD_1RD0LE_1LD1LC_0RE---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
@[reducible] private def holdout_0451_tm : Machine (Fin 2) (Fin 6) := target_tm
-- ============================================================================
-- Section 6: Direct-on-Cells (k, xs) Sk1 / TM91 Formalization
-- ============================================================================

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 0 = some config := rfl

@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 1 = step M config := rfl

@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma reaches_refl {M : Machine Γ Λ} (c : Cfg Γ Λ) : c [M]⊢* c := ⟨0, rfl⟩

lemma reaches_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans M c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

def IsHaltFrom (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ c', (c [holdout_0451_tm]⊢* c') ∧ (step holdout_0451_tm c').isNone

lemma isHaltFrom_of_reaches {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [holdout_0451_tm]⊢* c₂) (h₂ : IsHaltFrom c₂) : IsHaltFrom c₁ := by
  rcases h₂ with ⟨c', hc', hnone⟩
  exact ⟨c', reaches_trans h₁ hc', hnone⟩

@[simp] lemma zero_cons_default : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl

@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

@[simp] lemma append_nil_tape (s : ListBlank Γ) : ([] : List Γ) +> s = s := rfl

@[simp] lemma append_cons_tape (a : Γ) (l : List Γ) (s : ListBlank Γ) :
    (a :: l) +> s = a >> (l +> s) := rfl

@[simp] lemma append_assoc_tape (l₁ l₂ : List Γ) (s : ListBlank Γ) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp only [List.cons_append, append_cons_tape, ih]

lemma pow_add_list (w : List Γ) (m n : ℕ) : w ^ (m + n) = w ^ m ++ w ^ n := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    rw [Nat.succ_add]
    change w ++ (w ^ (m + n)) = (w ++ (w ^ m)) ++ w ^ n
    rw [ih, List.append_assoc]

lemma pow_append_tape (w : List Γ) (m n : ℕ) (s : ListBlank Γ) :
    (w ^ (m + n)) +> s = (w ^ m) +> ((w ^ n) +> s) := by
  rw [pow_add_list, append_assoc_tape]

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> rfl)
local macro "step_tm" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
local macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step_tm)))

def W : List (Fin 2) := [0, 1]
def bval (p : Bool) : ℕ := if p then 1 else 0
def bit (p : Bool) : List (Fin 2) := if p then [0] else [1]

def first_cell : List (Bool × ℕ) → Bool
  | [] => false
  | (p, _) :: _ => p

def words_tape : List (Bool × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (p, n) :: xs => (bit p) +> ((W ^ n) +> words_tape xs)

def start (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (([0] : List (Fin 2)) +> default) {{C}}> r

def denote_state (k : ℕ) (xs : List (Bool × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  start ((W ^ k) +> words_tape xs)

def retState (b : Bool) : Fin 6 := if b then D else C

def Side (b : Bool) (r r' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    ((([0] : List (Fin 2)) +> l) {{C}}> r) [holdout_0451_tm]⊢*
    (l <{{retState b}} (([1] : List (Fin 2)) +> r'))

def SideHalt (r : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    IsHaltFrom ((([0] : List (Fin 2)) +> l) {{C}}> r)

-- Micro-step primitives proved via execute
lemma wall_R (l r : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) +> l) {{C}}> ([0, 1] +> r)) [holdout_0451_tm]⊢*
    ((([0] : List (Fin 2)) +> (([1, 0] : List (Fin 2)) +> l)) {{C}}> r) := by
  dsimp [ListBlank.append]; execute

lemma wall_L_C (l r : ListBlank (Fin 2)) :
    ((([1, 0] : List (Fin 2)) +> l) <{{C}} ([1] +> r)) [holdout_0451_tm]⊢*
    (l <{{C}} (([1] : List (Fin 2)) +> (W +> r))) := by
  dsimp [W, ListBlank.append]; execute

lemma wall_L_D (l r : ListBlank (Fin 2)) :
    ((([1, 0] : List (Fin 2)) +> l) <{{D}} ([1] +> r)) [holdout_0451_tm]⊢*
    (l <{{D}} (([1] : List (Fin 2)) +> (W +> r))) := by
  dsimp [W, ListBlank.append]; execute

lemma inc_step (l r : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) +> l) {{C}}> ([1] +> r)) [holdout_0451_tm]⊢*
    (l <{{C}} (([1] : List (Fin 2)) +> ([0] +> r))) := by
  dsimp [ListBlank.append]; execute

lemma carry_R (l r : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) +> l) {{C}}> ([0, 0, 1, 0, 1] +> r)) [holdout_0451_tm]⊢*
    ((([0] : List (Fin 2)) +> (([1, 1, 1, 1, 0] : List (Fin 2)) +> l)) {{C}}> r) := by
  dsimp [ListBlank.append]; execute

lemma carry_L_C (l r : ListBlank (Fin 2)) :
    ((([1, 1, 1, 1, 0] : List (Fin 2)) +> l) <{{C}} ([1] +> r)) [holdout_0451_tm]⊢*
    (l <{{C}} (([1] : List (Fin 2)) +> ([0, 1, 0, 1, 1] +> r))) := by
  dsimp [ListBlank.append]; execute

lemma carry_L_D (l r : ListBlank (Fin 2)) :
    ((([1, 1, 1, 1, 0] : List (Fin 2)) +> l) <{{D}} ([1] +> r)) [holdout_0451_tm]⊢*
    (l <{{D}} (([1] : List (Fin 2)) +> ([0, 1, 1, 0, 1] +> r))) := by
  dsimp [ListBlank.append]; execute

lemma leaf0_step (l r : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) +> l) {{C}}> ([0, 0, 0] +> r)) [holdout_0451_tm]⊢*
    (l <{{D}} (([1] : List (Fin 2)) +> ([0, 1, 1] +> r))) := by
  dsimp [ListBlank.append]; execute

lemma leaf1_step (l r : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) +> l) {{C}}> ([0, 0, 1, 0, 0] +> r)) [holdout_0451_tm]⊢*
    (l <{{D}} (([1] : List (Fin 2)) +> ([1, 0, 1, 0, 0] +> r))) := by
  dsimp [ListBlank.append]; execute

lemma stop_step (l r : ListBlank (Fin 2)) :
    ((([0] : List (Fin 2)) +> l) {{C}}> ([0, 0, 1, 1] +> r)) [holdout_0451_tm]⊢*
    ((([1, 1, 1, 0] : List (Fin 2)) +> l) {{F}}> ([1] +> r)) := by
  dsimp [ListBlank.append]; execute

lemma stop_isNone (l r : ListBlank (Fin 2)) :
    (step holdout_0451_tm ((([1, 1, 1, 0] : List (Fin 2)) +> l) {{F}}> ([1] +> r))).isNone = true := by
  simp [step, holdout_0451_tm, target_tm, F, ListBlank.append, Turing.ListBlank.head_cons]

lemma emit_true_step (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) <{{D}} ([1] +> r)) [holdout_0451_tm]⊢*
    (start ([0, 1, 0] +> r)) := by
  unfold start
  dsimp [ListBlank.append]
  execute

-- Segment & Side composition lemmas
lemma wall_one_side (b : Bool) {r r' : ListBlank (Fin 2)} (h : Side b r r') :
    Side b (W +> r) (W +> r') := by
  intro l
  have h1 := wall_R l r
  have h2 := h (([1, 0] : List (Fin 2)) +> l)
  have h3 : ((([1, 0] : List (Fin 2)) +> l) <{{retState b}} ([1] +> r')) [holdout_0451_tm]⊢*
      (l <{{retState b}} ([1] +> (W +> r'))) := by
    cases b
    · exact wall_L_C l r'
    · exact wall_L_D l r'
  exact reaches_trans h1 (reaches_trans h2 h3)

lemma wall_side (b : Bool) (n : ℕ) {r r' : ListBlank (Fin 2)} (h : Side b r r') :
    Side b ((W ^ n) +> r) ((W ^ n) +> r') := by
  induction n with
  | zero => exact h
  | succ n ih =>
    change Side b ((W ++ (W ^ n)) +> r) ((W ++ (W ^ n)) +> r')
    rw [append_assoc_tape, append_assoc_tape]
    exact wall_one_side b ih

lemma wall_one_halt {r : ListBlank (Fin 2)} (h : SideHalt r) :
    SideHalt (W +> r) := by
  intro l
  exact isHaltFrom_of_reaches (wall_R l r) (h (([1, 0] : List (Fin 2)) +> l))

lemma wall_halt (n : ℕ) {r : ListBlank (Fin 2)} (h : SideHalt r) :
    SideHalt ((W ^ n) +> r) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    change SideHalt ((W ++ (W ^ n)) +> r)
    rw [append_assoc_tape]
    exact wall_one_halt ih

lemma carry_side (b : Bool) {r r' : ListBlank (Fin 2)} (h : Side b r r') :
    Side b ([0, 0, 1, 0, 1] +> r)
      ((if b then [0, 1, 1, 0, 1] else [0, 1, 0, 1, 1]) +> r') := by
  intro l
  have h1 := carry_R l r
  have h2 := h (([1, 1, 1, 1, 0] : List (Fin 2)) +> l)
  have h3 : ((([1, 1, 1, 1, 0] : List (Fin 2)) +> l) <{{retState b}} ([1] +> r')) [holdout_0451_tm]⊢*
      (l <{{retState b}} ([1] +> ((if b then [0, 1, 1, 0, 1] else [0, 1, 0, 1, 1]) +> r'))) := by
    cases b
    · exact carry_L_C l r'
    · exact carry_L_D l r'
  exact reaches_trans h1 (reaches_trans h2 h3)

lemma carry_halt {r : ListBlank (Fin 2)} (h : SideHalt r) :
    SideHalt ([0, 0, 1, 0, 1] +> r) := by
  intro l
  exact isHaltFrom_of_reaches (carry_R l r) (h (([1, 1, 1, 1, 0] : List (Fin 2)) +> l))

lemma inc_side (r : ListBlank (Fin 2)) : Side false ([1] +> r) ([0] +> r) := by
  intro l
  exact inc_step l r

lemma leaf0_side (r : ListBlank (Fin 2)) : Side true ([0, 0, 0] +> r) ([0, 1, 1] +> r) := by
  intro l
  exact leaf0_step l r

lemma leaf1_side (r : ListBlank (Fin 2)) :
    Side true ([0, 0, 1, 0, 0] +> r) ([1, 0, 1, 0, 0] +> r) := by
  intro l
  exact leaf1_step l r

lemma stop_halt (r : ListBlank (Fin 2)) : SideHalt ([0, 0, 1, 1] +> r) := by
  intro l
  exact ⟨(([1, 1, 1, 0] : List (Fin 2)) +> l) {{F}}> ([1] +> r),
    stop_step l r, stop_isNone l r⟩

lemma default_eq_zero_one :
    (default : ListBlank (Fin 2)) = ([0] : List (Fin 2)) +> default := by
  simp [zero_cons_default]

lemma default_eq_zero_three :
    (default : ListBlank (Fin 2)) = ([0, 0, 0] : List (Fin 2)) +> default := by
  simp [zero_cons_default]

lemma emit_side (b : Bool) {r r' : ListBlank (Fin 2)} (h : Side b r r') :
    (start r) [holdout_0451_tm]⊢* (start ((if b then [0, 1, 0] else W) +> r')) := by
  have h1 : (start r) [holdout_0451_tm]⊢*
      ((default : ListBlank (Fin 2)) <{{retState b}} ([1] +> r')) := h default
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, retState] at h1 ⊢
    have h2 : ((default : ListBlank (Fin 2)) <{{C}} ([1] +> r')) = start (W +> r') := by
      unfold start W
      simp only [append_cons_tape, append_nil_tape, Turing.ListBlank.head_cons,
        Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default]
    rw [← h2]
    exact h1
  · simp only [↓reduceIte, retState] at h1 ⊢
    exact reaches_trans h1 (emit_true_step r')

lemma init_reaches_start :
    (init [] : Cfg (Fin 2) (Fin 6)) [holdout_0451_tm]⊢* (denote_state 2 []) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : ListBlank (Fin 2)) {{A}}> default) := rfl
  rw [h0]
  unfold denote_state start words_tape W
  dsimp [ListBlank.append, list_nat_repeat]
  execute

-- ============================================================================
-- Section 7: Inductive Batch Relation & Proofs (ported from TM91)
-- ============================================================================

inductive Batch : ℕ → List (Bool × ℕ) → ℕ → List (Bool × ℕ) → Prop
  | BNil : Batch 0 [] 0 []
  | BCons (t : ℕ) (p : Bool) (n : ℕ) (xs : List (Bool × ℕ))
      (k : ℕ) (p' : Bool) (f : ℕ) (ys : List (Bool × ℕ)) (m : ℕ) :
      t + bval p = k * 2 + bval p' →
      Batch k xs f ys →
      (k = 0 ∨ k + 2 ≤ n + bval (first_cell xs) + bval (first_cell ys)) →
      m + k * 2 = n + f →
      Batch t ((p, n) :: xs) (k * 2) ((p', m) :: ys)

lemma batch_head {t : ℕ} {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch t xs e ys) : t + bval (first_cell xs) = e + bval (first_cell ys) := by
  cases h with
  | BNil => rfl
  | BCons t p n xs k p' f ys m hcount _ _ _ =>
    simpa [first_cell] using! hcount

lemma batch_even {t : ℕ} {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch t xs e ys) : ∃ k, e = k * 2 := by
  cases h with
  | BNil => exact ⟨0, rfl⟩
  | BCons _ _ _ _ k _ _ _ _ _ _ _ _ => exact ⟨k, rfl⟩

lemma batch_nil {t e : ℕ} {ys : List (Bool × ℕ)} (h : Batch t [] e ys) :
    t = 0 ∧ e = 0 ∧ ys = [] := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

lemma batch_refl (xs : List (Bool × ℕ)) : Batch 0 xs 0 xs := by
  induction xs with
  | nil => exact Batch.BNil
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    exact Batch.BCons 0 p n tl 0 p 0 tl n (by omega) ih (Or.inl rfl) (by omega)

lemma batch_zero {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch 0 xs e ys) : e = 0 ∧ ys = xs := by
  induction xs generalizing e ys with
  | nil =>
    rcases batch_nil h with ⟨_, rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    rcases h with _ | ⟨_, _, _, _, k, p', f, zs, m, hcount, hB, _, hgap⟩
    have hk : k = 0 ∧ p' = p := by
      cases p <;> cases p' <;> simp [bval] at hcount ⊢ <;> omega
    rcases hk with ⟨rfl, rfl⟩
    rcases ih hB with ⟨rfl, rfl⟩
    have hm : m = n := by omega
    subst hm
    exact ⟨rfl, rfl⟩

lemma first_one {xs : List (Bool × ℕ)} {f : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch 1 xs f ys) :
    bval (first_cell xs) + bval (first_cell ys) = 1 ∧ f = bval (first_cell xs) * 2 := by
  have hh := batch_head h
  rcases batch_even h with ⟨k, rfl⟩
  cases hfx : first_cell xs <;> cases hfy : first_cell ys <;>
    simp [hfx, hfy, bval] at hh ⊢ <;> omega

lemma guard_positive {k : ℕ} {xs : List (Bool × ℕ)} {f : ℕ} {ys : List (Bool × ℕ)} {n : ℕ}
    (hk : 0 < k) (hB : Batch k xs f ys)
    (hG : k + 2 ≤ n + bval (first_cell xs) + bval (first_cell ys)) : 2 ≤ n := by
  have hh := batch_head hB
  rcases batch_even hB with ⟨j, rfl⟩
  cases hfx : first_cell xs <;> cases hfy : first_cell ys <;>
    simp [hfx, hfy, bval] at hh hG ⊢ <;> omega

lemma split_guard_step {k' n f1 b_tl b_zs b_tail : ℕ}
    (hF1 : b_tl + b_zs = 1) (hF2 : f1 = b_tl * 2) (hn2 : 2 ≤ n)
    (hG2 : (k' + 1) + 2 ≤ n + b_tl + b_tail) :
    k' + 2 ≤ (n - 2 + f1) + b_zs + b_tail := by
  omega

lemma batch_split {t : ℕ} {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch (t + 1) xs e ys) :
    ∃ f zs g, Batch 1 xs f zs ∧ Batch t zs g ys ∧ e = f + g := by
  induction xs generalizing t e ys with
  | nil =>
    have := (batch_nil h).1
    omega
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    have hhead := batch_head h
    rcases h with _ | ⟨_, _, _, _, k, p', f, tail, m, _, hB, hG, hgap⟩
    dsimp only [first_cell] at hhead
    cases p
    · -- p = false
      refine ⟨0, (true, n) :: tl, k * 2, ?_, ?_, by omega⟩
      · exact Batch.BCons 1 false n tl 0 true 0 tl n (by rfl) (batch_refl tl) (Or.inl rfl) (by omega)
      · exact Batch.BCons t true n tl k p' f tail m (by simp [bval] at hhead ⊢; omega) hB hG hgap
    · -- p = true
      have hkpos : 0 < k := by
        cases p' <;> simp [bval] at hhead <;> omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rcases ih hB with ⟨f1, zs, f2, hB1, hB2, rfl⟩
      rcases first_one hB1 with ⟨hF1, hF2⟩
      have hn2 : 2 ≤ n := by
        rcases hG with hG0 | hG2
        · omega
        · exact guard_positive (by omega) hB hG2
      refine ⟨2, (false, n - 2 + f1) :: zs, k' * 2, ?_, ?_, by omega⟩
      · exact Batch.BCons 1 true n tl 1 false f1 zs (n - 2 + f1)
          (by rfl) hB1 (by right; omega) (by omega)
      · exact Batch.BCons t false (n - 2 + f1) zs k' p' f2 tail m
          (by simp [bval] at hhead ⊢; omega) hB2
          (by
            rcases hG with hG0 | hG2
            · omega
            · by_cases hk' : k' = 0
              · left; exact hk'
              · right
                exact split_guard_step hF1 hF2 hn2 hG2)
          (by omega)

lemma batch_one {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch 1 xs e ys) :
    Side false (words_tape xs) ((W ^ e) +> words_tape ys) := by
  induction xs generalizing e ys with
  | nil =>
    have := (batch_nil h).1
    omega
  | cons hd tl ih =>
    rcases hd with ⟨p, n⟩
    rcases h with _ | ⟨_, _, _, _, k, p', f, tail, m, hcount, hB, hG, hgap⟩
    have hkp : k = bval p ∧ p' = !p := by
      cases p <;> cases p' <;> simp [bval] at hcount ⊢ <;> omega
    rcases hkp with ⟨rfl, rfl⟩
    cases p
    · -- p = false: k = 0, p' = true
      rcases batch_zero hB with ⟨rfl, htail⟩
      have hm : m = n := by simp [bval] at hgap; omega
      rw [htail, hm]
      simpa [words_tape, bit, bval] using! inc_side ((W ^ n) +> words_tape tl)
    · -- p = true: k = 1, p' = false
      have hn2 : 2 ≤ n := by
        rcases hG with hG0 | hG2
        · simp [bval] at hG0
        · exact guard_positive (by decide) hB hG2
      have h_ih := ih hB
      have h_wall := wall_side false (n - 2) h_ih
      have h_carry := carry_side false h_wall
      simp only [Bool.false_eq_true, ↓reduceIte] at h_carry
      have hlhs : ([0, 0, 1, 0, 1] : List (Fin 2)) +> ((W ^ (n - 2)) +> words_tape tl) =
          words_tape ((true, n) :: tl) := by
        have hn_eq : n = 2 + (n - 2) := by omega
        conv_rhs => rw [words_tape, hn_eq, pow_append_tape]
        rfl
      have hrhs : ([0, 1, 0, 1, 1] : List (Fin 2)) +>
          ((W ^ (n - 2)) +> ((W ^ f) +> words_tape tail)) =
          (W ^ (1 * 2)) +> words_tape ((false, m) :: tail) := by
        have hm_eq : m = (n - 2) + f := by simp [bval] at hgap; omega
        subst hm_eq
        rw [words_tape, pow_append_tape]
        rfl
      rw [hlhs, hrhs] at h_carry
      exact h_carry

lemma batch_one_start {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch 1 xs e ys) (k : ℕ) :
    (denote_state k xs) [holdout_0451_tm]⊢* (denote_state (k + 1 + e) ys) := by
  have h1 := wall_side false k (batch_one h)
  have h2 := emit_side false h1
  have hrhs : (W +> ((W ^ k) +> ((W ^ e) +> words_tape ys))) =
      (W ^ (k + 1 + e)) +> words_tape ys := by
    have hk1 : k + 1 + e = 1 + k + e := by omega
    rw [hk1, pow_append_tape, pow_append_tape]
    rfl
  unfold denote_state
  rw [← hrhs]
  exact h2

lemma batch_steps {t : ℕ} {xs : List (Bool × ℕ)} {e : ℕ} {ys : List (Bool × ℕ)}
    (h : Batch t xs e ys) (k : ℕ) :
    (denote_state k xs) [holdout_0451_tm]⊢* (denote_state (k + t + e) ys) := by
  induction t generalizing xs e ys k with
  | zero =>
    rcases batch_zero h with ⟨rfl, hys⟩
    subst hys
    simpa using! reaches_refl _
  | succ t ih =>
    rcases batch_split h with ⟨f, zs, g, hB1, hB2, rfl⟩
    have h1 := batch_one_start hB1 k
    have h2 := ih hB2 (k + 1 + f)
    have heq : k + 1 + f + t + g = k + (t + 1) + (f + g) := by omega
    rw [heq] at h2
    exact reaches_trans h1 h2


-- ============================================================================
-- Section 8: FastCells Block-Accelerated Direct Evaluator & Soundness
-- ============================================================================

noncomputable section
set_option quotPrecheck false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


@[simp] theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
@[simp] theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

lemma wall_halt_start (k : ℕ) {r : ListBlank (Fin 2)} (h : SideHalt r) :
    IsHaltFrom (start ((W ^ k) +> r)) :=
  wall_halt k h default
-- ============================================================================
-- Section 8: FastCells definitions (identical to test_block_76331.lean)
-- ============================================================================

inductive FastCells where
  | nil : FastCells
  | cell (p : Bool) (n : Nat) (rest : FastCells) : FastCells
  | block (B pow2B max_v v F_next : Nat) (ns : List Nat) (rest : FastCells) : FastCells

inductive PushRes where
  | mk (k : Nat) (xs : FastCells) : PushRes

inductive PopRes where
  | mk (b : Nat) (k : Nat) (xs : FastCells) : PopRes

inductive OptCells where
  | none : OptCells
  | some (k : Nat) (xs : FastCells) : OptCells

inductive CallOutcome where
  | Failed : CallOutcome
  | Returned (b : Bool) (k : Nat) (xs : FastCells) : CallOutcome
  | Stopped : CallOutcome

inductive FusedRes where
  | mk (t : Nat) (e : Nat) (k_extra : Nat) (ys : FastCells) : FusedRes

inductive StepRes where
  | halted : StepRes
  | running (sb : Bool) (k : Nat) (xs : FastCells) : StepRes

inductive PackAcc where
  | mk (tk : Nat) (req : Nat) (ys : FastCells) : PackAcc

local notation "bval(" p ")" => (Bool.rec 0 1 p : Nat)
local notation "natMin(" a ", " b ")" => (Bool.rec b a (Nat.ble a b) : Nat)
@[simp] theorem bval_false_eq : (bval(false)) = 0 := rfl
@[simp] theorem bval_true_eq : (bval(true)) = 1 := rfl
local macro "omega_fast" : tactic =>
  `(tactic| ((try simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_div_eq, nat_mod_eq,
    bval_false_eq, bval_true_eq] at *); omega))

def is_nil (xs : FastCells) : Bool :=
  FastCells.rec
    true
    (fun _ _ _ _ => false)
    (fun _ _ _ _ _ _ _ _ => false)
    xs

def first_bit (xs : FastCells) : Bool :=
  FastCells.rec
    false
    (fun p _ _ _ => p)
    (fun _ _ _ v _ _ _ _ => Nat.beq (Nat.mod v 2) 1)
    xs

def pop_top_of_block (B pow2B max_v v F_next : Nat) (ns : List Nat) (rest : FastCells) : FastCells :=
  List.rec
    rest
    (fun n0 tail_ns _ =>
      let p := Nat.beq (Nat.mod v 2) 1
      let v_next := Nat.div v 2
      let K2 := Nat.mul 2 v_next
      List.rec
        (FastCells.cell p (Nat.sub (Nat.add n0 F_next) K2) rest)
        (fun _ _ _ =>
          let F_child := Nat.mul 2 (Nat.div v_next 2)
          let m := Nat.sub (Nat.add n0 F_child) K2
          FastCells.cell p m (FastCells.block (Nat.sub B 1) (Nat.div pow2B 2) (Nat.div max_v 2) v_next F_next tail_ns rest))
        tail_ns)
    ns

def push_cell (p : Bool) (m k : Nat) (xs : FastCells) : PushRes :=
  let mk := Nat.add m k
  Bool.rec
    (PushRes.mk 0 (FastCells.cell false mk xs))
    (Bool.rec
      (PushRes.mk 0 (FastCells.cell true mk xs))
      (FastCells.rec
        (PushRes.mk 0 FastCells.nil)
        (fun p2 n2 rest _ =>
          Bool.rec
            (PushRes.mk (Nat.add 1 n2) rest)
            (PushRes.mk 0 (FastCells.cell true 0 (FastCells.cell true n2 rest)))
            p2)
        (fun B pow2B max_v v F_next ns rest _ =>
          Bool.rec
            (List.rec
              (PushRes.mk 0 rest)
              (fun n0 tail_ns _ =>
                let v_next := Nat.div v 2
                let K2 := Nat.mul 2 v_next
                List.rec
                  (PushRes.mk (Nat.add 1 (Nat.sub (Nat.add n0 F_next) K2)) rest)
                  (fun _ _ _ =>
                    let F_child := Nat.mul 2 (Nat.div v_next 2)
                    let m0 := Nat.sub (Nat.add n0 F_child) K2
                    PushRes.mk (Nat.add 1 m0) (FastCells.block (Nat.sub B 1) (Nat.div pow2B 2) (Nat.div max_v 2) v_next F_next tail_ns rest))
                  tail_ns)
              ns)
            (PushRes.mk 0 (FastCells.cell true 0 (FastCells.block B pow2B max_v v F_next ns rest)))
            (Nat.beq (Nat.mod v 2) 1))
        xs)
      (Nat.beq mk 0))
    p

def pop_cell_bit (k : Nat) (xs : FastCells) : PopRes :=
  Bool.rec
    (FastCells.rec
      (PopRes.mk 0 0 FastCells.nil)
      (fun p n rest _ =>
        Bool.rec (PopRes.mk 1 n rest) (PopRes.mk 0 n rest) p)
      (fun B pow2B max_v v F_next ns rest _ =>
        List.rec
          (PopRes.mk 0 0 rest)
          (fun n0 tail_ns _ =>
            let p := Nat.beq (Nat.mod v 2) 1
            let b_out := Bool.rec 1 0 p
            let v_next := Nat.div v 2
            let K2 := Nat.mul 2 v_next
            List.rec
              (PopRes.mk b_out (Nat.sub (Nat.add n0 F_next) K2) rest)
              (fun _ _ _ =>
                let F_child := Nat.mul 2 (Nat.div v_next 2)
                let m0 := Nat.sub (Nat.add n0 F_child) K2
                PopRes.mk b_out m0 (FastCells.block (Nat.sub B 1) (Nat.div pow2B 2) (Nat.div max_v 2) v_next F_next tail_ns rest))
              tail_ns)
          ns)
      xs)
    (PopRes.mk 0 0 (FastCells.cell false (Nat.sub k 1) xs))
    (Nat.ble 1 k)

-- Unpacking and Well-Formedness
def unpack_block (v F_next : Nat) (ns : List Nat) (rest : List (Bool × Nat)) : List (Bool × Nat) :=
  List.rec
    (fun _ => rest)
    (fun n0 tail_ns ih v =>
      let p := Nat.beq (Nat.mod v 2) 1
      let v_next := Nat.div v 2
      let K2 := Nat.mul 2 v_next
      let F_child := List.rec F_next (fun _ _ _ => Nat.mul 2 (Nat.div v_next 2)) tail_ns
      let m := Nat.sub (Nat.add n0 F_child) K2
      (p, m) :: ih v_next)
    ns v

def to_cells (xs : FastCells) : List (Bool × Nat) :=
  FastCells.rec
    []
    (fun p n _ ih => (p, n) :: ih)
    (fun _ _ _ v F_next ns _ ih => unpack_block v F_next ns ih)
    xs

def WF_ns (max_v F_next : Nat) : List Nat → Prop
  | [] => False
  | [n0] => ∀ v', v' ≤ max_v → 2 * (v' / 2) + 2 ≤ n0 + F_next
  | n0 :: n1 :: tail =>
      (∀ v', v' ≤ max_v → 2 * (v' / 2) + 2 ≤ n0 + 2 * ((v' / 2) / 2)) ∧
      WF_ns (max_v / 2) F_next (n1 :: tail)

def WF_block (pow2B max_v v F_next : Nat) (ns : List Nat) : Prop :=
  pow2B = 2 ^ ns.length ∧ v ≤ max_v ∧ WF_ns max_v F_next ns

def WF : FastCells → Prop
  | FastCells.nil => True
  | FastCells.cell _ _ rest => WF rest
  | FastCells.block _ pow2B max_v v F_next ns rest =>
      WF_block pow2B max_v v F_next ns ∧ WF rest

lemma bval_rec_eq (p : Bool) : (bval(p)) = bval p := by
  cases p <;> rfl

lemma wf_ns_mono {m1 m2 f1 f2 : Nat} {ns : List Nat}
    (hm : m1 ≤ m2) (hf : f1 ≤ f2) (h : WF_ns m2 f1 ns) : WF_ns m1 f2 ns := by
  induction ns generalizing m1 m2 with
  | nil => exact h
  | cons n0 tail ih =>
    cases tail with
    | nil =>
      intro v' hv'
      have := h v' (by omega_fast)
      omega_fast
    | cons n1 tail2 =>
      refine ⟨fun v' hv' => h.1 v' (by omega_fast), ?_⟩
      exact ih (by omega_fast) h.2

lemma first_cell_unpack_block (v F_next : Nat) (n0 : Nat) (tail : List Nat) (rest : List (Bool × Nat)) :
    first_cell (unpack_block v F_next (n0 :: tail) rest) = (Nat.beq (Nat.mod v 2) 1) := rfl

lemma first_bit_eq (xs : FastCells) (hwf : WF xs) :
    first_bit xs = first_cell (to_cells xs) := by
  cases xs with
  | nil => rfl
  | cell p n rest => rfl
  | block B pow2B max_v v F_next ns rest =>
    rcases hwf with ⟨⟨_, _, hns⟩, _⟩
    cases ns with
    | nil => contradiction
    | cons n0 tail => rfl

lemma pop_top_of_block_to_cells (B pow2B max_v v F_next : Nat) (ns : List Nat) (rest : FastCells) :
    to_cells (pop_top_of_block B pow2B max_v v F_next ns rest) =
    unpack_block v F_next ns (to_cells rest) := by
  cases ns with
  | nil => rfl
  | cons n0 tail_ns =>
    cases tail_ns <;> rfl

lemma pow2_div2_cons (n1 : Nat) (tail : List Nat) :
    (2 ^ (n1 :: tail).length * 2) / 2 = 2 ^ (n1 :: tail).length := by
  omega_fast

lemma pop_top_of_block_wf (B pow2B max_v v F_next : Nat) (ns : List Nat) (rest : FastCells)
    (hb : WF_block pow2B max_v v F_next ns) (hr : WF rest) :
    WF (pop_top_of_block B pow2B max_v v F_next ns rest) := by
  rcases hb with ⟨hpow, hv, hns⟩
  cases ns with
  | nil => contradiction
  | cons n0 tail_ns =>
    cases tail_ns with
    | nil => exact hr
    | cons n1 tail2 =>
      refine ⟨⟨?_, by omega_fast, hns.2⟩, hr⟩
      rw [hpow, List.length_cons, Nat.pow_succ]
      omega_fast

def prepend_cell_to_packed (p : Bool) (raw_n : Nat) (ys : FastCells) : FastCells :=
  let bp := bval(p)
  FastCells.rec
    (FastCells.block 1 2 (Nat.sub raw_n 2) bp 0 [raw_n] FastCells.nil)
    (fun q m rest _ =>
      FastCells.block 1 2 (Nat.sub raw_n 2) bp 0 [raw_n] (FastCells.cell q m rest))
    (fun B pow2B max_v v F_next ns rest _ =>
      let n_new := Nat.sub (Nat.add raw_n (Nat.mul 2 v)) (Nat.mul 2 (Nat.div v 2))
      let v_new := Nat.add (Nat.mul 2 v) bp
      let lim0 := Nat.add v_new (Nat.mul 2 (Nat.sub raw_n 3))
      let lim_rest := Nat.add (Nat.mul 2 max_v) 1
      let B1 := Nat.add B 1
      let pow2B2 := Nat.mul 2 pow2B
      let ns1 := n_new :: ns
      Bool.rec
        (FastCells.block B1 pow2B2 lim_rest v_new F_next ns1 rest)
        (FastCells.block B1 pow2B2 lim0 v_new F_next ns1 rest)
        (Nat.ble lim0 lim_rest))
    ys

def repack_step (p : Bool) (raw_n : Nat) (acc : PackAcc) : PackAcc :=
  PackAcc.rec
    (fun tk req ys =>
      let req2 := Nat.mul 2 req
      Bool.rec
        (Bool.rec
          (PackAcc.mk 0 req2 (FastCells.cell p raw_n ys))
          (PackAcc.mk 0 req2 (prepend_cell_to_packed p raw_n ys))
          (and (Nat.ble 4 raw_n) (Nat.ble req raw_n)))
        (PackAcc.mk (Nat.sub tk 1) req2 (FastCells.cell p raw_n ys))
        (Nat.ble 1 tk))
    acc

def repack_block (v F_next : Nat) (ns : List Nat) (acc : PackAcc) : PackAcc :=
  List.rec
    (fun _ => acc)
    (fun n0 tail_ns ih v =>
      let p := Nat.beq (Nat.mod v 2) 1
      let v_next := Nat.div v 2
      let K2 := Nat.mul 2 v_next
      let F_child := List.rec F_next (fun _ _ _ => Nat.mul 2 (Nat.div v_next 2)) tail_ns
      let m := Nat.sub (Nat.add n0 F_child) K2
      repack_step p m (ih v_next))
    ns v

def repack_block_smart (B pow2B max_v v F_next : Nat) (ns : List Nat) (acc : PackAcc) : PackAcc :=
  PackAcc.rec
    (fun tk req ys =>
      Bool.rec
        (repack_block v F_next ns (PackAcc.mk tk req ys))
        (PackAcc.mk 0 (Nat.mul req pow2B) (FastCells.block B pow2B max_v v F_next ns ys))
        (and (Nat.ble 6 B) (Nat.ble (Nat.add v (Nat.mul (Nat.div req 2) pow2B)) max_v)))
    acc

def unroll_top_1 (ys : FastCells) : FastCells :=
  FastCells.rec
    FastCells.nil
    (fun p n rest _ => FastCells.cell p n rest)
    (fun B pow2B max_v v F_next ns rest _ =>
      pop_top_of_block B pow2B max_v v F_next ns rest)
    ys

def unroll_top_2 (ys : FastCells) : FastCells :=
  FastCells.rec
    FastCells.nil
    (fun p n rest _ => FastCells.cell p n (unroll_top_1 rest))
    (fun _ _ _ _ _ _ _ _ => ys)
    (unroll_top_1 ys)

def repack_cells (init_req : Nat) (xs : FastCells) : FastCells :=
  PackAcc.rec
    (fun _ _ ys => unroll_top_2 ys)
    (FastCells.rec
      (PackAcc.mk 1 init_req FastCells.nil)
      (fun p n _ ih => repack_step p n ih)
      (fun B pow2B max_v v F_next ns _ ih => repack_block_smart B pow2B max_v v F_next ns ih)
      xs)

lemma prepend_cell_to_packed_spec (p : Bool) (raw_n : Nat) (ys : FastCells)
    (hr : 4 ≤ raw_n) (hwf : WF ys) :
    to_cells (prepend_cell_to_packed p raw_n ys) = (p, raw_n) :: to_cells ys ∧
    WF (prepend_cell_to_packed p raw_n ys) := by
  cases ys with
  | nil =>
    cases p <;> refine ⟨rfl, ⟨rfl, by omega_fast, fun v' hv' => by omega_fast⟩, trivial⟩
  | cell q m rest =>
    cases p <;> refine ⟨rfl, ⟨rfl, by omega_fast, fun v' hv' => by omega_fast⟩, hwf⟩
  | block B pow2B max_v v F_next ns rest =>
    rcases hwf with ⟨⟨hpow, hv, hns⟩, hrest⟩
    cases ns with
    | nil => contradiction
    | cons n1 tail =>
      unfold prepend_cell_to_packed
      dsimp only
      have hp_mod : Nat.beq (Nat.mod (Nat.add (Nat.mul 2 v) (bval(p))) 2) 1 = p := by
        cases p <;> simp [Nat.beq] <;> omega
      have hv_div : Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2 = v := by
        cases p <;> dsimp <;> omega
      have hm_eq : Nat.sub (Nat.add (Nat.sub (Nat.add raw_n (Nat.mul 2 v)) (Nat.mul 2 (Nat.div v 2)))
          (Nat.mul 2 (Nat.div v 2))) (Nat.mul 2 v) = raw_n := by
        change (((raw_n + 2 * v) - 2 * (v / 2)) + 2 * (v / 2)) - 2 * v = raw_n
        omega_fast
      have hpow2 : Nat.mul 2 pow2B = 2 ^ (Nat.sub (Nat.add raw_n (Nat.mul 2 v)) (Nat.mul 2 (Nat.div v 2)) :: n1 :: tail).length := by
        rw [hpow, List.length_cons, Nat.pow_succ]
        change 2 * 2 ^ (n1 :: tail).length = 2 ^ (n1 :: tail).length * 2
        omega_fast
      cases hble : Nat.ble (Nat.add (Nat.add (Nat.mul 2 v) (bval(p))) (Nat.mul 2 (Nat.sub raw_n 3)))
          (Nat.add (Nat.mul 2 max_v) 1)
      · -- lim0 > lim_rest, so max_v' = lim_rest
        dsimp only
        have hle_gt : (2 * max_v + 1) < (2 * v + (bval(p))) + 2 * (raw_n - 3) := by
          have hnot : ¬ (Nat.add (Nat.add (Nat.mul 2 v) (bval(p))) (Nat.mul 2 (Nat.sub raw_n 3)) ≤ Nat.add (Nat.mul 2 max_v) 1) :=
            fun h => by rw [Nat.ble_eq.mpr h] at hble; contradiction
          omega_fast
        refine ⟨?_, ⟨hpow2, ?_, ?_, ?_⟩, hrest⟩
        · change (Nat.beq (Nat.mod (Nat.add (Nat.mul 2 v) (bval(p))) 2) 1,
            Nat.sub (Nat.add (Nat.sub (Nat.add raw_n (Nat.mul 2 v)) (Nat.mul 2 (Nat.div v 2)))
              (Nat.mul 2 (Nat.div (Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2) 2)))
              (Nat.mul 2 (Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2))) ::
            unpack_block (Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2) F_next (n1 :: tail) (to_cells rest) = _
          rw [hp_mod, hv_div, hm_eq]
          rfl
        · cases p <;> dsimp [Nat.add, Nat.mul] <;> omega
        · intro v' hv'
          change v' ≤ 2 * max_v + 1 at hv'
          change 2 * (v' / 2) + 2 ≤ ((raw_n + 2 * v) - 2 * (v / 2)) + 2 * ((v' / 2) / 2)
          cases p <;> dsimp at hle_gt <;> omega
        · exact wf_ns_mono (by change (2 * max_v + 1) / 2 ≤ max_v; omega_fast) (Nat.le_refl _) hns
      · -- lim0 ≤ lim_rest, so max_v' = lim0
        dsimp only
        have hle_le : (2 * v + (bval(p))) + 2 * (raw_n - 3) ≤ 2 * max_v + 1 := by
          exact Nat.ble_eq.mp hble
        refine ⟨?_, ⟨hpow2, ?_, ?_, ?_⟩, hrest⟩
        · change (Nat.beq (Nat.mod (Nat.add (Nat.mul 2 v) (bval(p))) 2) 1,
            Nat.sub (Nat.add (Nat.sub (Nat.add raw_n (Nat.mul 2 v)) (Nat.mul 2 (Nat.div v 2)))
              (Nat.mul 2 (Nat.div (Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2) 2)))
              (Nat.mul 2 (Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2))) ::
            unpack_block (Nat.div (Nat.add (Nat.mul 2 v) (bval(p))) 2) F_next (n1 :: tail) (to_cells rest) = _
          rw [hp_mod, hv_div, hm_eq]
          rfl
        · cases p <;> dsimp [Nat.add, Nat.mul, Nat.sub] <;> omega
        · intro v' hv'
          change v' ≤ (2 * v + (bval(p))) + 2 * (raw_n - 3) at hv'
          change 2 * (v' / 2) + 2 ≤ ((raw_n + 2 * v) - 2 * (v / 2)) + 2 * ((v' / 2) / 2)
          cases p <;> dsimp at hv' <;> omega
        · exact wf_ns_mono (by
            change ((2 * v + (bval(p))) + 2 * (raw_n - 3)) / 2 ≤ max_v
            cases p <;> dsimp at hle_le ⊢ <;> omega) (Nat.le_refl _) hns

def acc_cells : PackAcc → List (Bool × Nat)
  | PackAcc.mk _ _ ys => to_cells ys

def acc_wf : PackAcc → Prop
  | PackAcc.mk _ _ ys => WF ys

lemma repack_step_spec (p : Bool) (raw_n : Nat) (acc : PackAcc) (hwf : acc_wf acc) :
    acc_cells (repack_step p raw_n acc) = (p, raw_n) :: acc_cells acc ∧
    acc_wf (repack_step p raw_n acc) := by
  rcases acc with ⟨tk, req, ys⟩
  unfold repack_step
  dsimp only
  cases Nat.ble 1 tk
  · dsimp only
    cases hcond : (and (Nat.ble 4 raw_n) (Nat.ble req raw_n))
    · exact ⟨rfl, hwf⟩
    · dsimp only
      have hr4 : 4 ≤ raw_n := by
        have : Nat.ble 4 raw_n = true := by
          cases h4 : Nat.ble 4 raw_n
          · rw [h4] at hcond; contradiction
          · rfl
        exact Nat.ble_eq.mp this
      exact prepend_cell_to_packed_spec p raw_n ys hr4 hwf
  · exact ⟨rfl, hwf⟩

lemma repack_block_spec (v F_next : Nat) (ns : List Nat) (acc : PackAcc) (hwf : acc_wf acc) :
    acc_cells (repack_block v F_next ns acc) = unpack_block v F_next ns (acc_cells acc) ∧
    acc_wf (repack_block v F_next ns acc) := by
  induction ns generalizing v with
  | nil => exact ⟨rfl, hwf⟩
  | cons n0 tail_ns ih =>
    rcases ih (Nat.div v 2) with ⟨ih_c, ih_w⟩
    rcases repack_step_spec (Nat.beq (Nat.mod v 2) 1)
      (Nat.sub (Nat.add n0 (List.rec F_next (fun _ _ _ => Nat.mul 2 (Nat.div (Nat.div v 2) 2)) tail_ns))
        (Nat.mul 2 (Nat.div v 2)))
      (repack_block (Nat.div v 2) F_next tail_ns acc) ih_w with ⟨hs_c, hs_w⟩
    refine ⟨?_, hs_w⟩
    change acc_cells (repack_step (Nat.beq (Nat.mod v 2) 1)
      (Nat.sub (Nat.add n0 (List.rec F_next (fun _ _ _ => Nat.mul 2 (Nat.div (Nat.div v 2) 2)) tail_ns))
        (Nat.mul 2 (Nat.div v 2)))
      (repack_block (Nat.div v 2) F_next tail_ns acc)) = _
    rw [hs_c, ih_c]
    rfl

lemma repack_block_smart_spec (B pow2B max_v v F_next : Nat) (ns : List Nat) (acc : PackAcc)
    (hb : WF_block pow2B max_v v F_next ns) (hwf : acc_wf acc) :
    acc_cells (repack_block_smart B pow2B max_v v F_next ns acc) =
      unpack_block v F_next ns (acc_cells acc) ∧
    acc_wf (repack_block_smart B pow2B max_v v F_next ns acc) := by
  rcases acc with ⟨tk, req, ys⟩
  unfold repack_block_smart
  dsimp only
  cases (and (Nat.ble 6 B) (Nat.ble (Nat.add v (Nat.mul (Nat.div req 2) pow2B)) max_v))
  · exact repack_block_spec v F_next ns (PackAcc.mk tk req ys) hwf
  · exact ⟨rfl, hb, hwf⟩

lemma unroll_top_1_spec (ys : FastCells) (hwf : WF ys) :
    to_cells (unroll_top_1 ys) = to_cells ys ∧ WF (unroll_top_1 ys) := by
  cases ys with
  | nil => exact ⟨rfl, trivial⟩
  | cell p n rest => exact ⟨rfl, hwf⟩
  | block B pow2B max_v v F_next ns rest =>
    exact ⟨pop_top_of_block_to_cells B pow2B max_v v F_next ns rest,
      pop_top_of_block_wf B pow2B max_v v F_next ns rest hwf.1 hwf.2⟩

lemma unroll_top_2_spec (ys : FastCells) (hwf : WF ys) :
    to_cells (unroll_top_2 ys) = to_cells ys ∧ WF (unroll_top_2 ys) := by
  rcases unroll_top_1_spec ys hwf with ⟨h1_c, h1_w⟩
  unfold unroll_top_2
  generalize hu1 : unroll_top_1 ys = u1 at h1_c h1_w
  cases u1 with
  | nil => exact ⟨h1_c, trivial⟩
  | cell p n rest =>
    rcases unroll_top_1_spec rest h1_w with ⟨h2_c, h2_w⟩
    dsimp only
    change (p, n) :: to_cells (unroll_top_1 rest) = to_cells ys ∧ WF (unroll_top_1 rest)
    rw [h2_c]
    exact ⟨h1_c, h2_w⟩
  | block B pow2B max_v v F_next ns rest =>
    exact ⟨rfl, hwf⟩

def repack_fold (init_req : Nat) (xs : FastCells) : PackAcc :=
  FastCells.rec (PackAcc.mk 1 init_req FastCells.nil)
    (fun p n _ ih => repack_step p n ih)
    (fun B pow2B max_v v F_next ns _ ih => repack_block_smart B pow2B max_v v F_next ns ih) xs

lemma repack_cells_spec (init_req : Nat) (xs : FastCells) (hwf : WF xs) :
    to_cells (repack_cells init_req xs) = to_cells xs ∧ WF (repack_cells init_req xs) := by
  have hfold : ∀ xs, WF xs →
      acc_cells (repack_fold init_req xs) = to_cells xs ∧ acc_wf (repack_fold init_req xs) := by
    intro xs hwf
    induction xs with
    | nil => exact ⟨rfl, trivial⟩
    | cell p n rest ih =>
      rcases ih hwf with ⟨ih_c, ih_w⟩
      rcases repack_step_spec p n (repack_fold init_req rest) ih_w with ⟨hs_c, hs_w⟩
      change acc_cells (repack_step p n (repack_fold init_req rest)) = _ ∧
        acc_wf (repack_step p n (repack_fold init_req rest))
      rw [ih_c] at hs_c
      exact ⟨hs_c, hs_w⟩
    | block B pow2B max_v v F_next ns rest ih =>
      rcases ih hwf.2 with ⟨ih_c, ih_w⟩
      rcases repack_block_smart_spec B pow2B max_v v F_next ns (repack_fold init_req rest) hwf.1 ih_w with ⟨hs_c, hs_w⟩
      change acc_cells (repack_block_smart B pow2B max_v v F_next ns (repack_fold init_req rest)) = _ ∧
        acc_wf (repack_block_smart B pow2B max_v v F_next ns (repack_fold init_req rest))
      rw [ih_c] at hs_c
      exact ⟨hs_c, hs_w⟩
  rcases hfold xs hwf with ⟨hf_c, hf_w⟩
  change PackAcc.rec (fun _ _ ys => to_cells (unroll_top_2 ys) = to_cells xs ∧ WF (unroll_top_2 ys)) (repack_fold init_req xs)
  generalize hacc : repack_fold init_req xs = acc at hf_c hf_w
  rcases acc with ⟨tk, req, ys⟩
  rcases unroll_top_2_spec ys hf_w with ⟨hu_c, hu_w⟩
  dsimp only
  rw [hu_c]
  exact ⟨hf_c, hu_w⟩

def push_spec (p : Bool) (m k : Nat) (xs : FastCells) : PushRes → Prop
  | PushRes.mk k' xs' =>
    (W ^ k') +> words_tape (to_cells xs') =
      (bit p) +> ((W ^ (m + k)) +> words_tape (to_cells xs)) ∧ WF xs'

lemma push_cell_fast_spec (p : Bool) (m k : Nat) (xs : FastCells) (hwf : WF xs) :
    push_spec p m k xs (push_cell p m k xs) := by
  unfold push_cell
  dsimp only
  cases p
  · exact ⟨rfl, hwf⟩
  · dsimp only
    cases hmk : Nat.beq (Nat.add m k) 0
    · exact ⟨rfl, hwf⟩
    · dsimp only
      have hmk0 : m + k = 0 := Nat.beq_eq.mp hmk
      cases xs with
      | nil =>
        refine ⟨?_, trivial⟩
        rw [hmk0]
        dsimp [W, words_tape, bit, list_nat_repeat, to_cells]
        exact zero_cons_default.symm
      | cell p2 n2 rest =>
        cases p2
        · refine ⟨?_, hwf⟩
          rw [hmk0]
          dsimp [to_cells, words_tape, bit, list_nat_repeat]
          rw [pow_append_tape W 1 n2]
          rfl
        · refine ⟨?_, hwf⟩
          rw [hmk0]
          rfl
      | block B pow2B max_v v F_next ns rest =>
        dsimp only
        rcases hwf with ⟨⟨hpow, hv, hns⟩, hrest⟩
        cases hp2 : Nat.beq (Nat.mod v 2) 1
        · dsimp only
          cases ns with
          | nil => contradiction
          | cons n0 tail_ns =>
            cases tail_ns with
            | nil =>
              refine ⟨?_, hrest⟩
              rw [hmk0]
              dsimp only [to_cells, unpack_block, words_tape, nat_add_eq]
              rw [hp2, pow_append_tape W 1]
              rfl
            | cons n1 tail2 =>
              refine ⟨?_, ⟨?_, by omega_fast, hns.2⟩, hrest⟩
              · rw [hmk0]
                dsimp only [to_cells, unpack_block, words_tape, nat_add_eq]
                rw [hp2, pow_append_tape W 1]
                rfl
              · rw [hpow, List.length_cons, Nat.pow_succ]
                omega_fast
        · refine ⟨?_, ⟨hpow, hv, hns⟩, hrest⟩
          rw [hmk0]
          rfl

def nat_bit (b : Nat) : Fin 2 := if Nat.beq b 0 then 0 else 1

lemma bit_eq_nat_bit (p : Bool) : bit p = [nat_bit (Bool.rec 1 0 p)] := by
  cases p <;> rfl

lemma bit_beq_zero (b : Nat) : bit (Nat.beq b 0) = [nat_bit b] := by
  unfold nat_bit
  cases Nat.beq b 0 <;> rfl

def pop_spec (k : Nat) (xs : FastCells) : PopRes → Prop
  | PopRes.mk b' k' xs' =>
    (W ^ k) +> words_tape (to_cells xs) =
      (nat_bit b') >> ((W ^ k') +> words_tape (to_cells xs')) ∧ WF xs'

lemma pop_cell_bit_fast_spec (k : Nat) (xs : FastCells) (hwf : WF xs) :
    pop_spec k xs (pop_cell_bit k xs) := by
  unfold pop_cell_bit
  cases hk : Nat.ble 1 k
  · dsimp only
    have hk0 : k = 0 := by
      have hnot : ¬ (1 ≤ k) := fun h => by rw [Nat.ble_eq.mpr h] at hk; contradiction
      omega_fast
    cases xs with
    | nil =>
      refine ⟨?_, trivial⟩
      rw [hk0]
      dsimp [W, words_tape, list_nat_repeat, to_cells, nat_bit]
      exact zero_cons_default.symm
    | cell p n rest =>
      cases p <;> (refine ⟨?_, hwf⟩; rw [hk0]; rfl)
    | block B pow2B max_v v F_next ns rest =>
      dsimp only
      rcases hwf with ⟨⟨hpow, hv, hns⟩, hrest⟩
      cases ns with
      | nil => contradiction
      | cons n0 tail_ns =>
        cases tail_ns with
        | nil =>
          refine ⟨?_, hrest⟩
          rw [hk0]
          dsimp only [to_cells, unpack_block, words_tape]
          rw [bit_eq_nat_bit]
          rfl
        | cons n1 tail2 =>
          refine ⟨?_, ⟨?_, by omega_fast, hns.2⟩, hrest⟩
          · rw [hk0]
            dsimp only [to_cells, unpack_block, words_tape]
            rw [bit_eq_nat_bit]
            rfl
          · rw [hpow, List.length_cons, Nat.pow_succ]
            omega_fast
  · dsimp only
    have hk1 : 1 ≤ k := Nat.ble_eq.mp hk
    refine ⟨?_, hwf⟩
    have hk_eq : W ^ k = W ^ (1 + (k - 1)) := by congr 1; omega_fast
    rw [hk_eq, pow_append_tape W 1 (k - 1)]
    rfl

def remove_word (w : List Nat) (k : Nat) (xs : FastCells) : OptCells :=
  List.rec
    (fun k xs => OptCells.some k xs)
    (fun b _ ih k xs =>
      PopRes.rec (fun b' k' xs' =>
        Bool.rec OptCells.none (ih k' xs') (Nat.beq b b'))
        (pop_cell_bit k xs))
    w k xs

def put_word (w : List Nat) (k : Nat) (xs : FastCells) : PushRes :=
  List.rec
    (PushRes.mk k xs)
    (fun b _ ih =>
      PushRes.rec (fun k' xs' =>
        push_cell (Nat.beq b 0) 0 k' xs')
        ih)
    w

lemma remove_word_fast_spec (w : List Nat) (k : Nat) (xs : FastCells) (hwf : WF xs)
    (k' : Nat) (ys : FastCells) (h : remove_word w k xs = OptCells.some k' ys) :
    (W ^ k) +> words_tape (to_cells xs) =
      (w.map nat_bit) +> ((W ^ k') +> words_tape (to_cells ys)) ∧ WF ys := by
  induction w generalizing k xs with
  | nil =>
    injection h with hk hys
    subst hk hys
    exact ⟨rfl, hwf⟩
  | cons b w ih =>
    unfold remove_word at h
    dsimp only at h
    have hp := pop_cell_bit_fast_spec k xs hwf
    generalize hpop : pop_cell_bit k xs = pop_res at h hp
    rcases pop_res with ⟨b', k1, xs1⟩
    rcases hp with ⟨hp_t, hp_w⟩
    dsimp only at h
    cases hbeq : Nat.beq b b'
    · rw [hbeq] at h; contradiction
    · rw [hbeq] at h
      dsimp only at h
      have hbb' : b = b' := Nat.beq_eq.mp hbeq
      subst hbb'
      rcases ih k1 xs1 hp_w h with ⟨ih_t, ih_w⟩
      rw [hp_t, ih_t]
      exact ⟨rfl, ih_w⟩

def put_word_spec_prop (w : List Nat) (k : Nat) (xs : FastCells) : PushRes → Prop
  | PushRes.mk k' xs' =>
    (W ^ k') +> words_tape (to_cells xs') =
      (w.map nat_bit) +> ((W ^ k) +> words_tape (to_cells xs)) ∧ WF xs'

lemma put_word_fast_spec (w : List Nat) (k : Nat) (xs : FastCells) (hwf : WF xs) :
    put_word_spec_prop w k xs (put_word w k xs) := by
  induction w with
  | nil => exact ⟨rfl, hwf⟩
  | cons b w ih =>
    change PushRes.rec (fun k1 xs1 => put_word_spec_prop (b :: w) k xs (push_cell (Nat.beq b 0) 0 k1 xs1)) (put_word w k xs)
    generalize hpw : put_word w k xs = pw_res at ih
    rcases pw_res with ⟨k1, xs1⟩
    rcases ih with ⟨ih_t, ih_w⟩
    dsimp only
    have hpc := push_cell_fast_spec (Nat.beq b 0) 0 k1 xs1 ih_w
    generalize hpush : push_cell (Nat.beq b 0) 0 k1 xs1 = push_res at hpc
    rcases push_res with ⟨k', xs'⟩
    rcases hpc with ⟨hpc_t, hpc_w⟩
    rw [Nat.zero_add, bit_beq_zero, ih_t] at hpc_t
    exact ⟨hpc_t, hpc_w⟩

lemma bval_beq_mod2 (x : Nat) : bval (Nat.beq (Nat.mod x 2) 1) = x % 2 := by
  by_cases h : x % 2 = 1
  · have hb : Nat.beq (Nat.mod x 2) 1 = true := Nat.beq_eq.mpr h
    rw [hb]; dsimp [bval]; omega_fast
  · have h0 : x % 2 = 0 := by omega_fast
    have hb : Nat.beq (Nat.mod x 2) 1 = false := by
      cases hbeq : Nat.beq (Nat.mod x 2) 1
      · rfl
      · exfalso; exact h (Nat.beq_eq.mp hbeq)
    rw [hb]; dsimp [bval]; omega_fast

lemma unpack_block_batch (ns : List Nat) (v v_new max_v F_next f : Nat) (rest ys_rest : List (Bool × Nat))
    (hle : v ≤ v_new) (hv : v_new ≤ max_v) (hwf : WF_ns max_v F_next ns)
    (hB : Batch (v_new / (2 ^ ns.length) - v / (2 ^ ns.length)) rest f ys_rest) :
    Batch (v_new - v) (unpack_block v F_next ns rest)
      (2 * (v_new / 2 - v / 2)) (unpack_block v_new (F_next + f) ns ys_rest) := by
  induction ns generalizing v v_new max_v with
  | nil => contradiction
  | cons n0 tail_ns ih =>
    cases tail_ns with
    | nil =>
      change Batch (v_new / 2 - v / 2) rest f ys_rest at hB
      have hns0 := hwf v_new hv
      have he_eq : 2 * (v_new / 2 - v / 2) = (v_new / 2 - v / 2) * 2 := by omega_fast
      rw [he_eq]
      apply Batch.BCons (v_new - v) (Nat.beq (Nat.mod v 2) 1)
        (Nat.sub (Nat.add n0 F_next) (Nat.mul 2 (Nat.div v 2))) rest
        (v_new / 2 - v / 2) (Nat.beq (Nat.mod v_new 2) 1) f ys_rest
        (Nat.sub (Nat.add n0 (F_next + f)) (Nat.mul 2 (Nat.div v_new 2)))
      · rw [bval_beq_mod2, bval_beq_mod2]; omega_fast
      · exact hB
      · right
        change (v_new / 2 - v / 2) + 2 ≤ ((n0 + F_next) - 2 * (v / 2)) + bval (first_cell rest) + bval (first_cell ys_rest)
        omega_fast
      · change ((n0 + (F_next + f)) - 2 * (v_new / 2)) + (v_new / 2 - v / 2) * 2 = ((n0 + F_next) - 2 * (v / 2)) + f
        omega_fast
    | cons n1 tail2 =>
      rcases hwf with ⟨hns0, hns_tail⟩
      have hdiv_eq : ∀ x : Nat, x / (2 ^ (n0 :: n1 :: tail2).length) = (x / 2) / (2 ^ (n1 :: tail2).length) := by
        intro x
        rw [List.length_cons, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [hdiv_eq v_new, hdiv_eq v] at hB
      have h_ih := ih (v / 2) (v_new / 2) (max_v / 2) (by omega_fast) (by omega_fast) hns_tail hB
      have he_eq : 2 * (v_new / 2 - v / 2) = (v_new / 2 - v / 2) * 2 := by omega_fast
      rw [he_eq]
      apply Batch.BCons (v_new - v) (Nat.beq (Nat.mod v 2) 1)
        (Nat.sub (Nat.add n0 (Nat.mul 2 (Nat.div (Nat.div v 2) 2))) (Nat.mul 2 (Nat.div v 2)))
        (unpack_block (v / 2) F_next (n1 :: tail2) rest)
        (v_new / 2 - v / 2) (Nat.beq (Nat.mod v_new 2) 1)
        (2 * ((v_new / 2) / 2 - (v / 2) / 2))
        (unpack_block (v_new / 2) (F_next + f) (n1 :: tail2) ys_rest)
        (Nat.sub (Nat.add n0 (Nat.mul 2 (Nat.div (Nat.div v_new 2) 2))) (Nat.mul 2 (Nat.div v_new 2)))
      · rw [bval_beq_mod2, bval_beq_mod2]; omega_fast
      · exact h_ih
      · right
        rw [first_cell_unpack_block, first_cell_unpack_block, bval_beq_mod2, bval_beq_mod2]
        have := hns0 v_new hv
        change (v_new / 2 - v / 2) + 2 ≤
          ((n0 + 2 * ((v / 2) / 2)) - 2 * (v / 2)) + (v / 2) % 2 + (v_new / 2) % 2
        omega_fast
      · have := hns0 v_new hv
        change ((n0 + 2 * ((v_new / 2) / 2)) - 2 * (v_new / 2)) + (v_new / 2 - v / 2) * 2 =
          ((n0 + 2 * ((v / 2) / 2)) - 2 * (v / 2)) + 2 * ((v_new / 2) / 2 - (v / 2) / 2)
        omega_fast

lemma unpack_block_absorb_extra (ns : List Nat) (v max_v F_next k_extra : Nat)
    (ys_norm ys_rest : List (Bool × Nat))
    (hv : v ≤ max_v) (hwf : WF_ns max_v F_next ns)
    (hW : (W ^ k_extra) +> words_tape ys_norm = words_tape ys_rest) :
    words_tape (unpack_block v (F_next + k_extra) ns ys_norm) =
    words_tape (unpack_block v F_next ns ys_rest) := by
  induction ns generalizing v max_v with
  | nil => contradiction
  | cons n0 tail_ns ih =>
    cases tail_ns with
    | nil =>
      have hns0 := hwf v hv
      have hm_eq : Nat.sub (Nat.add n0 (F_next + k_extra)) (Nat.mul 2 (Nat.div v 2)) =
          Nat.sub (Nat.add n0 F_next) (Nat.mul 2 (Nat.div v 2)) + k_extra := by
        change (n0 + (F_next + k_extra)) - 2 * (v / 2) = ((n0 + F_next) - 2 * (v / 2)) + k_extra
        omega_fast
      change (bit _) +> ((W ^ Nat.sub (Nat.add n0 (F_next + k_extra)) (Nat.mul 2 (Nat.div v 2))) +> words_tape ys_norm) =
        (bit _) +> ((W ^ Nat.sub (Nat.add n0 F_next) (Nat.mul 2 (Nat.div v 2))) +> words_tape ys_rest)
      rw [hm_eq, pow_append_tape, hW]
    | cons n1 tail2 =>
      rcases hwf with ⟨_, hns_tail⟩
      have h_ih := ih (v / 2) (max_v / 2) (by omega_fast) hns_tail
      change (bit _) +> ((W ^ _) +> words_tape (unpack_block (v / 2) (F_next + k_extra) (n1 :: tail2) ys_norm)) =
        (bit _) +> ((W ^ _) +> words_tape (unpack_block (v / 2) F_next (n1 :: tail2) ys_rest))
      rw [h_ih]


lemma pow2_pos (ns : List Nat) : 0 < 2 ^ ns.length := by
  induction ns with
  | nil => decide
  | cons _ tail ih => rw [List.length_cons, Nat.pow_succ]; omega_fast

lemma div_succ_of_mod_ne (v d : Nat) (hd : 0 < d) (hne : v % d + 1 ≠ d) :
    (v + 1) / d = v / d := by
  have hlt : v % d < d := Nat.mod_lt v hd
  have hlt2 : v % d + 1 < d := by omega_fast
  have h1 : v + 1 = d * (v / d) + (v % d + 1) := by
    have := Nat.div_add_mod v d
    omega_fast
  rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt hlt2, Nat.add_zero]

lemma div_succ_of_mod_eq (v d : Nat) (hd : 0 < d) (heq : v % d + 1 = d) :
    (v + 1) / d = v / d + 1 := by
  have h1 : v + 1 = d * (v / d + 1) + 0 := by
    have := Nat.div_add_mod v d
    have : d * (v / d + 1) = d * (v / d) + d := Nat.mul_succ d (v / d)
    omega_fast
  rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt hd, Nat.add_zero]

def call_cells (xs : FastCells) : CallOutcome :=
  FastCells.rec
    (CallOutcome.Returned true 1 (FastCells.cell false 0 FastCells.nil))
    (fun p n rest ih =>
      Bool.rec
        (PushRes.rec (fun k' xs' => CallOutcome.Returned false k' xs') (push_cell true 0 n rest))
        (Bool.rec
          (OptCells.rec
            (OptCells.rec
              (OptCells.rec
                CallOutcome.Failed
                (fun _ _ => CallOutcome.Stopped)
                (remove_word [0, 0, 1, 1] 0 (FastCells.cell true n rest)))
              (fun k2 xs2 => PushRes.rec (fun k' xs' => CallOutcome.Returned true k' xs') (put_word [1, 0, 1, 0, 0] k2 xs2))
              (remove_word [0, 0, 1, 0, 0] 0 (FastCells.cell true n rest)))
            (fun k1 xs1 => PushRes.rec (fun k' xs' => CallOutcome.Returned true k' xs') (put_word [0, 1, 1] k1 xs1))
            (remove_word [0, 0, 0] 0 (FastCells.cell true n rest)))
          (CallOutcome.rec
            CallOutcome.Failed
            (fun b k_ret ys_ret =>
              let m := Nat.add (Nat.sub n 2) k_ret
              Bool.rec
                (CallOutcome.Returned false 2 (FastCells.cell false m ys_ret))
                (CallOutcome.Returned true 1 (FastCells.cell false (Nat.add 1 m) ys_ret))
                b)
            CallOutcome.Stopped
            ih)
          (Nat.ble 2 n))
        p)
    (fun B pow2B max_v v F_next ns rest ih =>
      let v_new := Nat.add v 1
      Bool.rec
        CallOutcome.Failed
        (let P := Nat.mod v pow2B
         Bool.rec
           (let k_ret := Nat.mul 2 (Nat.mod v 2)
            CallOutcome.Returned false k_ret (FastCells.block B pow2B max_v v_new F_next ns rest))
           (CallOutcome.rec
             CallOutcome.Failed
             (fun b k_ret ys_ret =>
               let ret_k := Bool.rec 2 1 b
               let f_add := Bool.rec k_ret (Nat.add k_ret 1) b
               CallOutcome.Returned b ret_k (FastCells.block B pow2B max_v v_new (Nat.add F_next f_add) ns ys_ret))
             CallOutcome.Stopped
             ih)
           (Nat.beq (Nat.add P 1) pow2B))
        (Nat.ble v_new max_v))
    xs

def call_fast_spec (r : ListBlank (Fin 2)) : CallOutcome → Prop
  | CallOutcome.Failed => True
  | CallOutcome.Stopped => SideHalt r
  | CallOutcome.Returned b k ys => Side b r ((W ^ k) +> words_tape (to_cells ys)) ∧ WF ys

lemma unpack_block_call_overflow (ns : List Nat) (v max_v F_next : Nat) (rest : FastCells)
    (hv : v + 1 ≤ max_v) (hwf : WF_ns max_v F_next ns)
    (hov : (v + 1) / (2 ^ ns.length) = v / (2 ^ ns.length) + 1)
    (out : CallOutcome) (hout : call_fast_spec (words_tape (to_cells rest)) out)
    (B pow2B : Nat) (hpow : pow2B = 2 ^ ns.length) :
    call_fast_spec (words_tape (unpack_block v F_next ns (to_cells rest)))
      (CallOutcome.rec
        CallOutcome.Failed
        (fun b k_ret ys_ret =>
          let ret_k := Bool.rec 2 1 b
          let f_add := Bool.rec k_ret (Nat.add k_ret 1) b
          CallOutcome.Returned b ret_k (FastCells.block B pow2B max_v (Nat.add v 1) (Nat.add F_next f_add) ns ys_ret))
        CallOutcome.Stopped
        out) := by
  have haux : ∀ (ns : List Nat) (v max_v : Nat),
      v + 1 ≤ max_v → WF_ns max_v F_next ns →
      (v + 1) / (2 ^ ns.length) = v / (2 ^ ns.length) + 1 →
      match out with
      | CallOutcome.Failed => True
      | CallOutcome.Stopped => SideHalt (words_tape (unpack_block v F_next ns (to_cells rest)))
      | CallOutcome.Returned b k_ret ys_ret =>
          Side b (words_tape (unpack_block v F_next ns (to_cells rest)))
            ((W ^ (Bool.rec 2 1 b : Nat)) +>
              words_tape (unpack_block (v + 1) (F_next + (Bool.rec k_ret (k_ret + 1) b : Nat)) ns (to_cells ys_ret))) := by
    intro ns
    induction ns with
    | nil => intros; contradiction
    | cons n0 tail_ns ih =>
      intro v max_v hv hwf hov
      cases tail_ns with
      | nil =>
        change (v + 1) / 2 = v / 2 + 1 at hov
        have hns0 := hwf (v + 1) hv
        have hp1 : Nat.beq (Nat.mod v 2) 1 = true := Nat.beq_eq.mpr (by omega_fast)
        have hp0 : Nat.beq (Nat.mod (v + 1) 2) 1 = false := by
          cases hbeq : Nat.beq (Nat.mod (v + 1) 2) 1
          · rfl
          · have := Nat.beq_eq.mp hbeq; omega_fast
        let m0 := Nat.sub (Nat.add n0 F_next) (Nat.mul 2 (Nat.div v 2))
        have hm0_ge2 : 2 ≤ m0 := by change 2 ≤ (n0 + F_next) - 2 * (v / 2); omega_fast
        have hlhs : ([0, 0, 1, 0, 1] : List (Fin 2)) +> ((W ^ (m0 - 2)) +> words_tape (to_cells rest)) =
            words_tape (unpack_block v F_next [n0] (to_cells rest)) := by
          have hm_eq : m0 = 2 + (m0 - 2) := by omega_fast
          change ([0, 0, 1, 0, 1] : List (Fin 2)) +> ((W ^ (m0 - 2)) +> words_tape (to_cells rest)) =
            (bit (Nat.beq (Nat.mod v 2) 1)) +> ((W ^ m0) +> words_tape (to_cells rest))
          rw [hp1]
          change (bit true) +> ((W ^ 2) +> ((W ^ (m0 - 2)) +> words_tape (to_cells rest))) =
            (bit true) +> ((W ^ m0) +> words_tape (to_cells rest))
          rw [← pow_append_tape W 2 (m0 - 2), ← hm_eq]
        cases out with
        | Failed => trivial
        | Stopped =>
          have h1 := wall_halt (m0 - 2) hout
          have h2 := carry_halt h1
          rw [hlhs] at h2
          exact h2
        | Returned b k_ret ys_ret =>
          rcases hout with ⟨hout_s, _⟩
          have h1 := wall_side b (m0 - 2) hout_s
          have h2 := carry_side b h1
          rw [hlhs] at h2
          cases b
          · dsimp only at h2 ⊢
            have hm'_eq : Nat.sub (Nat.add n0 (F_next + k_ret)) (Nat.mul 2 (Nat.div (v + 1) 2)) = (m0 - 2) + k_ret := by
              change (n0 + (F_next + k_ret)) - 2 * ((v + 1) / 2) = (((n0 + F_next) - 2 * (v / 2)) - 2) + k_ret
              omega_fast
            have hrhs : ([0, 1, 0, 1, 1] : List (Fin 2)) +>
                ((W ^ (m0 - 2)) +> ((W ^ k_ret) +> words_tape (to_cells ys_ret))) =
                (W ^ 2) +> words_tape (unpack_block (v + 1) (F_next + k_ret) [n0] (to_cells ys_ret)) := by
              change _ = (W ^ 2) +> ((bit (Nat.beq (Nat.mod (v + 1) 2) 1)) +>
                ((W ^ Nat.sub (Nat.add n0 (F_next + k_ret)) (Nat.mul 2 (Nat.div (v + 1) 2))) +> words_tape (to_cells ys_ret)))
              rw [hp0, hm'_eq, pow_append_tape W (m0 - 2) k_ret]
              rfl
            rw [← hrhs]
            exact h2
          · dsimp only at h2 ⊢
            have hm'_eq : Nat.sub (Nat.add n0 (F_next + (k_ret + 1))) (Nat.mul 2 (Nat.div (v + 1) 2)) = 1 + ((m0 - 2) + k_ret) := by
              change (n0 + (F_next + (k_ret + 1))) - 2 * ((v + 1) / 2) = 1 + ((((n0 + F_next) - 2 * (v / 2)) - 2) + k_ret)
              omega_fast
            have hrhs : ([0, 1, 1, 0, 1] : List (Fin 2)) +>
                ((W ^ (m0 - 2)) +> ((W ^ k_ret) +> words_tape (to_cells ys_ret))) =
                (W ^ 1) +> words_tape (unpack_block (v + 1) (F_next + (k_ret + 1)) [n0] (to_cells ys_ret)) := by
              change _ = (W ^ 1) +> ((bit (Nat.beq (Nat.mod (v + 1) 2) 1)) +>
                ((W ^ Nat.sub (Nat.add n0 (F_next + (k_ret + 1))) (Nat.mul 2 (Nat.div (v + 1) 2))) +> words_tape (to_cells ys_ret)))
              rw [hp0, hm'_eq, pow_append_tape W 1 ((m0 - 2) + k_ret), pow_append_tape W (m0 - 2) k_ret]
              rfl
            rw [← hrhs]
            exact h2
      | cons n1 tail2 =>
        rcases hwf with ⟨hns0, hns_tail⟩
        have hdiv_eq : ∀ x : Nat, x / (2 ^ (n0 :: n1 :: tail2).length) = (x / 2) / (2 ^ (n1 :: tail2).length) := by
          intro x
          rw [List.length_cons, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        rw [hdiv_eq (v + 1), hdiv_eq v] at hov
        have hv_div : (v + 1) / 2 = v / 2 + 1 := by
          by_cases h : (v + 1) / 2 = v / 2
          · rw [h] at hov; omega_fast
          · omega_fast
        rw [hv_div] at hov
        have h_ih := ih (v / 2) (max_v / 2) (by omega_fast) hns_tail hov
        have hdiv_eq2 : ∀ x : Nat, x / (2 ^ (n1 :: tail2).length) = (x / 2) / (2 ^ tail2.length) := by
          intro x
          rw [List.length_cons, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        have hov2 := hov
        rw [hdiv_eq2 (v / 2 + 1), hdiv_eq2 (v / 2)] at hov2
        have hv_div2 : (v / 2 + 1) / 2 = (v / 2) / 2 + 1 := by
          by_cases h : (v / 2 + 1) / 2 = (v / 2) / 2
          · rw [h] at hov2; omega_fast
          · omega_fast
        have hp1 : Nat.beq (Nat.mod v 2) 1 = true := Nat.beq_eq.mpr (by omega_fast)
        have hp0 : Nat.beq (Nat.mod (v + 1) 2) 1 = false := by
          cases hbeq : Nat.beq (Nat.mod (v + 1) 2) 1
          · rfl
          · have := Nat.beq_eq.mp hbeq; omega_fast
        let m0 := Nat.sub (Nat.add n0 (Nat.mul 2 (Nat.div (Nat.div v 2) 2))) (Nat.mul 2 (Nat.div v 2))
        have hm0_ge2 : 2 ≤ m0 := by
          have := hns0 (v + 1) hv
          change 2 ≤ (n0 + 2 * ((v / 2) / 2)) - 2 * (v / 2)
          omega_fast
        have hlhs : ([0, 0, 1, 0, 1] : List (Fin 2)) +> ((W ^ (m0 - 2)) +> words_tape (unpack_block (v / 2) F_next (n1 :: tail2) (to_cells rest))) =
            words_tape (unpack_block v F_next (n0 :: n1 :: tail2) (to_cells rest)) := by
          have hm_eq : m0 = 2 + (m0 - 2) := by omega_fast
          change ([0, 0, 1, 0, 1] : List (Fin 2)) +> ((W ^ (m0 - 2)) +> words_tape (unpack_block (v / 2) F_next (n1 :: tail2) (to_cells rest))) =
            (bit (Nat.beq (Nat.mod v 2) 1)) +> ((W ^ m0) +> words_tape (unpack_block (v / 2) F_next (n1 :: tail2) (to_cells rest)))
          rw [hp1]
          change (bit true) +> ((W ^ 2) +> ((W ^ (m0 - 2)) +> words_tape (unpack_block (v / 2) F_next (n1 :: tail2) (to_cells rest)))) =
            (bit true) +> ((W ^ m0) +> words_tape (unpack_block (v / 2) F_next (n1 :: tail2) (to_cells rest)))
          rw [← pow_append_tape W 2 (m0 - 2), ← hm_eq]
        cases out with
        | Failed => trivial
        | Stopped =>
          have h1 := wall_halt (m0 - 2) h_ih
          have h2 := carry_halt h1
          rw [hlhs] at h2
          exact h2
        | Returned b k_ret ys_ret =>
          have h1 := wall_side b (m0 - 2) h_ih
          have h2 := carry_side b h1
          rw [hlhs] at h2
          have hm'_eq : Nat.sub (Nat.add n0 (Nat.mul 2 (Nat.div (Nat.div (v + 1) 2) 2))) (Nat.mul 2 (Nat.div (v + 1) 2)) = m0 := by
            have := hns0 (v + 1) hv
            change (n0 + 2 * (((v + 1) / 2) / 2)) - 2 * ((v + 1) / 2) = (n0 + 2 * ((v / 2) / 2)) - 2 * (v / 2)
            omega_fast
          cases b
          · dsimp only at h_ih h2 ⊢
            have hm_add : (m0 - 2) + 2 = m0 := by omega_fast
            have hrhs : ([0, 1, 0, 1, 1] : List (Fin 2)) +>
                ((W ^ (m0 - 2)) +> ((W ^ 2) +> words_tape (unpack_block (v / 2 + 1) (F_next + k_ret) (n1 :: tail2) (to_cells ys_ret)))) =
                (W ^ 2) +> words_tape (unpack_block (v + 1) (F_next + k_ret) (n0 :: n1 :: tail2) (to_cells ys_ret)) := by
              change _ = (W ^ 2) +> ((bit (Nat.beq (Nat.mod (v + 1) 2) 1)) +>
                ((W ^ Nat.sub (Nat.add n0 (Nat.mul 2 (Nat.div (Nat.div (v + 1) 2) 2))) (Nat.mul 2 (Nat.div (v + 1) 2))) +>
                  words_tape (unpack_block (Nat.div (v + 1) 2) (F_next + k_ret) (n1 :: tail2) (to_cells ys_ret))))
              rw [hp0, hm'_eq, nat_div_eq, hv_div, ← pow_append_tape W (m0 - 2) 2, hm_add]
              rfl
            rw [← hrhs]
            exact h2
          · dsimp only at h_ih h2 ⊢
            have hm_add : 1 + ((m0 - 2) + 1) = m0 := by omega_fast
            have hrhs : ([0, 1, 1, 0, 1] : List (Fin 2)) +>
                ((W ^ (m0 - 2)) +> ((W ^ 1) +> words_tape (unpack_block (v / 2 + 1) (F_next + (k_ret + 1)) (n1 :: tail2) (to_cells ys_ret)))) =
                (W ^ 1) +> words_tape (unpack_block (v + 1) (F_next + (k_ret + 1)) (n0 :: n1 :: tail2) (to_cells ys_ret)) := by
              change _ = (W ^ 1) +> ((bit (Nat.beq (Nat.mod (v + 1) 2) 1)) +>
                ((W ^ Nat.sub (Nat.add n0 (Nat.mul 2 (Nat.div (Nat.div (v + 1) 2) 2))) (Nat.mul 2 (Nat.div (v + 1) 2))) +>
                  words_tape (unpack_block (Nat.div (v + 1) 2) (F_next + (k_ret + 1)) (n1 :: tail2) (to_cells ys_ret))))
              rw [hp0, hm'_eq, nat_div_eq, hv_div]
              change (W ^ 1) +> ((bit false) +> ((W ^ 1) +> ((W ^ (m0 - 2)) +> ((W ^ 1) +>
                  words_tape (unpack_block (v / 2 + 1) (F_next + (k_ret + 1)) (n1 :: tail2) (to_cells ys_ret)))))) =
                (W ^ 1) +> ((bit false) +> ((W ^ m0) +>
                  words_tape (unpack_block (v / 2 + 1) (F_next + (k_ret + 1)) (n1 :: tail2) (to_cells ys_ret))))
              rw [← pow_append_tape W (m0 - 2) 1, ← pow_append_tape W 1 ((m0 - 2) + 1), hm_add]
            rw [← hrhs]
            exact h2
  have hmain := haux ns v max_v hv hwf hov
  cases out with
  | Failed => trivial
  | Stopped => exact hmain
  | Returned b k_ret ys_ret =>
    rcases hout with ⟨_, hy_wf⟩
    refine ⟨hmain, ⟨hpow, hv, wf_ns_mono (Nat.le_refl _) ?_ hwf⟩, hy_wf⟩
    cases b <;> dsimp <;> omega_fast

lemma call_cells_fast_spec (xs : FastCells) (hwf : WF xs) :
    call_fast_spec (words_tape (to_cells xs)) (call_cells xs) := by
  induction xs with
  | nil =>
    unfold call_cells call_fast_spec
    have h0 := leaf0_side default
    rw [← default_eq_zero_three] at h0
    exact ⟨h0, trivial⟩
  | cell p n rest ih =>
    change call_fast_spec (words_tape ((p, n) :: to_cells rest)) (call_cells (FastCells.cell p n rest))
    cases p
    · -- p = false
      dsimp only [call_cells]
      have hpc := push_cell_fast_spec true 0 n rest hwf
      generalize hpush : push_cell true 0 n rest = push_res at hpc ⊢
      rcases push_res with ⟨k', xs'⟩
      rcases hpc with ⟨hpc_t, hpc_w⟩
      dsimp only [call_fast_spec]
      rw [Nat.zero_add] at hpc_t
      rw [hpc_t]
      exact ⟨inc_side ((W ^ n) +> words_tape (to_cells rest)), hpc_w⟩
    · -- p = true
      have h_ih := ih hwf
      dsimp only [call_cells]
      cases hn2 : Nat.ble 2 n
      · -- n < 2
        dsimp only
        cases hrw1 : remove_word [0, 0, 0] 0 (FastCells.cell true n rest) with
        | some k1 xs1 =>
          dsimp only
          rcases remove_word_fast_spec [0, 0, 0] 0 (FastCells.cell true n rest) hwf k1 xs1 hrw1 with ⟨hrw_t, hrw_w⟩
          have hpw := put_word_fast_spec [0, 1, 1] k1 xs1 hrw_w
          generalize hput : put_word [0, 1, 1] k1 xs1 = pw_res at hpw ⊢
          rcases pw_res with ⟨k', xs'⟩
          rcases hpw with ⟨hpw_t, hpw_w⟩
          dsimp only [call_fast_spec]
          change words_tape ((true, n) :: to_cells rest) = ([0, 0, 0] : List (Fin 2)) +> ((W ^ k1) +> words_tape (to_cells xs1)) at hrw_t
          change (W ^ k') +> words_tape (to_cells xs') = ([0, 1, 1] : List (Fin 2)) +> ((W ^ k1) +> words_tape (to_cells xs1)) at hpw_t
          rw [hpw_t, hrw_t]
          exact ⟨leaf0_side ((W ^ k1) +> words_tape (to_cells xs1)), hpw_w⟩
        | none =>
          dsimp only
          cases hrw2 : remove_word [0, 0, 1, 0, 0] 0 (FastCells.cell true n rest) with
          | some k2 xs2 =>
            dsimp only
            rcases remove_word_fast_spec [0, 0, 1, 0, 0] 0 (FastCells.cell true n rest) hwf k2 xs2 hrw2 with ⟨hrw_t, hrw_w⟩
            have hpw := put_word_fast_spec [1, 0, 1, 0, 0] k2 xs2 hrw_w
            generalize hput : put_word [1, 0, 1, 0, 0] k2 xs2 = pw_res at hpw ⊢
            rcases pw_res with ⟨k', xs'⟩
            rcases hpw with ⟨hpw_t, hpw_w⟩
            dsimp only [call_fast_spec]
            change words_tape ((true, n) :: to_cells rest) = ([0, 0, 1, 0, 0] : List (Fin 2)) +> ((W ^ k2) +> words_tape (to_cells xs2)) at hrw_t
            change (W ^ k') +> words_tape (to_cells xs') = ([1, 0, 1, 0, 0] : List (Fin 2)) +> ((W ^ k2) +> words_tape (to_cells xs2)) at hpw_t
            rw [hpw_t, hrw_t]
            exact ⟨leaf1_side ((W ^ k2) +> words_tape (to_cells xs2)), hpw_w⟩
          | none =>
            dsimp only
            cases hrw3 : remove_word [0, 0, 1, 1] 0 (FastCells.cell true n rest) with
            | some k3 xs3 =>
              rcases remove_word_fast_spec [0, 0, 1, 1] 0 (FastCells.cell true n rest) hwf k3 xs3 hrw3 with ⟨hrw_t, _⟩
              dsimp only [call_fast_spec]
              change words_tape ((true, n) :: to_cells rest) = ([0, 0, 1, 1] : List (Fin 2)) +> ((W ^ k3) +> words_tape (to_cells xs3)) at hrw_t
              rw [hrw_t]
              exact stop_halt ((W ^ k3) +> words_tape (to_cells xs3))
            | none => trivial
      · -- 2 ≤ n
        dsimp only
        have hn_ge2 : 2 ≤ n := Nat.ble_eq.mp hn2
        have hlhs : ([0, 0, 1, 0, 1] : List (Fin 2)) +> ((W ^ (n - 2)) +> words_tape (to_cells rest)) =
            words_tape ((true, n) :: to_cells rest) := by
          have hn_eq : n = 2 + (n - 2) := by omega_fast
          change (bit true) +> ((W ^ 2) +> ((W ^ (n - 2)) +> words_tape (to_cells rest))) =
            (bit true) +> ((W ^ n) +> words_tape (to_cells rest))
          rw [← pow_append_tape W 2 (n - 2), ← hn_eq]
        change call_fast_spec (words_tape ((true, n) :: to_cells rest)) (CallOutcome.rec _ _ _ (call_cells rest))
        generalize hcc : call_cells rest = out at h_ih ⊢
        cases out with
        | Failed => trivial
        | Stopped =>
          have h1 := wall_halt (n - 2) h_ih
          have h2 := carry_halt h1
          rw [hlhs] at h2
          exact h2
        | Returned b k_ret ys_ret =>
          rcases h_ih with ⟨h_ih_s, h_ih_w⟩
          have h1 := wall_side b (n - 2) h_ih_s
          have h2 := carry_side b h1
          rw [hlhs] at h2
          cases b
          · dsimp only [call_fast_spec] at h2 ⊢
            have hrhs : ([0, 1, 0, 1, 1] : List (Fin 2)) +>
                ((W ^ (n - 2)) +> ((W ^ k_ret) +> words_tape (to_cells ys_ret))) =
                (W ^ 2) +> words_tape (to_cells (FastCells.cell false (Nat.add (Nat.sub n 2) k_ret) ys_ret)) := by
              change _ = (W ^ 2) +> ((bit false) +> ((W ^ ((n - 2) + k_ret)) +> words_tape (to_cells ys_ret)))
              rw [pow_append_tape W (n - 2) k_ret]
              rfl
            rw [← hrhs]
            exact ⟨h2, h_ih_w⟩
          · dsimp only [call_fast_spec] at h2 ⊢
            have hrhs : ([0, 1, 1, 0, 1] : List (Fin 2)) +>
                ((W ^ (n - 2)) +> ((W ^ k_ret) +> words_tape (to_cells ys_ret))) =
                (W ^ 1) +> words_tape (to_cells (FastCells.cell false (Nat.add 1 (Nat.add (Nat.sub n 2) k_ret)) ys_ret)) := by
              change _ = (W ^ 1) +> ((bit false) +> ((W ^ (1 + ((n - 2) + k_ret))) +> words_tape (to_cells ys_ret)))
              rw [pow_append_tape W 1 ((n - 2) + k_ret), pow_append_tape W (n - 2) k_ret]
              rfl
            rw [← hrhs]
            exact ⟨h2, h_ih_w⟩
  | block B pow2B max_v v F_next ns rest ih =>
    rcases hwf with ⟨⟨hpow, hv, hns⟩, hrest⟩
    have h_ih := ih hrest
    dsimp only [call_cells]
    cases hv1 : Nat.ble (Nat.add v 1) max_v
    · trivial
    · dsimp only
      have hv_le : v + 1 ≤ max_v := Nat.ble_eq.mp hv1
      cases hov_b : Nat.beq (Nat.add (Nat.mod v pow2B) 1) pow2B
      · -- No overflow
        dsimp only [call_fast_spec]
        have hne : v % (2 ^ ns.length) + 1 ≠ 2 ^ ns.length := by
          intro heq
          rw [← hpow] at heq
          have htrue : Nat.beq (Nat.add (Nat.mod v pow2B) 1) pow2B = true := Nat.beq_eq.mpr heq
          rw [htrue] at hov_b; contradiction
        have hdiv_eq := div_succ_of_mod_ne v (2 ^ ns.length) (pow2_pos ns) hne
        have hsub0 : (v + 1) / (2 ^ ns.length) - v / (2 ^ ns.length) = 0 := by omega_fast
        have hB0 : Batch ((v + 1) / (2 ^ ns.length) - v / (2 ^ ns.length)) (to_cells rest) 0 (to_cells rest) := by
          rw [hsub0]; exact batch_refl (to_cells rest)
        have hB1 := unpack_block_batch ns v (v + 1) max_v F_next 0 (to_cells rest) (to_cells rest)
          (by omega_fast) hv_le hns hB0
        have hv_sub1 : (v + 1) - v = 1 := by omega_fast
        have hv_div2 : 2 * ((v + 1) / 2 - v / 2) = Nat.mul 2 (Nat.mod v 2) := by omega_fast
        rw [hv_sub1, hv_div2, Nat.add_zero] at hB1
        exact ⟨batch_one hB1, ⟨hpow, hv_le, hns⟩, hrest⟩
      · -- Overflow
        dsimp only
        have heq : v % (2 ^ ns.length) + 1 = 2 ^ ns.length := by
          have := Nat.beq_eq.mp hov_b
          rw [hpow] at this
          exact this
        have hdiv_eq := div_succ_of_mod_eq v (2 ^ ns.length) (pow2_pos ns) heq
        exact unpack_block_call_overflow ns v max_v F_next rest hv_le hns hdiv_eq (call_cells rest) h_ih B pow2B hpow

def batch_fused_ub (xs : FastCells) (ub : Nat) : FusedRes :=
  FastCells.rec
    (fun _ => FusedRes.mk 0 0 0 FastCells.nil)
    (fun p n rest ih ub =>
      Bool.rec
        (Bool.rec
          (let q := first_bit rest
           let bound := Nat.sub (Nat.mul 2 (Nat.add (Nat.mul 2 (Nat.div n 2)) (bval(q)))) (Nat.add (bval(p)) 1)
           let cur_ub := natMin(bound, ub)
           Bool.rec
             (let next_ub := Nat.div (Nat.add cur_ub (bval(p))) 2
              FusedRes.rec
                (fun rl f k_extra ys_norm =>
                  Bool.rec
                    (let cap := Bool.rec (Nat.add (Nat.mul 2 rl) 1) (Nat.mul 2 rl) p
                     let t := natMin(cur_ub, cap)
                     let k2 := Nat.mul rl 2
                     PushRes.rec
                       (fun k_pc ys_pc => FusedRes.mk t k2 k_pc ys_pc)
                       (push_cell (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1) (Nat.sub (Nat.add n f) k2) k_extra ys_norm))
                    (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
                    (and p (Nat.beq rl 0)))
                (ih next_ub))
             (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
             (Nat.beq cur_ub 0))
          (Bool.rec
            (PushRes.rec (fun k_pc ys_pc => FusedRes.mk 1 0 k_pc ys_pc) (push_cell true n 0 rest))
            (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
            p)
          (or (is_nil rest) (Nat.ble n 1)))
        (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
        (Nat.beq ub 0))
    (fun B pow2B max_v v F_next ns rest ih ub =>
      Bool.rec
        (let P := Nat.mod v pow2B
         let next_ub := Nat.div (Nat.add ub P) pow2B
         Bool.rec
           (FusedRes.rec
             (fun rl f k_extra ys_norm =>
               let cap := Nat.add (Nat.mul rl pow2B) (Nat.sub (Nat.sub pow2B 1) P)
               let t := natMin(ub, cap)
               let v_new := Nat.add v t
               Bool.rec
                 (FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
                 (let e_out := Nat.mul 2 (Nat.sub (Nat.div v_new 2) (Nat.div v 2))
                  FusedRes.mk t e_out 0 (FastCells.block B pow2B max_v v_new (Nat.add (Nat.add F_next f) k_extra) ns ys_norm))
                 (Nat.ble v_new max_v))
             (ih next_ub))
           (let v_new := Nat.add v ub
            Bool.rec
              (FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
              (let e_out := Nat.mul 2 (Nat.sub (Nat.div v_new 2) (Nat.div v 2))
               FusedRes.mk ub e_out 0 (FastCells.block B pow2B max_v v_new F_next ns rest))
              (Nat.ble v_new max_v))
           (Nat.beq next_ub 0))
        (FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
        (Nat.beq ub 0))
    xs ub

def batch_fused_top (xs : FastCells) : FusedRes :=
  FastCells.rec
    (FusedRes.mk 0 0 0 FastCells.nil)
    (fun p n rest _ =>
      Bool.rec
        (let q := first_bit rest
         let bound := Nat.sub (Nat.mul 2 (Nat.add (Nat.mul 2 (Nat.div n 2)) (bval(q)))) (Nat.add (bval(p)) 1)
         Bool.rec
           (let next_ub := Nat.div (Nat.add bound (bval(p))) 2
            FusedRes.rec
              (fun rl f k_extra ys_norm =>
                Bool.rec
                  (let cap := Bool.rec (Nat.add (Nat.mul 2 rl) 1) (Nat.mul 2 rl) p
                   let t := natMin(bound, cap)
                   let k2 := Nat.mul rl 2
                   PushRes.rec
                     (fun k_pc ys_pc => FusedRes.mk t k2 k_pc ys_pc)
                     (push_cell (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1) (Nat.sub (Nat.add n f) k2) k_extra ys_norm))
                  (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
                  (and p (Nat.beq rl 0)))
              (batch_fused_ub rest next_ub))
           (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
           (Nat.beq bound 0))
        (Bool.rec
          (PushRes.rec (fun k_pc ys_pc => FusedRes.mk 1 0 k_pc ys_pc) (push_cell true n 0 rest))
          (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
          p)
        (or (is_nil rest) (Nat.ble n 1)))
    (fun B pow2B max_v v F_next ns rest _ =>
      FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
    xs

@[simp] theorem bval_false : bval false = 0 := rfl
@[simp] theorem bval_true : bval true = 1 := rfl

lemma natMin_spec (a b : Nat) :
    (natMin(a, b)) ≤ a ∧ (natMin(a, b)) ≤ b ∧ ((natMin(a, b)) = a ∨ (natMin(a, b)) = b) := by
  cases h : Nat.ble a b
  · refine ⟨?_, Nat.le_refl _, Or.inr rfl⟩
    have hnot : ¬ (a ≤ b) := fun hle => by rw [Nat.ble_eq.mpr hle] at h; contradiction
    omega_fast
  · exact ⟨Nat.le_refl _, Nat.ble_eq.mp h, Or.inl rfl⟩

lemma div_sub_of_next_ub_zero (v ub d : Nat) (hd : 0 < d) (h0 : (ub + v % d) / d = 0) :
    (v + ub) / d - v / d = 0 := by
  have hlt : ub + v % d < d := by
    have hdiv := Nat.div_add_mod (ub + v % d) d
    have hmod := Nat.mod_lt (ub + v % d) hd
    rw [h0] at hdiv
    omega_fast
  have h1 : v + ub = d * (v / d) + (ub + v % d) := by
    have := Nat.div_add_mod v d
    omega_fast
  rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt hlt]
  omega_fast

lemma div_sub_of_cap (v ub rl d : Nat) (hd : 0 < d)
    (hrl : rl ≤ (ub + v % d) / d) :
    (v + natMin(ub, rl * d + (d - 1 - v % d))) / d - v / d = rl ∧
      natMin(ub, rl * d + (d - 1 - v % d)) ≤ ub := by
  have hP : v % d < d := Nat.mod_lt v hd
  have ht_ub := natMin_spec ub (rl * d + (d - 1 - v % d))
  generalize ht : (natMin(ub, rl * d + (d - 1 - v % d))) = t at ht_ub ⊢
  rcases ht_ub with ⟨ht_le_ub, ht_le_cap, ht_or⟩
  have h1 : v + t = d * (v / d + (v % d + t) / d) + (v % d + t) % d := by
    have hv_eq := Nat.div_add_mod v d
    have hpt_eq := Nat.div_add_mod (v % d + t) d
    have hmul : d * (v / d + (v % d + t) / d) = d * (v / d) + d * ((v % d + t) / d) := Nat.left_distrib d _ _
    omega_fast
  have hdiv_vt : (v + t) / d = v / d + (v % d + t) / d := by
    rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt (Nat.mod_lt _ hd), Nat.add_zero]
  have hq_eq : (v % d + t) / d = rl := by
    have hpt_eq := Nat.div_add_mod (v % d + t) d
    have hpt_mod := Nat.mod_lt (v % d + t) hd
    generalize hq : (v % d + t) / d = q at hpt_eq
    generalize hr : (v % d + t) % d = r at hpt_eq hpt_mod
    have hub_eq := Nat.div_add_mod (ub + v % d) d
    have hub_mod := Nat.mod_lt (ub + v % d) hd
    have hmul_rl : d * rl ≤ d * ((ub + v % d) / d) := Nat.mul_le_mul_left d hrl
    have hmul_comm : rl * d = d * rl := Nat.mul_comm rl d
    have h_low : d * rl ≤ v % d + t := by
      rcases ht_or with htu | htc <;> omega_fast
    have h_high : v % d + t < d * rl + d := by omega_fast
    by_cases hlt1 : q < rl
    · have hm1 : d * (q + 1) ≤ d * rl := Nat.mul_le_mul_left d (by omega_fast)
      have hm2 : d * (q + 1) = d * q + d := Nat.mul_succ d q
      omega_fast
    · by_cases hlt2 : rl < q
      · have hm1 : d * (rl + 1) ≤ d * q := Nat.mul_le_mul_left d (by omega_fast)
        have hm2 : d * (rl + 1) = d * rl + d := Nat.mul_succ d rl
        omega_fast
      · omega_fast
  rw [hdiv_vt, hq_eq]
  exact ⟨by omega_fast, ht_le_ub⟩

def fused_spec_ub (xs : FastCells) (ub : Nat) : FusedRes → Prop
  | FusedRes.mk t e k_extra ys_norm =>
    t ≤ ub ∧ WF ys_norm ∧
    ∃ ys, Batch t (to_cells xs) e ys ∧
      (W ^ k_extra) +> words_tape (to_cells ys_norm) = words_tape ys

def fused_spec_top (xs : FastCells) : FusedRes → Prop
  | FusedRes.mk t e k_extra ys_norm =>
    WF ys_norm ∧
    ∃ ys, Batch t (to_cells xs) e ys ∧
      (W ^ k_extra) +> words_tape (to_cells ys_norm) = words_tape ys

lemma cell_fused_step (p : Bool) (n : Nat) (rest : FastCells) (hwf : WF rest)
    (cur_ub : Nat) (hc_pos : 0 < cur_ub)
    (hc_bound : cur_ub ≤ Nat.sub (Nat.mul 2 (Nat.add (Nat.mul 2 (Nat.div n 2)) (bval(first_bit rest)))) (Nat.add (bval(p)) 1))
    (res : FusedRes) (hres : fused_spec_ub rest (Nat.div (Nat.add cur_ub (bval(p))) 2) res)
    (ub : Nat) (hub : cur_ub ≤ ub) :
    fused_spec_ub (FastCells.cell p n rest) ub
      (FusedRes.rec
        (fun rl f k_extra ys_norm =>
          Bool.rec
            (let cap := Bool.rec (Nat.add (Nat.mul 2 rl) 1) (Nat.mul 2 rl) p
             let t := natMin(cur_ub, cap)
             let k2 := Nat.mul rl 2
             PushRes.rec
               (fun k_pc ys_pc => FusedRes.mk t k2 k_pc ys_pc)
               (push_cell (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1) (Nat.sub (Nat.add n f) k2) k_extra ys_norm))
            (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
            (and p (Nat.beq rl 0)))
        res) := by
  rcases res with ⟨rl, f, k_extra, ys_norm⟩
  rcases hres with ⟨hrl_ub, hys_wf, ys, hB, hW⟩
  dsimp only
  cases hand : (and p (Nat.beq rl 0))
  · dsimp only
    have hnot_p_rl0 : ¬ (p = true ∧ rl = 0) := by
      rintro ⟨rfl, rfl⟩; contradiction
    have ht_min := natMin_spec cur_ub (Bool.rec (Nat.add (Nat.mul 2 rl) 1) (Nat.mul 2 rl) p : Nat)
    generalize ht : (natMin(cur_ub, (Bool.rec (Nat.add (Nat.mul 2 rl) 1) (Nat.mul 2 rl) p : Nat))) = t at ht_min ⊢
    rcases ht_min with ⟨ht_c, ht_cap, ht_or⟩
    have hpc := push_cell_fast_spec (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1)
      (Nat.sub (Nat.add n f) (Nat.mul rl 2)) k_extra ys_norm hys_wf
    generalize hpush : push_cell (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1)
      (Nat.sub (Nat.add n f) (Nat.mul rl 2)) k_extra ys_norm = push_res at hpc ⊢
    rcases push_res with ⟨k_pc, ys_pc⟩
    rcases hpc with ⟨hpc_t, hpc_w⟩
    dsimp only [fused_spec_ub]
    have hhead := batch_head hB
    rcases batch_even hB with ⟨j, rfl⟩
    have hq_eq : first_bit rest = first_cell (to_cells rest) := first_bit_eq rest hwf
    rw [hq_eq] at hc_bound
    have harith : t + bval p = rl * 2 + bval (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1) ∧
        (rl = 0 ∨ rl + 2 ≤ n + bval (first_cell (to_cells rest)) + bval (first_cell ys)) ∧
        Nat.sub (Nat.add n (j * 2)) (Nat.mul rl 2) + rl * 2 = n + j * 2 := by
      rw [bval_beq_mod2]
      cases p <;> cases hfr : first_cell (to_cells rest) <;> cases hfy : first_cell ys <;>
        simp only [hfr, hfy, bval_false, bval_true] at hc_bound hrl_ub hhead ht_cap ht_or hnot_p_rl0 ⊢ <;> omega_fast
    refine ⟨Nat.le_trans ht_c hub, hpc_w, ((Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1), Nat.sub (Nat.add n (j * 2)) (Nat.mul rl 2)) :: ys, ?_, ?_⟩
    · exact Batch.BCons t p n (to_cells rest) rl (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1)
        (j * 2) ys (Nat.sub (Nat.add n (j * 2)) (Nat.mul rl 2))
        harith.1 hB harith.2.1 harith.2.2
    · rw [hpc_t, pow_append_tape, hW]
      rfl
  · dsimp only [fused_spec_ub]
    exact ⟨Nat.zero_le ub, hwf, (p, n) :: to_cells rest, batch_refl _, rfl⟩

lemma batch_fused_ub_spec (xs : FastCells) (ub : Nat) (hwf : WF xs) :
    fused_spec_ub xs ub (batch_fused_ub xs ub) := by
  induction xs generalizing ub with
  | nil =>
    exact ⟨Nat.zero_le ub, trivial, [], Batch.BNil, rfl⟩
  | cell p n rest ih =>
    change fused_spec_ub (FastCells.cell p n rest) ub
      (Bool.rec
        (Bool.rec
          (let q := first_bit rest
           let bound := Nat.sub (Nat.mul 2 (Nat.add (Nat.mul 2 (Nat.div n 2)) (bval(q)))) (Nat.add (bval(p)) 1)
           let cur_ub := natMin(bound, ub)
           Bool.rec
             (let next_ub := Nat.div (Nat.add cur_ub (bval(p))) 2
              FusedRes.rec
                (fun rl f k_extra ys_norm =>
                  Bool.rec
                    (let cap := Bool.rec (Nat.add (Nat.mul 2 rl) 1) (Nat.mul 2 rl) p
                     let t := natMin(cur_ub, cap)
                     let k2 := Nat.mul rl 2
                     PushRes.rec
                       (fun k_pc ys_pc => FusedRes.mk t k2 k_pc ys_pc)
                       (push_cell (Nat.beq (Nat.mod (Nat.add t (bval(p))) 2) 1) (Nat.sub (Nat.add n f) k2) k_extra ys_norm))
                    (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
                    (and p (Nat.beq rl 0)))
                (batch_fused_ub rest next_ub))
             (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
             (Nat.beq cur_ub 0))
          (Bool.rec
            (PushRes.rec (fun k_pc ys_pc => FusedRes.mk 1 0 k_pc ys_pc) (push_cell true n 0 rest))
            (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
            p)
          (or (is_nil rest) (Nat.ble n 1)))
        (FusedRes.mk 0 0 0 (FastCells.cell p n rest))
        (Nat.beq ub 0))
    cases hub0 : Nat.beq ub 0
    · dsimp only
      cases hor : (or (is_nil rest) (Nat.ble n 1))
      · dsimp only
        let q := first_bit rest
        let bound := Nat.sub (Nat.mul 2 (Nat.add (Nat.mul 2 (Nat.div n 2)) (bval(q)))) (Nat.add (bval(p)) 1)
        let cur_ub : Nat := natMin(bound, ub)
        cases hcur0 : Nat.beq cur_ub 0
        · dsimp only
          have hc_pos : 0 < cur_ub := by
            have h0 : cur_ub ≠ 0 := fun h => by rw [Nat.beq_eq.mpr h] at hcur0; contradiction
            omega_fast
          have hmin := natMin_spec bound ub
          exact cell_fused_step p n rest hwf cur_ub hc_pos hmin.1
            (batch_fused_ub rest (Nat.div (Nat.add cur_ub (bval(p))) 2))
            (ih (Nat.div (Nat.add cur_ub (bval(p))) 2) hwf)
            ub hmin.2.1
        · exact ⟨Nat.zero_le ub, hwf, (p, n) :: to_cells rest, batch_refl _, rfl⟩
      · dsimp only
        cases p
        · dsimp only
          have hpc := push_cell_fast_spec true n 0 rest hwf
          generalize hpush : push_cell true n 0 rest = push_res at hpc ⊢
          rcases push_res with ⟨k_pc, ys_pc⟩
          rcases hpc with ⟨hpc_t, hpc_w⟩
          have hub_pos : 1 ≤ ub := by
            have h0 : ub ≠ 0 := fun h => by rw [Nat.beq_eq.mpr h] at hub0; contradiction
            omega_fast
          refine ⟨hub_pos, hpc_w, (true, n) :: to_cells rest, ?_, ?_⟩
          · exact Batch.BCons 1 false n (to_cells rest) 0 true 0 (to_cells rest) n
              rfl (batch_refl _) (Or.inl rfl) rfl
          · rw [hpc_t, Nat.add_zero]
            rfl
        · exact ⟨Nat.zero_le ub, hwf, (true, n) :: to_cells rest, batch_refl _, rfl⟩
    · exact ⟨Nat.zero_le ub, hwf, (p, n) :: to_cells rest, batch_refl _, rfl⟩
  | block B pow2B max_v v F_next ns rest ih =>
    rcases hwf with ⟨⟨hpow, hv, hns⟩, hrest⟩
    have hd_pos : 0 < pow2B := by rw [hpow]; exact pow2_pos ns
    change fused_spec_ub (FastCells.block B pow2B max_v v F_next ns rest) ub
      (Bool.rec
        (let P := Nat.mod v pow2B
         let next_ub := Nat.div (Nat.add ub P) pow2B
         Bool.rec
           (FusedRes.rec
             (fun rl f k_extra ys_norm =>
               let cap := Nat.add (Nat.mul rl pow2B) (Nat.sub (Nat.sub pow2B 1) P)
               let t := natMin(ub, cap)
               let v_new := Nat.add v t
               Bool.rec
                 (FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
                 (let e_out := Nat.mul 2 (Nat.sub (Nat.div v_new 2) (Nat.div v 2))
                  FusedRes.mk t e_out 0 (FastCells.block B pow2B max_v v_new (Nat.add (Nat.add F_next f) k_extra) ns ys_norm))
                 (Nat.ble v_new max_v))
             (batch_fused_ub rest next_ub))
           (let v_new := Nat.add v ub
            Bool.rec
              (FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
              (let e_out := Nat.mul 2 (Nat.sub (Nat.div v_new 2) (Nat.div v 2))
               FusedRes.mk ub e_out 0 (FastCells.block B pow2B max_v v_new F_next ns rest))
              (Nat.ble v_new max_v))
           (Nat.beq next_ub 0))
        (FusedRes.mk 0 0 0 (FastCells.block B pow2B max_v v F_next ns rest))
        (Nat.beq ub 0))
    cases hub0 : Nat.beq ub 0
    · dsimp only
      let P := Nat.mod v pow2B
      let next_ub := Nat.div (Nat.add ub P) pow2B
      cases hnext0 : Nat.beq next_ub 0
      · -- next_ub > 0
        have h_ih := ih next_ub hrest
        generalize hsub : batch_fused_ub rest next_ub = sub_res at h_ih ⊢
        rcases sub_res with ⟨rl, f, k_extra, ys_norm⟩
        rcases h_ih with ⟨hrl_le, hys_wf, ys_rest, hB, hW⟩
        dsimp only
        have hcap := div_sub_of_cap v ub rl pow2B hd_pos (by simpa [nat_div_eq, nat_add_eq, nat_mod_eq] using! hrl_le)
        let cap : Nat := Nat.add (Nat.mul rl pow2B) (Nat.sub (Nat.sub pow2B 1) P)
        let t : Nat := natMin(ub, cap)
        let v_new := Nat.add v t
        cases hv_ble : Nat.ble v_new max_v
        · exact ⟨Nat.zero_le ub, ⟨⟨hpow, hv, hns⟩, hrest⟩, to_cells (FastCells.block B pow2B max_v v F_next ns rest), batch_refl _, rfl⟩
        · dsimp only [fused_spec_ub]
          have hv_new_le : v + t ≤ max_v := Nat.ble_eq.mp hv_ble
          have hdiv_rl : (v + t) / (2 ^ ns.length) - v / (2 ^ ns.length) = rl := by
            rw [← hpow]
            exact hcap.1
          have hB_rl : Batch ((v + t) / (2 ^ ns.length) - v / (2 ^ ns.length)) (to_cells rest) f ys_rest := by
            rw [hdiv_rl]; exact hB
          have hB_blk := unpack_block_batch ns v (v + t) max_v F_next f (to_cells rest) ys_rest
            (by omega_fast) hv_new_le hns hB_rl
          have hvt_sub : (v + t) - v = t := by omega_fast
          rw [hvt_sub] at hB_blk
          have hwf_f : WF_ns max_v (F_next + f) ns := wf_ns_mono (Nat.le_refl _) (by omega_fast) hns
          have habs := unpack_block_absorb_extra ns (v + t) max_v (F_next + f) k_extra
            (to_cells ys_norm) ys_rest hv_new_le hwf_f hW
          refine ⟨hcap.2, ⟨⟨hpow, hv_new_le, wf_ns_mono (Nat.le_refl _) (by omega_fast) hns⟩, hys_wf⟩,
            unpack_block (v + t) (F_next + f) ns ys_rest, hB_blk, ?_⟩
          dsimp only [to_cells, words_tape, list_nat_repeat, append_nil_tape, nat_add_eq]
          exact habs
      · -- next_ub == 0
        dsimp only
        let v_new := Nat.add v ub
        cases hv_ble : Nat.ble v_new max_v
        · exact ⟨Nat.zero_le ub, ⟨⟨hpow, hv, hns⟩, hrest⟩, to_cells (FastCells.block B pow2B max_v v F_next ns rest), batch_refl _, rfl⟩
        · dsimp only [fused_spec_ub]
          have hv_new_le : v + ub ≤ max_v := Nat.ble_eq.mp hv_ble
          have hnext_eq0 : (ub + v % (2 ^ ns.length)) / (2 ^ ns.length) = 0 := by
            have h0 := Nat.beq_eq.mp hnext0
            change (ub + v % pow2B) / pow2B = 0 at h0
            rw [hpow] at h0
            exact h0
          have hdiv0 := div_sub_of_next_ub_zero v ub (2 ^ ns.length) (pow2_pos ns) hnext_eq0
          have hB0 : Batch ((v + ub) / (2 ^ ns.length) - v / (2 ^ ns.length)) (to_cells rest) 0 (to_cells rest) := by
            rw [hdiv0]; exact batch_refl (to_cells rest)
          have hB_blk := unpack_block_batch ns v (v + ub) max_v F_next 0 (to_cells rest) (to_cells rest)
            (by omega_fast) hv_new_le hns hB0
          have hvt_sub : (v + ub) - v = ub := by omega_fast
          rw [hvt_sub, Nat.add_zero] at hB_blk
          exact ⟨Nat.le_refl ub, ⟨⟨hpow, hv_new_le, hns⟩, hrest⟩,
            unpack_block (v + ub) F_next ns (to_cells rest), hB_blk, rfl⟩
    · exact ⟨Nat.zero_le ub, ⟨⟨hpow, hv, hns⟩, hrest⟩, to_cells (FastCells.block B pow2B max_v v F_next ns rest), batch_refl _, rfl⟩

lemma fused_spec_top_of_ub {xs : FastCells} {ub : Nat} {res : FusedRes} (h : fused_spec_ub xs ub res) :
    fused_spec_top xs res := by
  rcases res with ⟨t, e, k_extra, ys_norm⟩
  exact h.2

lemma batch_fused_top_spec (xs : FastCells) (hwf : WF xs) :
    fused_spec_top xs (batch_fused_top xs) := by
  cases xs with
  | nil =>
    exact ⟨trivial, [], Batch.BNil, rfl⟩
  | cell p n rest =>
    dsimp only [batch_fused_top]
    cases hor : (or (is_nil rest) (Nat.ble n 1))
    · dsimp only
      let q := first_bit rest
      let bound := Nat.sub (Nat.mul 2 (Nat.add (Nat.mul 2 (Nat.div n 2)) (bval(q)))) (Nat.add (bval(p)) 1)
      cases hbound0 : Nat.beq bound 0
      · dsimp only
        have hb_pos : 0 < bound := by
          have h0 : bound ≠ 0 := fun h => by rw [Nat.beq_eq.mpr h] at hbound0; contradiction
          omega_fast
        have hstep := cell_fused_step p n rest hwf bound hb_pos (Nat.le_refl bound)
          (batch_fused_ub rest (Nat.div (Nat.add bound (bval(p))) 2))
          (batch_fused_ub_spec rest (Nat.div (Nat.add bound (bval(p))) 2) hwf)
          bound (Nat.le_refl bound)
        exact fused_spec_top_of_ub hstep
      · exact ⟨hwf, (p, n) :: to_cells rest, batch_refl _, rfl⟩
    · dsimp only
      cases p
      · dsimp only
        have hpc := push_cell_fast_spec true n 0 rest hwf
        generalize hpush : push_cell true n 0 rest = push_res at hpc ⊢
        rcases push_res with ⟨k_pc, ys_pc⟩
        rcases hpc with ⟨hpc_t, hpc_w⟩
        refine ⟨hpc_w, (true, n) :: to_cells rest, ?_, ?_⟩
        · exact Batch.BCons 1 false n (to_cells rest) 0 true 0 (to_cells rest) n
            rfl (batch_refl _) (Or.inl rfl) rfl
        · rw [hpc_t, Nat.add_zero]
          rfl
      · exact ⟨hwf, (true, n) :: to_cells rest, batch_refl _, rfl⟩
  | block B pow2B max_v v F_next ns rest =>
    exact ⟨hwf, to_cells (FastCells.block B pow2B max_v v F_next ns rest), batch_refl _, rfl⟩

def step_call_only (k : Nat) (xs : FastCells) : StepRes :=
  CallOutcome.rec
    (StepRes.running false k xs)
    (fun b k_ret ys_ret =>
      let kk := Nat.add k k_ret
      Bool.rec
        (StepRes.running false (Nat.add 1 kk) ys_ret)
        (PushRes.rec (fun k_pc ys_pc =>
          StepRes.running false (Nat.add 1 k_pc) ys_pc)
          (push_cell true 0 kk ys_ret))
        b)
    StepRes.halted
    (call_cells xs)

def step_state (skip_bulk : Bool) (k : Nat) (xs : FastCells) : StepRes :=
  Bool.rec
    (FusedRes.rec
      (fun t e k_extra ys =>
        Bool.rec
          (step_call_only k xs)
          (let k' := Nat.add (Nat.add (Nat.add k t) e) k_extra
           Bool.rec
             (StepRes.running false k' ys)
             (StepRes.running true k' ys)
             (Nat.beq k_extra 0))
          (Nat.ble 1 t))
      (batch_fused_top xs))
    (step_call_only k xs)
    skip_bulk

def run_chunk (fuel : Nat) (sb : Bool) (k : Nat) (xs : FastCells) : StepRes :=
  Nat.rec
    (fun sb k xs => StepRes.running sb k xs)
    (fun _ ih sb k xs =>
      StepRes.rec
        StepRes.halted
        (fun sb' k' xs' => ih sb' k' xs')
        (step_state sb k xs))
    fuel sb k xs

def run_outer (outer inner init_req : Nat) (sb : Bool) (k : Nat) (xs : FastCells) : Bool :=
  Nat.rec
    (fun _ _ _ => false)
    (fun _ ih sb k xs =>
      StepRes.rec
        true
        (fun sb' k' xs' => ih sb' k' (repack_cells init_req xs'))
        (run_chunk inner sb k xs))
    outer sb k xs

def step_res_spec (k : Nat) (xs : FastCells) : StepRes → Prop
  | StepRes.halted => IsHaltFrom (denote_state k (to_cells xs))
  | StepRes.running _ k' xs' =>
      ((denote_state k (to_cells xs)) [holdout_0451_tm]⊢* (denote_state k' (to_cells xs'))) ∧ WF xs'

lemma step_call_only_fast_spec (k : Nat) (xs : FastCells) (hwf : WF xs) :
    step_res_spec k xs (step_call_only k xs) := by
  unfold step_call_only
  have hcc := call_cells_fast_spec xs hwf
  generalize hc : call_cells xs = out at hcc ⊢
  cases out with
  | Failed => exact ⟨reaches_refl _, hwf⟩
  | Stopped => exact wall_halt_start k hcc
  | Returned b k_ret ys_ret =>
    rcases hcc with ⟨hcc_s, hcc_w⟩
    have h_wall := wall_side b k hcc_s
    rw [← pow_append_tape] at h_wall
    have h_emit := emit_side b h_wall
    cases b
    · dsimp only [step_res_spec] at h_emit ⊢
      have hrhs : (W +> ((W ^ (k + k_ret)) +> words_tape (to_cells ys_ret))) =
          (W ^ (Nat.add 1 (Nat.add k k_ret))) +> words_tape (to_cells ys_ret) := by
        dsimp only [nat_add_eq]
        rw [pow_append_tape W 1 (k + k_ret)]
        rfl
      unfold denote_state
      rw [← hrhs]
      exact ⟨h_emit, hcc_w⟩
    · dsimp only at h_emit ⊢
      have hpc := push_cell_fast_spec true 0 (Nat.add k k_ret) ys_ret hcc_w
      generalize hpush : push_cell true 0 (Nat.add k k_ret) ys_ret = push_res at hpc ⊢
      rcases push_res with ⟨k_pc, ys_pc⟩
      rcases hpc with ⟨hpc_t, hpc_w⟩
      dsimp only [step_res_spec]
      rw [Nat.zero_add] at hpc_t
      have hrhs : (([0, 1, 0] : List (Fin 2)) +> ((W ^ (k + k_ret)) +> words_tape (to_cells ys_ret))) =
          (W ^ (Nat.add 1 k_pc)) +> words_tape (to_cells ys_pc) := by
        change (W ++ bit true) +> ((W ^ (Nat.add k k_ret)) +> words_tape (to_cells ys_ret)) =
          (W ^ (1 + k_pc)) +> words_tape (to_cells ys_pc)
        rw [append_assoc_tape, ← hpc_t, pow_append_tape W 1 k_pc]
        rfl
      unfold denote_state
      rw [← hrhs]
      exact ⟨h_emit, hpc_w⟩

lemma step_state_fast_spec (skip_bulk : Bool) (k : Nat) (xs : FastCells) (hwf : WF xs) :
    step_res_spec k xs (step_state skip_bulk k xs) := by
  unfold step_state
  cases skip_bulk
  · dsimp only
    have hf := batch_fused_top_spec xs hwf
    generalize htop : batch_fused_top xs = res at hf ⊢
    rcases res with ⟨t, e, k_extra, ys_norm⟩
    rcases hf with ⟨hys_wf, ys, hB, hW⟩
    dsimp only
    cases Nat.ble 1 t
    · exact step_call_only_fast_spec k xs hwf
    · dsimp only
      have hsteps := batch_steps hB k
      unfold denote_state at hsteps
      rw [← hW, ← pow_append_tape] at hsteps
      cases Nat.beq k_extra 0 <;> exact ⟨hsteps, hys_wf⟩
  · exact step_call_only_fast_spec k xs hwf

lemma run_chunk_fast_spec (fuel : Nat) (sb : Bool) (k : Nat) (xs : FastCells) (hwf : WF xs) :
    step_res_spec k xs (run_chunk fuel sb k xs) := by
  induction fuel generalizing sb k xs with
  | zero => exact ⟨reaches_refl _, hwf⟩
  | succ fuel ih =>
    change step_res_spec k xs (StepRes.rec StepRes.halted (fun sb' k' xs' => run_chunk fuel sb' k' xs') (step_state sb k xs))
    have hstep := step_state_fast_spec sb k xs hwf
    generalize hs : step_state sb k xs = sres at hstep ⊢
    cases sres with
    | halted => exact hstep
    | running sb' k' xs' =>
      dsimp only
      rcases hstep with ⟨h_reach, h_wf'⟩
      have h_ih := ih sb' k' xs' h_wf'
      generalize hrc : run_chunk fuel sb' k' xs' = rc_res at h_ih ⊢
      cases rc_res with
      | halted => exact isHaltFrom_of_reaches h_reach h_ih
      | running sb'' k'' xs'' =>
        rcases h_ih with ⟨h_reach2, h_wf2⟩
        exact ⟨reaches_trans h_reach h_reach2, h_wf2⟩

lemma run_outer_fast_spec (outer inner init_req : Nat) (sb : Bool) (k : Nat) (xs : FastCells)
    (hwf : WF xs) (h : run_outer outer inner init_req sb k xs = true) :
    IsHaltFrom (denote_state k (to_cells xs)) := by
  induction outer generalizing sb k xs with
  | zero => contradiction
  | succ outer ih =>
    change (StepRes.rec true (fun sb' k' xs' => run_outer outer inner init_req sb' k' (repack_cells init_req xs'))
      (run_chunk inner sb k xs)) = true at h
    have hrc := run_chunk_fast_spec inner sb k xs hwf
    generalize hc : run_chunk inner sb k xs = rc_res at hrc h
    cases rc_res with
    | halted => exact hrc
    | running sb' k' xs' =>
      rcases hrc with ⟨h_reach, h_wf'⟩
      rcases repack_cells_spec init_req xs' h_wf' with ⟨hrep_c, hrep_w⟩
      have h_ih := ih sb' k' (repack_cells init_req xs') hrep_w h
      rw [hrep_c] at h_ih
      exact isHaltFrom_of_reaches h_reach h_ih


set_option maxRecDepth 200000 in
lemma trajectory_halts : (run_outer 1273 60 24 false 2 FastCells.nil) = true := by decide +kernel

lemma holdout_0451_halt : IsHalt holdout_0451_tm := by
  have h := run_outer_fast_spec 1273 60 24 false 2 FastCells.nil trivial trajectory_halts
  exact isHaltFrom_of_reaches init_reaches_start h

end

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := holdout_0451_halt

end BusyBeaver.M_1RB0RC_1LC1RF_1RA1LD_1RD0LE_1LD1LC_0REHHH
