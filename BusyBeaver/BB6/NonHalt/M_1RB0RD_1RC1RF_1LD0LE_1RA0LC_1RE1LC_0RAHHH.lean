/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RA---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl

omit [Inhabited Γ] in
@[simp]
theorem list_pow_add (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, ← add_assoc, add_comm 1 m, list_pow_add]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [← List.append_assoc, ← List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

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

lemma stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

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

lemma stepStar_step_left {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h1 : step target_tm c₁ = some c₂) (h2 : c₂ [target_tm]⊢* c₃) :
    c₁ [target_tm]⊢* c₃ := stepStar_trans (step_stepStar target_tm c₁ c₂ h1) h2

@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

lemma append_nil_lb (s : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> s = s := rfl
lemma append_cons_lb (a : Fin 2) (l : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (a :: l) +> s = a >> (l +> s) := rfl
lemma pow_zero_lb (u : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (u ^ 0) +> s = s := rfl
lemma pow_succ_lb (u : List (Fin 2)) (k : Nat) (s : ListBlank (Fin 2)) :
    (u ^ (k + 1)) +> s = u +> ((u ^ k) +> s) := by
  change (u ++ (u ^ k)) +> s = u +> ((u ^ k) +> s)
  exact (listblank_append_append s (u ^ k) u).symm

lemma step_RR (q q' : Fin 6) (a b : Fin 2) (l r : ListBlank (Fin 2))
    (h : target_tm q a = some (some q', Stmt.write b Dir.right)) :
    (l {{q}}> (a >> r)) [target_tm]⊢ ((b >> l) {{q'}}> r) := by
  simp only [step, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, h, Option.map]; rfl

lemma step_RL (q q' : Fin 6) (a b : Fin 2) (l r : ListBlank (Fin 2))
    (h : target_tm q a = some (some q', Stmt.write b Dir.left)) :
    (l {{q}}> (a >> r)) [target_tm]⊢ (l <{{q'}} (b >> r)) := by
  simp only [step, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, h, Option.map]; rfl

lemma step_LR (q q' : Fin 6) (a b : Fin 2) (l r : ListBlank (Fin 2))
    (h : target_tm q a = some (some q', Stmt.write b Dir.right)) :
    ((a >> l) <{{q}} r) [target_tm]⊢ ((b >> l) {{q'}}> r) := by
  simp only [step, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, h, Option.map]; rfl

lemma step_LL (q q' : Fin 6) (a b : Fin 2) (l r : ListBlank (Fin 2))
    (h : target_tm q a = some (some q', Stmt.write b Dir.left)) :
    ((a >> l) <{{q}} r) [target_tm]⊢ (l <{{q'}} (b >> r)) := by
  simp only [step, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, h, Option.map]; rfl

lemma stepStar_RR {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> l) {{q'}}> r) [target_tm]⊢* c₃) :
    (l {{q}}> (a >> r)) [target_tm]⊢* c₃ :=
  stepStar_step_left (step_RR q q' a b l r h) h2

lemma stepStar_RL {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.left))
    (h2 : (l <{{q'}} (b >> r)) [target_tm]⊢* c₃) :
    (l {{q}}> (a >> r)) [target_tm]⊢* c₃ :=
  stepStar_step_left (step_RL q q' a b l r h) h2

lemma stepStar_LR {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> l) {{q'}}> r) [target_tm]⊢* c₃) :
    ((a >> l) <{{q}} r) [target_tm]⊢* c₃ :=
  stepStar_step_left (step_LR q q' a b l r h) h2

lemma stepStar_LL {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.left))
    (h2 : (l <{{q'}} (b >> r)) [target_tm]⊢* c₃) :
    ((a >> l) <{{q}} r) [target_tm]⊢* c₃ :=
  stepStar_step_left (step_LL q q' a b l r h) h2

lemma stepStar_R0R {q q' : Fin 6} {b : Fin 2} {l : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> l) {{q'}}> default) [target_tm]⊢* c₃) :
    (l {{q}}> default) [target_tm]⊢* c₃ := by
  rw [← zero_cons_default]; exact stepStar_RR h h2

lemma stepStar_R0L {q q' : Fin 6} {b : Fin 2} {l : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.left))
    (h2 : (l <{{q'}} (b >> default)) [target_tm]⊢* c₃) :
    (l {{q}}> default) [target_tm]⊢* c₃ := by
  rw [← zero_cons_default]; exact stepStar_RL h h2

lemma stepStar_L0R {q q' : Fin 6} {b : Fin 2} {r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> default) {{q'}}> r) [target_tm]⊢* c₃) :
    (default <{{q}} r) [target_tm]⊢* c₃ := by
  rw [← zero_cons_default]; exact stepStar_LR h h2

lemma stepStar_L0L {q q' : Fin 6} {b : Fin 2} {r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.left))
    (h2 : (default <{{q'}} (b >> r)) [target_tm]⊢* c₃) :
    (default <{{q}} r) [target_tm]⊢* c₃ := by
  rw [← zero_cons_default]; exact stepStar_LL h h2

lemma stepPlus_RR {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> l) {{q'}}> r) [target_tm]⊢* c₃) :
    (l {{q}}> (a >> r)) [target_tm]⊢⁺ c₃ :=
  step_stepStar_stepPlus (step_RR q q' a b l r h) h2

lemma stepPlus_RL {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.left))
    (h2 : (l <{{q'}} (b >> r)) [target_tm]⊢* c₃) :
    (l {{q}}> (a >> r)) [target_tm]⊢⁺ c₃ :=
  step_stepStar_stepPlus (step_RL q q' a b l r h) h2

lemma stepPlus_LR {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> l) {{q'}}> r) [target_tm]⊢* c₃) :
    ((a >> l) <{{q}} r) [target_tm]⊢⁺ c₃ :=
  step_stepStar_stepPlus (step_LR q q' a b l r h) h2

lemma stepPlus_LL {q q' : Fin 6} {a b : Fin 2} {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q a = some (some q', Stmt.write b Dir.left))
    (h2 : (l <{{q'}} (b >> r)) [target_tm]⊢* c₃) :
    ((a >> l) <{{q}} r) [target_tm]⊢⁺ c₃ :=
  step_stepStar_stepPlus (step_LL q q' a b l r h) h2

lemma stepPlus_R0R {q q' : Fin 6} {b : Fin 2} {l : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> l) {{q'}}> default) [target_tm]⊢* c₃) :
    (l {{q}}> default) [target_tm]⊢⁺ c₃ := by
  rw [← zero_cons_default]; exact stepPlus_RR h h2

lemma stepPlus_R0L {q q' : Fin 6} {b : Fin 2} {l : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.left))
    (h2 : (l <{{q'}} (b >> default)) [target_tm]⊢* c₃) :
    (l {{q}}> default) [target_tm]⊢⁺ c₃ := by
  rw [← zero_cons_default]; exact stepPlus_RL h h2

lemma stepPlus_L0R {q q' : Fin 6} {b : Fin 2} {r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.right))
    (h2 : ((b >> default) {{q'}}> r) [target_tm]⊢* c₃) :
    (default <{{q}} r) [target_tm]⊢⁺ c₃ := by
  rw [← zero_cons_default]; exact stepPlus_LR h h2

lemma stepPlus_L0L {q q' : Fin 6} {b : Fin 2} {r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (h : target_tm q 0 = some (some q', Stmt.write b Dir.left))
    (h2 : (default <{{q'}} (b >> r)) [target_tm]⊢* c₃) :
    (default <{{q}} r) [target_tm]⊢⁺ c₃ := by
  rw [← zero_cons_default]; exact stepPlus_LL h h2

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

lemma pow_01_cons_0 (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> s) =
    (0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    rw [ih s]

lemma pow_10_cons_1 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
    (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    rw [ih s]

lemma pow_01_default (k : Nat) :
    (([0, 1] : List (Fin 2)) ^ k) +> (default : ListBlank (Fin 2)) =
    (0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> default) := by
  have h := pow_01_cons_0 k default
  rwa [zero_cons_default] at h

lemma pow_10_append_snoc (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> ((0 : Fin 2) >> s)) =
    (([1, 0] : List (Fin 2)) ^ (k + 1)) +> s := by
  rw [pow_10_cons_1, pow_01_cons_0]
  simp only [pow_succ_lb, append_cons_lb, append_nil_lb]

lemma pow_01_append_snoc (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> ((1 : Fin 2) >> s)) =
    (([0, 1] : List (Fin 2)) ^ (k + 1)) +> s := by
  rw [pow_01_cons_0, pow_10_cons_1]
  simp only [pow_succ_lb, append_cons_lb, append_nil_lb]

lemma shift_A_right_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((((([1, 0] : List (Fin 2)) ^ k) +> l)) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    refine stepStar_RR rfl (stepStar_RR rfl ?_)
    have h2 := ih ((1 : Fin 2) >> ((0 : Fin 2) >> l)) r
    rw [pow_10_append_snoc] at h2
    simpa only [pow_succ_lb, append_cons_lb, append_nil_lb] using! h2

lemma shift_D_right_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ((([0, 1] : List (Fin 2)) ^ k) +> r)) [target_tm]⊢*
    ((((([0, 1] : List (Fin 2)) ^ k) +> l)) {{D}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    refine stepStar_RR rfl (stepStar_RR rfl ?_)
    have h2 := ih ((0 : Fin 2) >> ((1 : Fin 2) >> l)) r
    rw [pow_01_append_snoc] at h2
    simpa only [pow_succ_lb, append_cons_lb, append_nil_lb] using! h2

lemma shift_C_left_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((((([0, 1] : List (Fin 2)) ^ k) +> l)) <{{C}} r) [target_tm]⊢*
    (l <{{C}} ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    refine stepStar_LL rfl (stepStar_LL rfl ?_)
    have h2 := ih l ((0 : Fin 2) >> ((1 : Fin 2) >> r))
    rw [pow_01_append_snoc] at h2
    simpa only [pow_succ_lb, append_cons_lb, append_nil_lb] using! h2

lemma shift_D_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((((([1, 0] : List (Fin 2)) ^ k) +> l)) <{{D}} r) [target_tm]⊢*
    (l <{{D}} ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    refine stepStar_LL rfl (stepStar_LL rfl ?_)
    have h2 := ih l ((1 : Fin 2) >> ((0 : Fin 2) >> r))
    rw [pow_10_append_snoc] at h2
    simpa only [pow_succ_lb, append_cons_lb, append_nil_lb] using! h2

lemma shift_E_left_10_ctx (k : Nat) (l r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> l)) <{{E}} r) [target_tm]⊢*
    (((1 : Fin 2) >> l) <{{E}} ((([0, 1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [pow_succ_lb, append_cons_lb, append_nil_lb]
    refine stepStar_LL rfl (stepStar_LL rfl (stepStar_LR rfl ?_))
    refine stepStar_RR rfl (stepStar_RL rfl (stepStar_LL rfl ?_))
    have h2 := ih l ((0 : Fin 2) >> ((1 : Fin 2) >> r))
    rw [pow_01_append_snoc] at h2
    simpa only [pow_succ_lb, append_cons_lb, append_nil_lb] using! h2

lemma Start (h : Nat) (r : ListBlank (Fin 2)) :
    (default <{{D}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> r))) [target_tm]⊢⁺
    ((((default <+ (([0, 1] : List (Fin 2)) ^ (h + 4))) <+ [1, 1, 1]) <+ [0]) {{A}}> r) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepPlus_L0R rfl ?_
  refine stepStar_trans (shift_A_right_10 h _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 h _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_A_right_10 h _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 h _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_A_right_10 h _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 h _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_A_right_10 h _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma PassR (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{A}}> ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) [target_tm]⊢*
    (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <+ [0]) {{A}}> r) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_trans (shift_A_right_10 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  rw [pow_01_cons_0 q]
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_A_right_10 q _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma Borrow (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    (l {{A}}> ((([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ (q + 2)) +> ([0, 0, 0, 1] +> r)))) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> r)))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_trans (shift_A_right_10 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_D_right_01 q _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_C_left_01 q _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_D_right_01 q _ _) ?_
  refine stepStar_RL rfl ?_
  refine stepStar_trans (shift_C_left_01 q _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma PassL (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    (((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) <{{C}} r) [target_tm]⊢*
    ((l <+ [0]) <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 0, 1] +> r)))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 q _ _) ?_
  refine stepStar_LR rfl ?_
  refine stepStar_trans (shift_A_right_10 q _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 q _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma EndPh (h : Nat) (r : ListBlank (Fin 2)) :
    ((((default <+ (([0, 1] : List (Fin 2)) ^ (h + 4))) <+ [1, 1, 1]) <+ [0]) <{{C}} r) [target_tm]⊢*
    (default <{{D}} ((([1, 0] : List (Fin 2)) ^ (h + 4)) +> ([1, 1, 0, 0, 1] +> r))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_C_left_01 h _ _) ?_
  refine stepStar_L0L rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma EndT (l : ListBlank (Fin 2)) (p q : Nat) :
    ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{A}}> default) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ([1, 0, 1] +> default))))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 q _ _) ?_
  refine stepStar_LR rfl ?_
  refine stepStar_trans (shift_A_right_10 q _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 q _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma EndLastT (l : ListBlank (Fin 2)) (p : Nat) :
    (((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) {{A}}> default) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + 4)) +> ([1] +> default))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma MergeB (l : ListBlank (Fin 2)) (p p' : Nat) (r : ListBlank (Fin 2)) :
    (l {{A}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([0, 1] +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ p') +> r))))) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + p' + 3)) +> r)) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_trans (shift_A_right_10 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  simp only [pow_01_cons_0, pow_10_cons_1]; rw [← pow_add_append_right ([1, 0] : List (Fin 2)) p p' r]
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma MergeE (l : ListBlank (Fin 2)) (p : Nat) :
    (l {{A}}> ((([1, 0] : List (Fin 2)) ^ p) +> ([0, 1] +> ([0, 0, 0, 1] +> default)))) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + 2)) +> ([1] +> default))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_trans (shift_A_right_10 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  rw [zero_cons_default]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma OvT (l : ListBlank (Fin 2)) (t : Nat) :
    ((l <+ [0]) {{A}}> ((([1, 0] : List (Fin 2)) ^ t) +> ([1] +> default))) [target_tm]⊢*
    (l <{{C}} ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_trans (shift_A_right_10 t _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 t _ _) ?_
  refine stepStar_LR rfl ?_
  refine stepStar_trans (shift_A_right_10 t _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 t _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma OvL (l : ListBlank (Fin 2)) (p q : Nat) (r : ListBlank (Fin 2)) :
    ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ q)) <+ [1, 1]) <{{C}} r) [target_tm]⊢*
    (l <{{C}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (q + 1)) +> r)))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx q _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 p _ _) ?_
  refine stepStar_LR rfl ?_
  refine stepStar_trans (shift_A_right_10 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma OvEnd (h p : Nat) (r : ListBlank (Fin 2)) :
    (((default <+ (([0, 1] : List (Fin 2)) ^ (h + 4))) <+ [1, 1, 1]) <{{C}} ((([0, 1] : List (Fin 2)) ^ (p + 2)) +> ([0, 0, 0, 1] +> r))) [target_tm]⊢*
    (default <{{D}} ((([1, 0] : List (Fin 2)) ^ 2) +> ([1, 1, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (h + 5)) +> ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0] +> r)))))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  rw [pow_01_default h]
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx h _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  rw [pow_01_cons_0 h]
  refine stepStar_RR rfl ?_
  rw [pow_10_cons_1 h]
  refine stepStar_RR rfl ?_
  rw [pow_01_cons_0 h]
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_A_right_10 h _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_D_right_01 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_C_left_01 p _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_D_right_01 p _ _) ?_
  refine stepStar_RL rfl ?_
  refine stepStar_trans (shift_C_left_01 p _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx h _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma X1Sw (l : ListBlank (Fin 2)) (p : Nat) (r : ListBlank (Fin 2)) :
    ((((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ (p + 1))) <+ [0, 1, 1]) <+ [1, 1]) <+ [0]) <{{C}} r) [target_tm]⊢*
    (l <{{C}} ((([0, 1] : List (Fin 2)) ^ (p + 1)) +> ([0, 0, 1, 0, 1, 0, 1] +> r))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 p _ _) ?_
  refine stepStar_LR rfl ?_
  refine stepStar_trans (shift_A_right_10 p _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

lemma X2T (l : ListBlank (Fin 2)) (p q k : Nat) :
    ((((((l <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q + 1))) <+ [1, 1]) <+ [0]) {{A}}> ([1, 0, 1, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> default))) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ (p + 1)) +> ((([0, 1] : List (Fin 2)) ^ (q + 1)) +> ([0, 0, 1, 0] +> ((([1, 0] : List (Fin 2)) ^ 3) +> ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> ([0, 0, 0, 1] +> default))))))) := by
  simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb]
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_D_right_01 k _ _) ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_C_left_01 k _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_trans (shift_D_right_01 k _ _) ?_
  refine stepStar_RL rfl ?_
  refine stepStar_trans (shift_C_left_01 k _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 q _ _) ?_
  refine stepStar_LR rfl ?_
  refine stepStar_trans (shift_A_right_10 q _ _) ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_D_left_10 q _ _) ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_trans (shift_E_left_10_ctx p _ _) ?_
  refine stepStar_LL rfl ?_
  try simp only [pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, pow_01_cons_0, pow_10_cons_1, zero_cons_default]
  exact ⟨0, rfl⟩

def sd (d : Bool) : List (Fin 2) := if d then [0, 0, 0, 1] else [0, 0, 1, 0]

def RP : List (Nat × Nat × Bool) → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | (p, q, d) :: P', r => (([1, 0] : List (Fin 2)) ^ p) +> ((([0, 1] : List (Fin 2)) ^ q) +> (sd d +> RP P' r))

inductive Tl where
  | TN
  | TA (t : Nat)
  | TB (k : Nat)

def RT : Tl → ListBlank (Fin 2)
  | .TN => default
  | .TA t => (([1, 0] : List (Fin 2)) ^ t) +> ([1] +> default)
  | .TB k => [1, 0, 1, 1, 0, 1] +> ((([0, 1] : List (Fin 2)) ^ k) +> default)

def K (h : Nat) (P : List (Nat × Nat × Bool)) (T : Tl) : Cfg (Fin 2) (Fin 6) :=
  default <{{D}} ((([1, 0] : List (Fin 2)) ^ h) +> ([1, 1, 0, 0, 1] +> RP P (RT T)))

def reg (p q : Nat) (l : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ((((l <+ [0]) <+ (([1, 0] : List (Fin 2)) ^ p)) <+ [0, 1, 1]) <+ (([1, 0] : List (Fin 2)) ^ (q - 1))) <+ [1, 1]

def LP : List (Nat × Nat × Bool) → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], l => l
  | (p, q, _) :: Z', l => LP Z' (reg p q l)

def OvR : List (Nat × Nat × Bool) → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | (p, q, _) :: Z', r => (([0, 1] : List (Fin 2)) ^ p) +> ([0, 0, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ q) +> OvR Z' r))

def touch (x : Nat × Nat × Bool) : Nat × Nat × Bool :=
  (x.1 + 1, x.2.1 - 1, !x.2.2)

abbrev okR (x : Nat × Nat × Bool) : Prop := x.2.2 = false ∧ 1 ≤ x.2.1

abbrev okL (x : Nat × Nat × Bool) : Prop := x.2.2 = false ∧ 2 ≤ x.2.1

abbrev okO (x : Nat × Nat × Bool) : Prop := 1 ≤ x.1 ∧ 1 ≤ x.2.1

lemma RP_app (Z W : List (Nat × Nat × Bool)) (r : ListBlank (Fin 2)) :
    RP (Z ++ W) r = RP Z (RP W r) := by
  induction Z with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [RP]
    rw [ih]

lemma LP_app (Z W : List (Nat × Nat × Bool)) (l : ListBlank (Fin 2)) :
    LP (Z ++ W) l = LP W (LP Z l) := by
  induction Z generalizing l with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [LP]
    exact ih (reg p q l)

lemma PassesR (Z : List (Nat × Nat × Bool)) (hZ : ∀ x ∈ Z, okR x) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{A}}> RP Z r) [target_tm]⊢* ((LP Z l <+ [0]) {{A}}> r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hx := hZ (p, q, d) (List.Mem.head _)
    have hZ' : ∀ y ∈ Z, okR y := fun y hy => hZ y (List.Mem.tail _ hy)
    dsimp [okR] at hx
    rcases hx with ⟨rfl, hq⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    dsimp [RP, LP, sd, reg]
    refine stepStar_trans (PassR l p q' (RP Z r)) ?_
    exact ih hZ' _ r

lemma PassesL (Z : List (Nat × Nat × Bool)) (hZ : ∀ x ∈ Z, okL x) (l r : ListBlank (Fin 2)) :
    ((LP Z l <+ [0]) <{{C}} r) [target_tm]⊢* ((l <+ [0]) <{{C}} RP (Z.map touch) r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hx := hZ (p, q, d) (List.Mem.head _)
    have hZ' : ∀ y ∈ Z, okL y := fun y hy => hZ y (List.Mem.tail _ hy)
    dsimp [okL] at hx
    rcases hx with ⟨rfl, hq⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
    dsimp [RP, LP, List.map, touch, sd, reg]
    refine stepStar_trans (ih hZ' (reg p (q' + 2) l) r) ?_
    exact PassL l p q' (RP (Z.map touch) r)

lemma OvPasses (Z : List (Nat × Nat × Bool)) (hZ : ∀ x ∈ Z, okO x) (l r : ListBlank (Fin 2)) :
    (LP Z l <{{C}} r) [target_tm]⊢* (l <{{C}} OvR Z r) := by
  induction Z generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    have hx := hZ (p, q, d) (List.Mem.head _)
    have hZ' : ∀ y ∈ Z, okO y := fun y hy => hZ y (List.Mem.tail _ hy)
    dsimp [okO] at hx
    rcases hx with ⟨hp, hq⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    dsimp [OvR, LP, reg]
    refine stepStar_trans (ih hZ' (reg (p' + 1) (q' + 1) l) r) ?_
    exact OvL l p' q' (OvR Z r)

lemma okL_R {Z : List (Nat × Nat × Bool)} (hZ : ∀ x ∈ Z, okL x) : ∀ x ∈ Z, okR x := by
  intro x hx
  obtain ⟨h1, h2⟩ := hZ x hx
  exact ⟨h1, by omega⟩

lemma Dec (h : Nat) (Z : List (Nat × Nat × Bool)) (p q : Nat) (R : List (Nat × Nat × Bool)) (T : Tl)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ (p, q + 2, true) :: R) T) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch ++ (p + 1, q + 1, false) :: R) T) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd]
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  refine stepStar_trans (PassesR Z (okL_R hZ) _ _) ?_
  refine stepStar_trans (Borrow _ p q _) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  exact EndPh h _

lemma DecMerge (h : Nat) (Z : List (Nat × Nat × Bool)) (p p' q' : Nat) (d' : Bool) (R : List (Nat × Nat × Bool)) (T : Tl)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ (p, 1, true) :: (p', q', d') :: R) T) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch ++ (p + p' + 3, q', d') :: R) T) := by
  unfold K
  rw [RP_app, RP_app]
  dsimp [RP, sd]
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  refine stepStar_trans (PassesR Z (okL_R hZ) _ _) ?_
  refine stepStar_trans (MergeB _ p p' _) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  exact EndPh h _

lemma DecMergeTail (h : Nat) (Z : List (Nat × Nat × Bool)) (p t : Nat)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, 1, true)]) (.TA t)) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch) (.TA (p + t + 3))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  refine stepStar_trans (PassesR Z (okL_R hZ) _ _) ?_
  refine stepStar_trans (MergeB _ p t _) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  exact EndPh h _

lemma DecMergeEmpty (h : Nat) (Z : List (Nat × Nat × Bool)) (p : Nat)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, 1, true)]) .TN) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch) (.TA (p + 2))) := by
  unfold K
  rw [RP_app]
  dsimp [RP, sd, RT]
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  refine stepStar_trans (PassesR Z (okL_R hZ) _ _) ?_
  refine stepStar_trans (MergeE _ p) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  exact EndPh h _

lemma forall_snoc {α : Type*} {P : α → Prop} {Z : List α} {x : α}
    (hZ : ∀ y ∈ Z, P y) (hx : P x) : ∀ y ∈ Z ++ [x], P y := by
  intro y hy
  rcases List.mem_append.mp hy with hyZ | hyx
  · exact hZ y hyZ
  · rcases List.mem_singleton.mp hyx with rfl
    exact hx

lemma EndR (h : Nat) (Z : List (Nat × Nat × Bool)) (p q : Nat)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, q + 2, false)]) .TN) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch ++ [(p + 1, q + 1, false)]) (.TA 1)) := by
  unfold K
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  have hZR : ∀ x ∈ Z ++ [(p, q + 2, false)], okR x := forall_snoc (okL_R hZ) ⟨rfl, by dsimp; omega⟩
  refine stepStar_trans (PassesR (Z ++ [(p, q + 2, false)]) hZR _ _) ?_
  rw [LP_app]
  dsimp [LP, RT, reg]
  refine stepStar_trans (EndT _ p q) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  rw [RP_app]
  exact EndPh h _

lemma EndLast (h : Nat) (Z : List (Nat × Nat × Bool)) (p : Nat)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, 1, false)]) .TN) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch) (.TA (p + 4))) := by
  unfold K
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  have hZR : ∀ x ∈ Z ++ [(p, 1, false)], okR x := forall_snoc (okL_R hZ) ⟨rfl, by dsimp; omega⟩
  refine stepStar_trans (PassesR (Z ++ [(p, 1, false)]) hZR _ _) ?_
  rw [LP_app]
  dsimp [LP, RT, reg]
  refine stepStar_trans (EndLastT _ p) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  exact EndPh h _

lemma X2 (h : Nat) (Z : List (Nat × Nat × Bool)) (p q k : Nat)
    (hZ : ∀ x ∈ Z, okL x) :
    (K h (Z ++ [(p, q + 2, false)]) (.TB (k + 1))) [target_tm]⊢⁺
    (K (h + 4) (Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)]) .TN) := by
  unfold K
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  have hZR : ∀ x ∈ Z ++ [(p, q + 2, false)], okR x := forall_snoc (okL_R hZ) ⟨rfl, by dsimp; omega⟩
  refine stepStar_trans (PassesR (Z ++ [(p, q + 2, false)]) hZR _ _) ?_
  rw [LP_app]
  dsimp [LP, RT, reg]
  refine stepStar_trans (X2T _ p q k) ?_
  refine stepStar_trans (PassesL Z hZ _ _) ?_
  rw [RP_app]
  exact EndPh h _

def ovp (q : Nat) : List (Nat × Nat × Bool) → Nat → List (Nat × Nat × Bool)
  | [], t => [(q, t + 1, true)]
  | (p', q', _) :: Z', t => (q, p', true) :: ovp q' Z' t

lemma ovp_eq (Z : List (Nat × Nat × Bool)) (q t : Nat) :
    RP (ovp q Z t) default = (([1, 0] : List (Fin 2)) ^ q) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default)) := by
  induction Z generalizing q t with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q', d⟩
    unfold ovp RP OvR
    rw [ih]
    rfl

lemma Ov (h p1 q1 : Nat) (Z : List (Nat × Nat × Bool)) (t : Nat)
    (hq1 : 1 ≤ q1) (hR : ∀ x ∈ Z, okR x) (hO : ∀ x ∈ Z, okO x) :
    (K h ((p1 + 2, q1, false) :: Z) (.TA t)) [target_tm]⊢⁺
    (K 2 ((h + 5, p1 + 1, false) :: ovp q1 Z t) .TN) := by
  unfold K
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  have hZR : ∀ x ∈ (p1 + 2, q1, false) :: Z, okR x := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hxZ
    · exact ⟨rfl, hq1⟩
    · exact hR x hxZ
  refine stepStar_trans (PassesR ((p1 + 2, q1, false) :: Z) hZR _ _) ?_
  dsimp [RT, LP]
  refine stepStar_trans (OvT _ t) ?_
  refine stepStar_trans (OvPasses Z hO _ _) ?_
  obtain ⟨q1', rfl⟩ : ∃ q1', q1 = q1' + 1 := ⟨q1 - 1, by omega⟩
  dsimp [reg]
  refine stepStar_trans (OvL _ (p1 + 1) q1' _) ?_
  have hEnd := OvEnd h p1 ((([1, 0] : List (Fin 2)) ^ (q1' + 1)) +> OvR Z ((([0, 1] : List (Fin 2)) ^ (t + 1)) +> ([0, 0, 0, 1] +> default)))
  dsimp [RP, sd, RT]
  rw [ovp_eq]
  exact hEnd

def ovpX (q : Nat) : List (Nat × Nat × Bool) → Nat → List (Nat × Nat × Bool)
  | [], pa => [(q, pa, false)]
  | (p', q', _) :: Z', pa => (q, p', true) :: ovpX q' Z' pa

lemma ovpX_eq (Z : List (Nat × Nat × Bool)) (q pa : Nat) (r : ListBlank (Fin 2)) :
    RP (ovpX q Z pa) r = (([1, 0] : List (Fin 2)) ^ q) +> OvR Z ((([0, 1] : List (Fin 2)) ^ pa) +> ([0, 0, 1, 0] +> r)) := by
  induction Z generalizing q pa r with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q', d⟩
    unfold ovpX RP OvR
    rw [ih]
    rfl

lemma tailB_eq (n : Nat) :
    [0, 0, 1, 0, 1, 0, 1] +> ((([1, 0] : List (Fin 2)) ^ (n + 1)) +> ([1] +> default)) =
    [0, 0, 1, 0] +> RT (.TB n) := by
  dsimp [RT]
  rw [pow_10_cons_1]
  rfl

lemma X1 (h p1 q1 : Nat) (Z : List (Nat × Nat × Bool)) (pa pb : Nat)
    (hq1 : 1 ≤ q1) (hR : ∀ x ∈ Z, okR x) (hO : ∀ x ∈ Z, okO x) :
    (K h ((p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)]) .TN) [target_tm]⊢⁺
    (K 2 ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) (.TB (pb + 3))) := by
  unfold K
  refine stepPlus_stepStar_stepPlus (Start h _) ?_
  have hZR : ∀ x ∈ (p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)], okR x := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨rfl, hq1⟩
    · rcases List.mem_append.mp hx' with hxZ | hx2
      · exact hR x hxZ
      · rcases List.mem_cons.mp hx2 with rfl | hx1
        · exact ⟨rfl, by dsimp; omega⟩
        · rcases List.mem_singleton.mp hx1 with rfl
          exact ⟨rfl, by dsimp; omega⟩
  refine stepStar_trans (PassesR _ hZR _ _) ?_
  dsimp [LP]
  rw [LP_app]
  dsimp [LP, RT, reg]
  refine stepStar_trans (EndLastT _ pb) ?_
  dsimp [reg]
  refine stepStar_trans (X1Sw _ pa _) ?_
  refine stepStar_trans (OvPasses Z hO _ _) ?_
  obtain ⟨q1', rfl⟩ : ∃ q1', q1 = q1' + 1 := ⟨q1 - 1, by omega⟩
  dsimp [reg]
  refine stepStar_trans (OvL _ (p1 + 1) q1' _) ?_
  refine stepStar_trans (OvEnd h p1 _) ?_
  rw [pow_10_cons_1 (pb + 4)]
  dsimp [RP, sd, RT]
  rw [ovpX_eq]
  exact ⟨0, rfl⟩

lemma init0_chunk0 :
    (default {{A}}> default) [target_tm]⊢*
    (([1, 1, 0, 1] +> default) {{E}}> ([0, 1, 0, 0, 1, 0, 0, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk1 :
    (([1, 1, 0, 1] +> default) {{E}}> ([0, 1, 0, 0, 1, 0, 0, 0, 1] +> default)) [target_tm]⊢*
    (([1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1] +> default) <{{C}} ([1, 0, 1, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk2 :
    (([1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1] +> default) <{{C}} ([1, 0, 1, 0, 1] +> default)) [target_tm]⊢*
    (([0, 1, 0, 1, 0, 1, 0, 1] +> default) <{{C}} ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk3 :
    (([0, 1, 0, 1, 0, 1, 0, 1] +> default) <{{C}} ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default)) [target_tm]⊢*
    (([0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default) {{D}}> ([0, 1, 0, 1, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk4 :
    (([0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default) {{D}}> ([0, 1, 0, 1, 0, 1] +> default)) [target_tm]⊢*
    (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default) <{{E}} ([0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0R rfl ?_
  refine stepStar_R0L rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk5 :
    (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default) <{{E}} ([0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] +> default)) [target_tm]⊢*
    (([1, 1, 0, 1, 0, 1] +> default) {{B}}> ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  refine stepStar_L0R rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk6 :
    (([1, 1, 0, 1, 0, 1] +> default) {{B}}> ([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] +> default)) [target_tm]⊢*
    (([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1] +> default) <{{D}} ([1, 0, 1, 0, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0_chunk7 :
    (([1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1] +> default) <{{D}} ([1, 0, 1, 0, 0, 1] +> default)) [target_tm]⊢*
    (default <{{D}} ([1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1] +> default)) := by
  simp only [append_cons_lb, append_nil_lb]
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LR rfl ?_
  refine stepStar_RR rfl ?_
  refine stepStar_RL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_LL rfl ?_
  refine stepStar_L0L rfl ?_
  try simp only [append_cons_lb, append_nil_lb, zero_cons_default]
  exact ⟨0, rfl⟩

lemma init0 : (init []) [target_tm]⊢* (K 2 [(7, 4, false)] .TN) := by
  change (default {{A}}> default) [target_tm]⊢* _
  refine stepStar_trans init0_chunk0 ?_
  refine stepStar_trans init0_chunk1 ?_
  refine stepStar_trans init0_chunk2 ?_
  refine stepStar_trans init0_chunk3 ?_
  refine stepStar_trans init0_chunk4 ?_
  refine stepStar_trans init0_chunk5 ?_
  refine stepStar_trans init0_chunk6 ?_
  refine stepStar_trans init0_chunk7 ?_
  simp only [K, RP, RT, sd, pow_succ_lb, pow_zero_lb, append_cons_lb, append_nil_lb, zero_cons_default, Bool.false_eq_true, ↓reduceIte]
  exact ⟨0, rfl⟩

def base_0666 : List (Nat × Nat × Bool) := [(47, 32, false), (40, 33, true), (13, 34, true)]

lemma init_to_base : (K 2 [(7, 4, false)] .TN) [target_tm]⊢* (K 2 base_0666 .TN) := by
  refine stepStar_trans (stepPlus_stepStar (EndR 2 [] 7 2 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Ov 6 6 3 [] 1 (by decide) (by decide) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 2 [(11, 7, false)] 3 0 [] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 6 [] 12 4 [(4, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (EndLast 10 [(13, 5, false)] 4 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 14 [] 14 2 [] (.TA 8) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Ov 18 13 3 [] 8 (by decide) (by decide) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 2 [(23, 14, false)] 3 7 [] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 6 [] 24 11 [(4, 8, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (EndR 10 [(25, 12, false)] 4 6 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 14 [] 26 9 [(5, 7, false)] (.TA 1) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Ov 18 25 10 [(5, 7, false)] 1 (by decide) (by decide) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 2 [(23, 26, false)] 10 3 [(7, 2, true)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 6 [] 24 23 [(11, 4, false), (7, 2, true)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 10 [(25, 24, false), (11, 4, false)] 7 0 [] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 14 [] 26 21 [(12, 3, true), (8, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 18 [(27, 22, false)] 12 1 [(8, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 22 [] 28 19 [(13, 2, false), (8, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (EndLast 26 [(29, 20, false), (13, 2, false)] 8 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 30 [] 30 17 [(14, 1, true)] (.TA 12) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (DecMergeTail 34 [(31, 18, false)] 14 12 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 38 [] 32 15 [] (.TA 29) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Ov 42 31 16 [] 29 (by decide) (by decide) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 2 [(47, 32, false)] 16 28 [] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 6 [] 48 29 [(17, 29, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (EndR 10 [(49, 30, false)] 17 27 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 14 [] 50 27 [(18, 28, false)] (.TA 1) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Ov 18 49 28 [(18, 28, false)] 1 (by decide) (by decide) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 2 [(23, 50, false)] 28 16 [(28, 2, true)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 6 [] 24 47 [(29, 17, false), (28, 2, true)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 10 [(25, 48, false), (29, 17, false)] 28 0 [] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 14 [] 26 45 [(30, 16, true), (29, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 18 [(27, 46, false)] 30 14 [(29, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 22 [] 28 43 [(31, 15, false), (29, 1, false)] .TN (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (EndLast 26 [(29, 44, false), (31, 15, false)] 29 (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 30 [] 30 41 [(32, 14, true)] (.TA 33) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 34 [(31, 42, false)] 32 12 [] (.TA 33) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Dec 38 [] 32 39 [(33, 13, false)] (.TA 33) (by decide))) ?_
  refine stepStar_trans (stepPlus_stepStar (Ov 42 31 40 [(33, 13, false)] 33 (by decide) (by decide) (by decide))) ?_
  exact ⟨0, rfl⟩
-- ============================================================================
-- PART 2: Arithmetic Invariant J, Step Preservation Jstep, and Non-Halting
-- ============================================================================

abbrev Tri := Nat × Nat × Bool

def bv (d : Bool) : Nat := if d then 1 else 0

def dv : List Tri → Nat
  | [] => 0
  | (_, _, d) :: P' => bv d + 2 * dv P'

def dig (x : Tri) : Bool := x.2.2

def All0 : List Tri → Prop
  | [] => True
  | (_, _, d) :: Z => d = false ∧ All0 Z

lemma pow2_pos (n : Nat) : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)

lemma pow2_succ (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

lemma dv_lt (P : List Tri) : dv P < 2 ^ P.length := by
  induction P with
  | nil => decide
  | cons x P ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [dv, List.length]
    rw [pow2_succ]
    cases d <;> dsimp [bv] <;> omega

lemma dv_zeros (Z R : List Tri) (hZ : All0 Z) : dv (Z ++ R) = 2 ^ Z.length * dv R := by
  induction Z with
  | nil => dsimp [dv, List.length]; omega
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rcases hZ with ⟨rfl, hZ'⟩
    dsimp [dv, bv, List.length]
    rw [ih hZ', pow2_succ]
    ring

lemma dv_zero (Z : List Tri) (hZ : All0 Z) : dv Z = 0 := by
  have h := dv_zeros Z [] hZ
  rw [List.append_nil] at h
  dsimp [dv] at h
  omega

lemma dv_tz (Z R : List Tri) (hZ : All0 Z) :
    dv (Z.map touch ++ R) + 1 = 2 ^ Z.length + 2 ^ Z.length * dv R := by
  induction Z with
  | nil => dsimp [dv, List.length, List.map]; omega
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    rcases hZ with ⟨rfl, hZ'⟩
    dsimp [List.map, touch, dv, bv, List.length]
    have ih' := ih hZ'
    rw [pow2_succ, Nat.mul_assoc]
    omega

lemma dv_tz' (Z R : List Tri) (hZ : All0 Z) :
    dv (Z.map touch ++ R) = 2 ^ Z.length - 1 + 2 ^ Z.length * dv R := by
  have h := dv_tz Z R hZ
  have hp := pow2_pos Z.length
  omega

def AllI (Pr : Nat → Tri → List Tri → Prop) : Nat → List Tri → Prop
  | _, [] => True
  | i, x :: Y => Pr i x Y ∧ AllI Pr (i + 1) Y

lemma AllI_app (Pr : Nat → Tri → List Tri → Prop) (Z : List Tri) :
    ∀ (i : Nat) (R : List Tri), AllI Pr i (Z ++ R) → AllI Pr (i + Z.length) R := by
  induction Z with
  | nil => intro i R h; exact h
  | cons x Z ih =>
    intro i R h
    rcases h with ⟨_, h2⟩
    dsimp [List.length]
    have heq : i + (Z.length + 1) = (i + 1) + Z.length := by omega
    rw [heq]
    exact ih (i + 1) R h2

lemma AllI_mono (Pr Pr' : Nat → Tri → List Tri → Prop) (P : List Tri) :
    ∀ (i : Nat), (∀ j x Y, i ≤ j → Pr j x Y → Pr' j x Y) → AllI Pr i P → AllI Pr' i P := by
  induction P with
  | nil => intro _ _ _; trivial
  | cons x P ih =>
    intro i hm h
    rcases h with ⟨h1, h2⟩
    refine ⟨hm i x P (Nat.le_refl i) h1, ih (i + 1) ?_ h2⟩
    intro j y Y hj
    exact hm j y Y (by omega)

lemma AllI_shift (Pr Pr' : Nat → Tri → List Tri → Prop) (P : List Tri) :
    ∀ (i : Nat), (∀ j x Y, i ≤ j → Pr (j + 1) x Y → Pr' j x Y) → AllI Pr (i + 1) P → AllI Pr' i P := by
  induction P with
  | nil => intro _ _ _; trivial
  | cons x P ih =>
    intro i hm h
    rcases h with ⟨h1, h2⟩
    refine ⟨hm i x P (Nat.le_refl i) h1, ih (i + 1) ?_ h2⟩
    intro j y Y hj
    exact hm j y Y (by omega)

lemma AllI_touchZ (Pr Pr' : Nat → Tri → List Tri → Prop) (R R' : List Tri) :
    ∀ (Z : List Tri) (i : Nat),
    All0 Z →
    (∀ j p q Zr, All0 Zr → j + (Zr.length + 1) = i + Z.length →
      Pr j (p, q, false) (Zr ++ R) → Pr' j (p + 1, q - 1, true) (Zr.map touch ++ R')) →
    AllI Pr i (Z ++ R) →
    AllI Pr' (i + Z.length) R' →
    AllI Pr' i (Z.map touch ++ R') := by
  intro Z
  induction Z with
  | nil =>
    intro i _ _ _ hR'
    exact hR'
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    intro i hZ hob hA hR'
    rcases hZ with ⟨rfl, hZ'⟩
    rcases hA with ⟨h1, h2⟩
    dsimp [List.map, touch, AllI, List.length] at *
    refine ⟨hob i p q Z hZ' (by omega) h1, ?_⟩
    apply ih (i + 1) hZ'
    · intro j p' q' Zr hZr hj
      exact hob j p' q' Zr hZr (by omega)
    · exact h2
    · have heq : (i + 1) + Z.length = i + (Z.length + 1) := by omega
      rw [heq]
      exact hR'

inductive Phase where
  | E1 | E2 | E1t | E2t | T0 | L1 | L2 | LX
  deriving DecidableEq

def PN (ph : Phase) (c4 : Bool) (p q n tv : Nat) : Prop :=
  match ph with
  | .E1 => match n with
           | 0 => q ≥ tv + 2 ^ n + 1 ∧ p + tv + 2 ^ n ≥ 3
           | _ + 1 => q ≥ tv + 3 * 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv + 2 ^ n ≥ 3 * 2 ^ n
  | .E2 => match n with
           | 0 => q ≥ tv + 1 ∧ p + tv ≥ 3
           | _ + 1 => q ≥ tv + 2 * 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv ≥ 3 * 2 ^ n
  | .E1t => match n with
            | 0 => q ≥ tv + 2 ^ n + 1 ∧ p + tv + 2 ^ n = 5
            | _ + 1 => q ≥ tv + 2 * 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv + 2 ^ n ≥ 3 * 2 ^ n
  | .E2t => match n with
            | 0 => q ≥ tv + 1 ∧ p + tv = 5
            | _ + 1 => q ≥ tv + 2 ^ n + 1 ∧ (p + tv) % 2 = 1 ∧ p + tv ≥ 3 * 2 ^ n
  | .T0 => q ≥ tv + 7 * 2 ^ n + 1 ∧ p + tv + 5 * 2 ^ n ≥ 6 * 2 ^ n ∧
           match n with
           | 0 => tv = 0 ∧ p % 2 = 0
           | _ + 1 => (p + tv) % 2 = 1
  | .L1 => q + 2 ^ n ≥ tv + 2 ∧
           match n with
           | 0 => q = tv + 2 ^ n
           | 1 => p + tv + 2 ^ n ≥ (if c4 then 4 else 5) * 2 ^ n ∧
                  (q ≥ tv + 2 ^ n + 1 ∨ (q + tv) % 2 = 0) ∧ (if c4 then q = tv + 2 ^ n else True)
           | _ + 2 => p + tv + 2 ^ n ≥ (if c4 then 4 else 5) * 2 ^ n ∧ (q + tv) % 2 = 0
  | .LX => match n with
           | 0 => q = tv + 1
           | 1 => p + tv ≥ 4 * 2 ^ n ∧ q = tv + 1
           | _ + 2 => p + tv ≥ 4 * 2 ^ n ∧ (q + tv) % 2 = 0
  | .L2 => p + tv ≥ (if c4 then 4 else 5) * (2 * 2 ^ n) ∧
           match n with
           | 0 => (q ≥ tv + 1 ∨ (q + tv) % 2 = 0) ∧ (if c4 then q = tv else True)
           | _ + 1 => (q + tv) % 2 = 0

def PI (ph : Phase) (h i p q n tv : Nat) : Prop :=
  match i with
  | 1 => h % 2 = 0 ∧
         match ph with
         | .E1 | .E1t => 2 ≤ n ∧ p + tv + 2 ^ n + 3 ≥ 11 * 2 ^ n ∧ h + 4 * (tv + 2 ^ n) + 6 ≥ 12 * 2 ^ n
         | .E2 | .E2t => 2 ≤ n ∧ p + tv + 3 ≥ 11 * 2 ^ n ∧ h + 4 * tv + 6 ≥ 12 * 2 ^ n
         | .T0 => 2 ≤ n ∧ p + tv + 5 * 2 ^ n + 3 ≥ 22 * 2 ^ n ∧ h + 4 * (tv + 5 * 2 ^ n) + 6 ≥ 24 * 2 ^ n
         | .L1 => 2 ≤ n ∧ q ≥ tv + 3 * 2 ^ n ∧ h + 4 * (tv + 2 ^ n) + 6 ≥ 8 * 2 ^ n
         | .LX => 3 ≤ n ∧ q ≥ tv + 2 * 2 ^ n ∧ h + 4 * tv + 6 ≥ 8 * 2 ^ n
         | .L2 => 1 ≤ n ∧ q ≥ tv + 4 * 2 ^ n ∧ h + 4 * tv + 6 ≥ 16 * 2 ^ n
  | 2 => match ph with
         | .E1 | .E1t => p + tv + 2 ^ n + 1 ≥ 7 * 2 ^ n
         | .E2 | .E2t => p + tv + 1 ≥ 7 * 2 ^ n
         | .T0 => p + tv + 5 * 2 ^ n + 1 ≥ 14 * 2 ^ n
         | .L1 => q ≥ tv + 2 ^ n + 1
         | .LX | .L2 => q ≥ tv + 1
  | _ => True

def PC (ph : Phase) (c4 : Bool) (h i p q n tv : Nat) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ PN ph c4 p q n tv ∧ PI ph h i p q n tv

def PCx (ph : Phase) (c4 : Bool) (h : Nat) (i : Nat) (x : Tri) (Y : List Tri) : Prop :=
  PC ph c4 h i x.1 x.2.1 Y.length (dv (x :: Y))

lemma ob_touch (ph : Phase) (c4 : Bool) (h i p q n tv : Nat)
    (ht : 1 ≤ tv) (hq : 2 ≤ q) (hPC : PC ph c4 h i p q n tv) :
    PC ph c4 (h + 4) i (p + 1) (q - 1) n (tv - 1) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cases ph <;> cases c4 <;>
      (rcases n with _ | _ | n <;>
        (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))
  · rcases i with _ | _ | _ | i
    · trivial
    · cases ph <;>
        (try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega)
    · cases ph <;>
        (try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega)
    · trivial

lemma ob_merge (ph : Phase) (c4 : Bool) (h i p q n u U : Nat)
    (hph : ph = .L1 ∨ ph = .L2 ∨ ph = .LX)
    (hn : 1 ≤ n) (hu : 2 ≤ u) (hu2 : u % 2 = 0) (hU2 : U % 2 = 0) (hUu : U + u ≤ 2 * 2 ^ n)
    (hL1 : ph = .L1 → U + u ≤ 2 ^ n) (hLX : ph = .LX → 2 ≤ n) (hc4 : ph = .L1 → c4 = true → 2 ≤ n)
    (hi1 : i = 1 → 2 ≤ n) (hiX : ph = .LX → i = 1 → 3 ≤ n) (hq : 2 ≤ q)
    (hPC : PC ph c4 h i p q (n + 1) (u + 2 * U)) :
    PC ph c4 (h + 4) i (p + 1) (q - 1) n (u - 1 + U) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases hph with rfl | rfl | rfl
    · cases c4 <;>
        (rcases n with _ | _ | n <;>
          (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
           (try have := pow2_pos n); (try trivial) <;> omega))
    · cases c4 <;>
        (rcases n with _ | _ | n <;>
          (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
           (try have := pow2_pos n); (try trivial) <;> omega))
    · rcases n with _ | _ | n <;>
        (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega)
  · rcases i with _ | _ | _ | i
    · trivial
    · rcases hph with rfl | rfl | rfl <;>
        (try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         have := pow2_pos n; (try trivial) <;> omega)
    · rcases hph with rfl | rfl | rfl <;>
        (try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         have := pow2_pos n; (try trivial) <;> omega)
    · trivial

lemma ob_mt (c4 : Bool) (h i p q n : Nat) (hq : 2 ≤ q) (hi1 : i = 1 → 1 ≤ n)
    (hPC : PC .L2 c4 h i p q (n + 1) (2 * 2 ^ n)) :
    PC .L2 false (h + 4) i (p + 1) (q - 1) n (2 * 2 ^ n - 1) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cases c4 <;>
      (rcases n with _ | n <;>
        (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))
  · rcases i with _ | _ | _ | i
    · trivial
    · try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      have := pow2_pos n; (try trivial) <;> omega
    · try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      have := pow2_pos n; (try trivial) <;> omega
    · trivial

lemma ob_fuse (ph : Phase) (c4 : Bool) (h h' k p p' q' n tv : Nat)
    (hph : ph = .L1 ∨ ph = .L2 ∨ ph = .LX) (hk : 3 ≤ k)
    (hPC : PC ph c4 h (k + 1) p' q' n tv) :
    PC ph c4 h' k (p + p' + 3) q' n tv := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases hph with rfl | rfl | rfl <;> cases c4 <;>
      (rcases n with _ | _ | n <;>
        (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))
  · rcases k with _ | _ | _ | k <;> (try omega); trivial

lemma ob_far (ph : Phase) (c4 : Bool) (h h' i j p q n tv : Nat) (hi : 3 ≤ i) (hj : 3 ≤ j)
    (hPC : PC ph c4 h i p q n tv) :
    PC ph c4 h' j p q n tv := by
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨hp1, hq1, hN, ?_⟩
  rcases j with _ | _ | _ | j <;> (try omega); trivial

lemma ob_far2 (ph : Phase) (c4 : Bool) (h h' i p q n tv : Nat) (hi : 2 ≤ i)
    (hPC : PC ph c4 h i p q n tv) :
    PC ph c4 h' i p q n tv := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨hp1, hq1, hN, ?_⟩
  rcases i with _ | _ | _ | i <;> (try omega); exact hI; trivial

def endtr (ph ph' : Phase) : Prop :=
  (ph = .E1 ∧ ph' = .E2) ∨ (ph = .E1t ∧ ph' = .E2t)

lemma ob_end (ph ph' : Phase) (h i p q n : Nat) (htr : endtr ph ph') (hn : 1 ≤ n) (hq : 2 ≤ q)
    (hPC : PC ph false h i p q n 0) :
    PC ph' false (h + 4) i (p + 1) (q - 1) n (2 ^ n - 1) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases htr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (rcases n with _ | n <;>
        (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))
  · rcases i with _ | _ | _ | i
    · trivial
    · rcases htr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         have := pow2_pos n; (try trivial) <;> omega)
    · rcases htr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         have := pow2_pos n; (try trivial) <;> omega)
    · trivial

lemma ob_end_top (ph ph' : Phase) (h i p q : Nat) (htr : endtr ph ph') (hi : 3 ≤ i)
    (hPC : PC ph false h i p (q + 2) 0 0) :
    PC ph' false (h + 4) i (p + 1) (q + 1) 0 0 := by
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases htr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try trivial) <;> omega)
  · rcases i with _ | _ | _ | i <;> (try omega); trivial

lemma ob_endlast (c4 : Bool) (h i p q n : Nat) (hq : 2 ≤ q)
    (hPC : PC .L1 c4 h i p q (n + 1) 0) :
    PC .L2 c4 (h + 4) i (p + 1) (q - 1) n (2 * 2 ^ n - 1) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cases c4 <;>
      (rcases n with _ | n <;>
        (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))
  · rcases i with _ | _ | _ | i
    · trivial
    · try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      have := pow2_pos n; (try trivial) <;> omega
    · try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      have := pow2_pos n; (try trivial) <;> omega
    · trivial

lemma ob_x2 (h i p q n : Nat) (hn : 1 ≤ n) (hq : 2 ≤ q)
    (hPC : PC .T0 false h i p q n 0) :
    PC .E1t false (h + 4) i (p + 1) (q - 1) (n + 1) (3 * 2 ^ n - 1) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | n <;>
      (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try have := pow2_pos n); (try trivial) <;> omega)
  · rcases i with _ | _ | _ | i
    · trivial
    · try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      have := pow2_pos n; (try trivial) <;> omega
    · try simp only [PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      have := pow2_pos n; (try trivial) <;> omega
    · trivial

lemma ob_x2_top (h i p q : Nat) (hi : 3 ≤ i)
    (hPC : PC .T0 false h i p (q + 2) 0 0) :
    PC .E1t false (h + 4) i (p + 1) (q + 1) 1 2 := by
  rcases hPC with ⟨hp1, hq1, hN, _⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
    (try trivial) <;> omega
  · rcases i with _ | _ | _ | i <;> (try omega); trivial

lemma ob_x2_new (h i k : Nat) (hi : 3 ≤ i) (hk : 3 ≤ k) :
    PC .E1t false h i 3 k 0 1 := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies]
    trivial
  · rcases i with _ | _ | _ | i <;> (try omega); trivial

def ovtr (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) : Prop :=
  (ph = .E2 ∧ ph' = .L1 ∧ c4' = false ∧ Xp = (fun x => x ≠ 4)) ∨
  (ph = .E2 ∧ ph' = .LX ∧ c4' = false ∧ Xp = (fun x => x = 4)) ∨
  (ph = .E2t ∧ ph' = .L1 ∧ c4' = true ∧ Xp = (fun _ => True)) ∨
  (ph = .L2 ∧ ph' = .E1 ∧ c4' = false ∧ Xp = (fun _ => True))

lemma ob_ov_head (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h p1 q1 n : Nat)
    (htr : ovtr ph ph' c4' Xp)
    (hPC : PC ph false h 1 (p1 + 2) q1 n 0) :
    PC ph' c4' 2 1 (h + 5) (p1 + 1) (n + 1) (2 * (2 * 2 ^ n) - 2) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
      (rcases n with _ | _ | n <;>
        (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))
  · rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
      (rcases n with _ | _ | n <;>
        (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos n); (try trivial) <;> omega))

lemma ob_ov_step (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h i pp q p' q' m : Nat)
    (htr : ovtr ph ph' c4' Xp) (hi : 1 ≤ i)
    (hPC : PC ph false h i pp q (m + 1) 0)
    (hPC' : PC ph false h (i + 1) p' q' m 0)
    (hX : m = 0 → Xp p') :
    PC ph' c4' 2 (i + 1) q p' (m + 1) (2 * (2 * 2 ^ m) - 1) := by
  rcases hPC with ⟨hp, hq, hN, hI⟩
  rcases hPC' with ⟨hp', hq', hN', hI'⟩
  refine ⟨hq, hp', ?_, ?_⟩
  · rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      (rcases m with _ | _ | m <;>
        (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos m); (try trivial) <;> omega))
  · rcases i with _ | _ | i
    · omega
    · rcases htr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
        (rcases m with _ | _ | m <;>
          (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
           (try have := pow2_pos m); (try trivial) <;> omega))
    · trivial

lemma ob_ov_base (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h i pp q t : Nat)
    (htr : ovtr ph ph' c4' Xp) (hi : 1 ≤ i)
    (ht1 : ph = .L2 → 2 ≤ t) (ht2 : ph ≠ .L2 → t = 1)
    (hPC : PC ph false h i pp q 0 0) :
    PC ph' c4' 2 (i + 1) q (t + 1) 0 1 := by
  rcases hPC with ⟨hp, hq, hN, hI⟩
  refine ⟨hq, by omega, ?_, ?_⟩
  · rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
      (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try (have := ht2 (by decide); omega)) <;> (try omega))
  · rcases i with _ | _ | i
    · omega
    · rcases htr with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
        (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try (have := ht2 (by decide); omega)) <;> (try omega))
    · trivial

lemma ob_x1_head (h p1 q1 n : Nat)
    (hPC : PC .LX false h 1 (p1 + 2) q1 (n + 2) 0) :
    PC .T0 false 2 1 (h + 5) (p1 + 1) (n + 1) (2 * 2 ^ n - 2) := by
  rcases hPC with ⟨hp1, hq1, hN, hI⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases n with _ | _ | n <;>
      (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try have := pow2_pos n); (try trivial) <;> omega)
  · rcases n with _ | _ | n <;>
      (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try have := pow2_pos n); (try trivial) <;> omega)

lemma ob_x1_step (h i pp q p' q' m : Nat) (hi : 1 ≤ i)
    (hPC : PC .LX false h i pp q (m + 3) 0)
    (hPC' : PC .LX false h (i + 1) p' q' (m + 2) 0) :
    PC .T0 false 2 (i + 1) q p' (m + 1) (2 * 2 ^ m - 1) := by
  rcases hPC with ⟨hp, hq, hN, hI⟩
  rcases hPC' with ⟨hp', hq', hN', hI'⟩
  refine ⟨hq, hp', ?_, ?_⟩
  · rcases m with _ | m <;>
      (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try have := pow2_pos m); (try trivial) <;> omega)
  · rcases i with _ | _ | i
    · omega
    · rcases m with _ | m <;>
        (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
         (try have := pow2_pos m); (try trivial) <;> omega)
    · trivial

lemma ob_x1_base (h i pp q pa : Nat) (hi : 1 ≤ i)
    (hPC : PC .LX false h i pp q 2 0)
    (hPC' : PC .LX false h (i + 1) (pa + 1) 1 1 0) :
    PC .T0 false 2 (i + 1) q (pa + 1) 0 0 := by
  rcases hPC with ⟨hp, hq, hN, hI⟩
  rcases hPC' with ⟨hp', hq', hN', hI'⟩
  refine ⟨hq, by omega, ?_, ?_⟩
  · try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
    (try trivial) <;> omega
  · rcases i with _ | _ | i
    · omega
    · try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *
      (try trivial) <;> omega
    · trivial

lemma ovp_len (q : Nat) (Z : List Tri) (t : Nat) : (ovp q Z t).length = Z.length + 1 := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih => rcases x with ⟨p, q', d⟩; dsimp [ovp, List.length]; rw [ih]

lemma ovp_dv (q : Nat) (Z : List Tri) (t : Nat) : dv (ovp q Z t) + 1 = 2 ^ (Z.length + 1) := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q', d⟩
    dsimp [ovp, dv, bv, List.length]
    have ih' := ih q'
    rw [pow2_succ (Z.length + 1)]
    omega

lemma ovpX_len (q : Nat) (Z : List Tri) (pa : Nat) : (ovpX q Z pa).length = Z.length + 1 := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih => rcases x with ⟨p, q', d⟩; dsimp [ovpX, List.length]; rw [ih]

lemma ovpX_dv (q : Nat) (Z : List Tri) (pa : Nat) : dv (ovpX q Z pa) + 1 = 2 ^ Z.length := by
  induction Z generalizing q with
  | nil => rfl
  | cons x Z ih =>
    rcases x with ⟨p, q', d⟩
    dsimp [ovpX, dv, bv, List.length]
    have ih' := ih q'
    rw [pow2_succ Z.length]
    omega

def lastOK (Xp : Nat → Prop) : List Tri → Prop
  | [] => True
  | [(p, _, _)] => Xp p
  | _ :: Z' => lastOK Xp Z'

lemma lastOK_cons (Xp : Nat → Prop) (p q : Nat) (d : Bool) (Z : List Tri)
    (h : lastOK Xp ((p, q, d) :: Z)) : (Z = [] → Xp p) ∧ lastOK Xp Z := by
  cases Z with
  | nil => exact ⟨fun _ => h, trivial⟩
  | cons z Z' => exact ⟨(fun h' => by nomatch h'), h⟩

lemma lastOK_dec (Z : List Tri) : lastOK (fun x => x = 4) Z ∨ lastOK (fun x => x ≠ 4) Z := by
  induction Z with
  | nil => exact Or.inl trivial
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    cases Z with
    | nil =>
      dsimp [lastOK]
      if h : p = 4 then exact Or.inl h else exact Or.inr h
    | cons z Z' => exact ih

lemma lastOK_True (Z : List Tri) : lastOK (fun _ => True) Z := by
  induction Z with
  | nil => trivial
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    cases Z with
    | nil => trivial
    | cons z Z' => exact ih

lemma All0_app (Z R : List Tri) : All0 (Z ++ R) ↔ All0 Z ∧ All0 R := by
  induction Z with
  | nil => dsimp [All0]; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons x Z ih =>
    rcases x with ⟨p, q, d⟩
    dsimp [All0]
    rw [ih]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

lemma AllI_ovp (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h t : Nat)
    (htr : ovtr ph ph' c4' Xp) (ht1 : ph = .L2 → 2 ≤ t) (ht2 : ph ≠ .L2 → t = 1) :
    ∀ (Z : List Tri) (i pp q : Nat),
    1 ≤ i → All0 Z → lastOK Xp Z → PC ph false h i pp q Z.length 0 →
    AllI (PCx ph false h) (i + 1) Z → AllI (PCx ph' c4' 2) (i + 1) (ovp q Z t) := by
  intro Z
  induction Z with
  | nil =>
    intro i pp q hi _ _ hPC _
    dsimp [ovp, AllI, PCx, List.length, dv, bv]
    exact ⟨ob_ov_base ph ph' c4' Xp h i pp q t htr hi ht1 ht2 hPC, trivial⟩
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    intro i pp q hi hZ hX hPC hA
    rcases hZ with ⟨rfl, hZ'⟩
    rcases hA with ⟨hH, hA'⟩
    have ⟨hX1, hX2⟩ := lastOK_cons Xp p' q' false Z hX
    dsimp [PCx] at hH
    rw [dv_zero ((p', q', false) :: Z) ⟨rfl, hZ'⟩] at hH
    dsimp [ovp, AllI]
    refine ⟨?_, ih (i + 1) p' q' (by omega) hZ' hX2 hH hA'⟩
    dsimp [PCx]
    rw [ovp_len]
    have hdv : dv ((q, p', true) :: ovp q' Z t) = 2 * (2 * 2 ^ Z.length) - 1 := by
      dsimp [dv, bv]
      have E := ovp_dv q' Z t
      rw [pow2_succ] at E
      omega
    rw [hdv]
    apply ob_ov_step ph ph' c4' Xp h i pp q p' q' Z.length htr hi hPC hH
    intro hm
    apply hX1
    cases Z with
    | nil => rfl
    | cons _ _ => dsimp [List.length] at hm; omega

lemma AllI_ovpX (h pa pb : Nat) :
    ∀ (Z : List Tri) (i pp q : Nat),
    1 ≤ i → All0 Z →
    PC .LX false h i pp q (Z.length + 2) 0 →
    AllI (PCx .LX false h) (i + 1) (Z ++ [(pa + 1, 1, false), (pb, 1, false)]) →
    AllI (PCx .T0 false 2) (i + 1) (ovpX q Z (pa + 1)) := by
  intro Z
  induction Z with
  | nil =>
    intro i pp q hi _ hPC hA
    dsimp [ovpX, AllI, List.append] at hA ⊢
    rcases hA with ⟨hHa, _⟩
    dsimp [PCx, List.length, dv, bv] at hHa ⊢
    exact ⟨ob_x1_base h i pp q pa hi hPC hHa, trivial⟩
  | cons x Z ih =>
    rcases x with ⟨p', q', d'⟩
    intro i pp q hi hZ hPC hA
    rcases hZ with ⟨rfl, hZ'⟩
    dsimp [List.append, AllI] at hA
    rcases hA with ⟨hH, hA'⟩
    dsimp [PCx] at hH
    have hZall : All0 ((p', q', false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) := by
      refine ⟨rfl, (All0_app Z _).mpr ⟨hZ', rfl, rfl, trivial⟩⟩
    rw [dv_zero _ hZall, List.length_append] at hH
    dsimp [List.length] at hH
    dsimp [ovpX, AllI]
    refine ⟨?_, ih (i + 1) p' q' (by omega) hZ' hH hA'⟩
    dsimp [PCx]
    rw [ovpX_len]
    have hdv : dv ((q, p', true) :: ovpX q' Z (pa + 1)) = 2 * 2 ^ Z.length - 1 := by
      dsimp [dv, bv]
      have E := ovpX_dv q' Z (pa + 1)
      omega
    rw [hdv]
    exact ob_x1_step h i pp q p' q' Z.length hi hPC hH

lemma passq (ph : Phase) (c4 : Bool) (h i p q n tv : Nat)
    (hPC : PC ph c4 h i p q n tv) (ht : 2 ≤ tv) (ht2 : tv % 2 = 0) : 2 ≤ q := by
  rcases hPC with ⟨_, _, hN, _⟩
  cases ph <;> cases c4 <;>
    (rcases n with _ | _ | n <;>
      (simp only [PN, pow2_succ, Bool.false_eq_true, ↓reduceIte] at *;
       (try have := pow2_pos n); omega))

lemma Z_okL (ph : Phase) (c4 : Bool) (h : Nat) :
    ∀ (Z : List Tri) (i : Nat) (x : Tri) (R : List Tri),
    All0 Z → dig x = true → AllI (PCx ph c4 h) i (Z ++ x :: R) → ∀ y ∈ Z, okL y := by
  intro Z
  induction Z with
  | nil => intro _ _ _ _ _ _ y hy; nomatch hy
  | cons z Z ih =>
    rcases z with ⟨p, q, d⟩
    intro i x R hZ hx hA
    rcases hZ with ⟨rfl, hZ'⟩
    rcases hA with ⟨hH, hA'⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hyZ
    · refine ⟨rfl, ?_⟩
      dsimp [PCx] at hH
      apply passq ph c4 h i p q (Z ++ x :: R).length (dv ((p, q, false) :: (Z ++ x :: R))) hH
      · dsimp [dv, bv]
        rw [dv_zeros Z (x :: R) hZ']
        rcases x with ⟨px, qx, dx⟩
        dsimp [dig] at hx; subst hx
        dsimp [dv, bv]
        have hp := pow2_pos Z.length
        have hpos : 2 ^ Z.length * (1 + 2 * dv R) ≥ 1 := Nat.mul_pos hp (by omega)
        omega
      · dsimp [dv, bv]; omega
    · exact ih (i + 1) x R hZ' hx hA' y hyZ

lemma borrow1 (ph : Phase) (c4 : Bool) (h k p n tv : Nat)
    (hk : 1 ≤ k) (ht : tv % 2 = 1) (hPC : PC ph c4 h k p 1 n tv) :
    (ph = .L1 ∨ ph = .L2 ∨ ph = .LX) ∧ 3 ≤ k ∧
    (ph = .L1 → 1 ≤ n ∧ tv + 1 ≤ 2 ^ n ∧ (c4 = true → 2 ≤ n)) ∧ (ph = .LX → 2 ≤ n) := by
  rcases hPC with ⟨hp, hq, hN, hI⟩
  have hph : ph = .L1 ∨ ph = .L2 ∨ ph = .LX := by
    cases ph <;> (try exact Or.inl rfl) <;> (try exact Or.inr (Or.inl rfl)) <;> (try exact Or.inr (Or.inr rfl))
    all_goals (exfalso; rcases n with _ | n <;>
      (simp only [PN, pow2_succ, Bool.false_eq_true, ↓reduceIte] at *;
       (try have := pow2_pos n); omega))
  refine ⟨hph, ?_, ?_, ?_⟩
  · rcases k with _ | _ | _ | k
    · omega
    · rcases hph with rfl | rfl | rfl <;> (simp only [PI, pow2_succ] at hI; have := pow2_pos n; omega)
    · rcases hph with rfl | rfl | rfl <;> (simp only [PI, pow2_succ] at hI; have := pow2_pos n; omega)
    · omega
  · intro hL1; subst hL1
    cases c4 <;>
      (rcases n with _ | _ | n <;>
        (simp only [PN, pow2_succ, Bool.false_eq_true, ↓reduceIte] at *;
         (try have := pow2_pos n);
         refine ⟨by omega, by omega, fun hc => by cases hc <;> omega⟩))
  · intro hLX; subst hLX
    rcases n with _ | _ | n <;>
      (simp only [PN, pow2_succ, Bool.false_eq_true, ↓reduceIte] at *;
       (try have := pow2_pos n); omega)

lemma inv_Dec (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p q : Nat) (R : List Tri)
    (hZ : All0 Z)
    (hA : AllI (PCx ph c4 h) 1 (Z ++ (p, q + 2, true) :: R)) :
    AllI (PCx ph c4 (h + 4)) 1 (Z.map touch ++ (p + 1, q + 1, false) :: R) := by
  have hB := AllI_app (PCx ph c4 h) Z 1 ((p, q + 2, true) :: R) hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, hR⟩
  apply AllI_touchZ (PCx ph c4 h) (PCx ph c4 (h + 4)) ((p, q + 2, true) :: R) ((p + 1, q + 1, false) :: R) Z 1 hZ _ hA
  · refine ⟨?_, ?_⟩
    · dsimp [PCx, dv, bv] at hx ⊢
      have heq : 0 + 2 * dv R = (1 + 2 * dv R) - 1 := by omega
      rw [heq]
      exact ob_touch ph c4 h (1 + Z.length) p (q + 2) R.length (1 + 2 * dv R) (by omega) (by omega) hx
    · apply AllI_mono _ _ R ((1 + Z.length) + 1) _ hR
      intro j y Y hj hy
      rcases y with ⟨py, qy, dy⟩
      dsimp [PCx] at hy ⊢
      exact ob_far2 ph c4 h (h + 4) j py qy Y.length (dv ((py, qy, dy) :: Y)) (by omega) hy
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx] at h0 ⊢
    rw [List.length_append, List.length_cons] at h0
    rw [List.length_append, List.length_map, List.length_cons]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr ((p, q + 2, true) :: R) hZr] at h0
    rw [dv_tz' Zr ((p + 1, q + 1, false) :: R) hZr]
    dsimp [dv, bv] at h0 ⊢
    simp only [Nat.zero_add] at h0 ⊢
    have hp := pow2_pos Zr.length
    have hmul : 2 ^ Zr.length * (1 + 2 * dv R) = 2 ^ Zr.length + 2 ^ Zr.length * (2 * dv R) := by ring
    have heq2 : 1 + 2 * (2 ^ Zr.length - 1 + 2 ^ Zr.length * (2 * dv R)) =
        2 * (2 ^ Zr.length * (1 + 2 * dv R)) - 1 := by omega
    rw [heq2]
    apply ob_touch ph c4 h j p0 q0 (Zr.length + (R.length + 1)) (2 * (2 ^ Zr.length * (1 + 2 * dv R)))
    · omega
    · apply passq ph c4 h j p0 q0 (Zr.length + (R.length + 1)) (2 * (2 ^ Zr.length * (1 + 2 * dv R))) h0
      · omega
      · omega
    · exact h0

def minlen : Phase → Nat
  | .LX => 3
  | .L2 => 1
  | _ => 2

lemma head_len (ph : Phase) (c4 : Bool) (h : Nat) (x : Tri) (Y : List Tri)
    (hPCx : PCx ph c4 h 1 x Y) : minlen ph ≤ Y.length := by
  rcases x with ⟨p, q, d⟩
  rcases hPCx with ⟨_, _, _, hI⟩
  cases ph <;> (simp only [PI, minlen] at hI ⊢; omega)

lemma AllI_len (ph : Phase) (c4 : Bool) (h : Nat) (P : List Tri) (hP : P ≠ [])
    (hA : AllI (PCx ph c4 h) 1 P) : minlen ph + 1 ≤ P.length := by
  cases P with
  | nil => exact absurd rfl hP
  | cons x Y =>
    rcases hA with ⟨h1, _⟩
    have := head_len ph c4 h x Y h1
    dsimp [List.length]
    omega

lemma q2_V0 (ph : Phase) (c4 : Bool) (h i p q n : Nat)
    (hPC : PC ph c4 h i p q n 0) (hn : 1 ≤ n) (hX : ph = .LX → 2 ≤ n) : 2 ≤ q := by
  rcases hPC with ⟨_, _, hN, _⟩
  cases ph <;> cases c4 <;>
    (rcases n with _ | _ | n <;>
      (try simp only [PN, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try have := pow2_pos n); omega))

lemma p1_V0 (ph : Phase) (c4 : Bool) (h p q n : Nat)
    (hPC : PC ph c4 h 1 p q n 0) (hph : ph = .E2 ∨ ph = .E2t ∨ ph = .L2 ∨ ph = .LX) : 2 ≤ p := by
  rcases hPC with ⟨_, _, hN, hI⟩
  rcases hph with rfl | rfl | rfl | rfl <;> cases c4 <;>
    (rcases n with _ | _ | n <;>
      (try simp only [PN, PI, pow2_succ, Nat.pow_zero, Nat.add_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, and_true, true_and, true_implies] at *;
       (try have := pow2_pos n); omega))

lemma L2_c4_V0 (h i p q : Nat) (hPC : PC .L2 true h i p q 0 0) : False := by
  rcases hPC with ⟨_, _, hN, _⟩
  simp only [PN, Bool.false_eq_true, ↓reduceIte] at hN
  omega

lemma AllI_okRO (ph : Phase) (c4 : Bool) (h : Nat) :
    ∀ (Z : List Tri) (i : Nat), All0 Z → AllI (PCx ph c4 h) i Z → (∀ x ∈ Z, okR x) ∧ (∀ x ∈ Z, okO x) := by
  intro Z
  induction Z with
  | nil => intro _ _ _; exact ⟨(fun _ h => by nomatch h), (fun _ h => by nomatch h)⟩
  | cons z Z ih =>
    rcases z with ⟨p, q, d⟩
    intro i hZ hA
    rcases hZ with ⟨rfl, hZ'⟩
    rcases hA with ⟨hH, hA'⟩
    rcases hH with ⟨hp, hq, _⟩
    have ⟨hR, hO⟩ := ih (i + 1) hZ' hA'
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxZ
      · exact ⟨rfl, hq⟩
      · exact hR x hxZ
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxZ
      · exact ⟨hp, hq⟩
      · exact hO x hxZ

lemma inv_Merge (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p p' q' : Nat) (d' : Bool) (R0 : List Tri)
    (hZ : All0 Z)
    (hA : AllI (PCx ph c4 h) 1 (Z ++ (p, 1, true) :: (p', q', d') :: R0)) :
    AllI (PCx ph c4 (h + 4)) 1 (Z.map touch ++ (p + p' + 3, q', d') :: R0) := by
  have hB := AllI_app (PCx ph c4 h) Z 1 ((p, 1, true) :: (p', q', d') :: R0) hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, hy, hR⟩
  have hlt := dv_lt ((p', q', d') :: R0)
  dsimp [List.length] at hlt
  rw [pow2_succ] at hlt
  set Hd := dv ((p', q', d') :: R0)
  have hx' : PC ph c4 h (1 + Z.length) p 1 (R0.length + 1) (1 + 2 * Hd) := hx
  have ⟨hph, hk, hL1, hLX⟩ := borrow1 ph c4 h (1 + Z.length) p (R0.length + 1) (1 + 2 * Hd) (by omega) (by omega) hx'
  apply AllI_touchZ (PCx ph c4 h) (PCx ph c4 (h + 4)) ((p, 1, true) :: (p', q', d') :: R0) ((p + p' + 3, q', d') :: R0) Z 1 hZ _ hA
  · refine ⟨?_, ?_⟩
    · dsimp [PCx] at hy ⊢
      have hdv : dv ((p + p' + 3, q', d') :: R0) = dv ((p', q', d') :: R0) := rfl
      rw [hdv]
      exact ob_fuse ph c4 h (h + 4) (1 + Z.length) p p' q' R0.length Hd hph hk hy
    · apply AllI_shift _ _ R0 ((1 + Z.length) + 1) _ hR
      intro j y Y hj hy0
      rcases y with ⟨py, qy, dy⟩
      dsimp [PCx] at hy0 ⊢
      exact ob_far ph c4 h (h + 4) (j + 1) j py qy Y.length (dv ((py, qy, dy) :: Y)) (by omega) (by omega) hy0
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx] at h0 ⊢
    rw [List.length_append, List.length_cons, List.length_cons] at h0
    rw [List.length_append, List.length_map, List.length_cons]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr ((p, 1, true) :: (p', q', d') :: R0) hZr] at h0
    rw [dv_tz' Zr ((p + p' + 3, q', d') :: R0) hZr]
    dsimp [dv, bv] at h0 ⊢
    have hHd : (if d' = true then 1 else 0) + 2 * dv R0 = Hd := rfl
    rw [hHd] at h0 ⊢
    set A := 2 ^ Zr.length
    set B := 2 ^ R0.length
    have hA1 : 1 ≤ A := pow2_pos Zr.length
    have hB1 : 1 ≤ B := pow2_pos R0.length
    have hpow_sum : 2 ^ (Zr.length + (R0.length + 1)) = A * (2 * B) := by
      rw [Nat.pow_add, pow2_succ]
    have hlen_eq : Zr.length + (R0.length + 1 + 1) = (Zr.length + (R0.length + 1)) + 1 := by omega
    rw [hlen_eq] at h0
    have htv_in : 0 + 2 * (A * (1 + 2 * Hd)) = 2 * A + 2 * (2 * A * Hd) := by ring
    rw [htv_in] at h0
    have htv_out : 1 + 2 * (A - 1 + A * Hd) = (2 * A - 1) + 2 * (A * Hd) := by omega
    rw [show 2 * (A * Hd) = 2 * A * Hd by ring] at htv_out
    rw [htv_out]
    have hq2 : 2 ≤ q0 := by
      apply passq ph c4 h j p0 q0 ((Zr.length + (R0.length + 1)) + 1) (2 * A + 2 * (2 * A * Hd)) h0
      · omega
      · omega
    have hUu_bound : 2 * A * Hd + 2 * A ≤ 2 * 2 ^ (Zr.length + (R0.length + 1)) := by
      rw [hpow_sum, show 2 * A * Hd + 2 * A = (2 * A) * (Hd + 1) by ring, show 2 * (A * (2 * B)) = (2 * A) * (2 * B) by ring]
      exact Nat.mul_le_mul_left (2 * A) (by omega)
    apply ob_merge ph c4 h j p0 q0 (Zr.length + (R0.length + 1)) (2 * A) (2 * A * Hd) hph
      (by omega) (by omega) (by omega) (by omega) hUu_bound
    · intro hph1
      have ⟨_, hb, _⟩ := hL1 hph1
      rw [pow2_succ] at hb
      rw [hpow_sum, show 2 * A * Hd + 2 * A = (2 * A) * (Hd + 1) by ring, show A * (2 * B) = (2 * A) * B by ring]
      exact Nat.mul_le_mul_left (2 * A) (by omega)
    · intro hphX; have := hLX hphX; omega
    · intro hph1 hc4; have ⟨_, _, hc2⟩ := hL1 hph1; have := hc2 hc4; omega
    · intro hj1; omega
    · intro hphX hj1; have := hLX hphX; omega
    · exact hq2
    · exact h0

lemma inv_MT (c4 : Bool) (h : Nat) (Z : List Tri) (p : Nat)
    (hZ : All0 Z) (hA : AllI (PCx .L2 c4 h) 1 (Z ++ [(p, 1, true)])) :
    AllI (PCx .L2 false (h + 4)) 1 (Z.map touch) ∧ 2 ≤ Z.length := by
  have hB := AllI_app (PCx .L2 c4 h) Z 1 [(p, 1, true)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  have ⟨_, hk, _⟩ := borrow1 .L2 c4 h (1 + Z.length) p 0 1 (by omega) (by decide) hx
  refine ⟨?_, by omega⟩
  rw [← List.append_nil (Z.map touch)]
  apply AllI_touchZ (PCx .L2 c4 h) (PCx .L2 false (h + 4)) [(p, 1, true)] [] Z 1 hZ _ hA trivial
  intro j p0 q0 Zr hZr hj h0
  dsimp [PCx] at h0 ⊢
  rw [List.length_append, List.length_singleton] at h0
  rw [List.length_append, List.length_map, List.length_nil, Nat.add_zero]
  dsimp [dv, bv] at h0 ⊢
  rw [dv_zeros Zr [(p, 1, true)] hZr] at h0
  rw [dv_tz' Zr [] hZr]
  dsimp [dv, bv] at h0 ⊢
  have hp := pow2_pos Zr.length
  have hin : 0 + 2 * (2 ^ Zr.length * 1) = 2 * 2 ^ Zr.length := by ring
  rw [hin] at h0
  have hout : 1 + 2 * (2 ^ Zr.length - 1) = 2 * 2 ^ Zr.length - 1 := by omega
  rw [hout]
  apply ob_mt c4 h j p0 q0 Zr.length _ (by omega) h0
  exact passq .L2 c4 h j p0 q0 (Zr.length + 1) (2 * 2 ^ Zr.length) h0 (by omega) (by omega)

lemma snoc_nn {α : Type*} (Z : List α) (y : α) : Z ++ [y] ≠ [] := by
  cases Z <;> intro h <;> nomatch h

lemma inv_End (ph ph' : Phase) (h : Nat) (Z : List Tri) (p q : Nat)
    (htr : endtr ph ph') (hZ : All0 Z)
    (hA : AllI (PCx ph false h) 1 (Z ++ [(p, q + 2, false)])) :
    AllI (PCx ph' false (h + 4)) 1 (Z.map touch ++ [(p + 1, q + 1, false)]) := by
  have hlen := AllI_len ph false h (Z ++ [(p, q + 2, false)]) (snoc_nn Z _) hA
  rw [List.length_append, List.length_singleton] at hlen
  have hm : minlen ph = 2 := by rcases htr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hB := AllI_app (PCx ph false h) Z 1 [(p, q + 2, false)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  apply AllI_touchZ (PCx ph false h) (PCx ph' false (h + 4)) [(p, q + 2, false)] [(p + 1, q + 1, false)] Z 1 hZ _ hA
  · dsimp [AllI, PCx, List.length, dv, bv] at hx ⊢
    exact ⟨ob_end_top ph ph' h (1 + Z.length) p q htr (by omega) hx, trivial⟩
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx] at h0 ⊢
    rw [List.length_append, List.length_singleton] at h0
    rw [List.length_append, List.length_map, List.length_singleton]
    dsimp [dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, q + 2, false)] hZr] at h0
    rw [dv_tz' Zr [(p + 1, q + 1, false)] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hp := pow2_pos Zr.length
    have hout : 1 + 2 * (2 ^ Zr.length - 1) = 2 ^ (Zr.length + 1) - 1 := by
      rw [pow2_succ]; omega
    rw [hout]
    apply ob_end ph ph' h j p0 q0 (Zr.length + 1) htr (by omega) _ h0
    apply q2_V0 ph false h j p0 q0 (Zr.length + 1) h0 (by omega)
    intro hLX; rcases htr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> nomatch hLX

lemma inv_X2 (h : Nat) (Z : List Tri) (p q k : Nat) (hZ : All0 Z) (hk : 3 ≤ k)
    (hA : AllI (PCx .T0 false h) 1 (Z ++ [(p, q + 2, false)])) :
    AllI (PCx .E1t false (h + 4)) 1 (Z.map touch ++ [(p + 1, q + 1, false), (3, k, true)]) := by
  have hlen := AllI_len .T0 false h (Z ++ [(p, q + 2, false)]) (snoc_nn Z _) hA
  rw [List.length_append, List.length_singleton] at hlen
  dsimp [minlen] at hlen
  have hB := AllI_app (PCx .T0 false h) Z 1 [(p, q + 2, false)] hA
  dsimp [AllI] at hB
  rcases hB with ⟨hx, _⟩
  apply AllI_touchZ (PCx .T0 false h) (PCx .E1t false (h + 4)) [(p, q + 2, false)] [(p + 1, q + 1, false), (3, k, true)] Z 1 hZ _ hA
  · dsimp [AllI, PCx, List.length, dv, bv] at hx ⊢
    refine ⟨ob_x2_top h (1 + Z.length) p q (by omega) hx, ob_x2_new (h + 4) ((1 + Z.length) + 1) k (by omega) hk, trivial⟩
  · intro j p0 q0 Zr hZr hj h0
    dsimp [PCx] at h0 ⊢
    rw [List.length_append, List.length_singleton] at h0
    rw [List.length_append, List.length_map]
    dsimp [List.length, dv, bv] at h0 ⊢
    rw [dv_zeros Zr [(p, q + 2, false)] hZr] at h0
    rw [dv_tz' Zr [(p + 1, q + 1, false), (3, k, true)] hZr]
    dsimp [dv, bv] at h0 ⊢
    have hp := pow2_pos Zr.length
    have hout : 1 + 2 * (2 ^ Zr.length - 1 + 2 ^ Zr.length * 2) = 3 * 2 ^ (Zr.length + 1) - 1 := by
      rw [pow2_succ]; omega
    rw [hout]
    have hlen_eq : Zr.length + 2 = (Zr.length + 1) + 1 := rfl
    rw [hlen_eq]
    apply ob_x2 h j p0 q0 (Zr.length + 1) (by omega) _ h0
    exact q2_V0 .T0 false h j p0 q0 (Zr.length + 1) h0 (by omega) (fun h => by nomatch h)

lemma inv_EndLast (c4 : Bool) (h : Nat) (Z : List Tri) (p : Nat)
    (hZ : All0 Z) (hA : AllI (PCx .L1 c4 h) 1 (Z ++ [(p, 1, false)])) :
    AllI (PCx .L2 c4 (h + 4)) 1 (Z.map touch) ∧ 2 ≤ Z.length := by
  have hlen := AllI_len .L1 c4 h (Z ++ [(p, 1, false)]) (snoc_nn Z _) hA
  rw [List.length_append, List.length_singleton] at hlen
  dsimp [minlen] at hlen
  refine ⟨?_, by omega⟩
  rw [← List.append_nil (Z.map touch)]
  apply AllI_touchZ (PCx .L1 c4 h) (PCx .L2 c4 (h + 4)) [(p, 1, false)] [] Z 1 hZ _ hA trivial
  intro j p0 q0 Zr hZr hj h0
  dsimp [PCx] at h0 ⊢
  rw [List.length_append, List.length_singleton] at h0
  rw [List.length_append, List.length_map, List.length_nil, Nat.add_zero]
  dsimp [dv, bv] at h0 ⊢
  rw [dv_zeros Zr [(p, 1, false)] hZr] at h0
  rw [dv_tz' Zr [] hZr]
  dsimp [dv, bv] at h0 ⊢
  have hp := pow2_pos Zr.length
  have hout : 1 + 2 * (2 ^ Zr.length - 1) = 2 * 2 ^ Zr.length - 1 := by omega
  rw [hout]
  apply ob_endlast c4 h j p0 q0 Zr.length _ h0
  exact q2_V0 .L1 c4 h j p0 q0 (Zr.length + 1) h0 (by omega) (fun h => by nomatch h)

lemma inv_Ov (ph ph' : Phase) (c4' : Bool) (Xp : Nat → Prop) (h p1 q1 : Nat) (Z : List Tri) (t : Nat)
    (htr : ovtr ph ph' c4' Xp) (ht1 : ph = .L2 → 2 ≤ t) (ht2 : ph ≠ .L2 → t = 1)
    (hZ : All0 Z) (hX : lastOK Xp Z)
    (hA : AllI (PCx ph false h) 1 ((p1 + 2, q1, false) :: Z)) :
    AllI (PCx ph' c4' 2) 1 ((h + 5, p1 + 1, false) :: ovp q1 Z t) := by
  dsimp [AllI] at hA ⊢
  rcases hA with ⟨hH, hA'⟩
  have hH' := hH
  dsimp [PCx] at hH'
  rw [dv_zero ((p1 + 2, q1, false) :: Z) ⟨rfl, hZ⟩] at hH'
  refine ⟨?_, AllI_ovp ph ph' c4' Xp h t htr ht1 ht2 Z 1 (p1 + 2) q1 (by omega) hZ hX hH' hA'⟩
  dsimp [PCx]
  rw [ovp_len]
  have hdv : dv ((h + 5, p1 + 1, false) :: ovp q1 Z t) = 2 * (2 * 2 ^ Z.length) - 2 := by
    dsimp [dv, bv]
    have E := ovp_dv q1 Z t
    rw [pow2_succ] at E
    omega
  rw [hdv]
  exact ob_ov_head ph ph' c4' Xp h p1 q1 Z.length htr hH'

lemma inv_X1 (h p1 q1 : Nat) (Z : List Tri) (pa pb : Nat) (hZ : All0 Z)
    (hA : AllI (PCx .LX false h) 1 ((p1 + 2, q1, false) :: Z ++ [(pa + 1, 1, false), (pb, 1, false)])) :
    AllI (PCx .T0 false 2) 1 ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) := by
  dsimp [List.cons_append, AllI] at hA ⊢
  rcases hA with ⟨hH, hA'⟩
  have hH' := hH
  dsimp [PCx] at hH'
  have hZall : All0 ((p1 + 2, q1, false) :: (Z ++ [(pa + 1, 1, false), (pb, 1, false)])) :=
    ⟨rfl, (All0_app Z _).mpr ⟨hZ, rfl, rfl, trivial⟩⟩
  rw [dv_zero _ hZall, List.length_append] at hH'
  dsimp [List.length] at hH'
  refine ⟨?_, AllI_ovpX h pa pb Z 1 (p1 + 2) q1 (by omega) hZ hH' hA'⟩
  dsimp [PCx]
  rw [ovpX_len]
  have hdv : dv ((h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1)) = 2 * 2 ^ Z.length - 2 := by
    dsimp [dv, bv]
    have E := ovpX_dv q1 Z (pa + 1)
    omega
  rw [hdv]
  exact ob_x1_head h p1 q1 Z.length hH'

structure St where
  sh : Nat
  sP : List Tri
  sT : Tl
  sph : Phase
  sc4 : Bool

def Cf (s : St) : Cfg (Fin 2) (Fin 6) := K s.sh s.sP s.sT

def TC (ph : Phase) (c4 : Bool) (T : Tl) : Prop :=
  match ph with
  | .E1 | .E1t | .LX => T = .TN ∧ c4 = false
  | .L1 => T = .TN
  | .E2 | .E2t => T = .TA 1 ∧ c4 = false
  | .T0 => (∃ k, T = .TB k ∧ 3 ≤ k) ∧ c4 = false
  | .L2 => ∃ t, T = .TA t ∧ 2 ≤ t

def J (s : St) : Prop :=
  s.sP ≠ [] ∧ TC s.sph s.sc4 s.sT ∧ AllI (PCx s.sph s.sc4 s.sh) 1 s.sP

lemma split1 (P : List Tri) :
    (∃ Z x R, P = Z ++ x :: R ∧ All0 Z ∧ dig x = true) ∨ All0 P := by
  induction P with
  | nil => exact Or.inr trivial
  | cons x P ih =>
    rcases x with ⟨p, q, d⟩
    cases d
    · rcases ih with ⟨Z, x', R, rfl, hZ, hx'⟩ | h0
      · exact Or.inl ⟨(p, q, false) :: Z, x', R, rfl, ⟨rfl, hZ⟩, hx'⟩
      · exact Or.inr ⟨rfl, h0⟩
    · exact Or.inl ⟨[], (p, q, true), P, rfl, trivial, rfl⟩

lemma exists_last {α : Type*} : ∀ (l : List α), l ≠ [] → ∃ Z y, l = Z ++ [y]
  | [], h => absurd rfl h
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: rest, _ =>
    let ⟨Z, z, hZ⟩ := exists_last (y :: rest) (by intro h; nomatch h)
    ⟨x :: Z, z, by rw [hZ]; rfl⟩

lemma Z_okL_V0 (ph : Phase) (c4 : Bool) (h : Nat) (y : Tri) (hph : ph ≠ .LX) :
    ∀ (Z : List Tri) (i : Nat), All0 (Z ++ [y]) → AllI (PCx ph c4 h) i (Z ++ [y]) → ∀ x ∈ Z, okL x := by
  intro Z
  induction Z with
  | nil => intro _ _ _ x hx; nomatch hx
  | cons z Z ih =>
    rcases z with ⟨p, q, d⟩
    intro i hZ hA
    rcases hZ with ⟨rfl, hZ'⟩
    rcases hA with ⟨hH, hA'⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxZ
    · refine ⟨rfl, ?_⟩
      dsimp [PCx] at hH
      rw [dv_zero ((p, q, false) :: (Z ++ [y])) ⟨rfl, hZ'⟩, List.length_append, List.length_singleton] at hH
      exact q2_V0 ph c4 h i p q (Z.length + 1) hH (by omega) (fun h => absurd h hph)
    · exact ih (i + 1) hZ' hA' x hxZ

lemma last_pc (ph : Phase) (c4 : Bool) (h : Nat) (Z : List Tri) (p q : Nat) (d : Bool)
    (hZ : All0 (Z ++ [(p, q, d)])) (hA : AllI (PCx ph c4 h) 1 (Z ++ [(p, q, d)])) :
    d = false ∧ PC ph c4 h (1 + Z.length) p q 0 0 := by
  have ⟨_, hd, _⟩ := (All0_app Z [(p, q, d)]).mp hZ
  subst hd
  have hB := AllI_app (PCx ph c4 h) Z 1 [(p, q, false)] hA
  dsimp [AllI, PCx, List.length, dv, bv] at hB
  exact ⟨rfl, hB.1⟩

lemma first_pc (ph : Phase) (c4 : Bool) (h p q : Nat) (d : Bool) (Z : List Tri)
    (hZ : All0 ((p, q, d) :: Z)) (hA : AllI (PCx ph c4 h) 1 ((p, q, d) :: Z)) :
    d = false ∧ PC ph c4 h 1 p q Z.length 0 ∧ All0 Z ∧ AllI (PCx ph c4 h) 2 Z := by
  rcases hZ with ⟨rfl, hZ'⟩
  rcases hA with ⟨hH, hA'⟩
  dsimp [PCx] at hH
  rw [dv_zero ((p, q, false) :: Z) ⟨rfl, hZ'⟩] at hH
  exact ⟨rfl, hH, hZ', hA'⟩

lemma Jstep (s : St) (hJ : J s) : ∃ s', ((Cf s) [target_tm]⊢⁺ (Cf s')) ∧ J s' := by
  rcases s with ⟨h, P, T, ph, c4⟩
  rcases hJ with ⟨hP, hT, hA⟩
  dsimp [Cf] at *
  rcases split1 P with ⟨Z, ⟨p, q, d⟩, R, rfl, hZ, hd⟩ | h0
  · dsimp [dig] at hd; subst hd
    have hZL : ∀ x ∈ Z, okL x := Z_okL ph c4 h Z 1 (p, q, true) R hZ rfl hA
    have hB := AllI_app (PCx ph c4 h) Z 1 ((p, q, true) :: R) hA
    dsimp [AllI] at hB
    rcases hB with ⟨hx, hR⟩
    have hx' : PC ph c4 h (1 + Z.length) p q R.length (dv ((p, q, true) :: R)) := hx
    rcases q with _ | _ | q
    · exfalso; rcases hx' with ⟨_, hq, _⟩; omega
    · have ⟨hph, hk, hL1, hLX⟩ := borrow1 ph c4 h (1 + Z.length) p R.length (dv ((p, 1, true) :: R)) (by omega) (by dsimp [dv, bv]; omega) hx'
      cases R with
      | nil =>
        cases T with
        | TN =>
          exfalso
          rcases hph with rfl | rfl | rfl
          · have ⟨hn, _⟩ := hL1 rfl; dsimp [List.length] at hn; omega
          · rcases hT with ⟨t, ht, _⟩; nomatch ht
          · have hn := hLX rfl; dsimp [List.length] at hn; omega
        | TA t =>
          have hphL2 : ph = .L2 := by
            rcases hph with rfl | rfl | rfl
            · dsimp [TC] at hT; nomatch hT
            · rfl
            · dsimp [TC] at hT; nomatch hT.1
          subst hphL2
          rcases hT with ⟨t', ht, ht2⟩
          cases ht
          have ⟨hA', hlen⟩ := inv_MT c4 h Z p hZ hA
          refine ⟨⟨h + 4, Z.map touch, .TA (p + t + 3), .L2, false⟩, DecMergeTail h Z p t hZL, ?_⟩
          refine ⟨?_, ⟨p + t + 3, rfl, by omega⟩, hA'⟩
          cases Z with
          | nil => dsimp [List.length] at hlen; omega
          | cons _ _ => intro hc; nomatch hc
        | TB k =>
          exfalso
          rcases hph with rfl | rfl | rfl
          · dsimp [TC] at hT; nomatch hT
          · rcases hT with ⟨t, ht, _⟩; nomatch ht
          · dsimp [TC] at hT; nomatch hT.1
      | cons x' R0 =>
        rcases x' with ⟨p', q', d'⟩
        refine ⟨⟨h + 4, Z.map touch ++ (p + p' + 3, q', d') :: R0, T, ph, c4⟩, DecMerge h Z p p' q' d' R0 T hZL, ?_⟩
        refine ⟨(by cases Z <;> intro hc <;> nomatch hc), hT, inv_Merge ph c4 h Z p p' q' d' R0 hZ hA⟩
    · refine ⟨⟨h + 4, Z.map touch ++ (p + 1, q + 1, false) :: R, T, ph, c4⟩, Dec h Z p q R T hZL, ?_⟩
      refine ⟨(by cases Z <;> intro hc <;> nomatch hc), hT, inv_Dec ph c4 h Z p q R hZ hA⟩
  · cases ph
    · -- E1: EndR
      rcases hT with ⟨rfl, rfl⟩
      obtain ⟨Z, ⟨p, q, d⟩, rfl⟩ := exists_last P hP
      obtain ⟨rfl, hy⟩ := last_pc .E1 false h Z p q d h0 hA
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp only [PN] at hN; omega
      rcases q with _ | _ | q
      · omega
      · omega
      · have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 .E1 false h (p, q + 2, false) (by decide) Z 1 h0 hA
        have ⟨hZ, _⟩ := (All0_app Z [(p, q + 2, false)]).mp h0
        refine ⟨⟨h + 4, Z.map touch ++ [(p + 1, q + 1, false)], .TA 1, .E2, false⟩, EndR h Z p q hZL, ?_⟩
        exact ⟨snoc_nn _ _, ⟨rfl, rfl⟩, inv_End .E1 .E2 h Z p q (Or.inl ⟨rfl, rfl⟩) hZ hA⟩
    · -- E2: Ov
      rcases hT with ⟨rfl, rfl⟩
      cases P with
      | nil => exact absurd rfl hP
      | cons x1 Z =>
        rcases x1 with ⟨p1, q1, d1⟩
        obtain ⟨rfl, hH, hZ, hA2⟩ := first_pc .E2 false h p1 q1 d1 Z h0 hA
        have hp1 := p1_V0 .E2 false h p1 q1 Z.length hH (Or.inl rfl)
        rcases p1 with _ | _ | p1
        · omega
        · omega
        · have ⟨hR, hO⟩ := AllI_okRO .E2 false h Z 2 hZ hA2
          have hq1 : 1 ≤ q1 := hH.2.1
          rcases lastOK_dec Z with hX | hX
          · refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, .TN, .LX, false⟩, Ov h p1 q1 Z 1 hq1 hR hO, ?_⟩
            refine ⟨(by intro hc; nomatch hc), ⟨rfl, rfl⟩, ?_⟩
            exact inv_Ov .E2 .LX false (fun x => x = 4) h p1 q1 Z 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (fun hc => by nomatch hc) (fun _ => rfl) hZ hX hA
          · refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, .TN, .L1, false⟩, Ov h p1 q1 Z 1 hq1 hR hO, ?_⟩
            refine ⟨(by intro hc; nomatch hc), rfl, ?_⟩
            exact inv_Ov .E2 .L1 false (fun x => x ≠ 4) h p1 q1 Z 1 (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (fun hc => by nomatch hc) (fun _ => rfl) hZ hX hA
    · -- E1t: EndR
      rcases hT with ⟨rfl, rfl⟩
      obtain ⟨Z, ⟨p, q, d⟩, rfl⟩ := exists_last P hP
      obtain ⟨rfl, hy⟩ := last_pc .E1t false h Z p q d h0 hA
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp only [PN] at hN; omega
      rcases q with _ | _ | q
      · omega
      · omega
      · have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 .E1t false h (p, q + 2, false) (by decide) Z 1 h0 hA
        have ⟨hZ, _⟩ := (All0_app Z [(p, q + 2, false)]).mp h0
        refine ⟨⟨h + 4, Z.map touch ++ [(p + 1, q + 1, false)], .TA 1, .E2t, false⟩, EndR h Z p q hZL, ?_⟩
        exact ⟨snoc_nn _ _, ⟨rfl, rfl⟩, inv_End .E1t .E2t h Z p q (Or.inr ⟨rfl, rfl⟩) hZ hA⟩
    · -- E2t: Ov
      rcases hT with ⟨rfl, rfl⟩
      cases P with
      | nil => exact absurd rfl hP
      | cons x1 Z =>
        rcases x1 with ⟨p1, q1, d1⟩
        obtain ⟨rfl, hH, hZ, hA2⟩ := first_pc .E2t false h p1 q1 d1 Z h0 hA
        have hp1 := p1_V0 .E2t false h p1 q1 Z.length hH (Or.inr (Or.inl rfl))
        rcases p1 with _ | _ | p1
        · omega
        · omega
        · have ⟨hR, hO⟩ := AllI_okRO .E2t false h Z 2 hZ hA2
          have hq1 : 1 ≤ q1 := hH.2.1
          refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z 1, .TN, .L1, true⟩, Ov h p1 q1 Z 1 hq1 hR hO, ?_⟩
          refine ⟨(by intro hc; nomatch hc), rfl, ?_⟩
          exact inv_Ov .E2t .L1 true (fun _ => True) h p1 q1 Z 1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))) (fun hc => by nomatch hc) (fun _ => rfl) hZ (lastOK_True Z) hA
    · -- T0: X2
      rcases hT with ⟨⟨k, rfl, hk⟩, rfl⟩
      obtain ⟨Z, ⟨p, q, d⟩, rfl⟩ := exists_last P hP
      obtain ⟨rfl, hy⟩ := last_pc .T0 false h Z p q d h0 hA
      have hq : 2 ≤ q := by rcases hy with ⟨_, _, hN, _⟩; simp only [PN] at hN; omega
      rcases q with _ | _ | q
      · omega
      · omega
      · rcases k with _ | k
        · omega
        · have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 .T0 false h (p, q + 2, false) (by decide) Z 1 h0 hA
          have ⟨hZ, _⟩ := (All0_app Z [(p, q + 2, false)]).mp h0
          refine ⟨⟨h + 4, Z.map touch ++ [(p + 1, q + 1, false), (3, k + 1, true)], .TN, .E1t, false⟩, X2 h Z p q k hZL, ?_⟩
          exact ⟨(by cases Z <;> intro hc <;> nomatch hc), ⟨rfl, rfl⟩, inv_X2 h Z p q (k + 1) hZ hk hA⟩
    · -- L1: EndLast
      dsimp [TC] at hT; subst hT
      obtain ⟨Z, ⟨p, q, d⟩, rfl⟩ := exists_last P hP
      obtain ⟨rfl, hy⟩ := last_pc .L1 c4 h Z p q d h0 hA
      have hq : q = 1 := by rcases hy with ⟨_, _, hN, _⟩; simp only [PN] at hN; omega
      subst hq
      have hZL : ∀ x ∈ Z, okL x := Z_okL_V0 .L1 c4 h (p, 1, false) (by decide) Z 1 h0 hA
      have ⟨hZ, _⟩ := (All0_app Z [(p, 1, false)]).mp h0
      have ⟨hA', hlen⟩ := inv_EndLast c4 h Z p hZ hA
      refine ⟨⟨h + 4, Z.map touch, .TA (p + 4), .L2, c4⟩, EndLast h Z p hZL, ?_⟩
      refine ⟨?_, ⟨p + 4, rfl, by omega⟩, hA'⟩
      cases Z with
      | nil => dsimp [List.length] at hlen; omega
      | cons _ _ => intro hc; nomatch hc
    · -- L2: Ov
      rcases hT with ⟨t, rfl, ht⟩
      cases c4
      · cases P with
        | nil => exact absurd rfl hP
        | cons x1 Z =>
          rcases x1 with ⟨p1, q1, d1⟩
          obtain ⟨rfl, hH, hZ, hA2⟩ := first_pc .L2 false h p1 q1 d1 Z h0 hA
          have hp1 := p1_V0 .L2 false h p1 q1 Z.length hH (Or.inr (Or.inr (Or.inl rfl)))
          rcases p1 with _ | _ | p1
          · omega
          · omega
          · have ⟨hR, hO⟩ := AllI_okRO .L2 false h Z 2 hZ hA2
            have hq1 : 1 ≤ q1 := hH.2.1
            refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovp q1 Z t, .TN, .E1, false⟩, Ov h p1 q1 Z t hq1 hR hO, ?_⟩
            refine ⟨(by intro hc; nomatch hc), ⟨rfl, rfl⟩, ?_⟩
            exact inv_Ov .L2 .E1 false (fun _ => True) h p1 q1 Z t (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))) (fun _ => ht) (fun hc => absurd rfl hc) hZ (lastOK_True Z) hA
      · exfalso
        obtain ⟨Z, ⟨p, q, d⟩, rfl⟩ := exists_last P hP
        obtain ⟨rfl, hy⟩ := last_pc .L2 true h Z p q d h0 hA
        exact L2_c4_V0 h (1 + Z.length) p q hy
    · -- LX: X1
      rcases hT with ⟨rfl, rfl⟩
      have hlen := AllI_len .LX false h P hP hA
      dsimp [minlen] at hlen
      obtain ⟨P1, ⟨pb, qb, db⟩, rfl⟩ := exists_last P hP
      have hP1 : P1 ≠ [] := by
        cases P1 with
        | nil => dsimp [List.length] at hlen; omega
        | cons _ _ => intro hc; nomatch hc
      obtain ⟨P2, ⟨pa, qa, da⟩, rfl⟩ := exists_last P1 hP1
      cases P2 with
      | nil => dsimp [List.length] at hlen; omega
      | cons x1 Z =>
        rcases x1 with ⟨p1, q1, d1⟩
        have happ : ((p1, q1, d1) :: Z ++ [(pa, qa, da)]) ++ [(pb, qb, db)] =
            (p1, q1, d1) :: (Z ++ [(pa, qa, da), (pb, qb, db)]) := by simp [List.append_assoc]
        rw [happ] at h0 hA ⊢
        obtain ⟨rfl, hH, hZab, hA2⟩ := first_pc .LX false h p1 q1 d1 (Z ++ [(pa, qa, da), (pb, qb, db)]) h0 hA
        have ⟨hZ, hda, hdb, _⟩ := (All0_app Z [(pa, qa, da), (pb, qb, db)]).mp hZab
        subst hda; subst hdb
        have hB := AllI_app (PCx .LX false h) Z 2 [(pa, qa, false), (pb, qb, false)] hA2
        dsimp [AllI, PCx, List.length, dv, bv] at hB
        rcases hB with ⟨ha, hb, _⟩
        have hqa : qa = 1 := by rcases ha with ⟨_, _, hN, _⟩; simp only [PN] at hN; omega
        have hqb : qb = 1 := by rcases hb with ⟨_, _, hN, _⟩; simp only [PN] at hN; omega
        subst hqa; subst hqb
        have hpa : 1 ≤ pa := ha.1
        rcases pa with _ | pa
        · omega
        · have hp1 := p1_V0 .LX false h p1 q1 (Z ++ [(pa + 1, 1, false), (pb, 1, false)]).length hH (Or.inr (Or.inr (Or.inr rfl)))
          rcases p1 with _ | _ | p1
          · omega
          · omega
          · have ⟨hR, hO⟩ := AllI_okRO .LX false h (Z ++ [(pa + 1, 1, false), (pb, 1, false)]) 2 hZab hA2
            have hRZ : ∀ x ∈ Z, okR x := fun x hx => hR x (List.mem_append_left _ hx)
            have hOZ : ∀ x ∈ Z, okO x := fun x hx => hO x (List.mem_append_left _ hx)
            have hq1 : 1 ≤ q1 := hH.2.1
            refine ⟨⟨2, (h + 5, p1 + 1, false) :: ovpX q1 Z (pa + 1), .TB (pb + 3), .T0, false⟩, X1 h p1 q1 Z pa pb hq1 hRZ hOZ, ?_⟩
            refine ⟨(by intro hc; nomatch hc), ⟨⟨pb + 3, rfl, by omega⟩, rfl⟩, ?_⟩
            exact inv_X1 h p1 q1 Z pa pb hZ hA

def s_base_0666 : St := ⟨2, base_0666, .TN, .E1, false⟩

lemma J_base_0666 : J s_base_0666 := by
  dsimp [J, s_base_0666, base_0666, TC, AllI, PCx, PC, PN, PI, List.length, dv, bv]
  refine ⟨(by intro hc; nomatch hc), ⟨rfl, rfl⟩, by simp only []; decide⟩

lemma isSome_of_multiStep_add {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [multiStep_add] at h
  cases hj : multiStep target_tm c j with
  | none => rw [hj] at h; nomatch h
  | some _ => rfl

lemma reach_unbounded (m : Nat) :
    ∃ N ≥ m, ∃ s : St, multiStep target_tm (init []) N = some (Cf s) ∧ J s := by
  induction m with
  | zero =>
    obtain ⟨k1, hk1⟩ := stepStar_trans init0 init_to_base
    exact ⟨k1, Nat.zero_le k1, s_base_0666, hk1, J_base_0666⟩
  | succ m ih =>
    obtain ⟨N, hN, s, hms, hJ⟩ := ih
    obtain ⟨s', ⟨k, hk_pos, hstep⟩, hJ'⟩ := Jstep s hJ
    exact ⟨N + k, by omega, s', multiStep_trans target_tm _ _ _ N k hms hstep, hJ'⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨n, hn⟩
  obtain ⟨N, hN, _, hN_ms, _⟩ := reach_unbounded (n + 1)
  have heq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [← heq] at hN_ms
  have hsome := isSome_of_multiStep_add hN_ms
  rwa [multiStep_succ, hn] at hsome

end BusyBeaver.M_1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RAHHH
