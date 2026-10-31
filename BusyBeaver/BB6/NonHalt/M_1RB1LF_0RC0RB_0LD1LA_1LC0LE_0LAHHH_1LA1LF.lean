/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LAHHH_1LA1LF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 1 => none
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
-- ============================================================================
-- Section 2: Turing Machine Infrastructure & Notations
-- ============================================================================


/- A Turing machine statement writing a symbol and moving in direction `dir`. -/
-- ============================================================================
-- Section 5: Specific Turing Machine: holdout_0010
-- ============================================================================
/- Transition function for holdout_0010: `1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---` -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

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

omit [Inhabited Γ] in
theorem list_pow_add_comm (l : List Γ) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [← list_pow_add, add_comm, list_pow_add]

lemma listblank_append_append (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s

lemma list_pow_append_one (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := list_pow_add_comm u k 1
  dsimp -failIfUnchanged [HPow.hPow, list_nat_repeat] at h ⊢
  rw [List.append_nil] at h
  exact h

lemma cons_eq_singleton_append (x : Fin 2) (r : ListBlank (Fin 2)) :
    x >> r = [x] +> r := rfl

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

lemma pow_succ_append_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

lemma pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

lemma pow_succ_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m : Nat) :
    (s <+ (u ^ m)) <+ u = s <+ (u ^ (m + 1)) := by
  rw [listblank_append_append, ← pow_succ_list]

lemma step_multiStep {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

lemma step_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ := ⟨1, step_multiStep tm c₁ c₂ h⟩

lemma step_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, step_multiStep tm c₁ c₂ h⟩

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

lemma stepStar_stepPlus_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (stepPlus_stepStar h₂)

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂


@[simp] lemma init_nil : (init ([] : List (Fin 2))) = (default {{A}}> default) := rfl

macro "finish" : tactic =>
  `(tactic| (refine ⟨0, ?_⟩; simp only [init_nil, multiStep_zero, pow_zero_list, pow_succ_list, cons_append_list, append_nil_list, listblank_append_nil, listblank_append_cons, zero_cons_default]; rfl))
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [init_nil, pow_zero_list, pow_succ_list, cons_append_list, append_nil_list, listblank_append_nil, listblank_append_cons, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail]); rfl) ?_ <;>
    simp only [init_nil, pow_zero_list, pow_succ_list, cons_append_list, append_nil_list, listblank_append_nil, listblank_append_cons, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
macro "execute" : tactic =>
  `(tactic| (iterate 25 (all_goals (first | finish | step))))


-- ============================================================================
-- Section 6: PairCounter Arithmetic & Symbolic Counter Closure (BECv10.v)
-- ============================================================================

namespace PairCounter

lemma pow2_succ (k : Nat) : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
lemma pow2_one_add (k : Nat) : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
lemma pow2_two_add (k : Nat) : 2 ^ (2 + k) = 4 * 2 ^ k := by ring
lemma pow4_succ (k : Nat) : 4 ^ (k + 1) = 4 ^ k * 4 := by ring
lemma pow4_one_add (k : Nat) : 4 ^ (1 + k) = 4 * 4 ^ k := by ring
lemma pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k
lemma pow4_pos (k : Nat) : 0 < 4 ^ k := by positivity

inductive H : Nat → Nat → Prop where
  | even (n : Nat) : H (n * 2) (1 + n * 2)
  | carry (j : Nat) {x y : Nat} : H x y → H (x * 2 ^ (2 + j) + (2 ^ (1 + j) - 1)) (y * 2 ^ (2 + j))

inductive Steps : Nat → Nat → Nat → Prop where
  | zero (x : Nat) : Steps 0 x x
  | next {n x y z : Nat} : H x y → Steps n y z → Steps (1 + n) x z

lemma steps_one {x y : Nat} (h : H x y) : Steps 1 x y :=
  Steps.next h (Steps.zero y)

lemma steps_trans {n m x y z : Nat} (h1 : Steps n x y) (h2 : Steps m y z) : Steps (n + m) x z := by
  induction h1 with
  | zero x =>
    simpa only [Nat.zero_add] using h2
  | @next n' x' y' z' hxy _ ih =>
    have heq : 1 + n' + m = 1 + (n' + m) := by omega
    rw [heq]
    exact Steps.next hxy (ih h2)

lemma H_even_inv_aux {u y : Nat} (h : H u y) : ∀ x, u = x * 2 → y = 1 + x * 2 := by
  cases h with
  | even n =>
    intro x hx; omega
  | @carry j x' y' _ =>
    intro x hx
    have h1 : x' * 2 ^ (2 + j) = (x' * 2 ^ j) * 4 := by rw [pow2_two_add]; ring
    have h2 : 2 ^ (1 + j) = 2 * 2 ^ j := pow2_one_add j
    have hp : 0 < 2 ^ j := pow2_pos j
    rw [h1, h2] at hx
    omega

lemma H_even_inv {x y : Nat} (h : H (x * 2) y) : y = 1 + x * 2 :=
  H_even_inv_aux h x rfl

lemma steps_drop_even_aux {a u y : Nat} (h : Steps a u y) :
    0 < a → ∀ x, u = x * 2 → Steps (a - 1) (1 + x * 2) y := by
  cases h with
  | zero => intro ha; omega
  | @next n x' u' y' hxy hstep =>
    intro _ x hx
    subst hx
    have hu : u' = 1 + x * 2 := H_even_inv hxy
    subst hu
    have hn : 1 + n - 1 = n := by omega
    rw [hn]
    exact hstep

lemma steps_drop_even {a x y : Nat} (ha : 0 < a) (h : Steps a (x * 2) y) :
    Steps (a - 1) (1 + x * 2) y :=
  steps_drop_even_aux h ha x rfl

lemma H_four {x y : Nat} (h : H x y) : H (1 + x * 4) (y * 4) := by
  have hc := H.carry 0 h
  have h1 : x * 2 ^ (2 + 0) + (2 ^ (1 + 0) - 1) = 1 + x * 4 := by
    change x * 4 + 1 = 1 + x * 4; omega
  have h2 : y * 2 ^ (2 + 0) = y * 4 := rfl
  rw [h1, h2] at hc
  exact hc

lemma H_eight {x y : Nat} (h : H x y) : H (3 + x * 8) (y * 8) := by
  have hc := H.carry 1 h
  have h1 : x * 2 ^ (2 + 1) + (2 ^ (1 + 1) - 1) = 3 + x * 8 := by
    change x * 8 + 3 = 3 + x * 8; omega
  have h2 : y * 2 ^ (2 + 1) = y * 8 := rfl
  rw [h1, h2] at hc
  exact hc

lemma H_zero4 (x : Nat) : H (x * 4) (1 + x * 4) := by
  have he := H.even (x * 2)
  have h1 : x * 2 * 2 = x * 4 := by omega
  rw [h1] at he
  exact he

lemma pair_zero {x y : Nat} (h : H x y) : Steps 2 (x * 4) (y * 4) :=
  Steps.next (H_zero4 x) (steps_one (H_four h))

lemma pair_two {x y : Nat} (h : H x y) : Steps 2 (2 + x * 8) (y * 2 * 4) := by
  have he := H.even (1 + x * 4)
  have h1 : (1 + x * 4) * 2 = 2 + x * 8 := by omega
  have h2 : 1 + (2 + x * 8) = 3 + x * 8 := by omega
  rw [h1, h2] at he
  have h8 := steps_one (H_eight h)
  have h3 : y * 8 = y * 2 * 4 := by omega
  rw [h3] at h8
  exact Steps.next he h8

lemma steps_four {n x y : Nat} (h : Steps n x y) : Steps (n * 2) (x * 4) (y * 4) := by
  induction h with
  | zero x => exact Steps.zero (x * 4)
  | @next n' x' y' z' hxy _ ih =>
    have htr := steps_trans (pair_zero hxy) ih
    have heq : 2 + n' * 2 = (1 + n') * 2 := by omega
    rw [heq] at htr
    exact htr

lemma steps_zeros (k : Nat) {n x y : Nat} (h : Steps n x y) :
    Steps (n * 2 ^ k) (x * 4 ^ k) (y * 4 ^ k) := by
  induction k with
  | zero =>
    simpa only [Nat.pow_zero, Nat.mul_one] using h
  | succ k ih =>
    have hf := steps_four ih
    have h1 : n * 2 ^ k * 2 = n * 2 ^ (k + 1) := by rw [pow2_succ]; ring
    have h2 : x * 4 ^ k * 4 = x * 4 ^ (k + 1) := by rw [pow4_succ]; ring
    have h3 : y * 4 ^ k * 4 = y * 4 ^ (k + 1) := by rw [pow4_succ]; ring
    rw [h1, h2, h3] at hf
    exact hf

inductive Field : Nat → Nat → Nat → Nat → Prop where
  | nil (w : Nat) : Field 0 0 w w
  | zero {k z w x : Nat} : Field k z w x → Field (1 + k) (z * 2) w (x * 4)
  | one {k z w x : Nat} : Field k z w x → Field (1 + k) (1 + z * 2) w (1 + x * 4)

lemma field_bound {k z w x : Nat} (h : Field k z w x) : z < 2 ^ k := by
  induction h with
  | nil w => decide
  | @zero k' z' w' x' _ ih =>
    rw [pow2_one_add]; omega
  | @one k' z' w' x' _ ih =>
    rw [pow2_one_add]; omega

lemma field_zeros (k w : Nat) : Field k 0 w (w * 4 ^ k) := by
  induction k with
  | zero =>
    simpa only [Nat.pow_zero, Nat.mul_one] using Field.nil w
  | succ k ih =>
    have hz := Field.zero ih
    have h1 : 1 + k = k + 1 := by omega
    have h2 : w * 4 ^ k * 4 = w * 4 ^ (k + 1) := by rw [pow4_succ]; ring
    rw [h1, Nat.zero_mul, h2] at hz
    exact hz

lemma field_exists (k z w : Nat) (hz : z < 2 ^ k) : ∃ x, Field k z w x := by
  induction k generalizing z with
  | zero =>
    have hz0 : z = 0 := by change z < 1 at hz; omega
    subst hz0
    exact ⟨w, Field.nil w⟩
  | succ k ih =>
    rw [pow2_succ] at hz
    rcases (by omega : z = (z / 2) * 2 ∨ z = 1 + (z / 2) * 2) with hpar | hpar
    · obtain ⟨x, hx⟩ := ih (z / 2) (by omega)
      refine ⟨x * 4, ?_⟩
      have h1 : k + 1 = 1 + k := by omega
      rw [h1, hpar]
      exact Field.zero hx
    · obtain ⟨x, hx⟩ := ih (z / 2) (by omega)
      refine ⟨1 + x * 4, ?_⟩
      have h1 : k + 1 = 1 + k := by omega
      rw [h1, hpar]
      exact Field.one hx

lemma field_unique_aux {k1 z1 w1 x : Nat} (h1 : Field k1 z1 w1 x) :
    ∀ {k2 z2 y : Nat}, Field k2 z2 w1 y → k1 = k2 → z1 = z2 → x = y := by
  induction h1 with
  | nil w =>
    intro k2 z2 y h2 hk hz
    cases h2 with
    | nil => rfl
    | zero => omega
    | one => omega
  | @zero k1' z1' w1' x1' _ ih =>
    intro k2 z2 y h2 hk hz
    cases h2 with
    | nil => omega
    | @zero k2' z2' _ y' h2' =>
      rw [ih h2' (by omega) (by omega)]
    | one => omega
  | @one k1' z1' w1' x1' _ ih =>
    intro k2 z2 y h2 hk hz
    cases h2 with
    | nil => omega
    | zero => omega
    | @one k2' z2' _ y' h2' =>
      rw [ih h2' (by omega) (by omega)]

lemma field_unique {k z w x y : Nat} (h1 : Field k z w x) (h2 : Field k z w y) : x = y :=
  field_unique_aux h1 h2 rfl rfl

lemma field_compose {k z w x j v y : Nat}
    (h1 : Field k z w x) (h2 : Field j v x y) :
    Field (k + j) (z * 2 ^ j + v) w y := by
  induction h2 with
  | nil x0 =>
    simpa only [Nat.add_zero, Nat.pow_zero, Nat.mul_one] using h1
  | @zero j' v' x' y' _ ih =>
    have hz := Field.zero (ih h1)
    have h1_eq : 1 + (k + j') = k + (1 + j') := by omega
    have h2_eq : (z * 2 ^ j' + v') * 2 = z * 2 ^ (1 + j') + v' * 2 := by
      rw [pow2_one_add]; ring
    rw [h1_eq, h2_eq] at hz
    exact hz
  | @one j' v' x' y' _ ih =>
    have ho := Field.one (ih h1)
    have h1_eq : 1 + (k + j') = k + (1 + j') := by omega
    have h2_eq : 1 + (z * 2 ^ j' + v') * 2 = z * 2 ^ (1 + j') + (1 + v' * 2) := by
      rw [pow2_one_add]; ring
    rw [h1_eq, h2_eq] at ho
    exact ho

lemma field_fill {k z w x : Nat} (h : Field k z w x) : Steps z (w * 4 ^ k) x := by
  induction h with
  | nil w =>
    simpa only [Nat.pow_zero, Nat.mul_one] using Steps.zero w
  | @zero k' z' w' x' _ ih =>
    have hf := steps_four ih
    have h1 : w' * 4 ^ k' * 4 = w' * 4 ^ (1 + k') := by rw [pow4_one_add]; ring
    rw [h1] at hf
    exact hf
  | @one k' z' w' x' _ ih =>
    have hf := steps_trans (steps_four ih) (steps_one (H_zero4 x'))
    have h1 : z' * 2 + 1 = 1 + z' * 2 := by omega
    have h2 : w' * 4 ^ k' * 4 = w' * 4 ^ (1 + k') := by rw [pow4_one_add]; ring
    rw [h1, h2] at hf
    exact hf

lemma field_inc {k z w x : Nat} (h : Field k z w x) (hb : 1 + z < 2 ^ k) :
    ∃ y, Field k (1 + z) w y ∧ H x y := by
  induction h with
  | nil w =>
    change 1 + 0 < 1 at hb; omega
  | @zero k' z' w' x' h' _ =>
    exact ⟨1 + x' * 4, Field.one h', H_zero4 x'⟩
  | @one k' z' w' x' h' ih =>
    rw [pow2_one_add] at hb
    obtain ⟨y, hy, hh⟩ := ih (by omega)
    refine ⟨y * 4, ?_, H_four hh⟩
    have hf := Field.zero hy
    have heq : (1 + z') * 2 = 1 + (1 + z' * 2) := by omega
    rw [heq] at hf
    exact hf

lemma field_carry {k z w x y : Nat} (h : Field k z w x) (hb : 1 + z = 2 ^ k) (hw : H w y) :
    H x (y * 4 ^ k) := by
  induction h with
  | nil w =>
    simpa only [Nat.pow_zero, Nat.mul_one] using hw
  | @zero k' z' w' x' _ _ =>
    rw [pow2_one_add] at hb; omega
  | @one k' z' w' x' _ ih =>
    rw [pow2_one_add] at hb
    have hh := H_four (ih (by omega) hw)
    have heq : y * 4 ^ k' * 4 = y * 4 ^ (1 + k') := by rw [pow4_one_add]; ring
    rw [heq] at hh
    exact hh

lemma field_inv_zero {k1 z w x : Nat} (hf : Field k1 z w x) (hk : k1 = 0) : z = 0 ∧ x = w := by
  cases hf with
  | nil => exact ⟨rfl, rfl⟩
  | zero => omega
  | one => omega

lemma field_inv_succ {k1 z w x : Nat} (hf : Field k1 z w x) (k : Nat) (hk : k1 = k + 1) :
    (∃ z0 x0, z = z0 * 2 ∧ x = x0 * 4 ∧ Field k z0 w x0) ∨
    (∃ z0 x0, z = 1 + z0 * 2 ∧ x = 1 + x0 * 4 ∧ Field k z0 w x0) := by
  cases hf with
  | nil => omega
  | @zero k0 z0 _ x0 hf0 =>
    have hk0 : k0 = k := by omega
    subst hk0
    exact Or.inl ⟨z0, x0, rfl, rfl, hf0⟩
  | @one k0 z0 _ x0 hf0 =>
    have hk0 : k0 = k := by omega
    subst hk0
    exact Or.inr ⟨z0, x0, rfl, rfl, hf0⟩

lemma normalize (k : Nat) : ∀ {z w x y : Nat},
    Field k z w x → 0 < z → H w y → Steps ((2 ^ k - z) * 2) (x * 2) (y * 2 * 4 ^ k) := by
  induction k with
  | zero =>
    intro z w x y hf hz _
    obtain ⟨rfl, _⟩ := field_inv_zero hf rfl
    omega
  | succ k ih =>
    intro z w x y hf hz hw
    rcases field_inv_succ hf k rfl with ⟨z0, x0, rfl, rfl, hf0⟩ | ⟨z0, x0, rfl, rfl, hf0⟩
    · have hs := steps_four (ih hf0 (by omega) hw)
      have h1 : (2 ^ (k + 1) - z0 * 2) * 2 = (2 ^ k - z0) * 2 * 2 := by
        have hb0 := field_bound hf0
        rw [pow2_succ]; omega
      have h2 : x0 * 4 * 2 = x0 * 2 * 4 := by omega
      have h3 : y * 2 * 4 ^ (k + 1) = y * 2 * 4 ^ k * 4 := by rw [pow4_succ]; ring
      rw [h1, h2, h3]
      exact hs
    · have hb0 := field_bound hf0
      rcases (by omega : 1 + z0 = 2 ^ k ∨ 1 + z0 ≠ 2 ^ k) with he | he
      · have hp := pair_two (field_carry hf0 he hw)
        have h1 : (2 ^ (k + 1) - (1 + z0 * 2)) * 2 = 2 := by rw [pow2_succ]; omega
        have h2 : (1 + x0 * 4) * 2 = 2 + x0 * 8 := by omega
        have h3 : y * 2 * 4 ^ (k + 1) = y * 4 ^ k * 2 * 4 := by rw [pow4_succ]; ring
        rw [h1, h2, h3]
        exact hp
      · obtain ⟨u, hu, hhu⟩ := field_inc hf0 (by omega)
        have hp := steps_trans (pair_two hhu) (steps_four (ih hu (by omega) hw))
        have h1 : (2 ^ (k + 1) - (1 + z0 * 2)) * 2 = 2 + (2 ^ k - (1 + z0)) * 2 * 2 := by
          rw [pow2_succ]; omega
        have h2 : (1 + x0 * 4) * 2 = 2 + x0 * 8 := by omega
        have h3 : y * 2 * 4 ^ (k + 1) = y * 2 * 4 ^ k * 4 := by rw [pow4_succ]; ring
        rw [h1, h2, h3]
        exact hp

lemma packed_positive {k z w x y n q r y' : Nat}
    (hf : Field k z w x) (hz : 0 < z) (hw : H w y) (hq : Steps q (y * 2) y')
    (hn : n = (2 ^ k - z) * 2 + q * 2 ^ k + r) (hr : r < 2 ^ k) :
    ∃ x', Field k r y' x' ∧ Steps n (x * 2) x' := by
  obtain ⟨x', hfx'⟩ := field_exists k r y' hr
  refine ⟨x', hfx', ?_⟩
  subst hn
  exact steps_trans (steps_trans (normalize k hf hz hw) (steps_zeros k hq)) (field_fill hfx')

lemma packed_short {w k z x a h : Nat}
    (hf : Field k z w x) (hz : 0 < z) (hw : H w h)
    (hb : 2 * 2 ^ k ≤ a + z * 2) (hc : a + z * 2 < 4 * 2 ^ k) :
    ∃ q r u, q ≤ 1 ∧ r < 2 ^ k ∧ a + z * 2 = (2 + q) * 2 ^ k + r ∧
      Field k r (h * 2 + q) u ∧ Steps a (x * 2) u := by
  have hzb := field_bound hf
  rcases (by omega : 3 * 2 ^ k ≤ a + z * 2 ∨ ¬ (3 * 2 ^ k ≤ a + z * 2)) with hle | hle
  · obtain ⟨u, hfu, hsu⟩ := packed_positive hf hz hw (steps_one (H.even h))
      (n := a) (q := 1) (r := a + z * 2 - 3 * 2 ^ k) (by omega) (by omega)
    refine ⟨1, a + z * 2 - 3 * 2 ^ k, u, by omega, by omega, by omega, ?_, hsu⟩
    have heq : 1 + h * 2 = h * 2 + 1 := by omega
    rw [heq] at hfu
    exact hfu
  · obtain ⟨u, hfu, hsu⟩ := packed_positive hf hz hw (Steps.zero (h * 2))
      (n := a) (q := 0) (r := a + z * 2 - 2 * 2 ^ k) (by omega) (by omega)
    refine ⟨0, a + z * 2 - 2 * 2 ^ k, u, by omega, by omega, by omega, ?_, hsu⟩
    simpa only [Nat.add_zero] using hfu

lemma field_low {k z w x : Nat} (hf : Field k z w x) (hz : 0 < z) :
    ∃ t j v y, k = t + 1 + j ∧ z = (1 + v * 2) * 2 ^ t ∧ x = (1 + y * 4) * 4 ^ t ∧ Field j v w y := by
  induction hf with
  | nil w => omega
  | @zero k' z' w' x' hf' ih =>
    obtain ⟨t, j, v, y, hk, hze, hxe, hfj⟩ := ih (by omega)
    refine ⟨1 + t, j, v, y, by omega, ?_, ?_, hfj⟩
    · rw [hze, pow2_one_add]; ring
    · rw [hxe, pow4_one_add]; ring
  | @one k' z' w' x' hf' _ =>
    exact ⟨0, k', z', x', by omega, by simp, by simp, hf'⟩

inductive Normal : Bool → Nat → Nat → Prop where
  | D : Normal false 0 0
  | E2 : Normal true 2 2
  | E3 : Normal true 3 3
  | zero {e : Bool} {n x : Nat} : Normal e n x → Normal e (n * 2) (x * 4)
  | one {e : Bool} {n x : Nat} : Normal e n x → Normal e (1 + n * 2) (1 + x * 4)

lemma normal_step {e : Bool} {n x : Nat} (hn : Normal e n x) :
    ∃ y, Normal e (1 + n) y ∧ H x y := by
  induction hn with
  | D => exact ⟨1, Normal.one Normal.D, H.even 0⟩
  | E2 => exact ⟨3, Normal.E3, H.even 1⟩
  | E3 =>
    refine ⟨8, Normal.zero Normal.E2, ?_⟩
    simpa using H_eight (H.even 0)
  | @zero e' n' x' hn' _ =>
    exact ⟨1 + x' * 4, Normal.one hn', H_zero4 x'⟩
  | @one e' n' x' _ ih =>
    obtain ⟨y, hny, hhy⟩ := ih
    refine ⟨y * 4, ?_, H_four hhy⟩
    have hz := Normal.zero hny
    have heq : (1 + n') * 2 = 1 + (1 + n' * 2) := by omega
    rw [heq] at hz
    exact hz

lemma normal_steps {e : Bool} {n x : Nat} (a : Nat) (hn : Normal e n x) :
    ∃ y, Normal e (n + a) y ∧ Steps a x y := by
  induction a generalizing n x with
  | zero =>
    exact ⟨x, hn, Steps.zero x⟩
  | succ a ih =>
    obtain ⟨y, hny, hhy⟩ := normal_step hn
    obtain ⟨z, hnz, hsz⟩ := ih hny
    refine ⟨z, ?_, ?_⟩
    · have heq : 1 + n + a = n + (a + 1) := by omega
      rw [heq] at hnz
      exact hnz
    · have heq : 1 + a = a + 1 := by omega
      rw [← heq]
      exact Steps.next hhy hsz

lemma field_normal {k z w x : Nat} (hf : Field k z w x) {e : Bool} {n : Nat}
    (hn : Normal e n w) : Normal e (n * 2 ^ k + z) x := by
  induction hf with
  | nil w =>
    simpa only [Nat.pow_zero, Nat.mul_one, Nat.add_zero] using hn
  | @zero k' z' w' x' _ ih =>
    have hz := Normal.zero (ih hn)
    have heq : (n * 2 ^ k' + z') * 2 = n * 2 ^ (1 + k') + z' * 2 := by
      rw [pow2_one_add]; ring
    rw [heq] at hz
    exact hz
  | @one k' z' w' x' _ ih =>
    have ho := Normal.one (ih hn)
    have heq : 1 + (n * 2 ^ k' + z') * 2 = n * 2 ^ (1 + k') + (1 + z' * 2) := by
      rw [pow2_one_add]; ring
    rw [heq] at ho
    exact ho

lemma packed_normal {k z w x y j u : Nat} {e : Bool} {v a : Nat}
    (hf : Field k z w x) (hz : 0 < z) (hw : H w y) (hj : Steps j (y * 2) u)
    (hn : Normal e v u) (hb : (2 ^ k - z) * 2 + j * 2 ^ k ≤ a) :
    ∃ x', Normal e (v * 2 ^ k + (a - ((2 ^ k - z) * 2 + j * 2 ^ k))) x' ∧ Steps a (x * 2) x' := by
  obtain ⟨x', hnx', hsx'⟩ := normal_steps (a - ((2 ^ k - z) * 2 + j * 2 ^ k))
    (field_normal (field_zeros k u) hn)
  refine ⟨x', ?_, ?_⟩
  · simpa only [Nat.add_zero] using hnx'
  · have htr := steps_trans (steps_trans (normalize k hf hz hw) (steps_zeros k hj)) hsx'
    have heq : (2 ^ k - z) * 2 + j * 2 ^ k + (a - ((2 ^ k - z) * 2 + j * 2 ^ k)) = a := by omega
    rw [heq] at htr
    exact htr

lemma packed_zero {k w j u : Nat} {e : Bool} {v a : Nat}
    (hj : Steps j (w * 2) u) (hn : Normal e v u) (hb : j * 2 ^ k ≤ a) :
    ∃ x', Normal e (v * 2 ^ k + (a - j * 2 ^ k)) x' ∧ Steps a (w * 4 ^ k * 2) x' := by
  obtain ⟨x', hnx', hsx'⟩ := normal_steps (a - j * 2 ^ k) (field_normal (field_zeros k u) hn)
  refine ⟨x', ?_, ?_⟩
  · simpa only [Nat.add_zero] using hnx'
  · have htr := steps_trans (steps_zeros k hj) hsx'
    have h1 : j * 2 ^ k + (a - j * 2 ^ k) = a := by omega
    have h2 : w * 2 * 4 ^ k = w * 4 ^ k * 2 := by ring
    rw [h1, h2] at htr
    exact htr

lemma packed_zero_affine {k w j u : Nat} {e : Bool} {v a : Nat}
    (hj : Steps j (w * 2) u) (hn : Normal e (v + j) u) (hb : j * 2 ^ k ≤ a) :
    ∃ x', Normal e (a + v * 2 ^ k) x' ∧ Steps a (w * 4 ^ k * 2) x' := by
  obtain ⟨x', hnx', hsx'⟩ := packed_zero hj hn hb
  refine ⟨x', ?_, hsx'⟩
  have heq : (v + j) * 2 ^ k + (a - j * 2 ^ k) = a + v * 2 ^ k := by
    have : (v + j) * 2 ^ k = v * 2 ^ k + j * 2 ^ k := by ring
    omega
  rw [heq] at hnx'
  exact hnx'

lemma packed_positive_affine {k z w x y j u : Nat} {e : Bool} {v a : Nat}
    (hf : Field k z w x) (hz : 0 < z) (hw : H w y) (hj : Steps j (y * 2) u)
    (hn : Normal e (v + j + 2) u) (hb : (j + 2) * 2 ^ k ≤ a + z * 2) :
    ∃ x', Normal e (a + z * 2 + v * 2 ^ k) x' ∧ Steps a (x * 2) x' := by
  have hzb := field_bound hf
  have h1 : (j + 2) * 2 ^ k = j * 2 ^ k + 2 ^ k * 2 := by ring
  obtain ⟨x', hnx', hsx'⟩ := packed_normal hf hz hw hj hn (a := a) (by omega)
  refine ⟨x', ?_, hsx'⟩
  have heq : (v + j + 2) * 2 ^ k + (a - ((2 ^ k - z) * 2 + j * 2 ^ k)) = a + z * 2 + v * 2 ^ k := by
    have : (v + j + 2) * 2 ^ k = v * 2 ^ k + j * 2 ^ k + 2 ^ k * 2 := by ring
    omega
  rw [heq] at hnx'
  exact hnx'

lemma normal_zero_value_aux {e : Bool} {m x : Nat} (hn : Normal e m x) (hm : m = 0) : e = false ∧ x = 0 := by
  induction hn with
  | D => exact ⟨rfl, rfl⟩
  | E2 => omega
  | E3 => omega
  | @zero e' n' x' _ ih =>
    obtain ⟨he, hx⟩ := ih (by omega)
    exact ⟨he, by omega⟩
  | one => omega

lemma normal_zero_value {e : Bool} {x : Nat} (hn : Normal e 0 x) : e = false ∧ x = 0 :=
  normal_zero_value_aux hn rfl

lemma normal_top {e : Bool} {n x : Nat} (hn : Normal e n x) (hp : 0 < n) :
    ∃ k z w, Field k z w x ∧ n = w * 2 ^ k + z ∧
      ((e = false ∧ w = 1) ∨ (e = true ∧ (w = 2 ∨ w = 3))) := by
  induction hn with
  | D => omega
  | E2 => exact ⟨0, 0, 2, Field.nil 2, by simp, Or.inr ⟨rfl, Or.inl rfl⟩⟩
  | E3 => exact ⟨0, 0, 3, Field.nil 3, by simp, Or.inr ⟨rfl, Or.inr rfl⟩⟩
  | @zero e' n' x' _ ih =>
    obtain ⟨k, z, w, hf, hne, htop⟩ := ih (by omega)
    refine ⟨1 + k, z * 2, w, Field.zero hf, ?_, htop⟩
    rw [hne, pow2_one_add]; ring
  | @one e' n' x' hn' ih =>
    rcases (by omega : n' = 0 ∨ n' ≠ 0) with hn0 | hn0
    · subst hn0
      obtain ⟨he, hx⟩ := normal_zero_value hn'
      subst he hx
      exact ⟨0, 0, 1, Field.nil 1, by simp, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨k, z, w, hf, hne, htop⟩ := ih (by omega)
      refine ⟨1 + k, 1 + z * 2, w, Field.one hf, ?_, htop⟩
      rw [hne, pow2_one_add]; ring

inductive View : Bool → Nat → Nat → Prop where
  | low {e : Bool} (v x t : Nat) : Normal e v x → View e ((1 + v * 2) * 2 ^ t) ((1 + x * 4) * 4 ^ t)
  | two (t : Nat) : View true (2 * 2 ^ t) (2 * 4 ^ t)
  | three (t : Nat) : View true (3 * 2 ^ t) (3 * 4 ^ t)

lemma normal_view {e : Bool} {n x : Nat} (hn : Normal e n x) (hp : 0 < n) : View e n x := by
  induction hn with
  | D => omega
  | E2 => simpa using View.two 0
  | E3 => simpa using View.three 0
  | @zero e' n' x' _ ih =>
    rcases ih (by omega) with ⟨v0, x0, t, hnv⟩ | ⟨t⟩ | ⟨t⟩
    · have hv := View.low v0 x0 (1 + t) hnv
      have h1 : (1 + v0 * 2) * 2 ^ (1 + t) = (1 + v0 * 2) * 2 ^ t * 2 := by rw [pow2_one_add]; ring
      have h2 : (1 + x0 * 4) * 4 ^ (1 + t) = (1 + x0 * 4) * 4 ^ t * 4 := by rw [pow4_one_add]; ring
      rw [h1, h2] at hv
      exact hv
    · have hv := View.two (1 + t)
      have h1 : 2 * 2 ^ (1 + t) = 2 * 2 ^ t * 2 := by rw [pow2_one_add]; ring
      have h2 : 2 * 4 ^ (1 + t) = 2 * 4 ^ t * 4 := by rw [pow4_one_add]; ring
      rw [h1, h2] at hv
      exact hv
    · have hv := View.three (1 + t)
      have h1 : 3 * 2 ^ (1 + t) = 3 * 2 ^ t * 2 := by rw [pow2_one_add]; ring
      have h2 : 3 * 4 ^ (1 + t) = 3 * 4 ^ t * 4 := by rw [pow4_one_add]; ring
      rw [h1, h2] at hv
      exact hv
  | @one e' n' x' hn' _ =>
    simpa using View.low n' x' 0 hn'

inductive Return : Nat → Nat → Nat → Nat → Nat → Prop where
  | odd (t : Nat) {x y : Nat} (a : Nat) : H x y → Return ((1 + x * 2) * 4 ^ t) a y (a + t) 0
  | power (t a : Nat) : Return (2 * 4 ^ t) a 1 1 (a + t)

lemma field_return {k z w x : Nat} (a : Nat) (hf : Field k z w x) (hz : 0 < z) :
    ∃ t j v y, Field j v w y ∧ k = t + 1 + j ∧ z = (1 + v * 2) * 2 ^ t ∧
      Return x a (1 + y * 2) (a + t) 0 := by
  obtain ⟨t, j, v, y, hk, hze, hxe, hfj⟩ := field_low hf hz
  refine ⟨t, j, v, y, hfj, hk, hze, ?_⟩
  subst hxe
  have hr := Return.odd t a (H.even y)
  have heq : (1 + y * 2 * 2) * 4 ^ t = (1 + y * 4) * 4 ^ t := by ring
  rw [heq] at hr
  exact hr

def Round (x a b y a' b' : Nat) : Prop :=
  ∃ u, Steps (a - 1) x u ∧ Return u (a + b + 1) y a' b'

def Budget (a v : Nat) : Prop :=
  v < a ∧ (a % 2 = 1 → v * 2 < a)

inductive Safe : Nat → Nat → Nat → Prop where
  | main {e : Bool} {v x a : Nat} : Normal e v x → Budget a v → Safe (1 + x * 2) a 0
  | high {w k z x a : Nat} : (w = 6 ∨ w = 7) → Field k z w x → Budget a (w * 2 ^ k + z) → Safe (1 + x * 2) a 0
  | raw {x a : Nat} : (x = 4 ∨ x = 8 ∨ x = 16) → 0 < a → Safe x a 0
  | weak {e : Bool} {v x : Nat} : Normal e v x → 0 < v → Safe (1 + x * 2) (v * 2 - 1) 0
  | near {w k z x a : Nat} : (w = 10 ∨ w = 11) → Field k z w x → 8 * 2 ^ k ≤ a → Safe (1 + x * 2) a 0
  | reset {a b : Nat} : 0 < a → 0 < b → Safe 1 a b

lemma budget_strong {a v : Nat} (h : v * 2 < a) : Budget a v :=
  ⟨by omega, fun _ => h⟩

lemma safe_positive {x a b : Nat} (hs : Safe x a b) : 0 < a := by
  cases hs with
  | main _ hb => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hb.1
  | high _ _ hb => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hb.1
  | raw _ ha => exact ha
  | weak _ hv => omega
  | @near w k _ _ _ _ _ ha =>
    have hp := pow2_pos k
    omega
  | reset ha _ => exact ha

lemma budget_return {a n t v : Nat} (hn : n = (1 + v * 2) * 2 ^ t)
    (hcases : (a % 2 = 1 ∧ n % 2 = 1 ∧ n ≤ a * 2 + 1) ∨
              (a % 2 = 0 ∧ n % 2 = 0 ∧ n ≤ a * 3 - 2)) :
    Budget (a + 1 + t) v := by
  subst hn
  rcases hcases with ⟨ha, hn_odd, hle⟩ | ⟨ha, hn_even, hle⟩
  · cases t with
    | zero =>
      simp only [Nat.pow_zero, Nat.mul_one] at hle ⊢
      exact ⟨by omega, fun _ => by omega⟩
    | succ t =>
      have hmul : (1 + v * 2) * 2 ^ (t + 1) = ((1 + v * 2) * 2 ^ t) * 2 := by
        rw [pow2_succ]; ring
      rw [hmul] at hn_odd
      omega
  · rcases t with _ | _ | t
    · simp only [Nat.pow_zero, Nat.mul_one] at hn_even
      omega
    · change (1 + v * 2) * 2 ≤ a * 3 - 2 at hle
      exact ⟨by omega, fun hodd => by omega⟩
    · have hp : 0 < 2 ^ t := pow2_pos t
      have hpow : (1 + v * 2) * 2 ^ (t + 2) = (1 + v * 2) * 4 * 2 ^ t := by
        rw [pow2_succ, pow2_succ]; ring
      have hge : (1 + v * 2) * 4 * 1 ≤ (1 + v * 2) * 4 * 2 ^ t :=
        Nat.mul_le_mul_left ((1 + v * 2) * 4) hp
      rw [hpow] at hle
      exact ⟨by omega, fun _ => by omega⟩

lemma normal_return {e : Bool} {n x : Nat} (a : Nat) (hn : Normal e n x) (hp : 0 < n)
    (hb : ∀ t v, n = (1 + v * 2) * 2 ^ t → Budget (a + 1 + t) v) :
    ∃ y b c, Return x (a + 1) y b c ∧ Safe y b c := by
  rcases normal_view hn hp with ⟨v0, u0, t, hnv⟩ | ⟨t⟩ | ⟨t⟩
  · refine ⟨1 + u0 * 2, a + 1 + t, 0, ?_, Safe.main hnv (hb t v0 rfl)⟩
    have hr := Return.odd t (a + 1) (H.even u0)
    have heq : (1 + u0 * 2 * 2) * 4 ^ t = (1 + u0 * 4) * 4 ^ t := by ring
    rw [heq] at hr
    exact hr
  · exact ⟨1, 1, a + 1 + t, Return.power t (a + 1), Safe.reset (by omega) (by omega)⟩
  · refine ⟨4, a + 1 + t, 0, ?_, Safe.raw (Or.inl rfl) (by omega)⟩
    have hr := Return.odd t (a + 1) (H_four (H.even 0))
    simpa using hr

lemma normal_return_strong {e : Bool} {n x a : Nat}
    (hn : Normal e n x) (hp : 0 < n) (hle : n ≤ a + 1) :
    ∃ y b c, Return x (a + 1) y b c ∧ Safe y b c := by
  refine normal_return a hn hp (fun t v heq => budget_strong ?_)
  have hp2 : 0 < 2 ^ t := pow2_pos t
  have hge : (1 + v * 2) * 1 ≤ (1 + v * 2) * 2 ^ t := Nat.mul_le_mul_left (1 + v * 2) hp2
  omega

lemma reset_closed {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    ∃ y a' b', Round 1 a b y a' b' ∧ Safe y a' b' := by
  obtain ⟨u, hnu, hsu⟩ := normal_steps (a - 1) (Normal.one Normal.D)
  obtain ⟨y, a', b', hr, hs⟩ := normal_return_strong (a := a + b) hnu (by omega) (by omega)
  exact ⟨y, a', b', ⟨u, hsu, hr⟩, hs⟩

lemma normal_raw_return {e : Bool} {n x a : Nat}
    (hn : Normal e n x) (he : n = a + 3) (ha : 0 < a) :
    ∃ y b c, Return x (a + 1) y b c ∧ Safe y b c := by
  rcases normal_view hn (by omega) with ⟨v0, u0, t, hnv⟩ | ⟨t⟩ | ⟨t⟩
  · refine ⟨1 + u0 * 2, a + 1 + t, 0, ?_, ?_⟩
    · have hr := Return.odd t (a + 1) (H.even u0)
      have heq : (1 + u0 * 2 * 2) * 4 ^ t = (1 + u0 * 4) * 4 ^ t := by ring
      rw [heq] at hr
      exact hr
    · cases t with
      | zero =>
        simp only [Nat.pow_zero, Nat.mul_one] at he
        have hw := Safe.weak hnv (by omega)
        have heq : v0 * 2 - 1 = a + 1 + 0 := by omega
        rw [heq] at hw
        exact hw
      | succ t =>
        rw [pow2_succ] at he
        have hp2 : 0 < 2 ^ t := pow2_pos t
        have hge : (1 + v0 * 2) * 1 ≤ (1 + v0 * 2) * 2 ^ t := Nat.mul_le_mul_left (1 + v0 * 2) hp2
        have hmul : (1 + v0 * 2) * (2 ^ t * 2) = ((1 + v0 * 2) * 2 ^ t) * 2 := by ring
        rw [hmul] at he
        refine Safe.main hnv (budget_strong ?_)
        omega
  · exact ⟨1, 1, a + 1 + t, Return.power t (a + 1), Safe.reset (by omega) (by omega)⟩
  · refine ⟨4, a + 1 + t, 0, ?_, Safe.raw (Or.inl rfl) (by omega)⟩
    have hr := Return.odd t (a + 1) (H_four (H.even 0))
    simpa using hr

lemma raw_closed {x a : Nat} (hx : x = 4 ∨ x = 8 ∨ x = 16) (ha : 0 < a) :
    ∃ y a' b', Round x a 0 y a' b' ∧ Safe y a' b' := by
  rcases hx with rfl | rfl | rfl
  · obtain ⟨u, hnu, hsu⟩ := normal_steps (a - 1) (Normal.zero (Normal.one Normal.D))
    obtain ⟨y, a', b', hr, hs⟩ := normal_return_strong (a := a) hnu (by omega) (by omega)
    exact ⟨y, a', b', ⟨u, hsu, hr⟩, hs⟩
  · obtain ⟨u, hnu, hsu⟩ := normal_steps (a - 1) (Normal.zero Normal.E2)
    obtain ⟨y, a', b', hr, hs⟩ := normal_raw_return (a := a) hnu (by omega) ha
    exact ⟨y, a', b', ⟨u, hsu, hr⟩, hs⟩
  · obtain ⟨u, hnu, hsu⟩ := normal_steps (a - 1) (Normal.zero (Normal.zero (Normal.one Normal.D)))
    obtain ⟨y, a', b', hr, hs⟩ := normal_raw_return (a := a) hnu (by omega) ha
    exact ⟨y, a', b', ⟨u, hsu, hr⟩, hs⟩

lemma two22 : Steps 2 22 64 := by
  refine Steps.next (H.even 11) (steps_one ?_)
  simpa using H.carry 2 (H_four (H.even 0))

lemma two6 : Steps 2 6 16 := by
  refine Steps.next (H.even 3) (steps_one ?_)
  simpa using H.carry 2 (H.even 0)

lemma two14 : Steps 2 14 32 := by
  refine Steps.next (H.even 7) (steps_one ?_)
  simpa using H.carry 3 (H.even 0)

lemma weak_count {e : Bool} {v x : Nat} (hn : Normal e v x) (hv : 0 < v) :
    ∃ n y, Normal (!e) n y ∧ Steps (v * 2 - 1) (x * 2) y ∧
      0 < n ∧ n ≤ v * 4 - 1 ∧ n % 2 = 1 := by
  obtain ⟨k, z, w, hf, hve, htop⟩ := normal_top hn hv
  have hzb := field_bound hf
  have hN2 : Normal false 2 4 := Normal.zero (Normal.one Normal.D)
  have hN4 : Normal false 4 16 := Normal.zero hN2
  rcases htop with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · rcases (by omega : z = 0 ∨ z ≠ 0) with hz | hz
    · subst hz
      rw [field_unique hf (field_zeros k 1)]
      obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 1) (j := 0) (u := 2)
        (e := true) (v := 2) (a := v * 2 - 1) (Steps.zero 2) Normal.E2 (by omega)
      exact ⟨v * 2 - 1 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 1) (x := x)
        (y := 4) (j := 0) (u := 8) (e := true) (v := 2) (a := v * 2 - 1)
        hf (by omega) (H_four (H.even 0)) (Steps.zero 8) (Normal.zero Normal.E2) (by omega)
      exact ⟨v * 2 - 1 + z * 2 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
  · rcases (by omega : z = 0 ∨ z ≠ 0) with hz | hz
    · subst hz
      rw [field_unique hf (field_zeros k 2)]
      obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 2) (j := 0) (u := 4)
        (e := false) (v := 2) (a := v * 2 - 1) (Steps.zero 4) hN2 (by omega)
      exact ⟨v * 2 - 1 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 2) (x := x)
        (y := 3) (j := 2) (u := 16) (e := false) (v := 0) (a := v * 2 - 1)
        hf (by omega) (H.even 1) two6 hN4 (by omega)
      refine ⟨v * 2 - 1 + z * 2, y, ?_, hsy, by omega, by omega, by omega⟩
      change Normal false (v * 2 - 1 + z * 2) y
      simpa only [Nat.zero_mul, Nat.add_zero] using hny
  · rcases (by omega : z = 0 ∨ z ≠ 0) with hz | hz
    · subst hz
      rw [field_unique hf (field_zeros k 3)]
      obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 3) (j := 2) (u := 16)
        (e := false) (v := 2) (a := v * 2 - 1) two6 hN4 (by omega)
      exact ⟨v * 2 - 1 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 3) (x := x)
        (y := 8) (j := 0) (u := 16) (e := false) (v := 2) (a := v * 2 - 1)
        hf (by omega) (H_eight (H.even 0)) (Steps.zero 16) hN4 (by omega)
      exact ⟨v * 2 - 1 + z * 2 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩

lemma weak_closed {e : Bool} {v x : Nat} (hn : Normal e v x) (hv : 0 < v) :
    ∃ y a' b', Round (1 + x * 2) (v * 2 - 1) 0 y a' b' ∧ Safe y a' b' := by
  obtain ⟨n, u, hnu, hsu, hnp, hnb, hno⟩ := weak_count hn hv
  obtain ⟨y, a', b', hr, hs⟩ := normal_return (v * 2 - 1) hnu hnp (fun t w heq =>
    budget_return heq (Or.inl ⟨by omega, hno, by omega⟩))
  refine ⟨y, a', b', ⟨u, steps_drop_even (by omega) hsu, hr⟩, hs⟩

lemma normal_count_closed {v x a : Nat} {e : Bool} {n u : Nat}
    (hb : Budget a v) (hn : Normal e n u) (hs : Steps a (x * 2) u)
    (hp : 0 < n) (hu : n ≤ a + v * 2) (ho : n % 2 = a % 2) :
    ∃ y a' b', Round (1 + x * 2) a 0 y a' b' ∧ Safe y a' b' := by
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨y, a', b', hr, hsafe⟩ := normal_return a hn hp (fun t w heq => by
    refine budget_return heq ?_
    rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha1
    · exact Or.inr ⟨ha, by omega, by omega⟩
    · have hlt := hb2 ha1
      exact Or.inl ⟨ha1, by omega, by omega⟩)
  exact ⟨y, a', b', ⟨u, steps_drop_even (by omega) hs, hr⟩, hsafe⟩

lemma main_regular_count {w k z x a : Nat}
    (hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7)
    (hf : Field k z w x) (hb : Budget a (w * 2 ^ k + z))
    (hp1 : w = 1 → 0 < z → 2 * 2 ^ k ≤ a + z * 2)
    (hp2 : w = 2 → 0 < z → 4 * 2 ^ k ≤ a + z * 2) :
    ∃ e n y, Normal e n y ∧ Steps a (x * 2) y ∧
      a ≤ n ∧ n ≤ a + (w * 2 ^ k + z) * 2 ∧ n % 2 = a % 2 := by
  have hzb := field_bound hf
  obtain ⟨hb1, hb2⟩ := hb
  have hN2 : Normal false 2 4 := Normal.zero (Normal.one Normal.D)
  have hN4 : Normal false 4 16 := Normal.zero hN2
  have hE4 : Normal true 4 8 := Normal.zero Normal.E2
  have hE6 : Normal true 6 12 := Normal.zero Normal.E3
  have hE8 : Normal true 8 32 := Normal.zero hE4
  rcases (by omega : z = 0 ∨ z ≠ 0) with hz | hz
  · subst hz
    rw [field_unique hf (field_zeros k w)]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 1) (j := 0) (u := 2)
        (e := true) (v := 2) (a := a) (Steps.zero 2) Normal.E2 (by omega)
      exact ⟨true, a + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 2) (j := 0) (u := 4)
        (e := false) (v := 2) (a := a) (Steps.zero 4) hN2 (by omega)
      exact ⟨false, a + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 3) (j := 2) (u := 16)
        (e := false) (v := 2) (a := a) two6 hN4 (by omega)
      exact ⟨false, a + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 6) (j := 0) (u := 12)
        (e := true) (v := 6) (a := a) (Steps.zero 12) hE6 (by omega)
      exact ⟨true, a + 6 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 7) (j := 2) (u := 32)
        (e := true) (v := 6) (a := a) two14 hE8 (by omega)
      exact ⟨true, a + 6 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
  · rcases hw with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 1) (x := x)
        (y := 4) (j := 0) (u := 8) (e := true) (v := 2) (a := a)
        hf (by omega) (H_four (H.even 0)) (Steps.zero 8) hE4 (hp1 rfl (by omega))
      exact ⟨true, a + z * 2 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 2) (x := x)
        (y := 3) (j := 2) (u := 16) (e := false) (v := 0) (a := a)
        hf (by omega) (H.even 1) two6 hN4 (hp2 rfl (by omega))
      refine ⟨false, a + z * 2, y, ?_, hsy, by omega, by omega, by omega⟩
      simpa only [Nat.zero_mul, Nat.add_zero] using hny
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 3) (x := x)
        (y := 8) (j := 0) (u := 16) (e := false) (v := 2) (a := a)
        hf (by omega) (H_eight (H.even 0)) (Steps.zero 16) hN4 (by omega)
      exact ⟨false, a + z * 2 + 2 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 6) (x := x)
        (y := 7) (j := 2) (u := 32) (e := true) (v := 4) (a := a)
        hf (by omega) (H.even 3) two14 hE8 (by omega)
      exact ⟨true, a + z * 2 + 4 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · have hj7 : H 7 16 := by simpa using H.carry 2 (H.even 0)
      obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 7) (x := x)
        (y := 16) (j := 0) (u := 32) (e := true) (v := 6) (a := a)
        hf (by omega) hj7 (Steps.zero 32) hE8 (by omega)
      exact ⟨true, a + z * 2 + 6 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩

lemma main_regular_closed {w k z x a : Nat}
    (hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7)
    (hf : Field k z w x) (hb : Budget a (w * 2 ^ k + z))
    (hp1 : w = 1 → 0 < z → 2 * 2 ^ k ≤ a + z * 2)
    (hp2 : w = 2 → 0 < z → 4 * 2 ^ k ≤ a + z * 2) :
    ∃ y a' b', Round (1 + x * 2) a 0 y a' b' ∧ Safe y a' b' := by
  obtain ⟨e, n, u, hnu, hsu, hle, hub, hmod⟩ := main_regular_count hw hf hb hp1 hp2
  have ha : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le _) hb.1
  exact normal_count_closed hb hnu hsu (by omega) hub hmod

lemma high_return {w k z u a v : Nat}
    (hw : w = 6 ∨ w = 7) (hf : Field k z w u) (hz : 0 < z)
    (hb : Budget a v) (hu : w * 2 ^ k + z ≤ a + v * 2) (hp : (w * 2 ^ k + z) % 2 = a % 2) :
    ∃ y b c, Return u (a + 1) y b c ∧ Safe y b c := by
  obtain ⟨t, j, v', y, hfj, hk, hze, hr⟩ := field_return (a + 1) hf hz
  refine ⟨1 + y * 2, a + 1 + t, 0, hr, Safe.high hw hfj ?_⟩
  obtain ⟨hb1, hb2⟩ := hb
  refine budget_return (n := w * 2 ^ k + z) ?_ ?_
  · rw [hk, hze]
    have : 2 ^ (t + 1 + j) = 2 ^ j * 2 * 2 ^ t := by
      rw [Nat.add_assoc, Nat.pow_add, Nat.pow_add]; ring
    rw [this]; ring
  · rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha1
    · exact Or.inr ⟨ha, by omega, by omega⟩
    · have hlt := hb2 ha1
      exact Or.inl ⟨ha1, by omega, by omega⟩

lemma main_short2 {k z x a : Nat}
    (hf : Field k z 2 x) (hz : 0 < z) (hb : Budget a (2 * 2 ^ k + z))
    (hp : a + z * 2 < 4 * 2 ^ k) :
    ∃ y a' b', Round (1 + x * 2) a 0 y a' b' ∧ Safe y a' b' := by
  have hzb := field_bound hf
  obtain ⟨hb1, hb2⟩ := hb
  have ha_even : a % 2 = 0 := by
    rcases (by omega : a % 2 = 1 ∨ a % 2 = 0) with ha1 | ha0
    · have := hb2 ha1; omega
    · exact ha0
  obtain ⟨q, r, u, hq, hr, he, hfu, hsu⟩ := packed_short hf hz (H.even 1) (by omega) hp
  have hv : (6 + q) * 2 ^ k + r = a + (2 * 2 ^ k + z) * 2 := by
    have : (2 + q) * 2 ^ k = 2 * 2 ^ k + q * 2 ^ k := by ring
    have : (6 + q) * 2 ^ k = 6 * 2 ^ k + q * 2 ^ k := by ring
    omega
  have hw : 6 + q = 6 ∨ 6 + q = 7 := by omega
  rcases (by omega : r = 0 ∨ r ≠ 0) with hr0 | hr0
  · subst hr0
    have hq1 : q = 1 := by
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · exfalso; omega
      · rfl
    subst hq1
    rw [field_unique hfu (field_zeros k 7)] at hsu
    refine ⟨8, a + 1 + k, 0, ⟨7 * 4 ^ k, steps_drop_even (by omega) hsu, ?_⟩,
      Safe.raw (Or.inr (Or.inl rfl)) (by omega)⟩
    have hret := Return.odd k (a + 1) (H_eight (H.even 0))
    simpa using hret
  · obtain ⟨y, a', b', hret, hsafe⟩ := high_return hw hfu (by omega) ⟨hb1, hb2⟩
      (by omega) (by omega)
    exact ⟨y, a', b', ⟨u, steps_drop_even (by omega) hsu, hret⟩, hsafe⟩

lemma near_return {w k z u a : Nat}
    (hw : w = 10 ∨ w = 11) (hf : Field k z w u) (hz : 0 < z)
    (hp : z % 2 = 0) (hb : 2 * 2 ^ k < a) :
    ∃ y b c, Return u (a + 1) y b c ∧ Safe y b c := by
  obtain ⟨t, j, v, y, hfj, hk, hze, hr⟩ := field_return (a + 1) hf hz
  refine ⟨1 + y * 2, a + 1 + t, 0, hr, Safe.near hw hfj ?_⟩
  cases t with
  | zero =>
    simp only [Nat.pow_zero, Nat.mul_one] at hze
    omega
  | succ t =>
    have hpow : 2 ^ k = 2 ^ t * (4 * 2 ^ j) := by
      rw [hk, Nat.add_assoc, Nat.pow_add, Nat.pow_add, pow2_succ]; ring
    have hp2 : 0 < 2 ^ t := pow2_pos t
    have hge : 1 * (4 * 2 ^ j) ≤ 2 ^ t * (4 * 2 ^ j) := Nat.mul_le_mul_right (4 * 2 ^ j) hp2
    rw [hpow] at hb
    omega

lemma main_short1 {k z x a : Nat}
    (hf : Field k z 1 x) (hz : 0 < z) (hb : Budget a (2 ^ k + z))
    (hp : a + z * 2 < 2 * 2 ^ k) :
    ∃ y a' b', Round (1 + x * 2) a 0 y a' b' ∧ Safe y a' b' := by
  have hzb := field_bound hf
  obtain ⟨hb1, hb2⟩ := hb
  have ha_even : a % 2 = 0 := by
    rcases (by omega : a % 2 = 1 ∨ a % 2 = 0) with ha1 | ha0
    · have := hb2 ha1; omega
    · exact ha0
  cases k with
  | zero =>
    change z < 1 at hzb; omega
  | succ k =>
    rw [pow2_succ] at hb1 hb2 hp hzb
    obtain ⟨x', hfx'⟩ := field_exists k z 4 (by omega)
    have hxx' : x = x' := by
      refine field_unique hf ?_
      have hc := field_compose (Field.zero (Field.nil 1)) hfx'
      have h1 : 1 + 0 + k = k + 1 := by omega
      have h2 : 0 * 2 * 2 ^ k + z = z := by ring
      rw [h1, h2] at hc
      exact hc
    subst hxx'
    obtain ⟨q, r, u, hq, hr, he, hfu, hsu⟩ := packed_short hfx' hz (H.even 2) (a := a)
      (by omega) (by omega)
    have hw : 10 + q = 10 ∨ 10 + q = 11 := by omega
    rcases (by omega : r = 0 ∨ r ≠ 0) with hr0 | hr0
    · subst hr0
      have hq1 : q = 1 := by
        rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
        · exfalso; omega
        · rfl
      subst hq1
      rw [field_unique hfu (field_zeros k 11)] at hsu
      refine ⟨16, a + 1 + k, 0, ⟨11 * 4 ^ k, steps_drop_even (by omega) hsu, ?_⟩,
        Safe.raw (Or.inr (Or.inr rfl)) (by omega)⟩
      have hret := Return.odd k (a + 1) (H_four (H_four (H.even 0)))
      simpa using hret
    · have hr_even : r % 2 = 0 := by
        cases k with
        | zero => change r < 1 at hr; omega
        | succ k' =>
          have hmul : (2 + q) * 2 ^ (k' + 1) = ((2 + q) * 2 ^ k') * 2 := by
            rw [pow2_succ]; ring
          rw [hmul] at he
          omega
      have ha_gt : 2 * 2 ^ k < a := by
        have hmul : (2 + q) * 2 ^ k = 2 * 2 ^ k + q * 2 ^ k := by ring
        omega
      obtain ⟨y, a', b', hret, hsafe⟩ := near_return hw hfu (by omega) hr_even ha_gt
      exact ⟨y, a', b', ⟨u, steps_drop_even (by omega) hsu, hret⟩, hsafe⟩

lemma near_count {w k z x a : Nat}
    (hw : w = 10 ∨ w = 11) (hf : Field k z w x) (hb : 8 * 2 ^ k ≤ a) :
    ∃ n y, Normal false n y ∧ Steps a (x * 2) y ∧
      a ≤ n ∧ n < a + 8 * 2 ^ k ∧ n % 2 = a % 2 := by
  have hzb := field_bound hf
  have hN8 : Normal false 8 64 := Normal.zero (Normal.zero (Normal.zero (Normal.one Normal.D)))
  have hN6 : Normal false 6 20 := Normal.zero (Normal.one (Normal.one Normal.D))
  rcases (by omega : z = 0 ∨ z ≠ 0) with hz | hz
  · subst hz
    rw [field_unique hf (field_zeros k w)]
    rcases hw with rfl | rfl
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 10) (j := 0) (u := 20)
        (e := false) (v := 6) (a := a) (Steps.zero 20) hN6 (by omega)
      exact ⟨a + 6 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · obtain ⟨y, hny, hsy⟩ := packed_zero_affine (k := k) (w := 11) (j := 2) (u := 64)
        (e := false) (v := 6) (a := a) two22 hN8 (by omega)
      exact ⟨a + 6 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
  · rcases hw with rfl | rfl
    · obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 10) (x := x)
        (y := 11) (j := 2) (u := 64) (e := false) (v := 4) (a := a)
        hf (by omega) (H.even 5) two22 hN8 (by omega)
      exact ⟨a + z * 2 + 4 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩
    · have hj11 : H 11 32 := by simpa using H_eight (H_four (H.even 0))
      obtain ⟨y, hny, hsy⟩ := packed_positive_affine (k := k) (z := z) (w := 11) (x := x)
        (y := 32) (j := 0) (u := 64) (e := false) (v := 6) (a := a)
        hf (by omega) hj11 (Steps.zero 64) hN8 (by omega)
      exact ⟨a + z * 2 + 6 * 2 ^ k, y, hny, hsy, by omega, by omega, by omega⟩

lemma near_closed {w k z x a : Nat}
    (hw : w = 10 ∨ w = 11) (hf : Field k z w x) (hb : 8 * 2 ^ k ≤ a) :
    ∃ y a' b', Round (1 + x * 2) a 0 y a' b' ∧ Safe y a' b' := by
  obtain ⟨n, u, hnu, hsu, hle, hub, hmod⟩ := near_count hw hf hb
  have hp2 : 0 < 2 ^ k := pow2_pos k
  obtain ⟨y, a', b', hr, hsafe⟩ := normal_return a hnu (by omega) (fun t v heq => by
    refine budget_return heq ?_
    rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha1
    · exact Or.inr ⟨ha, by omega, by omega⟩
    · exact Or.inl ⟨ha1, by omega, by omega⟩)
  exact ⟨y, a', b', ⟨u, steps_drop_even (by omega) hsu, hr⟩, hsafe⟩

lemma main_closed {w k z x a : Nat}
    (hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7)
    (hf : Field k z w x) (hb : Budget a (w * 2 ^ k + z)) :
    ∃ y a' b', Round (1 + x * 2) a 0 y a' b' ∧ Safe y a' b' := by
  rcases (by omega : z = 0 ∨ z ≠ 0) with hz | hz
  · subst hz
    exact main_regular_closed hw hf hb (fun _ h => by omega) (fun _ h => by omega)
  · rcases (by omega : w = 1 ∨ w ≠ 1) with hw1 | hw1
    · subst hw1
      rcases (by omega : 2 * 2 ^ k ≤ a + z * 2 ∨ ¬ (2 * 2 ^ k ≤ a + z * 2)) with hle | hle
      · exact main_regular_closed (Or.inl rfl) hf hb (fun _ _ => hle) (fun h _ => by omega)
      · have h1 : 1 * 2 ^ k + z = 2 ^ k + z := by ring
        rw [h1] at hb
        exact main_short1 hf (by omega) hb (by omega)
    · rcases (by omega : w = 2 ∨ w ≠ 2) with hw2 | hw2
      · subst hw2
        rcases (by omega : 4 * 2 ^ k ≤ a + z * 2 ∨ ¬ (4 * 2 ^ k ≤ a + z * 2)) with hle | hle
        · exact main_regular_closed (Or.inr (Or.inl rfl)) hf hb (fun h _ => by omega) (fun _ _ => hle)
        · exact main_short2 hf (by omega) hb (by omega)
      · exact main_regular_closed hw hf hb (fun h _ => False.elim (hw1 h)) (fun h _ => False.elim (hw2 h))

lemma closed {x a b : Nat} (hs : Safe x a b) :
    ∃ y a' b', Round x a b y a' b' ∧ Safe y a' b' := by
  cases hs with
  | @main e v x a hnv hb =>
    rcases (by omega : v = 0 ∨ v ≠ 0) with hv | hv
    · subst hv
      obtain ⟨rfl, rfl⟩ := normal_zero_value hnv
      obtain ⟨u, hnu, hsu⟩ := normal_steps a Normal.D
      have hnu' : Normal false a u := by simpa only [Nat.zero_add] using hnu
      have ha : 0 < a := hb.1
      exact normal_count_closed (v := 0) (x := 0) (a := a) hb hnu' hsu ha (by omega) rfl
    · obtain ⟨k, z, w, hf, hve, htop⟩ := normal_top hnv (by omega)
      rw [hve] at hb
      have hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7 := by
        rcases htop with ⟨_, rfl⟩ | ⟨_, rfl | rfl⟩ <;> omega
      exact main_closed hw hf hb
  | high hw hf hb => exact main_closed (by rcases hw with rfl | rfl <;> omega) hf hb
  | raw hx ha => exact raw_closed hx ha
  | weak hnv hv => exact weak_closed hnv hv
  | near hw hf hb => exact near_closed hw hf hb
  | reset ha hb => exact reset_closed ha hb

-- ============================================================================
-- Section 7: Tape Number Representation (`Num`) & Generic `Rules` Engine
-- ============================================================================

inductive Num : Nat → ListBlank (Fin 2) → Prop where
  | nil : Num 0 default
  | zero {n : Nat} {l : ListBlank (Fin 2)} : Num n l → Num (n * 2) (l <+ ([0] : List (Fin 2)))
  | one {n : Nat} {l : ListBlank (Fin 2)} : Num n l → Num (1 + n * 2) (l <+ ([1] : List (Fin 2)))

lemma default_append_zero : (default : ListBlank (Fin 2)) <+ ([0] : List (Fin 2)) = default :=
  zero_cons_default

lemma Num_even_aux {m : Nat} {l : ListBlank (Fin 2)} (h : Num m l) :
    ∀ n, m = n * 2 → ∃ s, l = s <+ ([0] : List (Fin 2)) ∧ Num n s := by
  cases h with
  | nil =>
    intro n hm
    have hn : n = 0 := by omega
    subst hn
    exact ⟨default, default_append_zero.symm, Num.nil⟩
  | @zero n' s hn' =>
    intro n hm
    have hn : n' = n := by omega
    subst hn
    exact ⟨s, rfl, hn'⟩
  | one =>
    intro n hm; omega

lemma Num_even {n : Nat} {l : ListBlank (Fin 2)} (h : Num (n * 2) l) :
    ∃ s, l = s <+ ([0] : List (Fin 2)) ∧ Num n s :=
  Num_even_aux h n rfl

lemma Num_odd_aux {m : Nat} {l : ListBlank (Fin 2)} (h : Num m l) :
    ∀ n, m = 1 + n * 2 → ∃ s, l = s <+ ([1] : List (Fin 2)) ∧ Num n s := by
  cases h with
  | nil => intro n hm; omega
  | zero => intro n hm; omega
  | @one n' s hn' =>
    intro n hm
    have hn : n' = n := by omega
    subst hn
    exact ⟨s, rfl, hn'⟩

lemma Num_odd {n : Nat} {l : ListBlank (Fin 2)} (h : Num (1 + n * 2) l) :
    ∃ s, l = s <+ ([1] : List (Fin 2)) ∧ Num n s :=
  Num_odd_aux h n rfl

lemma Num_zeros (k : Nat) {n : Nat} {l : ListBlank (Fin 2)} (h : Num n l) :
    Num (n * 2 ^ k) (l <+ (([0] : List (Fin 2)) ^ k)) := by
  induction k with
  | zero =>
    simpa only [Nat.pow_zero, Nat.mul_one, pow_zero_list, listblank_append_nil] using h
  | succ k ih =>
    have hz := Num.zero ih
    have h1 : n * 2 ^ k * 2 = n * 2 ^ (k + 1) := by rw [pow2_succ]; ring
    rw [h1, pow_succ_append_left] at hz
    exact hz

lemma Num_zero_inv_aux {m : Nat} {l : ListBlank (Fin 2)} (h : Num m l) (hm : m = 0) : l = default := by
  induction h with
  | nil => rfl
  | @zero n' s _ ih =>
    rw [ih (by omega), default_append_zero]
  | one => omega

lemma Num_zero_inv {l : ListBlank (Fin 2)} (h : Num 0 l) : l = default :=
  Num_zero_inv_aux h rfl

lemma Num_unique {n : Nat} {l s : ListBlank (Fin 2)} (h1 : Num n l) (h2 : Num n s) : l = s := by
  induction h1 generalizing s with
  | nil => exact (Num_zero_inv h2).symm
  | @zero n' l' _ ih =>
    obtain ⟨s', rfl, hs'⟩ := Num_even h2
    rw [ih hs']
  | @one n' l' _ ih =>
    obtain ⟨s', rfl, hs'⟩ := Num_odd h2
    rw [ih hs']

lemma Num_pairs (k : Nat) : ∀ {n : Nat} {l : ListBlank (Fin 2)},
    Num (n * 4 ^ k) l → ∃ s, Num n s ∧ l = s <+ (([0, 0] : List (Fin 2)) ^ k) := by
  induction k with
  | zero =>
    intro n l hn
    simp only [Nat.pow_zero, Nat.mul_one] at hn
    exact ⟨l, hn, rfl⟩
  | succ k ih =>
    intro n l hn
    have h1 : n * 4 ^ (k + 1) = n * 4 ^ k * 2 * 2 := by rw [pow4_succ]; ring
    rw [h1] at hn
    obtain ⟨u, rfl, hu⟩ := Num_even hn
    obtain ⟨v, rfl, hv⟩ := Num_even hu
    obtain ⟨s, hs, rfl⟩ := ih hv
    refine ⟨s, hs, ?_⟩
    rw [listblank_append_append]
    change (s <+ (([0, 0] : List (Fin 2)) ^ k)) <+ ([0, 0] : List (Fin 2)) =
      s <+ (([0, 0] : List (Fin 2)) ^ (k + 1))
    exact pow_succ_append_left s ([0, 0] : List (Fin 2)) k

lemma Num_run (j : Nat) : ∀ {n : Nat} {l : ListBlank (Fin 2)},
    Num (n * 2 ^ (1 + j) + (2 ^ j - 1)) l →
    ∃ s, l = (s <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j) ∧ Num n s := by
  induction j with
  | zero =>
    intro n l hn
    have heq : n * 2 ^ (1 + 0) + (2 ^ 0 - 1) = n * 2 := by simp
    rw [heq] at hn
    obtain ⟨s, rfl, hs⟩ := Num_even hn
    exact ⟨s, rfl, hs⟩
  | succ j ih =>
    intro n l hn
    have hp : 0 < 2 ^ j := pow2_pos j
    have heq : n * 2 ^ (1 + (j + 1)) + (2 ^ (j + 1) - 1) =
        1 + (n * 2 ^ (1 + j) + (2 ^ j - 1)) * 2 := by
      have h1 : n * 2 ^ (1 + (j + 1)) = (n * 2 ^ (1 + j)) * 2 := by
        rw [pow2_one_add, pow2_succ, pow2_one_add]; ring
      have h2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow2_succ j
      rw [h1, h2]; omega
    rw [heq] at hn
    obtain ⟨l', rfl, hl'⟩ := Num_odd hn
    obtain ⟨s, rfl, hs⟩ := ih hl'
    refine ⟨s, ?_, hs⟩
    rw [pow_succ_append_left]

structure Rules (tm : Machine (Fin 2) (Fin 6)) (q h g : Fin 6) : Prop where
  left_zero : ∀ (l r : ListBlank (Fin 2)),
    ((l <+ ([0] : List (Fin 2))) <{{h}} r) [tm]⊢* ((l <+ ([1] : List (Fin 2))) {{q}}> r)
  left_carry : ∀ (l r : ListBlank (Fin 2)) (j : Nat),
    (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ (1 + j))) <{{h}} r) [tm]⊢*
    (l <{{h}} ((([1] : List (Fin 2)) ^ (2 + j)) +> r))
  scan_right : ∀ (l r : ListBlank (Fin 2)) (j : Nat),
    (l {{q}}> ((([1] : List (Fin 2)) ^ j) +> r)) [tm]⊢*
    ((l <+ (([0] : List (Fin 2)) ^ j)) {{q}}> r)
  right_inc : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    (l {{q}}> (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (2 + n)) +> (([0] : List (Fin 2)) +> r)))) [tm]⊢*
    (l <{{h}} (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (1 + n)) +> (([0, 1, 0] : List (Fin 2)) +> r))))
  right_overflow : ∀ (l r : ListBlank (Fin 2)),
    (l {{q}}> (([1, 1, 0, 0] : List (Fin 2)) +> r)) [tm]⊢⁺
    (l <{{g}} (([1, 0, 1, 0] : List (Fin 2)) +> r))
  scan_overflow : ∀ (l r : ListBlank (Fin 2)) (j : Nat),
    ((l <+ (([0, 0] : List (Fin 2)) ^ j)) <{{g}} r) [tm]⊢*
    (l <{{g}} ((([1, 0] : List (Fin 2)) ^ j) +> r))
  overflow_one : ∀ (l r : ListBlank (Fin 2)),
    ((l <+ ([1] : List (Fin 2))) <{{g}} r) [tm]⊢*
    (l <{{h}} (([1] : List (Fin 2)) +> r))
  overflow_two : ∀ (l r : ListBlank (Fin 2)),
    ((l <+ ([0, 1, 0] : List (Fin 2))) <{{g}} r) [tm]⊢*
    (l <{{h}} (([0, 0, 0] : List (Fin 2)) +> r))
  overflow_resume : ∀ (l r : ListBlank (Fin 2)),
    (l {{q}}> (([0, 0, 0] : List (Fin 2)) +> r)) [tm]⊢*
    (l <{{g}} (([1, 0, 0] : List (Fin 2)) +> r))

lemma H_spec {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    {x y : Nat} (hxy : H x y) :
    ∀ {l : ListBlank (Fin 2)}, Num x l →
      ∃ l', Num y l' ∧ ∀ r, (l <{{h}} r) [tm]⊢* (l' {{q}}> r) := by
  induction hxy with
  | even n =>
    intro l hn
    obtain ⟨s, rfl, hs⟩ := Num_even hn
    exact ⟨s <+ ([1] : List (Fin 2)), Num.one hs, fun r => rules.left_zero s r⟩
  | @carry j x' y' _ ih =>
    intro l hn
    have h2j : 2 + j = 1 + (1 + j) := by omega
    rw [h2j] at hn
    obtain ⟨s, rfl, hs⟩ := Num_run (1 + j) hn
    obtain ⟨s', hs', hstep⟩ := ih hs
    refine ⟨s' <+ (([0] : List (Fin 2)) ^ (2 + j)), ?_, fun r => ?_⟩
    · exact Num_zeros (2 + j) hs'
    · exact stepStar_trans (rules.left_carry s r j)
        (stepStar_trans (hstep ((([1] : List (Fin 2)) ^ (2 + j)) +> r))
          (rules.scan_right s' r (2 + j)))

def right_tape (a b : Nat) : ListBlank (Fin 2) :=
  ([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ a) +> (([0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ b) +> default)))

lemma count_spec {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    {n x y : Nat} (hsteps : Steps n x y) :
    ∀ {l : ListBlank (Fin 2)}, Num x l →
      ∃ l', Num y l' ∧ ∀ a b,
        (l {{q}}> right_tape (1 + n + a) b) [tm]⊢* (l' {{q}}> right_tape (1 + a) (n + b)) := by
  induction hsteps with
  | zero x =>
    intro l hn
    refine ⟨l, hn, fun a b => ?_⟩
    have h1 : 1 + 0 + a = 1 + a := by omega
    have h2 : 0 + b = b := by omega
    rw [h1, h2]
    exact ⟨0, rfl⟩
  | @next n' x' y' z' hxy _ ih =>
    intro l hn
    obtain ⟨l', hl', hstep1⟩ := H_spec rules hxy hn
    obtain ⟨l'', hl'', hstep2⟩ := ih hl'
    refine ⟨l'', hl'', fun a b => ?_⟩
    have hinc := rules.right_inc l ((([1, 0] : List (Fin 2)) ^ b) +> default) (n' + a)
    have h1 : 2 + (n' + a) = 1 + (1 + n') + a := by omega
    have h1' : 1 + (n' + a) = 1 + n' + a := by omega
    rw [h1, h1'] at hinc
    have hinc' : (l {{q}}> right_tape (1 + (1 + n') + a) b) [tm]⊢*
        (l <{{h}} right_tape (1 + n' + a) (1 + b)) := by
      unfold right_tape
      have hrew : (([0, 1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ b) +> default)) =
          (([0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> default)) := by
        have : (1 + b) = b + 1 := by omega
        rw [this, pow_succ_append_right]
        rfl
      rw [← hrew]
      exact hinc
    have h2 := hstep1 (right_tape (1 + n' + a) (1 + b))
    have h3 := hstep2 a (1 + b)
    have h4 : n' + (1 + b) = 1 + n' + b := by omega
    rw [h4] at h3
    exact stepStar_trans hinc' (stepStar_trans h2 h3)

lemma overflow_spec {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    {n x y : Nat} (hsteps : Steps n x y) {l : ListBlank (Fin 2)} (hn : Num x l) :
    ∃ l', Num y l' ∧ ∀ b,
      (l {{q}}> right_tape (1 + n) b) [tm]⊢⁺ (l' <{{g}} ((([1, 0] : List (Fin 2)) ^ (2 + n + b)) +> default)) := by
  obtain ⟨l', hl', hcount⟩ := count_spec rules hsteps hn
  refine ⟨l', hl', fun b => ?_⟩
  have hc := hcount 0 b
  have h1 : 1 + n + 0 = 1 + n := by omega
  rw [h1] at hc
  have hov := rules.right_overflow l' ((([1, 0] : List (Fin 2)) ^ (n + b)) +> default)
  have hrt : right_tape 1 (n + b) = (([1, 1, 0, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (n + b)) +> default)) := rfl
  have hpow : (([1, 0, 1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (n + b)) +> default)) =
      ((([1, 0] : List (Fin 2)) ^ (2 + n + b)) +> default) := by
    have : 2 + n + b = (n + b) + 1 + 1 := by omega
    rw [this, pow_succ_append_right, pow_succ_append_right]
    rfl
  rw [← hrt, hpow] at hov
  exact stepStar_stepPlus_stepPlus hc hov

lemma right_tape_zero (m : Nat) :
    (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ m) +> default)) = right_tape m 0 := by
  unfold right_tape
  simp only [pow_zero_list, listblank_append_nil]
  have h0 : (([0] : List (Fin 2)) +> default) = default := zero_cons_default
  rw [h0]

lemma return_odd {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    (t : Nat) {x y : Nat} (hxy : H x y) {l : ListBlank (Fin 2)} (hn : Num ((1 + x * 2) * 4 ^ t) l) :
    ∃ l', Num y l' ∧ ∀ a,
      (l <{{g}} ((([1, 0] : List (Fin 2)) ^ a) +> default)) [tm]⊢* (l' {{q}}> right_tape (a + t) 0) := by
  obtain ⟨s, hs, rfl⟩ := Num_pairs t hn
  obtain ⟨s', rfl, hs'⟩ := Num_odd hs
  obtain ⟨s'', hs'', hstep⟩ := H_spec rules hxy hs'
  refine ⟨s'', hs'', fun a => ?_⟩
  have h1 := rules.scan_overflow (s' <+ ([1] : List (Fin 2))) ((([1, 0] : List (Fin 2)) ^ a) +> default) t
  have h2 := rules.overflow_one s' ((([1, 0] : List (Fin 2)) ^ t) +> ((([1, 0] : List (Fin 2)) ^ a) +> default))
  have h3 := hstep (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ t) +> ((([1, 0] : List (Fin 2)) ^ a) +> default)))
  have h123 := stepStar_trans h1 (stepStar_trans h2 h3)
  have hmerge : ((([1, 0] : List (Fin 2)) ^ t) +> ((([1, 0] : List (Fin 2)) ^ a) +> default)) =
      ((([1, 0] : List (Fin 2)) ^ (a + t)) +> default) := by
    rw [Nat.add_comm a t, pow_add_append_right]
  rw [hmerge, right_tape_zero] at h123
  exact h123

lemma return_power {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    (t a : Nat) {l : ListBlank (Fin 2)} (hn : Num (2 * 4 ^ t) l) :
    (l <{{g}} ((([1, 0] : List (Fin 2)) ^ a) +> default)) [tm]⊢*
      ((default <+ ([1] : List (Fin 2))) {{q}}> right_tape 1 (a + t)) := by
  obtain ⟨s, hs, rfl⟩ := Num_pairs t hn
  have hs_eq : s = (default <+ ([1] : List (Fin 2))) <+ ([0] : List (Fin 2)) :=
    Num_unique hs (Num.zero (Num.one Num.nil))
  subst hs_eq
  let R := ((([1, 0] : List (Fin 2)) ^ t) +> ((([1, 0] : List (Fin 2)) ^ a) +> default))
  have h1 := rules.scan_overflow ((default <+ ([1] : List (Fin 2))) <+ ([0] : List (Fin 2)))
    ((([1, 0] : List (Fin 2)) ^ a) +> default) t
  have hs_pal : ((default <+ ([1] : List (Fin 2))) <+ ([0] : List (Fin 2))) =
      default <+ ([0, 1, 0] : List (Fin 2)) := by
    change (0 : Fin 2) >> (1 : Fin 2) >> default = (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default
    rw [zero_cons_default]
  have h2 := rules.overflow_two default R
  rw [← hs_pal] at h2
  have h3 := rules.left_zero default (([0, 0, 0] : List (Fin 2)) +> R)
  rw [default_append_zero] at h3
  have h4 := rules.overflow_resume (default <+ ([1] : List (Fin 2))) R
  have h5 := rules.overflow_one default (([1, 0, 0] : List (Fin 2)) +> R)
  have h6 := rules.left_zero default (([1] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> R))
  rw [default_append_zero] at h6
  have h123456 := stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))
  have hR_eq : (([1] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> R)) = right_tape 1 (a + t) := by
    unfold R right_tape
    rw [Nat.add_comm a t, pow_add_append_right]
    rfl
  rw [hR_eq] at h123456
  exact h123456

lemma Return_spec {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    {x a y b c : Nat} (hret : Return x a y b c) {l : ListBlank (Fin 2)} (hn : Num x l) :
    ∃ l', Num y l' ∧
      (l <{{g}} ((([1, 0] : List (Fin 2)) ^ a) +> default)) [tm]⊢* (l' {{q}}> right_tape b c) := by
  cases hret with
  | odd t a hxy =>
    obtain ⟨l', hl', hstep⟩ := return_odd rules t hxy hn
    exact ⟨l', hl', hstep a⟩
  | power t a =>
    exact ⟨default <+ ([1] : List (Fin 2)), Num.one Num.nil, return_power rules t a hn⟩

lemma Round_spec {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    {x a b y a' b' : Nat} (hrnd : Round x a b y a' b') (ha : 0 < a)
    {l : ListBlank (Fin 2)} (hn : Num x l) :
    ∃ l', Num y l' ∧
      (l {{q}}> right_tape a b) [tm]⊢⁺ (l' {{q}}> right_tape a' b') := by
  obtain ⟨u, hsteps, hret⟩ := hrnd
  obtain ⟨s, hs, hov⟩ := overflow_spec rules hsteps hn
  obtain ⟨l', hl', hret_step⟩ := Return_spec rules hret hs
  refine ⟨l', hl', ?_⟩
  have hov_b := hov b
  have h1 : 1 + (a - 1) = a := by omega
  have h2 : 2 + (a - 1) + b = a + b + 1 := by omega
  rw [h1, h2] at hov_b
  exact stepPlus_stepStar_stepPlus hov_b hret_step

theorem nonhalt_from {tm : Machine (Fin 2) (Fin 6)} {q h g : Fin 6} (rules : Rules tm q h g)
    {x a b : Nat} {l : ListBlank (Fin 2)}
    (hinit : (init []) [tm]⊢* (l {{q}}> right_tape a b))
    (hsafe : Safe x a b) (hnum : Num x l) :
    IsDoesNotHalt tm := by
  have hreach : ∀ k : Nat, ∃ l' x' a' b', Num x' l' ∧ Safe x' a' b' ∧
      ∃ m ≥ k, multiStep tm (init []) m = some (l' {{q}}> right_tape a' b') := by
    intro k
    induction k with
    | zero =>
      obtain ⟨m, hm⟩ := hinit
      exact ⟨l, x, a, b, hnum, hsafe, m, Nat.zero_le m, hm⟩
    | succ k ih =>
      obtain ⟨l0, x0, a0, b0, hn0, hs0, m, hge, hm⟩ := ih
      obtain ⟨y, a', b', hrnd, hs'⟩ := closed hs0
      obtain ⟨l', hn', ⟨d, hd_pos, hd⟩⟩ := Round_spec rules hrnd (safe_positive hs0) hn0
      refine ⟨l', y, a', b', hn', hs', m + d, by omega, ?_⟩
      exact multiStep_trans tm (init []) (l0 {{q}}> right_tape a0 b0) (l' {{q}}> right_tape a' b') m d hm hd
  intro cfg ⟨n, hn⟩
  rw [Option.isSome_iff_ne_none]
  intro hnone
  obtain ⟨l', x', a', b', _, _, m, hge, hm⟩ := hreach (n + 1)
  have hm_eq : m = n + (1 + (m - n - 1)) := by omega
  rw [hm_eq, multiStep_add tm (init []) n (1 + (m - n - 1)), hn] at hm
  simp only [Option.bind] at hm
  rw [multiStep_add tm cfg 1 (m - n - 1), multiStep_one, hnone] at hm
  simp only [Option.bind] at hm
  cases hm

end PairCounter

-- ============================================================================
-- Section 8: Specific Rules & Initial Stem for Holdout #249 (`TM12`)
-- `1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LF`
-- ============================================================================

lemma shift_F_left (j : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ j)) <{{F}} r) [target_tm]⊢*
    (l <{{F}} ((([1] : List (Fin 2)) ^ j) +> r)) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([1] : List (Fin 2)) ^ j)) <+ ([1] : List (Fin 2))) <{{F}} r) [target_tm]⊢*
        ((l <+ (([1] : List (Fin 2)) ^ j)) <{{F}} (([1] : List (Fin 2)) +> r)) := by execute
    have h2 := ih l (([1] : List (Fin 2)) +> r)
    have hrew : ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r)) =
        ((([1] : List (Fin 2)) ^ (j + 1)) +> r) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma rule_left_carry (l r : ListBlank (Fin 2)) (j : Nat) :
    (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ (1 + j))) <{{A}} r) [target_tm]⊢*
    (l <{{A}} ((([1] : List (Fin 2)) ^ (2 + j)) +> r)) := by
  have hj : 1 + j = j + 1 := by omega
  rw [hj, pow_succ_list, ← listblank_append_append]
  have h1 : ((((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <+ ([1] : List (Fin 2))) <{{A}} r) [target_tm]⊢*
      (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <{{F}} (([1] : List (Fin 2)) +> r)) := by execute
  have h2 := shift_F_left j (l <+ ([0] : List (Fin 2))) (([1] : List (Fin 2)) +> r)
  have h3 : ((l <+ ([0] : List (Fin 2))) <{{F}} ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r))) [target_tm]⊢*
      (l <{{A}} (([1] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r)))) := by execute
  have hrew1 : ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r)) =
      ((([1] : List (Fin 2)) ^ (j + 1)) +> r) := by
    rw [listblank_append_append, list_pow_append_one]
  have hrew2 : (([1] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ (j + 1)) +> r)) =
      ((([1] : List (Fin 2)) ^ (2 + j)) +> r) := by
    have : 2 + j = (j + 1) + 1 := by omega
    rw [← pow_succ_append_right, this]
  rw [hrew1] at h2 h3
  rw [hrew2] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

lemma rule_scan_right (l r : ListBlank (Fin 2)) (j : Nat) :
    (l {{B}}> ((([1] : List (Fin 2)) ^ j) +> r)) [target_tm]⊢*
    ((l <+ (([0] : List (Fin 2)) ^ j)) {{B}}> r) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{B}}> (([1] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ j) +> r))) [target_tm]⊢*
        ((l <+ ([0] : List (Fin 2))) {{B}}> ((([1] : List (Fin 2)) ^ j) +> r)) := by execute
    have h2 := ih (l <+ ([0] : List (Fin 2))) r
    have hrew : ((l <+ ([0] : List (Fin 2))) <+ (([0] : List (Fin 2)) ^ j)) =
        (l <+ (([0] : List (Fin 2)) ^ (j + 1))) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma rule_scan_overflow (l r : ListBlank (Fin 2)) (j : Nat) :
    ((l <+ (([0, 0] : List (Fin 2)) ^ j)) <{{C}} r) [target_tm]⊢*
    (l <{{C}} ((([1, 0] : List (Fin 2)) ^ j) +> r)) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([0, 0] : List (Fin 2)) ^ j)) <+ ([0, 0] : List (Fin 2))) <{{C}} r) [target_tm]⊢*
        ((l <+ (([0, 0] : List (Fin 2)) ^ j)) <{{C}} (([1, 0] : List (Fin 2)) +> r)) := by execute
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    have hrew : ((([1, 0] : List (Fin 2)) ^ j) +> (([1, 0] : List (Fin 2)) +> r)) =
        ((([1, 0] : List (Fin 2)) ^ (j + 1)) +> r) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma shift_inc_right (j : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 0] : List (Fin 2))) {{C}}> ((([1, 0] : List (Fin 2)) ^ j) +> r)) [target_tm]⊢*
    (((l <+ (([1, 0] : List (Fin 2)) ^ j)) <+ ([0, 0] : List (Fin 2))) {{C}}> r) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rw [pow_succ_append_right]
    have h1 : ((l <+ ([0, 0] : List (Fin 2))) {{C}}> (([1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ j) +> r))) [target_tm]⊢*
        (((l <+ ([1, 0] : List (Fin 2))) <+ ([0, 0] : List (Fin 2))) {{C}}> ((([1, 0] : List (Fin 2)) ^ j) +> r)) := by execute
    have h2 := ih (l <+ ([1, 0] : List (Fin 2))) r
    have hrew : ((l <+ ([1, 0] : List (Fin 2))) <+ (([1, 0] : List (Fin 2)) ^ j)) =
        (l <+ (([1, 0] : List (Fin 2)) ^ (j + 1))) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma shift_inc_left (j : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1, 0] : List (Fin 2)) ^ j)) <{{A}} r) [target_tm]⊢*
    (l <{{A}} ((([1, 1] : List (Fin 2)) ^ j) +> r)) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rw [pow_succ_list, ← listblank_append_append]
    have h1 : (((l <+ (([1, 0] : List (Fin 2)) ^ j)) <+ ([1, 0] : List (Fin 2))) <{{A}} r) [target_tm]⊢*
        ((l <+ (([1, 0] : List (Fin 2)) ^ j)) <{{A}} (([1, 1] : List (Fin 2)) +> r)) := by execute
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    have hrew : ((([1, 1] : List (Fin 2)) ^ j) +> (([1, 1] : List (Fin 2)) +> r)) =
        ((([1, 1] : List (Fin 2)) ^ (j + 1)) +> r) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma scan_right_pair (j : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ((([1, 1] : List (Fin 2)) ^ j) +> r)) [target_tm]⊢*
    ((l <+ (([0, 0] : List (Fin 2)) ^ j)) {{B}}> r) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rw [pow_succ_append_right]
    have h1 : (l {{B}}> (([1, 1] : List (Fin 2)) +> ((([1, 1] : List (Fin 2)) ^ j) +> r))) [target_tm]⊢*
        ((l <+ ([0, 0] : List (Fin 2))) {{B}}> ((([1, 1] : List (Fin 2)) ^ j) +> r)) := by execute
    have h2 := ih (l <+ ([0, 0] : List (Fin 2))) r
    have hrew : ((l <+ ([0, 0] : List (Fin 2))) <+ (([0, 0] : List (Fin 2)) ^ j)) =
        (l <+ (([0, 0] : List (Fin 2)) ^ (j + 1))) := by
      rw [listblank_append_append, list_pow_append_one]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma rule_right_inc (l r : ListBlank (Fin 2)) (n : Nat) :
    (l {{B}}> (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (2 + n)) +> (([0] : List (Fin 2)) +> r)))) [target_tm]⊢*
    (l <{{A}} (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (1 + n)) +> (([0, 1, 0] : List (Fin 2)) +> r)))) := by
  have h2n : 2 + n = (n + 1) + 1 := by omega
  rw [h2n, pow_succ_append_right]
  have h1 : (l {{B}}> (([1] : List (Fin 2)) +> (([1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ (n + 1)) +> (([0] : List (Fin 2)) +> r))))) [target_tm]⊢*
      (((l <+ ([0] : List (Fin 2))) <+ ([0, 0] : List (Fin 2))) {{C}}> ((([1, 0] : List (Fin 2)) ^ (n + 1)) +> (([0] : List (Fin 2)) +> r))) := by execute
  have h2 := shift_inc_right (n + 1) (l <+ ([0] : List (Fin 2))) (([0] : List (Fin 2)) +> r)
  rw [pow_succ_list, ← listblank_append_append] at h2
  have h3 : (((((l <+ ([0] : List (Fin 2))) <+ (([1, 0] : List (Fin 2)) ^ n)) <+ ([1, 0] : List (Fin 2))) <+ ([0, 0] : List (Fin 2))) {{C}}> (([0] : List (Fin 2)) +> r)) [target_tm]⊢*
      (((l <+ ([0] : List (Fin 2))) <+ (([1, 0] : List (Fin 2)) ^ n)) <{{A}} (([0, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by execute
  have h4 := shift_inc_left n (l <+ ([0] : List (Fin 2))) (([0, 0, 0, 1, 0] : List (Fin 2)) +> r)
  have h5 : ((l <+ ([0] : List (Fin 2))) <{{A}} ((([1, 1] : List (Fin 2)) ^ n) +> (([0, 0, 0, 1, 0] : List (Fin 2)) +> r))) [target_tm]⊢*
      ((l <+ ([1] : List (Fin 2))) {{B}}> ((([1, 1] : List (Fin 2)) ^ n) +> (([0, 0, 0, 1, 0] : List (Fin 2)) +> r))) := by execute
  have h6 := scan_right_pair n (l <+ ([1] : List (Fin 2))) (([0, 0, 0, 1, 0] : List (Fin 2)) +> r)
  have h7 : (((l <+ ([1] : List (Fin 2))) <+ (([0, 0] : List (Fin 2)) ^ n)) {{B}}> (([0, 0, 0, 1, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
      (((l <+ ([1] : List (Fin 2))) <+ (([0, 0] : List (Fin 2)) ^ n)) <{{C}} (([1, 0, 0, 1, 0] : List (Fin 2)) +> r)) := by execute
  have h8 := rule_scan_overflow (l <+ ([1] : List (Fin 2))) (([1, 0, 0, 1, 0] : List (Fin 2)) +> r) n
  have h9 : ((l <+ ([1] : List (Fin 2))) <{{C}} ((([1, 0] : List (Fin 2)) ^ n) +> (([1, 0, 0, 1, 0] : List (Fin 2)) +> r))) [target_tm]⊢*
      (l <{{A}} (([1] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ n) +> (([1, 0, 0, 1, 0] : List (Fin 2)) +> r)))) := by execute
  have hrew : ((([1, 0] : List (Fin 2)) ^ n) +> (([1, 0, 0, 1, 0] : List (Fin 2)) +> r)) =
      ((([1, 0] : List (Fin 2)) ^ (1 + n)) +> (([0, 1, 0] : List (Fin 2)) +> r)) := by
    have h1n : 1 + n = n + 1 := by omega
    have hsplit : (([1, 0, 0, 1, 0] : List (Fin 2)) +> r) = (([1, 0] : List (Fin 2)) +> (([0, 1, 0] : List (Fin 2)) +> r)) := rfl
    rw [hsplit, listblank_append_append, list_pow_append_one, h1n]
  rw [hrew] at h8 h9
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 (stepStar_trans h7 (stepStar_trans h8 h9)))))))

lemma tm249_rules : PairCounter.Rules target_tm B A C where
  left_zero := fun l r => by execute
  left_carry := rule_left_carry
  scan_right := rule_scan_right
  right_inc := rule_right_inc
  right_overflow := fun l r => by execute
  scan_overflow := rule_scan_overflow
  overflow_one := fun l r => by execute
  overflow_two := fun l r => by execute
  overflow_resume := fun l r => by execute

lemma tm249_init :
    (init []) [target_tm]⊢* ((default <+ ([1] : List (Fin 2))) {{B}}> PairCounter.right_tape 1 0) := by
  unfold PairCounter.right_tape
  execute

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  refine PairCounter.nonhalt_from tm249_rules tm249_init ?_ (PairCounter.Num.one PairCounter.Num.nil)
  exact PairCounter.Safe.main PairCounter.Normal.D ⟨by decide, fun _ => by decide⟩

end BusyBeaver.M_1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LAHHH_1LA1LF
