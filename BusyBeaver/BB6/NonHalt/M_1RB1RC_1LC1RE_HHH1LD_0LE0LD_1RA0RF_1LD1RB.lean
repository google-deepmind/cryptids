/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RC_1LC1RE_---1LD_0LE0LD_1RA0RF_1LD1RB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RC_1LC1RE_---1LD_0LE0LD_1RA0RF_1LD1RB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RC_1LC1RE_HHH1LD_0LE0LD_1RA0RF_1LD1RB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RC_1LC1RE_---1LD_0LE0LD_1RA0RF_1LD1RB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 1, Stmt.write 1 Dir.right)

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
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
-- ============================================================================
-- Section 2: Turing Machine Infrastructure & Notations
-- ============================================================================


/- A Turing machine statement writing a symbol and moving in direction `dir`. -/
-- ============================================================================
-- Section 5: Specific Turing Machine: holdout_0779
-- ============================================================================
/- Transition function for holdout_0779: `1RB1RC_1LC1RE_---1LD_0LE0LD_1RA0RF_1LD1RB` -/

-- ============================================================================
-- Section 6: Step & Execution Infrastructure
-- ============================================================================

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000

open Counter

local infixr:60 " ⋙ " => stepPlus_trans

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

@[simp] lemma append_nil_lb (s : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> s = s := rfl
@[simp] lemma cons_append_lb (a : Fin 2) (l : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (a :: l) +> s = a >> (l +> s) := rfl

lemma append_assoc_lb (l₁ l₂ : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp [ih]

@[simp] lemma pow_zero_list (w : List (Fin 2)) : w ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (w : List (Fin 2)) (n : Nat) : w ^ (n + 1) = w ++ w ^ n := rfl

lemma pow_add_list (w : List (Fin 2)) (m n : Nat) :
    w ^ (m + n) = w ^ m ++ w ^ n := by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih =>
    have h1 : m + 1 + n = (m + n) + 1 := by omega
    rw [h1, pow_succ_list, pow_succ_list, ih, List.append_assoc]

lemma pow_succ_right_lb (w : List (Fin 2)) (a : Nat) (r : ListBlank (Fin 2)) :
    (w ^ a) +> (w +> r) = (w ^ (a + 1)) +> r := by
  have h1 : w +> r = (w ^ 1) +> r := by simp [pow_succ_list]
  rw [h1, ← append_assoc_lb, ← pow_add_list, Nat.add_comm a 1]

-- ============================================================================
-- Section 7: Pair7Ternary (SOCMisc.v lines 6690-6777)
-- ============================================================================

abbrev e0 : List (Fin 2) := [0, 0, 0]
abbrev e1 : List (Fin 2) := [1, 1, 0]
abbrev e2 : List (Fin 2) := [0, 1, 0]
abbrev w111 : List (Fin 2) := [1, 1, 1]
abbrev w011 : List (Fin 2) := [0, 1, 1]

inductive TC (tail : ListBlank (Fin 2)) : Nat → Nat → ListBlank (Fin 2) → Prop
  | nil : TC tail 0 0 tail
  | d0 (h v : Nat) (r : ListBlank (Fin 2)) : TC tail h v r → TC tail (h + 1) (v * 3) (e0 +> r)
  | d1 (h v : Nat) (r : ListBlank (Fin 2)) : TC tail h v r → TC tail (h + 1) (1 + v * 3) (e1 +> r)
  | d2 (h v : Nat) (r : ListBlank (Fin 2)) : TC tail h v r → TC tail (h + 1) (2 + v * 3) (e2 +> r)

lemma TC_bound {tail : ListBlank (Fin 2)} {h v : Nat} {r : ListBlank (Fin 2)}
    (H : TC tail h v r) : v < 3 ^ h := by
  induction H with
  | nil => decide
  | d0 h v r _ ih => rw [Nat.pow_succ]; omega
  | d1 h v r _ ih => rw [Nat.pow_succ]; omega
  | d2 h v r _ ih => rw [Nat.pow_succ]; omega

lemma TC_unique_aux {tail : ListBlank (Fin 2)} {h h' v v' : Nat} {r s : ListBlank (Fin 2)}
    (H1 : TC tail h v r) (H2 : TC tail h' v' s) (hh : h = h') (hv : v = v') : r = s := by
  induction H1 generalizing h' v' s with
  | nil => cases H2 <;> first | rfl | omega
  | d0 h v r _ ih =>
    cases H2 with
    | d0 h' v' s h2 => exact congrArg (e0 +> ·) (ih h2 (by omega) (by omega))
    | _ => omega
  | d1 h v r _ ih =>
    cases H2 with
    | d1 h' v' s h2 => exact congrArg (e1 +> ·) (ih h2 (by omega) (by omega))
    | _ => omega
  | d2 h v r _ ih =>
    cases H2 with
    | d2 h' v' s h2 => exact congrArg (e2 +> ·) (ih h2 (by omega) (by omega))
    | _ => omega

lemma TC_unique {tail : ListBlank (Fin 2)} {h v : Nat} {r s : ListBlank (Fin 2)}
    (H1 : TC tail h v r) (H2 : TC tail h v s) : r = s :=
  TC_unique_aux H1 H2 rfl rfl

lemma TC_zero (tail : ListBlank (Fin 2)) (h : Nat) : TC tail h 0 ((e0 ^ h) +> tail) := by
  induction h with
  | zero => exact TC.nil
  | succ h ih =>
    rw [pow_succ_list, append_assoc_lb]
    exact TC.d0 h 0 ((e0 ^ h) +> tail) ih

lemma pow_pos (b i : Nat) (hb : 0 < b) : 0 < b ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih hb

lemma pow_mono (b i j : Nat) (hb : 0 < b) (hij : i ≤ j) : b ^ i ≤ b ^ j :=
  Nat.pow_le_pow_right hb hij

lemma TC_full (tail : ListBlank (Fin 2)) (h : Nat) : TC tail h (3 ^ h - 1) ((e2 ^ h) +> tail) := by
  induction h with
  | zero => exact TC.nil
  | succ h ih =>
    rw [pow_succ_list, append_assoc_lb]
    have hp : 0 < 3 ^ h := pow_pos 3 h (by decide)
    have heq : 3 ^ (h + 1) - 1 = 2 + (3 ^ h - 1) * 3 := by rw [Nat.pow_succ]; omega
    rw [heq]
    exact TC.d2 h (3 ^ h - 1) ((e2 ^ h) +> tail) ih

lemma TC_zero_unique {tail : ListBlank (Fin 2)} {h : Nat} {r : ListBlank (Fin 2)}
    (H : TC tail h 0 r) : r = (e0 ^ h) +> tail :=
  TC_unique H (TC_zero tail h)

lemma TC_full_unique {tail : ListBlank (Fin 2)} {h : Nat} {r : ListBlank (Fin 2)}
    (H : TC tail h (3 ^ h - 1) r) : r = (e2 ^ h) +> tail :=
  TC_unique H (TC_full tail h)

lemma TC_carry {tail : ListBlank (Fin 2)} {h v : Nat} {r : ListBlank (Fin 2)}
    (H : TC tail h v r) (Hb : v + 1 < 3 ^ h) :
    ∃ j b q s, h = j + (b + 1) ∧ TC tail b q s ∧
      ((r = (e2 ^ j) +> (e0 +> s) ∧ TC tail h (v + 1) ((e0 ^ j) +> (e1 +> s))) ∨
       (r = (e2 ^ j) +> (e1 +> s) ∧ TC tail h (v + 1) ((e0 ^ j) +> (e2 +> s)))) := by
  induction H with
  | nil => simp at Hb
  | d0 h v r htc _ =>
    refine ⟨0, h, v, r, by omega, htc, Or.inl ⟨rfl, ?_⟩⟩
    have heq : v * 3 + 1 = 1 + v * 3 := by omega
    rw [heq]; exact TC.d1 h v r htc
  | d1 h v r htc _ =>
    refine ⟨0, h, v, r, by omega, htc, Or.inr ⟨rfl, ?_⟩⟩
    have heq : (1 + v * 3) + 1 = 2 + v * 3 := by omega
    rw [heq]; exact TC.d2 h v r htc
  | d2 h v r htc ih =>
    have hv : v + 1 < 3 ^ h := by rw [Nat.pow_succ] at Hb; omega
    rcases ih hv with ⟨j, b, q, s, hh, hs, ⟨hr, hn⟩ | ⟨hr, hn⟩⟩
    · refine ⟨j + 1, b, q, s, by omega, hs, Or.inl ⟨?_, ?_⟩⟩
      · rw [pow_succ_list, append_assoc_lb, hr]
      · rw [pow_succ_list, append_assoc_lb]
        have heq : (2 + v * 3) + 1 = (v + 1) * 3 := by omega
        rw [heq]; exact TC.d0 h (v + 1) _ hn
    · refine ⟨j + 1, b, q, s, by omega, hs, Or.inr ⟨?_, ?_⟩⟩
      · rw [pow_succ_list, append_assoc_lb, hr]
      · rw [pow_succ_list, append_assoc_lb]
        have heq : (2 + v * 3) + 1 = (v + 1) * 3 := by omega
        rw [heq]; exact TC.d0 h (v + 1) _ hn

lemma TC_positive {tail : ListBlank (Fin 2)} {h v : Nat} {r : ListBlank (Fin 2)}
    (H : TC tail h v r) (Hv : 0 < v) :
    ∃ j b q s, h = j + (b + 1) ∧ TC tail b q s ∧
      ((r = (e0 ^ j) +> (e1 +> s) ∧ v = 3 ^ j * (1 + q * 3)) ∨
       (r = (e0 ^ j) +> (e2 +> s) ∧ v = 3 ^ j * (2 + q * 3))) := by
  induction H with
  | nil => omega
  | d0 h v r htc ih =>
    have hp : 0 < v := by omega
    rcases ih hp with ⟨j, b, q, s, hh, hs, ⟨hr, hv⟩ | ⟨hr, hv⟩⟩
    · refine ⟨j + 1, b, q, s, by omega, hs, Or.inl ⟨?_, ?_⟩⟩
      · rw [pow_succ_list, append_assoc_lb, hr]
      · rw [hv, Nat.pow_succ]; ring
    · refine ⟨j + 1, b, q, s, by omega, hs, Or.inr ⟨?_, ?_⟩⟩
      · rw [pow_succ_list, append_assoc_lb, hr]
      · rw [hv, Nat.pow_succ]; ring
  | d1 h v r htc _ =>
    exact ⟨0, h, v, r, by omega, htc, Or.inl ⟨rfl, by simp⟩⟩
  | d2 h v r htc _ =>
    exact ⟨0, h, v, r, by omega, htc, Or.inr ⟨rfl, by simp⟩⟩

-- ============================================================================
-- Section 8: Pair7Bounds (SOCMisc.v lines 6780-6918)
-- ============================================================================

lemma pow6 (i : Nat) : 6 ^ i = 2 ^ i * 3 ^ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]; ring

lemma deficit_next (A i a d d' : Nat) (ha : a ≤ i)
    (hd : d + 1 ≤ 2 ^ i * A + 2 * 6 ^ i) (hstep : d' ≤ 2 * d + 8 * 6 ^ a + 1) :
    d' + 1 ≤ 2 ^ (1 + i) * A + 2 * 6 ^ (1 + i) := by
  have h6a : 6 ^ a ≤ 6 ^ i := pow_mono 6 a i (by decide) ha
  have h2 : 2 ^ (1 + i) * A = 2 * (2 ^ i * A) := by rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
  have h6 : 6 ^ (1 + i) = 6 * 6 ^ i := by rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
  (try omega)
lemma deficit_guard (C A i k d : Nat)
    (hsum : k + d = C * 2 ^ i) (hd : d + 1 ≤ 2 ^ i * A + 2 * 6 ^ i) (hC : A + 6 * 3 ^ i ≤ C) :
    4 * 6 ^ i < k := by
  have h1 : 2 ^ i * (A + 6 * 3 ^ i) ≤ 2 ^ i * C := Nat.mul_le_mul_left (2 ^ i) hC
  have h2 : 2 ^ i * (A + 6 * 3 ^ i) = 2 ^ i * A + 6 * 6 ^ i := by rw [pow6]; ring
  have h3 : C * 2 ^ i = 2 ^ i * C := Nat.mul_comm C (2 ^ i)
  (try omega)
lemma deficit3_budget (C h i : Nat) (hi : i ≤ h) (hC : 3 * 3 ^ h ≤ C) :
    2 + 6 * 3 ^ i ≤ 4 * C := by
  have h1 := pow_mono 3 i h (by decide) hi
  have h2 := pow_pos 3 i (by decide)
  (try omega)
lemma deficit26_budget (C j t A : Nat) (hC : 3 * 3 ^ (j + 1 + t) ≤ C) (hA : A + 6 ≤ 36 * 3 ^ j) :
    A + 6 * 3 ^ t ≤ 4 * C := by
  cases t with
  | zero =>
    have h1 : 3 * 3 ^ (j + 1 + 0) = 9 * 3 ^ j := by
      rw [Nat.add_zero, Nat.pow_succ]; ring
    simp at *
    (try omega)
  | succ t =>
    have h1 : 3 * 3 ^ (j + 1 + (t + 1)) = 9 * (3 ^ j * 3 ^ (t + 1)) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]; ring
    have h2 : 3 ≤ 3 ^ (t + 1) := by
      have := pow_pos 3 t (by decide)
      rw [Nat.pow_succ]; omega
    have h3 : 1 ≤ 3 ^ j := pow_pos 3 j (by decide)
    have h4 : 3 ^ j * 3 ≤ 3 ^ j * 3 ^ (t + 1) := Nat.mul_le_mul_left (3 ^ j) h2
    have h5 : 1 * 3 ^ (t + 1) ≤ 3 ^ j * 3 ^ (t + 1) := Nat.mul_le_mul_right (3 ^ (t + 1)) h3
    (try omega)
lemma deficit26_budget_scaled (C j t q A : Nat)
    (hq : q ≤ t) (hC : 3 * 3 ^ (j + 1 + t) ≤ C) (hA : A + 6 ≤ 36 * 3 ^ j) :
    2 ^ (j + 1) * A + 6 * 3 ^ q ≤ 2 ^ (j + 1) * (4 * C) := by
  have h1 := deficit26_budget C j t A hC hA
  have h2 := pow_mono 3 q t (by decide) hq
  have h3 : 1 ≤ 2 ^ (j + 1) := pow_pos 2 (j + 1) (by decide)
  have h4 : 1 * (6 * 3 ^ q) ≤ 2 ^ (j + 1) * (6 * 3 ^ t) := Nat.mul_le_mul h3 (by omega)
  have h5 : 2 ^ (j + 1) * (A + 6 * 3 ^ t) ≤ 2 ^ (j + 1) * (4 * C) := Nat.mul_le_mul_left _ h1
  have h6 : 2 ^ (j + 1) * (A + 6 * 3 ^ t) = 2 ^ (j + 1) * A + 2 ^ (j + 1) * (6 * 3 ^ t) := by ring
  (try omega)
lemma zeros_next (i b d : Nat) (h : d + 2 ^ i * b = 12 * 6 ^ i) :
    (2 * d + 8 * 6 ^ (1 + i)) + 2 ^ (1 + i) * b = 12 * 6 ^ (1 + i) := by
  have h2 : 2 ^ (1 + i) * b = 2 * (2 ^ i * b) := by rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
  have h6 : 6 ^ (1 + i) = 6 * 6 ^ i := by rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
  (try omega)
lemma zeros_guard (C h i b k d : Nat)
    (hi : i < h) (hC : 3 * 3 ^ h ≤ C) (hb : 0 < b)
    (hsum : k + d = 4 * C * 2 ^ i) (hd : d + 2 ^ i * b = 12 * 6 ^ i) :
    4 * 6 ^ (1 + i) < k := by
  have h1 : 3 ^ (1 + i) ≤ 3 ^ h := pow_mono 3 (1 + i) h (by decide) (by omega)
  have h2 : 3 ^ (1 + i) = 3 * 3 ^ i := by rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
  have h3 : 2 ^ i * (9 * 3 ^ i) ≤ 2 ^ i * C := Nat.mul_le_mul_left (2 ^ i) (by omega)
  have h4 : 2 ^ i * (9 * 3 ^ i) = 9 * 6 ^ i := by rw [pow6]; ring
  have h5 : 4 * C * 2 ^ i = 4 * (2 ^ i * C) := by ring
  have h6 : 4 * 6 ^ (1 + i) = 24 * 6 ^ i := by rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
  have h7 : 1 ≤ 2 ^ i := pow_pos 2 i (by decide)
  have h8 : 1 * 1 ≤ 2 ^ i * b := Nat.mul_le_mul h7 hb
  (try omega)
lemma zeros_end (C h b k d : Nat)
    (hC : 3 * 3 ^ h ≤ C) (hsum : k + d = 4 * C * 2 ^ h) (hd : d + 2 ^ h * b = 12 * 6 ^ h) :
    2 ^ h * b ≤ k := by
  have h1 : 2 ^ h * (3 * 3 ^ h) ≤ 2 ^ h * C := Nat.mul_le_mul_left (2 ^ h) hC
  have h2 : 2 ^ h * (3 * 3 ^ h) = 3 * 6 ^ h := by rw [pow6]; ring
  have h3 : 4 * C * 2 ^ h = 4 * (2 ^ h * C) := by ring
  (try omega)
lemma pow2_mod3 (n : Nat) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Nat.pow_succ]
    (try omega)
lemma pow2_remainder (n : Nat) : ∃ q, 2 ^ n = 1 + q * 3 ∨ 2 ^ n = 2 + q * 3 := by
  rcases pow2_mod3 n with h | h <;> refine ⟨2 ^ n / 3, ?_⟩ <;> omega

lemma hard0_remainder (n h : Nat) (hlo : 6 * 3 ^ h + 1 ≤ 2 ^ n) (hhi : 2 ^ n + 2 < 9 * 3 ^ h) :
    ∃ q, (2 ^ n + 1 - 6 * 3 ^ h = q * 3 ∧ 1 ≤ q ∧ q < 3 ^ h) ∨
         (2 ^ n + 1 - 6 * 3 ^ h = 2 + q * 3 ∧ 1 + q < 3 ^ h) := by
  rcases pow2_remainder n with ⟨t, ht | ht⟩
  · exact ⟨t - 2 * 3 ^ h, Or.inr ⟨by omega, by omega⟩⟩
  · exact ⟨1 + t - 2 * 3 ^ h, Or.inl ⟨by omega, by omega, by omega⟩⟩

lemma hard2_remainder (n h : Nat) (hlo : 6 * 3 ^ h ≤ 2 ^ n) (hhi : 2 ^ n + 1 < 9 * 3 ^ h) :
    ∃ q, (2 ^ n - 6 * 3 ^ h = 1 + q * 3 ∧ q < 3 ^ h) ∨
         (2 ^ n - 6 * 3 ^ h = 2 + q * 3 ∧ 1 + q < 3 ^ h) := by
  rcases pow2_remainder n with ⟨t, ht | ht⟩
  · exact ⟨t - 2 * 3 ^ h, Or.inl ⟨by omega, by omega⟩⟩
  · exact ⟨t - 2 * 3 ^ h, Or.inr ⟨by omega, by omega⟩⟩

lemma normal_budget (a u : Nat) : 4 * 6 ^ a < 2 ^ a * (1 + u * 2) ↔ 2 * 3 ^ a ≤ u := by
  have h1 : 4 * 6 ^ a = 2 ^ a * (4 * 3 ^ a) := by rw [pow6]; ring
  have h2 : 0 < 2 ^ a := pow_pos 2 a (by decide)
  rw [h1]
  constructor
  · intro h
    have h3 : 4 * 3 ^ a < 1 + u * 2 := (Nat.mul_lt_mul_left h2).mp h
    (try omega)
  · intro h
    refine (Nat.mul_lt_mul_left h2).mpr ?_
    (try omega)
lemma power_exit (m a : Nat) (ha : 1 ≤ a) (hm : 3 ^ a ≤ 2 ^ m) :
    11 ≤ 2 ^ (a + 1) * (2 ^ (m + 1) - 2 * 3 ^ a + 3) - 1 ∧
    2 ^ (a + 1) * (2 ^ (m + 1) - 2 * 3 ^ a + 3) - 1 ≤ 2 ^ (m + a + 2) - 13 := by
  have h2a : 4 ≤ 2 ^ (a + 1) := by
    change 2 ^ 2 ≤ 2 ^ (a + 1)
    exact pow_mono 2 2 (a + 1) (by decide) (by omega)
  have h3a : 3 ≤ 3 ^ a := by
    change 3 ^ 1 ≤ 3 ^ a
    exact pow_mono 3 1 a (by decide) ha
  have hm1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring
  have hma : 2 ^ (m + a + 2) = 2 ^ (a + 1) * (2 * 2 ^ m) := by
    have heq : m + a + 2 = (a + 1) + (m + 1) := by omega
    rw [heq, Nat.pow_add, hm1]
  rw [hm1, hma]
  set X := 2 ^ (a + 1)
  set Y := 2 ^ m
  set Z := 3 ^ a
  have hsub : 3 ≤ 2 * Y - 2 * Z + 3 := by omega
  have hmul1 : 4 * 3 ≤ X * (2 * Y - 2 * Z + 3) := Nat.mul_le_mul h2a hsub
  have hmul2 : X * (2 * Y - 2 * Z + 3) + X * (2 * Z - 3) = X * (2 * Y) := by
    rw [← Nat.left_distrib]
    congr 1; omega
  have hmul3 : 4 * 3 ≤ X * (2 * Z - 3) := Nat.mul_le_mul h2a (by omega)
  (try omega)
-- ============================================================================
-- Section 9: TM7 Base Windows & Left Counter LC (SOCMisc.v lines 6920-7118)
-- ============================================================================

def LBar (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (l <{{E}} ([0] +> r))

def RBar (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (([1] +> l) {{B}}> r)

def QBar (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  RBar l ([1, 1] +> r)

def outer : ListBlank (Fin 2) := [1] +> default

lemma R100 (l r : ListBlank (Fin 2)) :
    (RBar l ([1, 0, 0] +> r)) [target_tm]⊢⁺ (RBar (w111 +> l) r) := by
  unfold RBar w111; simp only [cons_append_lb, append_nil_lb]; execute

lemma R111 (l r : ListBlank (Fin 2)) :
    (RBar l (w111 +> r)) [target_tm]⊢⁺ (RBar (w011 +> l) r) := by
  unfold RBar w111 w011; simp only [cons_append_lb, append_nil_lb]; execute

lemma R110 (l r : ListBlank (Fin 2)) :
    (RBar l (e1 +> r)) [target_tm]⊢⁺ (LBar l (w111 +> r)) := by
  unfold RBar LBar e1 w111; simp only [cons_append_lb, append_nil_lb]; execute

lemma R0 (l r : ListBlank (Fin 2)) :
    (RBar l ([0] +> r)) [target_tm]⊢⁺ (l <{{D}} ([1, 1] +> r)) := by
  unfold RBar; simp only [cons_append_lb, append_nil_lb]; execute

lemma step_L_111 (l r : ListBlank (Fin 2)) :
    (LBar (w111 +> l) r) [target_tm]⊢⁺ (LBar l (w111 +> r)) := by
  unfold LBar w111; simp only [cons_append_lb, append_nil_lb]; execute

lemma sweep_L_111 (a : Nat) (l r : ListBlank (Fin 2)) :
    (LBar ((w111 ^ a) +> l) r) [target_tm]⊢* (LBar l ((w111 ^ a) +> r)) := by
  induction a generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : (LBar ((w111 ^ (a + 1)) +> l) r) = (LBar (w111 +> ((w111 ^ a) +> l)) r) := by
      rw [pow_succ_list, append_assoc_lb]
    rw [h1]
    have h2 := stepPlus_stepStar_stepPlus (step_L_111 ((w111 ^ a) +> l) r) (ih l (w111 +> r))
    rw [pow_succ_right_lb] at h2
    exact stepPlus_stepStar h2

lemma sweep_R111 (a : Nat) (l r : ListBlank (Fin 2)) :
    (RBar l ((w111 ^ a) +> r)) [target_tm]⊢* (RBar ((w011 ^ a) +> l) r) := by
  induction a generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : (RBar l ((w111 ^ (a + 1)) +> r)) = (RBar l (w111 +> ((w111 ^ a) +> r))) := by
      rw [pow_succ_list, append_assoc_lb]
    rw [h1]
    have h2 := stepPlus_stepStar_stepPlus (R111 l ((w111 ^ a) +> r)) (ih (w011 +> l) r)
    rw [pow_succ_right_lb] at h2
    exact stepPlus_stepStar h2

lemma LInc_base (l r : ListBlank (Fin 2)) :
    (LBar (w011 +> l) r) [target_tm]⊢⁺ (RBar (w111 +> l) r) := by
  unfold LBar RBar w011 w111; simp only [cons_append_lb, append_nil_lb]; execute

lemma LInc (l r : ListBlank (Fin 2)) (a : Nat) :
    (LBar ((w111 ^ a) +> (w011 +> l)) r) [target_tm]⊢⁺
      (RBar ((w011 ^ a) +> (w111 +> l)) r) :=
  stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus (sweep_L_111 a (w011 +> l) r) (LInc_base l ((w111 ^ a) +> r)))
    (sweep_R111 a (w111 +> l) r)

lemma LBlank1_base (r : ListBlank (Fin 2)) :
    (LBar outer r) [target_tm]⊢⁺ (RBar outer ([1] +> r)) := by
  unfold LBar RBar outer; simp only [cons_append_lb, append_nil_lb]; execute

lemma LBlank1 (r : ListBlank (Fin 2)) (n : Nat) :
    (LBar ((w111 ^ n) +> outer) r) [target_tm]⊢⁺
      (RBar ((w011 ^ n) +> outer) ([1] +> r)) := by
  have h2 : ([1] +> ((w111 ^ n) +> r)) = ((w111 ^ n) +> ([1] +> r)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have lhs : ([1] +> ((w111 ^ (n + 1)) +> r)) = (w111 +> ([1] +> ((w111 ^ n) +> r))) := by
        rw [pow_succ_list, append_assoc_lb]; rfl
      have rhs : ((w111 ^ (n + 1)) +> ([1] +> r)) = (w111 +> ((w111 ^ n) +> ([1] +> r))) := by
        rw [pow_succ_list, append_assoc_lb]
      rw [lhs, rhs, ih]
  have h1 := stepStar_stepPlus_stepPlus (sweep_L_111 n outer r) (LBlank1_base ((w111 ^ n) +> r))
  rw [h2] at h1
  exact stepPlus_stepStar_stepPlus h1 (sweep_R111 n outer ([1] +> r))

inductive LC (o : ListBlank (Fin 2)) : Nat → Nat → ListBlank (Fin 2) → Prop
  | nil : LC o 0 0 o
  | d0 (n k : Nat) (l : ListBlank (Fin 2)) : LC o n k l → LC o (1 + n) (k * 2) (w111 +> l)
  | d1 (n k : Nat) (l : ListBlank (Fin 2)) : LC o n k l → LC o (1 + n) (1 + k * 2) (w011 +> l)

lemma LC_bound {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)}
    (H : LC o n k l) : k < 2 ^ n := by
  induction H with
  | nil => decide
  | d0 n k l _ ih => rw [Nat.add_comm 1 n, Nat.pow_succ]; omega
  | d1 n k l _ ih => rw [Nat.add_comm 1 n, Nat.pow_succ]; omega

lemma LC_unique_aux {o : ListBlank (Fin 2)} {n n' k k' : Nat} {l l' : ListBlank (Fin 2)}
    (H1 : LC o n k l) (H2 : LC o n' k' l') (hn : n = n') (hk : k = k') : l = l' := by
  induction H1 generalizing n' k' l' with
  | nil => cases H2 <;> first | rfl | omega
  | d0 n k l _ ih =>
    cases H2 with
    | d0 n' k' l' h2 => exact congrArg (w111 +> ·) (ih h2 (by omega) (by omega))
    | _ => omega
  | d1 n k l _ ih =>
    cases H2 with
    | d1 n' k' l' h2 => exact congrArg (w011 +> ·) (ih h2 (by omega) (by omega))
    | _ => omega

lemma LC_unique {o : ListBlank (Fin 2)} {n k : Nat} {l l' : ListBlank (Fin 2)}
    (H1 : LC o n k l) (H2 : LC o n k l') : l = l' :=
  LC_unique_aux H1 H2 rfl rfl

lemma LC_zeros {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a : Nat)
    (H : LC o n k l) : LC o (n + a) (k * 2 ^ a) ((w111 ^ a) +> l) := by
  induction a with
  | zero => simpa using H
  | succ a ih =>
    rw [pow_succ_list, append_assoc_lb]
    have h1 := LC.d0 (n + a) (k * 2 ^ a) ((w111 ^ a) +> l) ih
    have hn : 1 + (n + a) = n + (a + 1) := by omega
    have hk : k * 2 ^ a * 2 = k * 2 ^ (a + 1) := by rw [Nat.pow_succ]; ring
    rw [hn, hk] at h1
    exact h1

lemma LC_ones {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a : Nat)
    (H : LC o n k l) : LC o (n + a) ((1 + k) * 2 ^ a - 1) ((w011 ^ a) +> l) := by
  induction a with
  | zero =>
    have hk : (1 + k) * 2 ^ 0 - 1 = k := by omega
    rw [hk]; exact H
  | succ a ih =>
    rw [pow_succ_list, append_assoc_lb]
    have h1 := LC.d1 (n + a) ((1 + k) * 2 ^ a - 1) ((w011 ^ a) +> l) ih
    have hp : 1 ≤ 2 ^ a := pow_pos 2 a (by decide)
    have hp2 : 1 ≤ (1 + k) * 2 ^ a := Nat.le_trans hp (Nat.le_mul_of_pos_left _ (by omega))
    have hn : 1 + (n + a) = n + (a + 1) := by omega
    have hk : 1 + ((1 + k) * 2 ^ a - 1) * 2 = (1 + k) * 2 ^ (a + 1) - 1 := by
      rw [Nat.pow_succ]
      have : (1 + k) * (2 ^ a * 2) = ((1 + k) * 2 ^ a) * 2 := by ring
      (try omega)
    rw [hn, hk] at h1
    exact h1

lemma LC_zero (o : ListBlank (Fin 2)) (n : Nat) : LC o n 0 ((w111 ^ n) +> o) := by
  have h := LC_zeros n (LC.nil (o := o))
  simpa using h

lemma LC_full (o : ListBlank (Fin 2)) (n : Nat) : LC o n (2 ^ n - 1) ((w011 ^ n) +> o) := by
  have h := LC_ones n (LC.nil (o := o))
  simpa using h

lemma LC_zero_unique {o : ListBlank (Fin 2)} {n : Nat} {l : ListBlank (Fin 2)}
    (H : LC o n 0 l) : l = (w111 ^ n) +> o :=
  LC_unique H (LC_zero o n)

lemma LC_positive_split {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)}
    (H : LC o n k l) (Hk : 0 < k) :
    ∃ a m u hi, n = m + 1 + a ∧ k = 2 ^ a * (1 + u * 2) ∧
      LC o m u hi ∧ l = (w111 ^ a) +> (w011 +> hi) := by
  induction H with
  | nil => omega
  | d0 n k l hlc ih =>
    rcases ih (by omega) with ⟨a, m, u, hi, hn, hk, hc, hl⟩
    refine ⟨1 + a, m, u, hi, by omega, ?_, hc, ?_⟩
    · rw [hk, Nat.add_comm 1 a, Nat.pow_succ]; ring
    · rw [hl, Nat.add_comm 1 a, pow_succ_list, append_assoc_lb]
  | d1 n k l hlc _ =>
    exact ⟨0, n, k, l, by omega, by simp, hlc, rfl⟩

lemma LC_borrow {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)}
    (H : LC o n (1 + k) l) :
    ∃ l', LC o n k l' ∧ ∀ r, (LBar l r) [target_tm]⊢⁺ (RBar l' r) := by
  rcases LC_positive_split H (by omega) with ⟨a, m, u, hi, hn, hk, hc, hl⟩
  refine ⟨(w011 ^ a) +> (w111 +> hi), ?_, ?_⟩
  · have h1 := LC_ones a (LC.d0 m u hi hc)
    have hn' : (1 + m) + a = n := by omega
    have hp : 1 ≤ 2 ^ a := pow_pos 2 a (by decide)
    have hk' : (1 + u * 2) * 2 ^ a - 1 = k := by
      have : (1 + u * 2) * 2 ^ a = 2 ^ a * (1 + u * 2) := Nat.mul_comm _ _
      (try omega)
    rw [hn', hk'] at h1
    exact h1
  · intro r
    rw [hl]
    exact LInc hi r a

lemma LC_R100 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o n k l) :
    ∃ l', LC o (1 + n) (k * 2) l' ∧ (RBar l ([1, 0, 0] +> r)) [target_tm]⊢⁺ (RBar l' r) :=
  ⟨w111 +> l, LC.d0 n k l H, R100 l r⟩

lemma LC_R111 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o n k l) :
    ∃ l', LC o (1 + n) (1 + k * 2) l' ∧ (RBar l (w111 +> r)) [target_tm]⊢⁺ (RBar l' r) :=
  ⟨w011 +> l, LC.d1 n k l H, R111 l r⟩

lemma LC_R110 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o n k l) (Hk : 0 < k) :
    ∃ l', LC o (1 + n) (k * 2 - 1) l' ∧ (RBar l (e1 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  have hc : LC o n (1 + (k - 1)) l := by
    have heq : 1 + (k - 1) = k := by omega
    rw [heq]; exact H
  rcases LC_borrow hc with ⟨l', h', hb⟩
  refine ⟨w011 +> l', ?_, ?_⟩
  · have h1 := LC.d1 n (k - 1) l' h'
    have heq : 1 + (k - 1) * 2 = k * 2 - 1 := by omega
    rw [heq] at h1
    exact h1
  · exact (R110 l r) ⋙ (hb (w111 +> r)) ⋙ (R111 l' r)

lemma LC_Lzero {n : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC outer n 0 l) :
    ∃ l', LC outer n (2 ^ n - 1) l' ∧ (LBar l r) [target_tm]⊢⁺ (RBar l' ([1] +> r)) := by
  rw [LC_zero_unique H]
  exact ⟨(w011 ^ n) +> outer, LC_full outer n, LBlank1 r n⟩

lemma step_D_111 (l r : ListBlank (Fin 2)) :
    ((w111 +> l) <{{D}} r) [target_tm]⊢⁺ (l <{{D}} (e0 +> r)) := by
  unfold w111 e0; simp only [cons_append_lb, append_nil_lb]; execute

lemma sweep_D_111 (a : Nat) (l r : ListBlank (Fin 2)) :
    (((w111 ^ a) +> l) <{{D}} r) [target_tm]⊢* (l <{{D}} ((e0 ^ a) +> r)) := by
  induction a generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : (((w111 ^ (a + 1)) +> l) <{{D}} r) = ((w111 +> ((w111 ^ a) +> l)) <{{D}} r) := by
      rw [pow_succ_list, append_assoc_lb]
    rw [h1]
    have h2 := stepPlus_stepStar_stepPlus (step_D_111 ((w111 ^ a) +> l) r) (ih l (e0 +> r))
    rw [pow_succ_right_lb] at h2
    exact stepPlus_stepStar h2

lemma DReturn_base (l r : ListBlank (Fin 2)) :
    ((w011 +> l) <{{D}} r) [target_tm]⊢⁺ (LBar l ([1, 1] +> r)) := by
  unfold LBar w011; simp only [cons_append_lb, append_nil_lb]; execute

lemma DReturn (l r : ListBlank (Fin 2)) (a : Nat) :
    (((w111 ^ a) +> (w011 +> l)) <{{D}} r) [target_tm]⊢⁺
      (LBar l ([1, 1] +> ((e0 ^ a) +> r))) :=
  stepStar_stepPlus_stepPlus (sweep_D_111 a (w011 +> l) r) (DReturn_base l ((e0 ^ a) +> r))

lemma LC_Dpositive {o : ListBlank (Fin 2)} {m u : Nat} {hi : ListBlank (Fin 2)}
    (a : Nat) (r : ListBlank (Fin 2)) (H : LC o m (1 + u) hi) :
    ∃ l', LC o m u l' ∧
      (((w111 ^ a) +> (w011 +> hi)) <{{D}} r) [target_tm]⊢⁺
        (RBar l' ([1, 1] +> ((e0 ^ a) +> r))) := by
  rcases LC_borrow H with ⟨l', hc, hb⟩
  exact ⟨l', hc, (DReturn hi r a) ⋙ (hb ([1, 1] +> ((e0 ^ a) +> r)))⟩

lemma LC_Dpower {m : Nat} {hi : ListBlank (Fin 2)} (a : Nat) (r : ListBlank (Fin 2))
    (H : LC outer m 0 hi) :
    ∃ l', LC outer m (2 ^ m - 1) l' ∧
      (((w111 ^ a) +> (w011 +> hi)) <{{D}} r) [target_tm]⊢⁺
        (RBar l' (w111 +> ((e0 ^ a) +> r))) := by
  rw [LC_zero_unique H]
  refine ⟨(w011 ^ m) +> outer, LC_full outer m, ?_⟩
  have h1 := DReturn ((w111 ^ m) +> outer) r a
  have h2 := LBlank1 ([1, 1] +> ((e0 ^ a) +> r)) m
  exact h1 ⋙ h2

lemma LC_factor {o : ListBlank (Fin 2)} {m a u : Nat} {l : ListBlank (Fin 2)}
    (H : LC o (m + 1 + a) (2 ^ a * (1 + u * 2)) l) :
    ∃ hi, LC o m u hi ∧ l = (w111 ^ a) +> (w011 +> hi) := by
  induction a generalizing l with
  | zero =>
    have hn : m + 1 + 0 = 1 + m := by omega
    have hk : 2 ^ 0 * (1 + u * 2) = 1 + u * 2 := by simp
    rw [hn, hk] at H
    generalize hm1 : 1 + m = n0 at H
    generalize hk1 : 1 + u * 2 = k0 at H
    cases H with
    | nil => omega
    | d0 => omega
    | d1 n' k' hi hc =>
      have hn' : m = n' := by omega
      have hk' : u = k' := by omega
      subst hn'; subst hk'
      exact ⟨hi, hc, rfl⟩
  | succ a ih =>
    have hn : m + 1 + (a + 1) = 1 + (m + 1 + a) := by omega
    have hk : 2 ^ (a + 1) * (1 + u * 2) = (2 ^ a * (1 + u * 2)) * 2 := by rw [Nat.pow_succ]; ring
    rw [hn, hk] at H
    generalize hm1 : 1 + (m + 1 + a) = n0 at H
    generalize hk1 : (2 ^ a * (1 + u * 2)) * 2 = k0 at H
    cases H with
    | nil => omega
    | d1 => omega
    | d0 n' k' hi hc =>
      have hn' : m + 1 + a = n' := by omega
      have hk' : 2 ^ a * (1 + u * 2) = k' := by omega
      subst hn'; subst hk'
      rcases ih hc with ⟨hi', hc', heq⟩
      refine ⟨hi', hc', ?_⟩
      rw [heq, pow_succ_list, append_assoc_lb]

lemma LC_R0positive {o : ListBlank (Fin 2)} {m a u : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o (m + 1 + a) (2 ^ a * (1 + (1 + u) * 2)) l) :
    ∃ l', LC o m u l' ∧
      (RBar l ([0] +> r)) [target_tm]⊢⁺ (RBar l' ([1, 1] +> ((e0 ^ a) +> ([1, 1] +> r)))) := by
  rcases LC_factor H with ⟨hi, hc, hl⟩
  rcases LC_Dpositive a ([1, 1] +> r) hc with ⟨l', hc', hs⟩
  rw [hl]
  exact ⟨l', hc', (R0 ((w111 ^ a) +> (w011 +> hi)) r) ⋙ hs⟩

lemma LC_R0power {m a : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC outer (m + 1 + a) (2 ^ a) l) :
    ∃ l', LC outer m (2 ^ m - 1) l' ∧
      (RBar l ([0] +> r)) [target_tm]⊢⁺ (RBar l' (w111 +> ((e0 ^ a) +> ([1, 1] +> r)))) := by
  have H0 : LC outer (m + 1 + a) (2 ^ a * (1 + 0 * 2)) l := by simpa using H
  rcases LC_factor H0 with ⟨hi, hc, hl⟩
  rcases LC_Dpower a ([1, 1] +> r) hc with ⟨l', hc', hs⟩
  rw [hl]
  exact ⟨l', hc', (R0 ((w111 ^ a) +> (w011 +> hi)) r) ⋙ hs⟩

-- ============================================================================
-- Section 10: Pair7Counting (SOCMisc.v lines 7120-7277)
-- ============================================================================

lemma QLow (l r : ListBlank (Fin 2)) :
    (QBar l (e0 +> r)) [target_tm]⊢⁺ (LBar l ([1, 1, 1, 0, 0] +> r)) :=
  R110 l ([0, 0] +> r)

lemma QLowBack (l r : ListBlank (Fin 2)) :
    (RBar l ([1, 1, 1, 0, 0] +> r)) [target_tm]⊢⁺ (LBar l ([1, 1, 1, 1, 0] +> r)) := by
  unfold RBar LBar; simp only [cons_append_lb, append_nil_lb]; execute

lemma step_QEnter (l r : ListBlank (Fin 2)) :
    (QBar l (e1 +> r)) [target_tm]⊢⁺ (RBar (w011 +> l) ([1, 0] +> r)) := by
  unfold QBar RBar e1 w011; simp only [cons_append_lb, append_nil_lb]; execute

lemma sweep_R100_e2 (j : Nat) (l r : ListBlank (Fin 2)) :
    (RBar l ([1, 0] +> ((e2 ^ j) +> r))) [target_tm]⊢*
      (RBar ((w111 ^ j) +> l) ([1, 0] +> r)) := by
  induction j generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 : (RBar l ([1, 0] +> ((e2 ^ (j + 1)) +> r))) =
        (RBar l ([1, 0, 0] +> ([1, 0] +> ((e2 ^ j) +> r)))) := by
      rw [pow_succ_list, append_assoc_lb]; rfl
    rw [h1]
    have h2 := stepPlus_stepStar_stepPlus (R100 l ([1, 0] +> ((e2 ^ j) +> r))) (ih (w111 +> l) r)
    rw [pow_succ_right_lb] at h2
    exact stepPlus_stepStar h2

lemma step_QEnd0 (l r : ListBlank (Fin 2)) :
    (RBar l ([1, 0] +> (e0 +> r))) [target_tm]⊢⁺ ((w111 +> l) <{{D}} (e1 +> r)) := by
  unfold RBar e0 w111 e1; simp only [cons_append_lb, append_nil_lb]; execute

lemma step_QEnd1 (l r : ListBlank (Fin 2)) :
    (RBar l ([1, 0] +> (e1 +> r))) [target_tm]⊢⁺ ((w111 +> l) <{{D}} (e2 +> r)) := by
  unfold RBar e1 w111 e2; simp only [cons_append_lb, append_nil_lb]; execute

lemma step_QEndTail (l r : ListBlank (Fin 2)) :
    (RBar l ([1, 0] +> ([1, 1] +> r))) [target_tm]⊢⁺ ((w111 +> l) <{{D}} ([0, 1] +> r)) := by
  unfold RBar w111; simp only [cons_append_lb, append_nil_lb]; execute

lemma QCarry0 (l r : ListBlank (Fin 2)) (j : Nat) :
    (QBar l (e1 +> ((e2 ^ j) +> (e0 +> r)))) [target_tm]⊢⁺
      (LBar l ([1, 1] +> ((e0 ^ (1 + j)) +> (e1 +> r)))) := by
  have h1 := stepPlus_stepStar_stepPlus (step_QEnter l ((e2 ^ j) +> (e0 +> r)))
    (sweep_R100_e2 j (w011 +> l) (e0 +> r))
  have h2 := h1 ⋙ (step_QEnd0 ((w111 ^ j) +> (w011 +> l)) r)
  have h3 : (w111 +> ((w111 ^ j) +> (w011 +> l))) = ((w111 ^ (1 + j)) +> (w011 +> l)) := by
    rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
  rw [h3] at h2
  exact h2 ⋙ (DReturn l (e1 +> r) (1 + j))

lemma QCarry1 (l r : ListBlank (Fin 2)) (j : Nat) :
    (QBar l (e1 +> ((e2 ^ j) +> (e1 +> r)))) [target_tm]⊢⁺
      (LBar l ([1, 1] +> ((e0 ^ (1 + j)) +> (e2 +> r)))) := by
  have h1 := stepPlus_stepStar_stepPlus (step_QEnter l ((e2 ^ j) +> (e1 +> r)))
    (sweep_R100_e2 j (w011 +> l) (e1 +> r))
  have h2 := h1 ⋙ (step_QEnd1 ((w111 ^ j) +> (w011 +> l)) r)
  have h3 : (w111 +> ((w111 ^ j) +> (w011 +> l))) = ((w111 ^ (1 + j)) +> (w011 +> l)) := by
    rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
  rw [h3] at h2
  exact h2 ⋙ (DReturn l (e2 +> r) (1 + j))

lemma QCarryTail (l r : ListBlank (Fin 2)) (j : Nat) :
    (QBar l (e1 +> ((e2 ^ j) +> ([1, 1] +> r)))) [target_tm]⊢⁺
      (LBar l ([1, 1] +> ((e0 ^ (1 + j)) +> ([0, 1] +> r)))) := by
  have h1 := stepPlus_stepStar_stepPlus (step_QEnter l ((e2 ^ j) +> ([1, 1] +> r)))
    (sweep_R100_e2 j (w011 +> l) ([1, 1] +> r))
  have h2 := h1 ⋙ (step_QEndTail ((w111 ^ j) +> (w011 +> l)) r)
  have h3 : (w111 +> ((w111 ^ j) +> (w011 +> l))) = ((w111 ^ (1 + j)) +> (w011 +> l)) := by
    rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
  rw [h3] at h2
  exact h2 ⋙ (DReturn l ([0, 1] +> r) (1 + j))

lemma QExit (l r : ListBlank (Fin 2)) (j : Nat) :
    (QBar l (e1 +> ((e2 ^ j) +> ([0, 1] +> r)))) [target_tm]⊢⁺
      (RBar ((w111 ^ (1 + j)) +> (w011 +> l)) ([1] +> r)) := by
  have h1 := stepPlus_stepStar_stepPlus (step_QEnter l ((e2 ^ j) +> ([0, 1] +> r)))
    (sweep_R100_e2 j (w011 +> l) ([0, 1] +> r))
  have h2 : ([1, 0] +> ([0, 1] +> r)) = ([1, 0, 0] +> ([1] +> r)) := rfl
  rw [h2] at h1
  have h3 := h1 ⋙ (R100 ((w111 ^ j) +> (w011 +> l)) ([1] +> r))
  have h4 : (w111 +> ((w111 ^ j) +> (w011 +> l))) = ((w111 ^ (1 + j)) +> (w011 +> l)) := by
    rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
  rw [h4] at h3
  exact h3

lemma Q0 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o n (2 + k) l) :
    ∃ l', LC o n k l' ∧ (QBar l (e0 +> r)) [target_tm]⊢⁺ (QBar l' (e1 +> r)) := by
  have H0 : LC o n (1 + (1 + k)) l := by
    have : 1 + (1 + k) = 2 + k := by omega
    rw [this]; exact H
  rcases LC_borrow H0 with ⟨l1, h1, s1⟩
  rcases LC_borrow h1 with ⟨l2, h2, s2⟩
  refine ⟨l2, h2, ?_⟩
  exact (QLow l r) ⋙ (s1 ([1, 1, 1, 0, 0] +> r)) ⋙ (QLowBack l1 r) ⋙ (s2 ([1, 1, 1, 1, 0] +> r))

lemma Q1 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (j : Nat)
    (H : LC o n (1 + k) l) :
    ∃ l', LC o n k l' ∧
      (QBar l (e1 +> ((e2 ^ j) +> (e0 +> r)))) [target_tm]⊢⁺
        (QBar l' ((e0 ^ (1 + j)) +> (e1 +> r))) := by
  rcases LC_borrow H with ⟨l', h', hs⟩
  exact ⟨l', h', (QCarry0 l r j) ⋙ (hs ([1, 1] +> ((e0 ^ (1 + j)) +> (e1 +> r))))⟩

lemma Q2 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (j : Nat)
    (H : LC o n (1 + k) l) :
    ∃ l', LC o n k l' ∧
      (QBar l (e1 +> ((e2 ^ j) +> (e1 +> r)))) [target_tm]⊢⁺
        (QBar l' ((e0 ^ (1 + j)) +> (e2 +> r))) := by
  rcases LC_borrow H with ⟨l', h', hs⟩
  exact ⟨l', h', (QCarry1 l r j) ⋙ (hs ([1, 1] +> ((e0 ^ (1 + j)) +> (e2 +> r))))⟩

lemma Q3 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (j : Nat)
    (H : LC o n (1 + k) l) :
    ∃ l', LC o n k l' ∧
      (QBar l (e1 +> ((e2 ^ j) +> ([1, 1] +> r)))) [target_tm]⊢⁺
        (QBar l' ((e0 ^ (1 + j)) +> ([0, 1] +> r))) := by
  rcases LC_borrow H with ⟨l', h', hs⟩
  exact ⟨l', h', (QCarryTail l r j) ⋙ (hs ([1, 1] +> ((e0 ^ (1 + j)) +> ([0, 1] +> r))))⟩

lemma Q4 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (j : Nat)
    (H : LC o n k l) :
    ∃ l', LC o (n + j + 2) ((1 + k * 2) * 2 ^ (1 + j)) l' ∧
      (QBar l (e1 +> ((e2 ^ j) +> ([0, 1] +> r)))) [target_tm]⊢⁺
        (RBar l' ([1] +> r)) := by
  refine ⟨(w111 ^ (1 + j)) +> (w011 +> l), ?_, QExit l r j⟩
  have h1 := LC_zeros (1 + j) (LC.d1 n k l H)
  have hn : (1 + n) + (1 + j) = n + j + 2 := by omega
  rw [hn] at h1
  exact h1

lemma TC_next {o tail : ListBlank (Fin 2)} {n k h v : Nat} {l r : ListBlank (Fin 2)}
    (Hl : LC o n (3 + k) l) (Hr : TC tail h v r) (Hb : v + 1 < 3 ^ h) :
    ∃ l' r', LC o n k l' ∧ TC tail h (v + 1) r' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (QBar l' (e0 +> r')) := by
  rcases TC_carry Hr Hb with ⟨j, b, q, s, hh, hs, ⟨hr, hn⟩ | ⟨hr, hn⟩⟩
  · subst hr
    have Hl' : LC o n (2 + (1 + k)) l := by
      have : 2 + (1 + k) = 3 + k := by omega
      rw [this]; exact Hl
    rcases Q0 ((e2 ^ j) +> (e0 +> s)) Hl' with ⟨l1, h1, s1⟩
    rcases Q1 s j h1 with ⟨l2, h2, s2⟩
    refine ⟨l2, (e0 ^ j) +> (e1 +> s), h2, hn, ?_⟩
    have h_r : ((e0 ^ (1 + j)) +> (e1 +> s)) = (e0 +> ((e0 ^ j) +> (e1 +> s))) := by
      rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
    rw [h_r] at s2
    exact s1 ⋙ s2
  · subst hr
    have Hl' : LC o n (2 + (1 + k)) l := by
      have : 2 + (1 + k) = 3 + k := by omega
      rw [this]; exact Hl
    rcases Q0 ((e2 ^ j) +> (e1 +> s)) Hl' with ⟨l1, h1, s1⟩
    rcases Q2 s j h1 with ⟨l2, h2, s2⟩
    refine ⟨l2, (e0 ^ j) +> (e2 +> s), h2, hn, ?_⟩
    have h_r : ((e0 ^ (1 + j)) +> (e2 +> s)) = (e0 +> ((e0 ^ j) +> (e2 +> s))) := by
      rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
    rw [h_r] at s2
    exact s1 ⋙ s2

lemma TC_steps (count : Nat) {o tail : ListBlank (Fin 2)} {n k h v : Nat} {l r : ListBlank (Fin 2)}
    (Hl : LC o n (3 * count + k) l) (Hr : TC tail h v r) (Hb : v + count < 3 ^ h) :
    ∃ l' r', LC o n k l' ∧ TC tail h (v + count) r' ∧
      (QBar l (e0 +> r)) [target_tm]⊢* (QBar l' (e0 +> r')) := by
  induction count generalizing k l v r with
  | zero =>
    have hk : 3 * 0 + k = k := by omega
    rw [hk] at Hl
    exact ⟨l, r, Hl, Hr, ⟨0, rfl⟩⟩
  | succ count ih =>
    have Hl1 : LC o n (3 + (3 * count + k)) l := by
      have : 3 + (3 * count + k) = 3 * (count + 1) + k := by omega
      rw [this]; exact Hl
    rcases TC_next Hl1 Hr (by omega) with ⟨l1, r1, h1, t1, s1⟩
    rcases ih h1 t1 (by omega) with ⟨l2, r2, h2, t2, s2⟩
    have hv : (v + 1) + count = v + (count + 1) := by omega
    rw [hv] at t2
    exact ⟨l2, r2, h2, t2, stepPlus_stepStar (stepPlus_stepStar_stepPlus s1 s2)⟩

lemma TC_first {o : ListBlank (Fin 2)} {n k h v : Nat} {l r : ListBlank (Fin 2)} (tail : ListBlank (Fin 2))
    (Hl : LC o n (3 * (3 ^ h - v) + k) l) (Hr : TC ([1, 1] +> tail) h v r) :
    ∃ l', LC o n k l' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (QBar l' (e0 +> ((e0 ^ h) +> ([0, 1] +> tail)))) := by
  have hb := TC_bound Hr
  have Hl1 : LC o n (3 * (3 ^ h - 1 - v) + (3 + k)) l := by
    have : 3 * (3 ^ h - 1 - v) + (3 + k) = 3 * (3 ^ h - v) + k := by omega
    rw [this]; exact Hl
  rcases TC_steps (3 ^ h - 1 - v) Hl1 Hr (by omega) with ⟨l1, r1, h1, t1, s1⟩
  have hv : v + (3 ^ h - 1 - v) = 3 ^ h - 1 := by omega
  rw [hv] at t1
  rw [TC_full_unique t1] at s1
  have h1' : LC o n (2 + (1 + k)) l1 := by
    have : 2 + (1 + k) = 3 + k := by omega
    rw [this]; exact h1
  rcases Q0 ((e2 ^ h) +> ([1, 1] +> tail)) h1' with ⟨l2, h2, s2⟩
  rcases Q3 tail h h2 with ⟨l3, h3, s3⟩
  have h_r : ((e0 ^ (1 + h)) +> ([0, 1] +> tail)) = (e0 +> ((e0 ^ h) +> ([0, 1] +> tail))) := by
    rw [Nat.add_comm 1 h, pow_succ_list, append_assoc_lb]
  rw [h_r] at s3
  exact ⟨l3, h3, stepStar_stepPlus_stepPlus s1 (s2 ⋙ s3)⟩

lemma TC_exit {o : ListBlank (Fin 2)} {n k h v : Nat} {l r : ListBlank (Fin 2)} (tail : ListBlank (Fin 2))
    (Hl : LC o n (3 * (3 ^ h - v) - 1 + k) l) (Hr : TC ([0, 1] +> tail) h v r) :
    ∃ l', LC o (n + h + 2) ((1 + k * 2) * 2 ^ (1 + h)) l' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' ([1] +> tail)) := by
  have hb := TC_bound Hr
  have Hl1 : LC o n (3 * (3 ^ h - 1 - v) + (2 + k)) l := by
    have : 3 * (3 ^ h - 1 - v) + (2 + k) = 3 * (3 ^ h - v) - 1 + k := by omega
    rw [this]; exact Hl
  rcases TC_steps (3 ^ h - 1 - v) Hl1 Hr (by omega) with ⟨l1, r1, h1, t1, s1⟩
  have hv : v + (3 ^ h - 1 - v) = 3 ^ h - 1 := by omega
  rw [hv] at t1
  rw [TC_full_unique t1] at s1
  rcases Q0 ((e2 ^ h) +> ([0, 1] +> tail)) h1 with ⟨l2, h2, s2⟩
  rcases Q4 tail h h2 with ⟨l3, h3, s3⟩
  exact ⟨l3, h3, stepStar_stepPlus_stepPlus s1 (s2 ⋙ s3)⟩

lemma Q_return {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (h : Nat) (tail : ListBlank (Fin 2))
    (Hl : LC o n (2 * 3 ^ (1 + h) - 1 + k) l) :
    ∃ l', LC o (n + h + 2) ((1 + k * 2) * 2 ^ (1 + h)) l' ∧
      (QBar l ((e0 ^ (1 + h)) +> ([1, 1] +> tail))) [target_tm]⊢⁺ (RBar l' ([1] +> tail)) := by
  have hp : 0 < 3 ^ h := pow_pos 3 h (by decide)
  have Hl1 : LC o n (3 * (3 ^ h - 0) + (3 * 3 ^ h - 1 + k)) l := by
    have : 3 * (3 ^ h - 0) + (3 * 3 ^ h - 1 + k) = 2 * 3 ^ (1 + h) - 1 + k := by
      rw [Nat.add_comm 1 h, Nat.pow_succ]; omega
    rw [this]; exact Hl
  rcases TC_first tail Hl1 (TC_zero ([1, 1] +> tail) h) with ⟨l1, h1, s1⟩
  have h1' : LC o n (3 * (3 ^ h - 0) - 1 + k) l1 := by simpa using h1
  rcases TC_exit tail h1' (TC_zero ([0, 1] +> tail) h) with ⟨l2, h2, s2⟩
  have h_r : (e0 +> ((e0 ^ h) +> ([1, 1] +> tail))) = ((e0 ^ (1 + h)) +> ([1, 1] +> tail)) := by
    rw [Nat.add_comm 1 h, pow_succ_list, append_assoc_lb]
  rw [h_r] at s1
  exact ⟨l2, h2, s1 ⋙ s2⟩

-- ============================================================================
-- Section 11: Pair7Low, Pair7Normal, Pair7Repair (SOCMisc.v lines 7280-7475)
-- ============================================================================

lemma zero11 {n : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (H : LC outer n 0 l) :
    ∃ l', LC outer (n + 1) (2 ^ (n + 1) - 1) l' ∧
      (LBar l ([1, 1] +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases LC_Lzero ([1, 1] +> r) H with ⟨l1, h1, s1⟩
  rcases LC_R111 r h1 with ⟨l2, h2, s2⟩
  have hn : 1 + n = n + 1 := by omega
  have hp : 1 ≤ 2 ^ n := pow_pos 2 n (by decide)
  have hk : 1 + (2 ^ n - 1) * 2 = 2 ^ (n + 1) - 1 := by rw [Nat.pow_succ]; omega
  rw [hn, hk] at h2
  exact ⟨l2, h2, s1 ⋙ s2⟩

lemma clear0 {n : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (H : LC outer n 0 l) :
    ∃ l', LC outer (n + 2) (2 ^ (n + 2) - 2) l' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases zero11 ([1, 0, 0] +> r) H with ⟨l1, h1, s1⟩
  rcases LC_R100 r h1 with ⟨l2, h2, s2⟩
  have hn : 1 + (n + 1) = n + 2 := by omega
  have hp : 1 ≤ 2 ^ (n + 1) := pow_pos 2 (n + 1) (by decide)
  have hk : (2 ^ (n + 1) - 1) * 2 = 2 ^ (n + 2) - 2 := by
    have : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by rw [Nat.pow_succ]
    (try omega)
  rw [hn, hk] at h2
  exact ⟨l2, h2, (QLow l r) ⋙ s1 ⋙ s2⟩

lemma clear1 {n : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2)) (H : LC outer n 1 l) :
    ∃ l', LC outer (n + 2) (2 ^ (n + 2) - 3) l' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  have H0 : LC outer n (1 + 0) l := H
  rcases LC_borrow H0 with ⟨l1, h1, s1⟩
  rcases zero11 ([1, 1, 0] +> r) h1 with ⟨l2, h2, s2⟩
  have hp : 0 < 2 ^ (n + 1) - 1 := by
    have : 1 ≤ 2 ^ n := pow_pos 2 n (by decide)
    rw [Nat.pow_succ]; omega
  rcases LC_R110 r h2 hp with ⟨l3, h3, s3⟩
  have hn : 1 + (n + 1) = n + 2 := by omega
  have hk : (2 ^ (n + 1) - 1) * 2 - 1 = 2 ^ (n + 2) - 3 := by
    have : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by rw [Nat.pow_succ]
    (try omega)
  rw [hn, hk] at h3
  exact ⟨l3, h3, (QLow l r) ⋙ (s1 ([1, 1, 1, 0, 0] +> r)) ⋙ (QLowBack l1 r) ⋙ s2 ⋙ s3⟩

lemma clear2a {tail : ListBlank (Fin 2)} {n h v : Nat} {l r : ListBlank (Fin 2)}
    (Hl : LC outer n 2 l) (Hr : TC tail h v r) (Hb : v + 1 < 3 ^ h) :
    ∃ l' r', LC outer (n + 1) (2 ^ (n + 1) - 1) l' ∧ TC tail h (v + 1) r' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' (e0 +> r')) := by
  rcases TC_carry Hr Hb with ⟨j, b, q, s, hh, hs, ⟨hr, hn⟩ | ⟨hr, hn⟩⟩
  · subst hr
    have Hl0 : LC outer n (2 + 0) l := Hl
    rcases Q0 ((e2 ^ j) +> (e0 +> s)) Hl0 with ⟨l1, h1, s1⟩
    rcases zero11 ((e0 ^ (1 + j)) +> (e1 +> s)) h1 with ⟨l2, h2, s2⟩
    have s12 := s1 ⋙ (QCarry0 l1 s j) ⋙ s2
    have h_r : (RBar l2 ((e0 ^ (1 + j)) +> (e1 +> s))) = (RBar l2 (e0 +> ((e0 ^ j) +> (e1 +> s)))) := by
      rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
    rw [h_r] at s12
    exact ⟨l2, (e0 ^ j) +> (e1 +> s), h2, hn, s12⟩
  · subst hr
    have Hl0 : LC outer n (2 + 0) l := Hl
    rcases Q0 ((e2 ^ j) +> (e1 +> s)) Hl0 with ⟨l1, h1, s1⟩
    rcases zero11 ((e0 ^ (1 + j)) +> (e2 +> s)) h1 with ⟨l2, h2, s2⟩
    have s12 := s1 ⋙ (QCarry1 l1 s j) ⋙ s2
    have h_r : (RBar l2 ((e0 ^ (1 + j)) +> (e2 +> s))) = (RBar l2 (e0 +> ((e0 ^ j) +> (e2 +> s)))) := by
      rw [Nat.add_comm 1 j, pow_succ_list, append_assoc_lb]
    rw [h_r] at s12
    exact ⟨l2, (e0 ^ j) +> (e2 +> s), h2, hn, s12⟩

lemma clear2_full_low {n h : Nat} {l r : ListBlank (Fin 2)} (tail : ListBlank (Fin 2))
    (Hl : LC outer n 2 l) (Hr : TC ([1, 1] +> tail) h (3 ^ h - 1) r) :
    ∃ l' r', LC outer (n + 1) (2 ^ (n + 1) - 1) l' ∧
      TC ([0, 1] +> tail) h 0 r' ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' (e0 +> r')) := by
  rw [TC_full_unique Hr]
  have Hl0 : LC outer n (2 + 0) l := Hl
  rcases Q0 ((e2 ^ h) +> ([1, 1] +> tail)) Hl0 with ⟨l1, h1, s1⟩
  rcases zero11 ((e0 ^ (1 + h)) +> ([0, 1] +> tail)) h1 with ⟨l2, h2, s2⟩
  have s12 := s1 ⋙ (QCarryTail l1 tail h) ⋙ s2
  have h_r : (RBar l2 ((e0 ^ (1 + h)) +> ([0, 1] +> tail))) = (RBar l2 (e0 +> ((e0 ^ h) +> ([0, 1] +> tail)))) := by
    rw [Nat.add_comm 1 h, pow_succ_list, append_assoc_lb]
  rw [h_r] at s12
  exact ⟨l2, (e0 ^ h) +> ([0, 1] +> tail), h2, TC_zero ([0, 1] +> tail) h, s12⟩

lemma OddPrefix {o : ListBlank (Fin 2)} {m v : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o (1 + m) (3 + v * 2) l) :
    ∃ l', LC o (1 + m) (1 + v * 2) l' ∧
      (RBar l ([0] +> r)) [target_tm]⊢⁺ (RBar l' ([1] +> r)) := by
  have HC : LC o (m + 1 + 0) (2 ^ 0 * (1 + (1 + v) * 2)) l := by
    have hn : m + 1 + 0 = 1 + m := by omega
    have hk : 2 ^ 0 * (1 + (1 + v) * 2) = 3 + v * 2 := by omega
    rw [hn, hk]; exact H
  rcases LC_R0positive r HC with ⟨l1, h1, s1⟩
  rcases LC_R111 ([1] +> r) h1 with ⟨l2, h2, s2⟩
  exact ⟨l2, h2, s1 ⋙ s2⟩

lemma EvenPrefix {o : ListBlank (Fin 2)} {m h v : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o (m + h + 2) (2 ^ (1 + h) * (1 + (2 * 3 ^ (1 + h) + v) * 2)) l) :
    ∃ l', LC o (m + h + 2) (2 ^ (1 + h) * (1 + v * 2)) l' ∧
      (RBar l ([0] +> r)) [target_tm]⊢⁺ (RBar l' ([1] +> r)) := by
  have hp : 1 ≤ 3 ^ (1 + h) := pow_pos 3 (1 + h) (by decide)
  have HC : LC o (m + 1 + (1 + h)) (2 ^ (1 + h) * (1 + (1 + (2 * 3 ^ (1 + h) - 1 + v)) * 2)) l := by
    have hn : m + 1 + (1 + h) = m + h + 2 := by omega
    have hk : 1 + (1 + (2 * 3 ^ (1 + h) - 1 + v)) * 2 = 1 + (2 * 3 ^ (1 + h) + v) * 2 := by omega
    rw [hn, hk]; exact H
  rcases LC_R0positive r HC with ⟨l1, h1, s1⟩
  rcases Q_return h r h1 with ⟨l2, h2, s2⟩
  have hk2 : (1 + v * 2) * 2 ^ (1 + h) = 2 ^ (1 + h) * (1 + v * 2) := Nat.mul_comm _ _
  rw [hk2] at h2
  exact ⟨l2, h2, s1 ⋙ s2⟩

lemma Odd000 {o : ListBlank (Fin 2)} {m v : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o (1 + m) (3 + v * 2) l) :
    ∃ l', LC o (2 + m) (2 + v * 4) l' ∧
      (RBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases OddPrefix ([0, 0] +> r) H with ⟨l1, h1, s1⟩
  rcases LC_R100 r h1 with ⟨l2, h2, s2⟩
  have hn : 1 + (1 + m) = 2 + m := by omega
  have hk : (1 + v * 2) * 2 = 2 + v * 4 := by omega
  rw [hn, hk] at h2
  exact ⟨l2, h2, s1 ⋙ s2⟩

lemma Even000 {o : ListBlank (Fin 2)} {m h v : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (H : LC o (m + h + 2) (2 ^ (1 + h) * (1 + (2 * 3 ^ (1 + h) + v) * 2)) l) :
    ∃ l', LC o (m + h + 3) (2 ^ (2 + h) * (1 + v * 2)) l' ∧
      (RBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases EvenPrefix ([0, 0] +> r) H with ⟨l1, h1, s1⟩
  rcases LC_R100 r h1 with ⟨l2, h2, s2⟩
  have hn : 1 + (m + h + 2) = m + h + 3 := by omega
  have hk : (2 ^ (1 + h) * (1 + v * 2)) * 2 = 2 ^ (2 + h) * (1 + v * 2) := by
    have : 2 + h = (1 + h) + 1 := by omega
    rw [this, Nat.pow_succ]; ring
  rw [hn, hk] at h2
  exact ⟨l2, h2, s1 ⋙ s2⟩

lemma FullRead {n : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hn : 3 ≤ 2 ^ n) (Hl : LC outer (n + 1) (2 ^ (n + 1) - 1) l) :
    ∃ l', LC outer (n + 2) (2 ^ (n + 2) - 6) l' ∧
      (RBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  have HC : LC outer (1 + n) (3 + (2 ^ n - 2) * 2) l := by
    have hn : 1 + n = n + 1 := by omega
    have hk : 3 + (2 ^ n - 2) * 2 = 2 ^ (n + 1) - 1 := by rw [Nat.pow_succ]; omega
    rw [hn, hk]; exact Hl
  rcases Odd000 r HC with ⟨l', h', hs⟩
  have hn' : 2 + n = n + 2 := by omega
  have hk' : 2 + (2 ^ n - 2) * 4 = 2 ^ (n + 2) - 6 := by
    have : 2 ^ (n + 2) = 2 ^ n * 4 := by rw [Nat.pow_add]
    (try omega)
  rw [hn', hk'] at h'
  exact ⟨l', h', hs⟩

lemma clear2 {tail : ListBlank (Fin 2)} {n h v : Nat} {l r : ListBlank (Fin 2)}
    (Hl : LC outer n 2 l) (Hr : TC tail h v r) (Hv : v + 1 < 3 ^ h) :
    ∃ l' r', LC outer (n + 2) (2 ^ (n + 2) - 6) l' ∧
      TC tail h (v + 1) r' ∧ (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r') := by
  have hn := LC_bound Hl
  rcases clear2a Hl Hr Hv with ⟨l1, r1, h1, t1, s1⟩
  rcases FullRead r1 (by omega) h1 with ⟨l2, h2, s2⟩
  exact ⟨l2, r1, h2, t1, s1 ⋙ s2⟩

lemma clear2_full {n h : Nat} {l r : ListBlank (Fin 2)} (tail : ListBlank (Fin 2))
    (Hl : LC outer n 2 l) (Hr : TC ([1, 1] +> tail) h (3 ^ h - 1) r) :
    ∃ l' r', LC outer (n + 2) (2 ^ (n + 2) - 6) l' ∧
      TC ([0, 1] +> tail) h 0 r' ∧ (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r') := by
  have hn := LC_bound Hl
  rcases clear2_full_low tail Hl Hr with ⟨l1, r1, h1, t1, s1⟩
  rcases FullRead r1 (by omega) h1 with ⟨l2, h2, s2⟩
  exact ⟨l2, r1, h2, t1, s1 ⋙ s2⟩

lemma HardEntry (n h k : Nat) {l : ListBlank (Fin 2)}
    (Hl : LC outer (n + h + 2) (2 ^ (1 + h) * (1 + (1 + 3 * 3 ^ h + k) * 2)) l) :
    ∃ l', LC outer n k l' ∧
      (RBar l ([0, 1] +> default)) [target_tm]⊢⁺
        (QBar l' (e0 +> ((e0 ^ h) +> ([0, 1, 1, 0] +> default)))) := by
  have HC : LC outer (n + 1 + (1 + h)) (2 ^ (1 + h) * (1 + (1 + (3 * 3 ^ h + k)) * 2)) l := by
    have hn : n + 1 + (1 + h) = n + h + 2 := by omega
    have hk : 1 + (3 * 3 ^ h + k) = 1 + 3 * 3 ^ h + k := by omega
    rw [hn, hk]; exact Hl
  rcases LC_R0positive ([1, 0] +> default) HC with ⟨l1, h1, s1⟩
  have h1' : LC outer n (3 * (3 ^ h - 0) + k) l1 := by simpa using h1
  rcases TC_first ([1, 0] +> default) h1' (TC_zero ([1, 1] +> ([1, 0] +> default)) h) with ⟨l2, h2, s2⟩
  have hr0 : ([0] +> ([1, 0] +> (default : ListBlank (Fin 2)))) = ([0, 1] +> default) := by simp
  rw [hr0] at s1
  have hr1 : (RBar l1 ([1, 1] +> ((e0 ^ (1 + h)) +> ([1, 1] +> ([1, 0] +> default))))) =
      (QBar l1 (e0 +> ((e0 ^ h) +> ([1, 1] +> ([1, 0] +> default))))) := by
    unfold QBar
    rw [Nat.add_comm 1 h, pow_succ_list, append_assoc_lb]
  rw [hr1] at s1
  have hr2 : ([0, 1] +> ([1, 0] +> (default : ListBlank (Fin 2)))) = ([0, 1, 1, 0] +> default) := by simp
  rw [hr2] at s2
  exact ⟨l2, h2, s1 ⋙ s2⟩

-- ============================================================================
-- Section 12: Pair7Read (SOCMisc.v lines 7478-7575)
-- ============================================================================

def cost : Nat → Nat
  | 0 => 4
  | h + 1 => 8 * 6 ^ (h + 1)

lemma cost_bounds (a : Nat) : 4 ≤ cost a ∧ cost a ≤ 8 * 6 ^ a := by
  cases a with
  | zero => decide
  | succ h =>
    have hp : 0 < 6 ^ (h + 1) := pow_pos 6 (h + 1) (by decide)
    change 4 ≤ 8 * 6 ^ (h + 1) ∧ 8 * 6 ^ (h + 1) ≤ 8 * 6 ^ (h + 1)
    (try omega)
lemma LC_adic_width {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a u : Nat)
    (Hl : LC o n k l) (Hk : k = 2 ^ a * (1 + u * 2)) : a < n := by
  have hb := LC_bound Hl
  by_contra hge
  have hle : n ≤ a := by omega
  have hpow : 2 ^ n ≤ 2 ^ a := pow_mono 2 n a (by decide) hle
  have hpos : 0 < 2 ^ a := pow_pos 2 a (by decide)
  have : 2 ^ a ≤ k := by
    rw [Hk]
    have : 1 ≤ 1 + u * 2 := by omega
    exact Nat.le_mul_of_pos_right (2 ^ a) (by omega)
  (try omega)
lemma ReadPrefix {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a u : Nat)
    (r : ListBlank (Fin 2)) (Hl : LC o n k l) (Hk : k = 2 ^ a * (1 + u * 2)) (Hg : 4 * 6 ^ a < k) :
    ∃ l' p v, LC o n p l' ∧ p = 2 ^ a * (1 + v * 2) ∧
      2 ≤ p ∧ p * 2 + cost a = k * 2 ∧
      (RBar l ([0] +> r)) [target_tm]⊢⁺ (RBar l' ([1] +> r)) := by
  have Hn := LC_adic_width a u Hl Hk
  cases a with
  | zero =>
    have Hk0 : k = 1 + u * 2 := by simpa using Hk
    have Hg0 : 4 < k := by simpa using Hg
    have HC : LC o (1 + (n - 1)) (3 + (u - 1) * 2) l := by
      have hn : 1 + (n - 1) = n := by omega
      have hk : 3 + (u - 1) * 2 = k := by omega
      rw [hn, hk]; exact Hl
    rcases OddPrefix r HC with ⟨l', h', hs⟩
    have hn' : 1 + (n - 1) = n := by omega
    rw [hn'] at h'
    refine ⟨l', 1 + (u - 1) * 2, u - 1, h', ?_, ?_, ?_, hs⟩
    · simp
    · omega
    · change (1 + (u - 1) * 2) * 2 + 4 = k * 2; omega
  | succ a =>
    have Hk_lt : 4 * 6 ^ (a + 1) < 2 ^ (a + 1) * (1 + u * 2) := by rw [← Hk]; exact Hg
    have Hu : 2 * 3 ^ (a + 1) ≤ u := (normal_budget (a + 1) u).mp Hk_lt
    have HC : LC o ((n - 2 - a) + a + 2) (2 ^ (1 + a) * (1 + (2 * 3 ^ (1 + a) + (u - 2 * 3 ^ (1 + a))) * 2)) l := by
      have hn : (n - 2 - a) + a + 2 = n := by omega
      have ha1 : 1 + a = a + 1 := by omega
      have hk : 2 ^ (a + 1) * (1 + (2 * 3 ^ (a + 1) + (u - 2 * 3 ^ (a + 1))) * 2) = k := by
        have : 2 * 3 ^ (a + 1) + (u - 2 * 3 ^ (a + 1)) = u := by omega
        rw [this, Hk]
      rw [hn, ha1, hk]; exact Hl
    rcases EvenPrefix r HC with ⟨l', h', hs⟩
    have hn' : (n - 2 - a) + a + 2 = n := by omega
    have ha1 : 1 + a = a + 1 := by omega
    rw [hn', ha1] at h'
    refine ⟨l', 2 ^ (a + 1) * (1 + (u - 2 * 3 ^ (a + 1)) * 2), u - 2 * 3 ^ (a + 1), h', rfl, ?_, ?_, hs⟩
    · have hp : 2 ≤ 2 ^ (a + 1) := by
        have := pow_mono 2 1 (a + 1) (by decide) (by omega)
        simpa using this
      have : 1 ≤ 1 + (u - 2 * 3 ^ (a + 1)) * 2 := by omega
      have := Nat.mul_le_mul hp this
      (try omega)
    · change 2 ^ (a + 1) * (1 + (u - 2 * 3 ^ (a + 1)) * 2) * 2 + 8 * 6 ^ (a + 1) = k * 2
      rw [pow6 (a + 1), Hk]
      have hu_eq : (u - 2 * 3 ^ (a + 1)) * 2 + 4 * 3 ^ (a + 1) = u * 2 := by omega
      calc 2 ^ (a + 1) * (1 + (u - 2 * 3 ^ (a + 1)) * 2) * 2 + 8 * (2 ^ (a + 1) * 3 ^ (a + 1))
        _ = 2 ^ (a + 1) * (1 + ((u - 2 * 3 ^ (a + 1)) * 2 + 4 * 3 ^ (a + 1))) * 2 := by ring
        _ = 2 ^ (a + 1) * (1 + u * 2) * 2 := by rw [hu_eq]

lemma Read0 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a u : Nat)
    (r : ListBlank (Fin 2)) (Hl : LC o n k l) (Hk : k = 2 ^ a * (1 + u * 2)) (Hg : 4 * 6 ^ a < k) :
    ∃ l' k' u', LC o (1 + n) k' l' ∧
      k' = 2 ^ (1 + a) * (1 + u' * 2) ∧ k' + cost a = k * 2 ∧
      (RBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases ReadPrefix a u ([0, 0] +> r) Hl Hk Hg with ⟨l1, p, v, h1, hp, hpos, he, s1⟩
  rcases LC_R100 r h1 with ⟨l2, h2, s2⟩
  refine ⟨l2, p * 2, v, h2, ?_, he, s1 ⋙ s2⟩
  have : 2 ^ (1 + a) = 2 ^ a * 2 := by rw [Nat.add_comm 1 a, Nat.pow_succ]
  rw [hp, this]
  ring

lemma Read1 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hl : LC o n k l) (Hk : 2 ≤ k) :
    ∃ l' k' u', LC o (1 + n) k' l' ∧
      k' = 1 + u' * 2 ∧ 3 ≤ k' ∧ k' + 1 = k * 2 ∧
      (RBar l (e1 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases LC_R110 r Hl (by omega) with ⟨l', h', hs⟩
  refine ⟨l', k * 2 - 1, k - 1, h', ?_, ?_, ?_, hs⟩ <;> omega

lemma Read2 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a u : Nat)
    (r : ListBlank (Fin 2)) (Hl : LC o n k l) (Hk : k = 2 ^ a * (1 + u * 2)) (Hg : 4 * 6 ^ a < k) :
    ∃ l' k' u', LC o (1 + n) k' l' ∧
      k' = 1 + u' * 2 ∧ 3 ≤ k' ∧ k' + cost a + 1 = k * 2 ∧
      (RBar l (e2 +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases ReadPrefix a u ([1, 0] +> r) Hl Hk Hg with ⟨l1, p, v, h1, hp, hpos, he, s1⟩
  rcases LC_R110 r h1 (by omega) with ⟨l2, h2, s2⟩
  refine ⟨l2, p * 2 - 1, p - 1, h2, ?_, ?_, ?_, s1 ⋙ s2⟩ <;> omega

lemma Read011 {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a u : Nat)
    (r : ListBlank (Fin 2)) (Hl : LC o n k l) (Hk : k = 2 ^ a * (1 + u * 2)) (Hg : 4 * 6 ^ a < k) :
    ∃ l' k' u', LC o (1 + n) k' l' ∧
      k' = 1 + u' * 2 ∧ 3 ≤ k' ∧ k' + cost a = k * 2 + 1 ∧
      (RBar l ([0, 1, 1] +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases ReadPrefix a u ([1, 1] +> r) Hl Hk Hg with ⟨l1, p, v, h1, hp, hpos, he, s1⟩
  rcases LC_R111 r h1 with ⟨l2, h2, s2⟩
  refine ⟨l2, 1 + p * 2, p, h2, rfl, ?_, ?_, s1 ⋙ s2⟩ <;> omega

-- ============================================================================
-- Section 13: Pair7Scan (SOCMisc.v lines 7578-7862)
-- ============================================================================

inductive EndTail : ListBlank (Fin 2) → Prop where
  | End11 : EndTail ([1, 1] +> default)
  | End01 : EndTail ([0, 1] +> default)
  | End0110 : EndTail ([0, 1, 1, 0] +> default)

inductive Trit : List (Fin 2) → Prop where
  | Trit0 : Trit e0
  | Trit1 : Trit e1
  | Trit2 : Trit e2

lemma trit_step {w : List (Fin 2)} {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)}
    (a u d : Nat) (r : ListBlank (Fin 2))
    (Hw : Trit w) (Hl : LC o n k l) (Hk : k = 2 ^ a * (1 + u * 2)) (Hg : 4 * 6 ^ a < k) (Hd : 1 ≤ d) :
    ∃ l' k' d' a' u', LC o (1 + n) k' l' ∧
      k' + d' = 2 * (k + d) ∧ 1 ≤ d' ∧ d' ≤ 2 * d + 8 * 6 ^ a + 1 ∧
      a' ≤ 1 + a ∧ k' = 2 ^ a' * (1 + u' * 2) ∧
      (RBar l (w +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  have hc := cost_bounds a
  cases Hw with
  | Trit0 =>
    rcases Read0 a u r Hl Hk Hg with ⟨l', k', u', hl', hk', hcost, hs⟩
    refine ⟨l', k', 2 * d + cost a, 1 + a, u', hl', ?_, ?_, ?_, ?_, hk', hs⟩ <;> omega
  | Trit1 =>
    have hp6 : 0 < 6 ^ a := pow_pos 6 a (by decide)
    have hk2 : 2 ≤ k := by omega
    rcases Read1 r Hl hk2 with ⟨l', k', u', hl', hk', hp', hcost, hs⟩
    refine ⟨l', k', 2 * d + 1, 0, u', hl', ?_, ?_, ?_, ?_, ?_, hs⟩
    · omega
    · omega
    · omega
    · omega
    · simpa using hk'
  | Trit2 =>
    rcases Read2 a u r Hl Hk Hg with ⟨l', k', u', hl', hk', hp', hcost, hs⟩
    refine ⟨l', k', 2 * d + cost a + 1, 0, u', hl', ?_, ?_, ?_, ?_, ?_, hs⟩
    · omega
    · omega
    · omega
    · omega
    · simpa using hk'

lemma terminal {o : ListBlank (Fin 2)} {n k : Nat} {l : ListBlank (Fin 2)} (a u : Nat)
    {tail : ListBlank (Fin 2)} (HE : EndTail tail) (Hl : LC o n k l)
    (Hk : k = 2 ^ a * (1 + u * 2)) (Hg : 4 * 6 ^ a < k) :
    ∃ l' v, LC o (n + 1) (3 + v * 2) l' ∧ 6 + v * 2 ≤ 2 ^ (n + 1) ∧
      (RBar l tail) [target_tm]⊢⁺ (RBar l' default) := by
  have hb := LC_bound Hl
  have hc := cost_bounds a
  have hp6 : 0 < 6 ^ a := pow_pos 6 a (by decide)
  have hk2 : 2 ≤ k := by omega
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
  cases HE with
  | End11 =>
    rcases Read1 default Hl hk2 with ⟨l', k', u', hl', hk', hp', hcost, hs⟩
    have hn : 1 + n = n + 1 := by omega
    have hk_eq : k' = 3 + (u' - 1) * 2 := by omega
    rw [hn, hk_eq] at hl'
    have htail : (e1 +> (default : ListBlank (Fin 2))) = ([1, 1] +> default) := by
      unfold e1; simp
    rw [htail] at hs
    refine ⟨l', u' - 1, hl', ?_, hs⟩
    (try omega)
  | End01 =>
    rcases Read2 a u default Hl Hk Hg with ⟨l', k', u', hl', hk', hp', hcost, hs⟩
    have hn : 1 + n = n + 1 := by omega
    have hk_eq : k' = 3 + (u' - 1) * 2 := by omega
    rw [hn, hk_eq] at hl'
    have htail : (e2 +> (default : ListBlank (Fin 2))) = ([0, 1] +> default) := by
      unfold e2; simp
    rw [htail] at hs
    refine ⟨l', u' - 1, hl', ?_, hs⟩
    (try omega)
  | End0110 =>
    rcases Read011 a u default Hl Hk Hg with ⟨l', k', u', hl', hk', hp', hcost, hs⟩
    have hn : 1 + n = n + 1 := by omega
    have hk_eq : k' = 3 + (u' - 1) * 2 := by omega
    rw [hn, hk_eq] at hl'
    have htail : ([0, 1, 1] +> (default : ListBlank (Fin 2))) = ([0, 1, 1, 0] +> default) := by simp
    rw [htail] at hs
    refine ⟨l', u' - 1, hl', ?_, hs⟩
    (try omega)
lemma bounded_cons (o : ListBlank (Fin 2)) (C A h : Nat) (r : ListBlank (Fin 2)) (w : List (Fin 2))
    (Hw : Trit w)
    (IH : ∀ n k l i d a u,
      LC o n k l → k = 2 ^ a * (1 + u * 2) → a ≤ i → k + d = C * 2 ^ i →
      1 ≤ d → d + 1 ≤ 2 ^ i * A + 2 * 6 ^ i → A + 6 * 3 ^ (i + h) ≤ C →
      ∃ l' v, LC o (n + h + 1) (3 + v * 2) l' ∧
        6 + v * 2 ≤ 2 ^ (n + h + 1) ∧ (RBar l r) [target_tm]⊢⁺ (RBar l' default)) :
    ∀ n k l i d a u,
      LC o n k l → k = 2 ^ a * (1 + u * 2) → a ≤ i → k + d = C * 2 ^ i →
      1 ≤ d → d + 1 ≤ 2 ^ i * A + 2 * 6 ^ i → A + 6 * 3 ^ (i + (h + 1)) ≤ C →
      ∃ l' v, LC o (n + (h + 1) + 1) (3 + v * 2) l' ∧
        6 + v * 2 ≤ 2 ^ (n + (h + 1) + 1) ∧ (RBar l (w +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  intro n k l i d a u Hl Hk Ha Hsum Hd Hdef HC
  have h3mono : 3 ^ i ≤ 3 ^ (i + (h + 1)) := pow_mono 3 i (i + (h + 1)) (by decide) (by omega)
  have Hci : A + 6 * 3 ^ i ≤ C := by omega
  have Hgi := deficit_guard C A i k d Hsum Hdef Hci
  have h6mono : 6 ^ a ≤ 6 ^ i := pow_mono 6 a i (by decide) Ha
  have Hg : 4 * 6 ^ a < k := by omega
  rcases trit_step a u d r Hw Hl Hk Hg Hd with ⟨l1, k1, d1, a1, u1, HL, HS, HD, HB, HA, HK, HT⟩
  have Hsum1 : k1 + d1 = C * 2 ^ (1 + i) := by
    rw [HS, Hsum, Nat.add_comm 1 i, Nat.pow_succ]
    ring
  have Hdef1 := deficit_next A i a d d1 Ha Hdef HB
  have HC1 : A + 6 * 3 ^ ((1 + i) + h) ≤ C := by
    have : (1 + i) + h = i + (h + 1) := by omega
    rw [this]; exact HC
  rcases IH (1 + n) k1 l1 (1 + i) d1 a1 u1 HL HK (by omega) Hsum1 HD Hdef1 HC1 with ⟨l2, v, HL2, HB2, HT2⟩
  have hn_eq : (1 + n) + h + 1 = n + (h + 1) + 1 := by omega
  rw [hn_eq] at HL2 HB2
  exact ⟨l2, v, HL2, HB2, HT ⋙ HT2⟩

lemma bounded_scan (o : ListBlank (Fin 2)) (C A : Nat) {tail : ListBlank (Fin 2)} {h v : Nat} {r : ListBlank (Fin 2)}
    (Hr : TC tail h v r) (HE : EndTail tail) :
    ∀ n k l i d a u,
      LC o n k l → k = 2 ^ a * (1 + u * 2) → a ≤ i → k + d = C * 2 ^ i →
      1 ≤ d → d + 1 ≤ 2 ^ i * A + 2 * 6 ^ i → A + 6 * 3 ^ (i + h) ≤ C →
      ∃ l' q, LC o (n + h + 1) (3 + q * 2) l' ∧
        6 + q * 2 ≤ 2 ^ (n + h + 1) ∧ (RBar l r) [target_tm]⊢⁺ (RBar l' default) := by
  induction Hr with
  | nil =>
    intro n k l i d a u Hl Hk Ha Hsum Hd Hdef HC
    have HC0 : A + 6 * 3 ^ i ≤ C := by simpa using HC
    have Hgi := deficit_guard C A i k d Hsum Hdef HC0
    have h6mono : 6 ^ a ≤ 6 ^ i := pow_mono 6 a i (by decide) Ha
    have Hg : 4 * 6 ^ a < k := by omega
    exact terminal a u HE Hl Hk Hg
  | d0 h v r htc ih =>
    exact bounded_cons o C A h r e0 Trit.Trit0 ih
  | d1 h v r htc ih =>
    exact bounded_cons o C A h r e1 Trit.Trit1 ih
  | d2 h v r htc ih =>
    exact bounded_cons o C A h r e2 Trit.Trit2 ih

lemma D3 (n : Nat) {l : ListBlank (Fin 2)} (h v : Nat) {r tail : ListBlank (Fin 2)}
    (Hl : LC outer (n + 2) (2 ^ (n + 2) - 3) l) (Hr : TC tail h v r) (HE : EndTail tail)
    (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (RBar l r) [target_tm]⊢⁺ (RBar l' default) := by
  have hp : 0 < 3 ^ h := pow_pos 3 h (by decide)
  have Hpow : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [Nat.pow_add]; ring
  have Hk : 2 ^ (n + 2) - 3 = 2 ^ 0 * (1 + (2 * 2 ^ n - 2) * 2) := by simp; omega
  have Hsum : (2 ^ (n + 2) - 3) + 3 = (4 * 2 ^ n) * 2 ^ 0 := by simp; omega
  have HB : 2 + 6 * 3 ^ (0 + h) ≤ 4 * 2 ^ n := deficit3_budget (2 ^ n) h (0 + h) (by omega) HC
  rcases bounded_scan outer (4 * 2 ^ n) 2 Hr HE (n + 2) (2 ^ (n + 2) - 3) l 0 3 0 (2 * 2 ^ n - 2)
      Hl Hk (by omega) Hsum (by omega) (by decide) HB with ⟨l', u, HL, HG, HS⟩
  have hn_eq : (n + 2) + h + 1 = n + h + 3 := by omega
  rw [hn_eq] at HL HG
  exact ⟨l', u, HL, HG, HS⟩

lemma zero_scan (count : Nat) (o : ListBlank (Fin 2)) (C b : Nat) (r : ListBlank (Fin 2)) :
    ∀ n k l i d u,
      LC o n k l → k = 2 ^ (1 + i) * (1 + u * 2) → k + d = 4 * C * 2 ^ i →
      d + 2 ^ i * b = 12 * 6 ^ i → 1 ≤ d → 0 < b → 3 * 3 ^ (i + count) ≤ C →
      ∃ l' k' d' u', LC o (n + count) k' l' ∧
        k' = 2 ^ (1 + (i + count)) * (1 + u' * 2) ∧ k' + d' = 4 * C * 2 ^ (i + count) ∧
        d' + 2 ^ (i + count) * b = 12 * 6 ^ (i + count) ∧ 1 ≤ d' ∧
        (RBar l ((e0 ^ count) +> r)) [target_tm]⊢* (RBar l' r) := by
  induction count with
  | zero =>
    intro n k l i d u Hl Hk Hsum Hd Hp Hb HC
    exact ⟨l, k, d, u, Hl, Hk, Hsum, Hd, Hp, ⟨0, rfl⟩⟩
  | succ count ih =>
    intro n k l i d u Hl Hk Hsum Hd Hp Hb HC
    have Hg : 4 * 6 ^ (1 + i) < k := zeros_guard C (i + (count + 1)) i b k d (by omega) HC Hb Hsum Hd
    rcases Read0 (1 + i) u ((e0 ^ count) +> r) Hl Hk Hg with ⟨l1, k1, u1, HL, HK, HD, HS⟩
    have hcost : cost (1 + i) = 8 * 6 ^ (1 + i) := by
      have : 1 + i = i + 1 := by omega
      rw [this]; rfl
    rw [hcost] at HD
    have Hsum1 : k1 + (2 * d + 8 * 6 ^ (1 + i)) = 4 * C * 2 ^ (1 + i) := by
      have hpow : 4 * C * 2 ^ (1 + i) = (4 * C * 2 ^ i) * 2 := by
        rw [Nat.add_comm 1 i, Nat.pow_succ]; ring
      (try omega)
    have Hd1 := zeros_next i b d Hd
    have HC1 : 3 * 3 ^ ((1 + i) + count) ≤ C := by
      have : (1 + i) + count = i + (count + 1) := by omega
      rw [this]; exact HC
    rcases ih (1 + n) k1 l1 (1 + i) (2 * d + 8 * 6 ^ (1 + i)) u1 HL HK Hsum1 Hd1 (by omega) Hb HC1
      with ⟨l2, k2, d2, u2, HL2, HK2, HS2, HD2, HP2, HT2⟩
    have hn_eq : (1 + n) + count = n + (count + 1) := by omega
    have hi_eq : (1 + i) + count = i + (count + 1) := by omega
    rw [hn_eq] at HL2
    rw [hi_eq] at HK2 HS2 HD2
    have hr_eq : ((e0 ^ (count + 1)) +> r) = (e0 +> ((e0 ^ count) +> r)) := by
      rw [pow_succ_list, append_assoc_lb]
    rw [hr_eq]
    exact ⟨l2, k2, d2, u2, HL2, HK2, HS2, HD2, HP2, stepPlus_stepStar (stepPlus_stepStar_stepPlus HS HT2)⟩

lemma initial26 (n h d : Nat) (Hd : d = 2 ∨ d = 6) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ b u, 6 ≤ b ∧ b ≤ 10 ∧ d + b = 12 ∧
      2 ^ (n + 2) - d = 2 ^ 1 * (1 + u * 2) ∧ (2 ^ (n + 2) - d) + d = 4 * 2 ^ n ∧ 1 ≤ d := by
  have hp : 0 < 3 ^ h := pow_pos 3 h (by decide)
  have Hpow : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [Nat.pow_add]; ring
  rcases Hd with rfl | rfl
  · refine ⟨10, 2 ^ n - 1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨6, 2 ^ n - 2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

lemma Zero26 (n h d : Nat) {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hd : d = 2 ∨ d = 6) (HC : 3 * 3 ^ h ≤ 2 ^ n) (Hl : LC outer (n + 2) (2 ^ (n + 2) - d) l) :
    ∃ l', LC outer (n + h + 2) (2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h + (12 - d))) l' ∧
      (RBar l ((e0 ^ h) +> r)) [target_tm]⊢* (RBar l' r) := by
  rcases initial26 n h d Hd HC with ⟨b, u, Hb, Hb', Hdb, Hk, Hsum, Hp⟩
  have HS : (2 ^ (n + 2) - d) + d = 4 * 2 ^ n * 2 ^ 0 := by simp [Hsum]
  have HD : d + 2 ^ 0 * b = 12 * 6 ^ 0 := by simp [Hdb]
  rcases zero_scan h outer (2 ^ n) b r (n + 2) (2 ^ (n + 2) - d) l 0 d u Hl Hk HS HD Hp (by omega) (by simpa using HC)
    with ⟨l1, k1, d1, u1, HL, HK, HS1, HD1, HP1, HT⟩
  have hn_eq : (n + 2) + h = n + h + 2 := by omega
  have Hvalue : k1 = 2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h + (12 - d)) := by
    have hs1 : k1 + d1 = 2 ^ h * (4 * 2 ^ n) := by
      have h0 : 4 * 2 ^ n * 2 ^ (0 + h) = 2 ^ h * (4 * 2 ^ n) := by rw [Nat.zero_add]; ring
      (try omega)
    have hd1 : d1 + 2 ^ h * b = 2 ^ h * (12 * 3 ^ h) := by
      have h0 : 2 ^ (0 + h) * b = 2 ^ h * b := by rw [Nat.zero_add]
      have h1 : 12 * 6 ^ (0 + h) = 2 ^ h * (12 * 3 ^ h) := by
        rw [Nat.zero_add, pow6 h]; ring
      (try omega)
    have hb_eq : b = 12 - d := by omega
    subst hb_eq
    have hdist1 : 2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h + (12 - d)) =
        2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h) + 2 ^ h * (12 - d) := by
      rw [Nat.mul_add]
    have hdist2 : 2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h) + 2 ^ h * (12 * 3 ^ h) = 2 ^ h * (4 * 2 ^ n) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    (try omega)
  rw [hn_eq, Hvalue] at HL
  exact ⟨l1, HL, HT⟩

lemma Z26 (n : Nat) {l : ListBlank (Fin 2)} (h d : Nat) {r : ListBlank (Fin 2)}
    (Hl : LC outer (n + 2) (2 ^ (n + 2) - d) l) (Hr : TC ([1, 1] +> default) h 0 r)
    (Hd : d = 2 ∨ d = 6) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (RBar l r) [target_tm]⊢⁺ (RBar l' default) := by
  rw [TC_zero_unique Hr]
  rcases initial26 n h d Hd HC with ⟨b, u, Hb, Hb', Hdb, Hk, Hsum, Hp⟩
  have HS : (2 ^ (n + 2) - d) + d = 4 * 2 ^ n * 2 ^ 0 := by simp [Hsum]
  have HD : d + 2 ^ 0 * b = 12 * 6 ^ 0 := by simp [Hdb]
  rcases zero_scan h outer (2 ^ n) b ([1, 1] +> default) (n + 2) (2 ^ (n + 2) - d) l 0 d u
      Hl Hk HS HD Hp (by omega) (by simpa using HC)
    with ⟨l1, k1, d1, u1, HL, HK, HS1, HD1, HP1, HT⟩
  have hs1 : k1 + d1 = 4 * 2 ^ n * 2 ^ h := by simpa using HS1
  have hd1 : d1 + 2 ^ h * b = 12 * 6 ^ h := by simpa using HD1
  have Hpos := zeros_end (2 ^ n) h b k1 d1 HC hs1 hd1
  have hp2 : 1 ≤ 2 ^ h := pow_pos 2 h (by decide)
  have hmul : 1 * 6 ≤ 2 ^ h * b := Nat.mul_le_mul hp2 Hb
  have hk2 : 2 ≤ k1 := by omega
  rcases Read1 default HL hk2 with ⟨l2, k2, u2, HL2, HK2, HP2, HD2, HT2⟩
  have Hbound := LC_bound HL
  have hn_eq : 1 + ((n + 2) + h) = n + h + 3 := by omega
  have hk_eq : k2 = 3 + (u2 - 1) * 2 := by omega
  rw [hn_eq, hk_eq] at HL2
  have hpow : 2 ^ (n + h + 3) = 2 ^ ((n + 2) + h) * 2 := by
    have : n + h + 3 = ((n + 2) + h) + 1 := by omega
    rw [this, Nat.pow_succ]
  have htail : (e1 +> (default : ListBlank (Fin 2))) = ([1, 1] +> default) := by unfold e1; simp
  rw [htail] at HT2
  refine ⟨l2, u2 - 1, HL2, ?_, stepStar_stepPlus_stepPlus HT HT2⟩
  (try omega)
lemma after_nonzero (o : ListBlank (Fin 2)) (C j t A n k : Nat) {l : ListBlank (Fin 2)} (u : Nat)
    {tail : ListBlank (Fin 2)} {v : Nat} {r : ListBlank (Fin 2)}
    (Hr : TC tail t v r) (HE : EndTail tail) (Hl : LC o n k l) (Hk : k = 1 + u * 2)
    (Hsum : k + (2 ^ (j + 1) * A + 1) = 2 ^ (j + 1) * (4 * C))
    (HA : A + 6 ≤ 36 * 3 ^ j) (HC : 3 * 3 ^ (j + 1 + t) ≤ C) :
    ∃ l' q, LC o (n + t + 1) (3 + q * 2) l' ∧ 6 + q * 2 ≤ 2 ^ (n + t + 1) ∧
      (RBar l r) [target_tm]⊢⁺ (RBar l' default) := by
  have HK : k = 2 ^ 0 * (1 + u * 2) := by simpa using Hk
  have HS : k + (2 ^ (j + 1) * A + 1) = (2 ^ (j + 1) * (4 * C)) * 2 ^ 0 := by simpa using Hsum
  have HB : 2 ^ (j + 1) * A + 6 * 3 ^ (0 + t) ≤ 2 ^ (j + 1) * (4 * C) :=
    deficit26_budget_scaled C j t (0 + t) A (by omega) HC HA
  exact bounded_scan o (2 ^ (j + 1) * (4 * C)) (2 ^ (j + 1) * A) Hr HE n k l 0
    (2 ^ (j + 1) * A + 1) 0 u Hl HK (by omega) HS (by omega) (by simp) HB

lemma D26 (n : Nat) {l : ListBlank (Fin 2)} (h v : Nat) {r tail : ListBlank (Fin 2)} (d : Nat)
    (Hl : LC outer (n + 2) (2 ^ (n + 2) - d) l) (Hr : TC tail h v r) (HE : EndTail tail)
    (Hd : d = 2 ∨ d = 6) (Hv : 0 < v) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (RBar l r) [target_tm]⊢⁺ (RBar l' default) := by
  rcases initial26 n h d Hd HC with ⟨b, u, Hb, Hb', Hdb, Hk, Hsum, Hp⟩
  rcases TC_positive Hr Hv with ⟨j, t, q, s, Hh, HT, ⟨Er, Ev⟩ | ⟨Er, Ev⟩⟩
  · subst Er
    have h3mono : 3 ^ j ≤ 3 ^ h := pow_mono 3 j h (by decide) (by omega)
    have HCj : 3 * 3 ^ j ≤ 2 ^ n := by omega
    have HCt : 3 * 3 ^ (j + 1 + t) ≤ 2 ^ n := by
      have : j + 1 + t = h := by omega
      rw [this]; exact HC
    have HS : (2 ^ (n + 2) - d) + d = 4 * 2 ^ n * 2 ^ 0 := by simp [Hsum]
    have HD : d + 2 ^ 0 * b = 12 * 6 ^ 0 := by simp [Hdb]
    rcases zero_scan j outer (2 ^ n) b (e1 +> s) (n + 2) (2 ^ (n + 2) - d) l 0 d u
        Hl Hk HS HD Hp (by omega) (by simpa using HCj)
      with ⟨l1, k1, d1, u1, HL, HK, HS1, HD1, HP1, HT1⟩
    have hp3j : 0 < 3 ^ j := pow_pos 3 j (by decide)
    have Hbnd : b ≤ 12 * 3 ^ j := by omega
    have hd1 : d1 + 2 ^ j * b = 12 * 6 ^ j := by simpa using HD1
    have Hdef : d1 = 2 ^ j * (12 * 3 ^ j - b) := by
      rw [pow6 j] at hd1
      have : 2 ^ j * (12 * 3 ^ j - b) + 2 ^ j * b = 12 * (2 ^ j * 3 ^ j) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel Hbnd]; ring
      (try omega)
    have hs1 : k1 + d1 = 4 * 2 ^ n * 2 ^ j := by simpa using HS1
    have Hg : 4 * 6 ^ (1 + j) < k1 := zeros_guard (2 ^ n) h j b k1 d1 (by omega) HC (by omega) hs1 hd1
    have hp6 : 0 < 6 ^ (1 + j) := pow_pos 6 (1 + j) (by decide)
    have hk2 : 2 ≤ k1 := by omega
    rcases Read1 s HL hk2 with ⟨l2, k2, u2, HL2, HK2, HP2, HD2, HT2⟩
    have HA : (12 * 3 ^ j - b) + 6 ≤ 36 * 3 ^ j := by omega
    have Hsum2 : k2 + (2 ^ (j + 1) * (12 * 3 ^ j - b) + 1) = 2 ^ (j + 1) * (4 * 2 ^ n) := by
      have h1 : 2 ^ (j + 1) * (12 * 3 ^ j - b) = 2 * d1 := by
        rw [Hdef, Nat.pow_succ]; ring
      have h2 : 2 ^ (j + 1) * (4 * 2 ^ n) = 2 * (4 * 2 ^ n * 2 ^ j) := by
        rw [Nat.pow_succ]; ring
      (try omega)
    rcases after_nonzero outer (2 ^ n) j t (12 * 3 ^ j - b) (1 + (n + 2 + j)) k2 u2
        HT HE HL2 HK2 Hsum2 HA HCt with ⟨l3, w, HL3, HB3, HT3⟩
    have hn_eq : (1 + (n + 2 + j)) + t + 1 = n + h + 3 := by omega
    rw [hn_eq] at HL3 HB3
    exact ⟨l3, w, HL3, HB3, stepStar_stepPlus_stepPlus HT1 (HT2 ⋙ HT3)⟩
  · subst Er
    have h3mono : 3 ^ j ≤ 3 ^ h := pow_mono 3 j h (by decide) (by omega)
    have HCj : 3 * 3 ^ j ≤ 2 ^ n := by omega
    have HCt : 3 * 3 ^ (j + 1 + t) ≤ 2 ^ n := by
      have : j + 1 + t = h := by omega
      rw [this]; exact HC
    have HS : (2 ^ (n + 2) - d) + d = 4 * 2 ^ n * 2 ^ 0 := by simp [Hsum]
    have HD : d + 2 ^ 0 * b = 12 * 6 ^ 0 := by simp [Hdb]
    rcases zero_scan j outer (2 ^ n) b (e2 +> s) (n + 2) (2 ^ (n + 2) - d) l 0 d u
        Hl Hk HS HD Hp (by omega) (by simpa using HCj)
      with ⟨l1, k1, d1, u1, HL, HK, HS1, HD1, HP1, HT1⟩
    have hp3j : 0 < 3 ^ j := pow_pos 3 j (by decide)
    have Hbnd : b ≤ 12 * 3 ^ j := by omega
    have hd1 : d1 + 2 ^ j * b = 12 * 6 ^ j := by simpa using HD1
    have Hdef : d1 = 2 ^ j * (12 * 3 ^ j - b) := by
      rw [pow6 j] at hd1
      have : 2 ^ j * (12 * 3 ^ j - b) + 2 ^ j * b = 12 * (2 ^ j * 3 ^ j) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel Hbnd]; ring
      (try omega)
    have hs1 : k1 + d1 = 4 * 2 ^ n * 2 ^ j := by simpa using HS1
    have Hg : 4 * 6 ^ (1 + j) < k1 := zeros_guard (2 ^ n) h j b k1 d1 (by omega) HC (by omega) hs1 hd1
    have HK' : k1 = 2 ^ (1 + j) * (1 + u1 * 2) := by simpa using HK
    rcases Read2 (1 + j) u1 s HL HK' Hg with ⟨l2, k2, u2, HL2, HK2, HP2, HD2, HT2⟩
    have hcost : cost (1 + j) = 8 * 6 ^ (1 + j) := by
      have : 1 + j = j + 1 := by omega
      rw [this]; rfl
    rw [hcost] at HD2
    have HA : (36 * 3 ^ j - b) + 6 ≤ 36 * 3 ^ j := by omega
    have Hsum2 : k2 + (2 ^ (j + 1) * (36 * 3 ^ j - b) + 1) = 2 ^ (j + 1) * (4 * 2 ^ n) := by
      have hsub : 36 * 3 ^ j - b = (12 * 3 ^ j - b) + 24 * 3 ^ j := by omega
      have h1 : 2 ^ (j + 1) * (36 * 3 ^ j - b) = 2 * d1 + 8 * 6 ^ (1 + j) := by
        rw [hsub, Nat.mul_add, Hdef, Nat.add_comm 1 j, pow6 (j + 1), Nat.pow_succ, Nat.pow_succ]
        ring
      have h2 : 2 ^ (j + 1) * (4 * 2 ^ n) = 2 * (4 * 2 ^ n * 2 ^ j) := by
        rw [Nat.pow_succ]; ring
      (try omega)
    rcases after_nonzero outer (2 ^ n) j t (36 * 3 ^ j - b) (1 + (n + 2 + j)) k2 u2
        HT HE HL2 HK2 Hsum2 HA HCt with ⟨l3, w, HL3, HB3, HT3⟩
    have hn_eq : (1 + (n + 2 + j)) + t + 1 = n + h + 3 := by omega
    rw [hn_eq] at HL3 HB3
    exact ⟨l3, w, HL3, HB3, stepStar_stepPlus_stepPlus HT1 (HT2 ⋙ HT3)⟩

-- ============================================================================
-- Section 14: Pair7Power (SOCMisc.v lines 7865-7957)
-- ============================================================================

lemma PowerStart (m h : Nat) {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hg : 3 ^ (1 + h) ≤ 2 ^ m) (H : LC outer (m + h + 2) (2 ^ (1 + h)) l) :
    ∃ l', LC outer (m + 2) (2 ^ (m + 2) - 6) l' ∧
      (RBar l ([0, 0] +> r)) [target_tm]⊢⁺ (RBar l' ((e0 ^ h) +> (e1 +> r))) := by
  have h3_le : 3 ≤ 3 ^ (1 + h) := by
    have := pow_mono 3 1 (1 + h) (by decide) (by omega)
    simpa using this
  have H3 : 3 ≤ 2 ^ m := by omega
  have HC : LC outer (m + 1 + (1 + h)) (2 ^ (1 + h)) l := by
    have : m + 1 + (1 + h) = m + h + 2 := by omega
    rw [this]; exact H
  rcases LC_R0power ([0] +> r) HC with ⟨l1, h1, s1⟩
  rcases LC_R111 ((e0 ^ (1 + h)) +> (e1 +> r)) h1 with ⟨l2, h2, s2⟩
  have HC2 : LC outer (1 + m) (3 + (2 ^ m - 2) * 2) l2 := by
    have hk : 1 + (2 ^ m - 1) * 2 = 3 + (2 ^ m - 2) * 2 := by omega
    rw [hk] at h2; exact h2
  rcases Odd000 ((e0 ^ h) +> (e1 +> r)) HC2 with ⟨l3, h3', s3⟩
  have hn : 2 + m = m + 2 := by omega
  have hk3 : 2 + (2 ^ m - 2) * 4 = 2 ^ (m + 2) - 6 := by
    have : 2 ^ (m + 2) = 2 ^ m * 4 := by rw [Nat.pow_add]
    (try omega)
  rw [hn, hk3] at h3'
  have hr0 : ([0] +> ([0] +> r)) = ([0, 0] +> r) := rfl
  rw [hr0] at s1
  have hr1 : ([1, 1] +> ([0] +> r)) = (e1 +> r) := rfl
  rw [hr1] at s1
  have hr2 : (e0 +> ((e0 ^ h) +> (e1 +> r))) = ((e0 ^ (1 + h)) +> (e1 +> r)) := by
    rw [Nat.add_comm 1 h, pow_succ_list, append_assoc_lb]
  rw [hr2] at s3
  exact ⟨l3, h3', s1 ⋙ s2 ⋙ s3⟩

lemma PowerZeros (m j t : Nat) {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hg : 3 ^ (1 + j + t) ≤ 2 ^ m)
    (H : LC outer (m + j + 2) (2 ^ (1 + j) * (1 + (2 ^ m - 3 ^ (1 + j) + 1) * 2)) l) :
    ∃ l', LC outer (m + j + t + 2) (2 ^ (1 + j + t) * (1 + (2 ^ m - 3 ^ (1 + j + t) + 1) * 2)) l' ∧
      (RBar l ((e0 ^ t) +> (e1 +> r))) [target_tm]⊢* (RBar l' (e1 +> r)) := by
  induction t generalizing j l with
  | zero =>
    exact ⟨l, H, ⟨0, rfl⟩⟩
  | succ t ih =>
    have h3mono : 3 ^ (2 + j) ≤ 3 ^ (1 + j + (t + 1)) := pow_mono 3 (2 + j) (1 + j + (t + 1)) (by decide) (by omega)
    have Hj : 3 ^ (2 + j) ≤ 2 ^ m := by omega
    have Hu : 2 * 3 ^ (1 + j) + (2 ^ m - 3 ^ (2 + j) + 1) = 2 ^ m - 3 ^ (1 + j) + 1 := by
      have : 3 ^ (2 + j) = 3 ^ (1 + j) * 3 := by
        have : 2 + j = (1 + j) + 1 := by omega
        rw [this, Nat.pow_succ]
      (try omega)
    have HC : LC outer (m + j + 2) (2 ^ (1 + j) * (1 + (2 * 3 ^ (1 + j) + (2 ^ m - 3 ^ (2 + j) + 1)) * 2)) l := by
      rw [Hu]; exact H
    rcases Even000 ((e0 ^ t) +> (e1 +> r)) HC with ⟨l1, h1, s1⟩
    have HC1 : LC outer (m + (1 + j) + 2) (2 ^ (1 + (1 + j)) * (1 + (2 ^ m - 3 ^ (1 + (1 + j)) + 1) * 2)) l1 := by
      have hn : m + j + 3 = m + (1 + j) + 2 := by omega
      have hj : 2 + j = 1 + (1 + j) := by omega
      rw [hn, hj] at h1; exact h1
    have Hg1 : 3 ^ (1 + (1 + j) + t) ≤ 2 ^ m := by
      have : 1 + (1 + j) + t = 1 + j + (t + 1) := by omega
      rw [this]; exact Hg
    rcases ih (1 + j) Hg1 HC1 with ⟨l2, h2, s2⟩
    have hn2 : m + (1 + j) + t + 2 = m + j + (t + 1) + 2 := by omega
    have hj2 : 1 + (1 + j) + t = 1 + j + (t + 1) := by omega
    rw [hn2, hj2] at h2
    have hr : ((e0 ^ (t + 1)) +> (e1 +> r)) = (e0 +> ((e0 ^ t) +> (e1 +> r))) := by
      rw [pow_succ_list, append_assoc_lb]
    rw [hr]
    exact ⟨l2, h2, stepPlus_stepStar (stepPlus_stepStar_stepPlus s1 s2)⟩

lemma Power (m h : Nat) {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hg : 3 ^ (1 + h) ≤ 2 ^ m) (H : LC outer (m + h + 2) (2 ^ (1 + h)) l) :
    ∃ l', LC outer (m + h + 3) (2 ^ (2 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) - 1) l' ∧
      (RBar l ([0, 0] +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases PowerStart m h r Hg H with ⟨l1, h1, s1⟩
  have h3_le : 3 ≤ 3 ^ (1 + h) := by
    have := pow_mono 3 1 (1 + h) (by decide) (by omega)
    simpa using this
  have H3 : 3 ≤ 2 ^ m := by omega
  have HC : LC outer (m + 0 + 2) (2 ^ (1 + 0) * (1 + (2 ^ m - 3 ^ (1 + 0) + 1) * 2)) l1 := by
    have hk : 2 ^ (m + 2) - 6 = 2 ^ (1 + 0) * (1 + (2 ^ m - 3 ^ (1 + 0) + 1) * 2) := by
      have : 2 ^ (m + 2) = 2 ^ m * 4 := by rw [Nat.pow_add]
      simp [this]; omega
    rw [← hk]; exact h1
  have Hg0 : 3 ^ (1 + 0 + h) ≤ 2 ^ m := by simpa using Hg
  rcases PowerZeros m 0 h r Hg0 HC with ⟨l2, h2, s2⟩
  have hp2 : 0 < 2 ^ (1 + 0 + h) := pow_pos 2 (1 + 0 + h) (by decide)
  have Hp : 0 < 2 ^ (1 + 0 + h) * (1 + (2 ^ m - 3 ^ (1 + 0 + h) + 1) * 2) :=
    Nat.mul_pos hp2 (by omega)
  rcases LC_R110 r h2 Hp with ⟨l3, h4, s3⟩
  have hn : 1 + (m + 0 + h + 2) = m + h + 3 := by omega
  have hk4 : (2 ^ (1 + 0 + h) * (1 + (2 ^ m - 3 ^ (1 + 0 + h) + 1) * 2)) * 2 - 1 =
      2 ^ (2 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) - 1 := by
    have h1 : 1 + 0 + h = 1 + h := by omega
    rw [h1]
    have h_inner : 1 + (2 ^ m - 3 ^ (1 + h) + 1) * 2 = 2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3 := by
      rw [Nat.pow_succ]; omega
    have h_outer : 2 ^ (2 + h) = 2 ^ (1 + h) * 2 := by
      have : 2 + h = (1 + h) + 1 := by omega
      rw [this, Nat.pow_succ]
    rw [h_inner, h_outer]
    have h_comm : 2 ^ (1 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) * 2 =
        2 ^ (1 + h) * 2 * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) := by ring
    rw [h_comm]
  rw [hn, hk4] at h4
  exact ⟨l3, h4, (stepPlus_stepStar_stepPlus s1 s2) ⋙ s3⟩

lemma Power_Bo (m h : Nat) {l : ListBlank (Fin 2)} (r : ListBlank (Fin 2))
    (Hg : 3 ^ (1 + h) ≤ 2 ^ m) (H : LC outer (m + h + 2) (2 ^ (1 + h)) l) :
    ∃ l' v, LC outer (m + h + 3) (3 + v * 2) l' ∧
      6 + v * 2 ≤ 2 ^ (m + h + 3) ∧ (RBar l ([0, 0] +> r)) [target_tm]⊢⁺ (RBar l' r) := by
  rcases Power m h r Hg H with ⟨l', HC, HS⟩
  rcases power_exit m (1 + h) (by omega) Hg with ⟨Hlo, Hhi⟩
  have h2h : 1 + h + 1 = 2 + h := by omega
  have hmh : m + (1 + h) + 2 = m + h + 3 := by omega
  rw [h2h] at Hlo Hhi
  rw [hmh] at Hhi
  have h_pow : 2 ^ (2 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) =
      (2 ^ (1 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3)) * 2 := by
    have : 2 ^ (2 + h) = 2 ^ (1 + h) * 2 := by
      have : 2 + h = (1 + h) + 1 := by omega
      rw [this, Nat.pow_succ]
    rw [this]; ring
  have He : 2 ^ (2 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) - 1 =
      3 + (2 ^ (1 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) - 2) * 2 := by
    (try omega)
  rw [He] at HC
  refine ⟨l', 2 ^ (1 + h) * (2 ^ (m + 1) - 2 * 3 ^ (1 + h) + 3) - 2, HC, ?_, HS⟩
  (try omega)
-- ============================================================================
-- Section 15: Pair7Closure (SOCMisc.v lines 7960-8053)
-- ============================================================================

inductive Allowed : Cfg (Fin 2) (Fin 6) → Prop where
  | Bo (n v : Nat) (l : ListBlank (Fin 2)) :
      LC outer n (3 + v * 2) l → 6 + v * 2 ≤ 2 ^ n → Allowed (RBar l default)
  | Be (m a u : Nat) (l : ListBlank (Fin 2)) :
      LC outer (m + a + 2) (2 ^ (1 + a) * (1 + u * 2)) l →
      u + 3 ^ (1 + a) ≤ 2 ^ m → Allowed (RBar l default)
  | S11 (n k h v : Nat) (l r : ListBlank (Fin 2)) :
      LC outer n k l → TC ([1, 1] +> default) h v r →
      k + v * 3 + 3 * 3 ^ h + 1 ≤ 2 ^ n → Allowed (QBar l (e0 +> r))
  | S01 (n k h v : Nat) (l r : ListBlank (Fin 2)) :
      LC outer n k l → TC ([0, 1] +> default) h v r →
      k + v * 3 + 6 * 3 ^ h + 1 ≤ 2 ^ n → Allowed (QBar l (e0 +> r))

lemma Bo_step (n v : Nat) (l : ListBlank (Fin 2))
    (Hl : LC outer n (3 + v * 2) l) (Hg : 6 + v * 2 ≤ 2 ^ n) :
    ∃ c', ((RBar l default) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  cases n with
  | zero => omega
  | succ m =>
    have Hl' : LC outer (1 + m) (3 + v * 2) l := by
      have : 1 + m = m + 1 := by omega
      rw [this]; exact Hl
    rcases Odd000 default Hl' with ⟨l', HC, HS⟩
    have hr : (e0 +> (default : ListBlank (Fin 2))) = default := by unfold e0; simp
    rw [hr] at HS
    have hn : 2 + m = m + 0 + 2 := by omega
    have hk : 2 + v * 4 = 2 ^ (1 + 0) * (1 + v * 2) := by simp; omega
    rw [hn, hk] at HC
    refine ⟨RBar l' default, HS, Allowed.Be m 0 v l' HC ?_⟩
    have : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
    simp at *; omega

lemma Be_step (m a u : Nat) (l : ListBlank (Fin 2))
    (Hl : LC outer (m + a + 2) (2 ^ (1 + a) * (1 + u * 2)) l) (Hg : u + 3 ^ (1 + a) ≤ 2 ^ m) :
    ∃ c', ((RBar l default) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  cases u with
  | zero =>
    have HC : LC outer (m + a + 2) (2 ^ (1 + a)) l := by simpa using Hl
    rcases Power_Bo m a default (by omega) HC with ⟨l', v, H1, H2, HS⟩
    have hr : ([0, 0] +> (default : ListBlank (Fin 2))) = default := by simp
    rw [hr] at HS
    exact ⟨RBar l' default, HS, Allowed.Bo (m + a + 3) v l' H1 H2⟩
  | succ u =>
    have HC : LC outer (m + 1 + (1 + a)) (2 ^ (1 + a) * (1 + (1 + u) * 2)) l := by
      have hn : m + 1 + (1 + a) = m + a + 2 := by omega
      have hu : 1 + u = u + 1 := by omega
      rw [hn, hu]; exact Hl
    rcases LC_R0positive default HC with ⟨l', H1, HS⟩
    have hr0 : ([0] +> (default : ListBlank (Fin 2))) = default := by simp
    rw [hr0] at HS
    have hr1 : (RBar l' ([1, 1] +> ((e0 ^ (1 + a)) +> ([1, 1] +> default)))) =
        (QBar l' (e0 +> ((e0 ^ a) +> ([1, 1] +> default)))) := by
      unfold QBar
      rw [Nat.add_comm 1 a, pow_succ_list, append_assoc_lb]
    rw [hr1] at HS
    refine ⟨QBar l' (e0 +> ((e0 ^ a) +> ([1, 1] +> default))), HS,
      Allowed.S11 m u a 0 l' ((e0 ^ a) +> ([1, 1] +> default)) H1 (TC_zero ([1, 1] +> default) a) ?_⟩
    have : 3 ^ (1 + a) = 3 * 3 ^ a := by rw [Nat.add_comm 1 a, Nat.pow_succ]; ring
    (try omega)
lemma S01_exit (n k h : Nat) (l r : ListBlank (Fin 2))
    (Hl : LC outer n (2 + k) l) (Hr : TC ([0, 1] +> default) h (3 ^ h - 1) r)
    (Hg : 2 + k + (3 ^ h - 1) * 3 + 6 * 3 ^ h + 1 ≤ 2 ^ n) :
    ∃ c', ((QBar l (e0 +> r)) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  have hp : 0 < 3 ^ h := pow_pos 3 h (by decide)
  have HC : LC outer n (3 * (3 ^ h - (3 ^ h - 1)) - 1 + k) l := by
    have : 3 * (3 ^ h - (3 ^ h - 1)) - 1 + k = 2 + k := by omega
    rw [this]; exact Hl
  rcases TC_exit default HC Hr with ⟨l1, H1, S1⟩
  rcases LC_R100 default H1 with ⟨l2, H2, S2⟩
  have hr1 : ([1, 0, 0] +> (default : ListBlank (Fin 2))) = ([1] +> default) := by simp
  rw [hr1] at S2
  have hn : 1 + (n + h + 2) = n + (1 + h) + 2 := by omega
  have hk : ((1 + k * 2) * 2 ^ (1 + h)) * 2 = 2 ^ (1 + (1 + h)) * (1 + k * 2) := by
    have : 1 + (1 + h) = (1 + h) + 1 := by omega
    rw [this, Nat.pow_succ]; ring
  rw [hn, hk] at H2
  refine ⟨RBar l2 default, S1 ⋙ S2, Allowed.Be n (1 + h) k l2 H2 ?_⟩
  have : 3 ^ (1 + (1 + h)) = 9 * 3 ^ h := by
    have : 1 + (1 + h) = h + 2 := by omega
    rw [this, Nat.pow_add]; ring
  (try omega)
lemma S11_step (n k h v : Nat) (l r : ListBlank (Fin 2))
    (Hl : LC outer n (3 + k) l) (Hr : TC ([1, 1] +> default) h v r)
    (Hg : 3 + k + v * 3 + 3 * 3 ^ h + 1 ≤ 2 ^ n) :
    ∃ c', ((QBar l (e0 +> r)) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  by_cases Hv : v + 1 < 3 ^ h
  · rcases TC_next Hl Hr Hv with ⟨l', r', HC, HT, HS⟩
    exact ⟨QBar l' (e0 +> r'), HS, Allowed.S11 n k h (v + 1) l' r' HC HT (by omega)⟩
  · have hb := TC_bound Hr
    have Ev : v = 3 ^ h - 1 := by omega
    subst Ev
    have HC : LC outer n (3 * (3 ^ h - (3 ^ h - 1)) + k) l := by
      have : 3 * (3 ^ h - (3 ^ h - 1)) + k = 3 + k := by omega
      rw [this]; exact Hl
    rcases TC_first default HC Hr with ⟨l', H1, HS⟩
    exact ⟨QBar l' (e0 +> ((e0 ^ h) +> ([0, 1] +> default))), HS,
      Allowed.S01 n k h 0 l' ((e0 ^ h) +> ([0, 1] +> default)) H1 (TC_zero ([0, 1] +> default) h) (by omega)⟩

lemma S01_step (n k h v : Nat) (l r : ListBlank (Fin 2))
    (Hl : LC outer n (3 + k) l) (Hr : TC ([0, 1] +> default) h v r)
    (Hg : 3 + k + v * 3 + 6 * 3 ^ h + 1 ≤ 2 ^ n) :
    ∃ c', ((QBar l (e0 +> r)) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  by_cases Hv : v + 1 < 3 ^ h
  · rcases TC_next Hl Hr Hv with ⟨l', r', HC, HT, HS⟩
    exact ⟨QBar l' (e0 +> r'), HS, Allowed.S01 n k h (v + 1) l' r' HC HT (by omega)⟩
  · have hb := TC_bound Hr
    have Ev : v = 3 ^ h - 1 := by omega
    subst Ev
    have Hl' : LC outer n (2 + (1 + k)) l := by
      have : 2 + (1 + k) = 3 + k := by omega
      rw [this]; exact Hl
    exact S01_exit n (1 + k) h l r Hl' Hr (by omega)

-- ============================================================================
-- Section 16: Pair7LowReturn & Nonhalt (SOCMisc.v lines 8056-8259)
-- ============================================================================

lemma Good0 (n : Nat) {l : ListBlank (Fin 2)} (h v : Nat) {r tail : ListBlank (Fin 2)}
    (Hl : LC outer n 0 l) (Hr : TC tail h v r) (HE : EndTail tail)
    (Hv : 0 < v) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  rcases clear0 r Hl with ⟨l1, H1, S1⟩
  rcases D26 n h v 2 H1 Hr HE (Or.inl rfl) Hv HC with ⟨l2, u, H2, H3, S2⟩
  exact ⟨l2, u, H2, H3, S1 ⋙ S2⟩

lemma Good1 (n : Nat) {l : ListBlank (Fin 2)} (h v : Nat) {r tail : ListBlank (Fin 2)}
    (Hl : LC outer n 1 l) (Hr : TC tail h v r) (HE : EndTail tail)
    (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  rcases clear1 r Hl with ⟨l1, H1, S1⟩
  rcases D3 n h v H1 Hr HE HC with ⟨l2, u, H2, H3, S2⟩
  exact ⟨l2, u, H2, H3, S1 ⋙ S2⟩

lemma Good2 (n : Nat) {l : ListBlank (Fin 2)} (h v : Nat) {r tail : ListBlank (Fin 2)}
    (Hl : LC outer n 2 l) (Hr : TC tail h v r) (HE : EndTail tail)
    (Hv : v + 1 < 3 ^ h) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  rcases clear2 Hl Hr Hv with ⟨l1, r1, H1, T1, S1⟩
  rcases D26 n h (v + 1) 6 H1 T1 HE (Or.inr rfl) (by omega) HC with ⟨l2, u, H2, H3, S2⟩
  exact ⟨l2, u, H2, H3, S1 ⋙ S2⟩

lemma Zero11 (n : Nat) {l : ListBlank (Fin 2)} (h : Nat) {r : ListBlank (Fin 2)}
    (Hl : LC outer n 0 l) (Hr : TC ([1, 1] +> default) h 0 r) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  rcases clear0 r Hl with ⟨l1, H1, S1⟩
  rcases Z26 n h 2 H1 Hr (Or.inl rfl) HC with ⟨l2, u, H2, H3, S2⟩
  exact ⟨l2, u, H2, H3, S1 ⋙ S2⟩

lemma RemainderReturn (n h q b : Nat) {l : ListBlank (Fin 2)}
    (Hl : LC outer n (3 * q + b) l) (Hb : b ≤ 2) (Hq : q < 3 ^ h)
    (H0 : b = 0 → 0 < q) (H2 : b = 2 → q + 1 < 3 ^ h) (HC : 3 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> ((e0 ^ h) +> ([0, 1, 1, 0] +> default)))) [target_tm]⊢⁺ (RBar l' default) := by
  rcases TC_steps q Hl (TC_zero ([0, 1, 1, 0] +> default) h) (by omega) with ⟨l1, r1, H1, T1, S1⟩
  have h0q : 0 + q = q := by omega
  rw [h0q] at T1
  have HR : ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l1 (e0 +> r1)) [target_tm]⊢⁺ (RBar l' default) := by
    rcases b with _ | _ | b
    · exact Good0 n h q H1 T1 EndTail.End0110 (H0 rfl) HC
    · exact Good1 n h q H1 T1 EndTail.End0110 HC
    · have hb0 : b = 0 := by omega
      subst hb0
      exact Good2 n h q H1 T1 EndTail.End0110 (H2 rfl) HC
  rcases HR with ⟨l2, u, HL, HG, HS⟩
  exact ⟨l2, u, HL, HG, stepStar_stepPlus_stepPlus S1 HS⟩

lemma remaining_safe (n h p : Nat) (Hp : p ≤ 1) (HC : 6 * 3 ^ h + p ≤ 2 ^ n) (HT : 2 ^ n + 1 + p < 9 * 3 ^ h) :
    ∃ q b, 2 ^ n - 6 * 3 ^ h + p = 3 * q + b ∧ b ≤ 2 ∧ q < 3 ^ h ∧
      (b = 0 → 0 < q) ∧ (b = 2 → q + 1 < 3 ^ h) := by
  cases p with
  | zero =>
    rcases hard2_remainder n h (by omega) (by omega) with ⟨q, ⟨HQ, Hq⟩ | ⟨HQ, Hq⟩⟩
    · refine ⟨q, 1, ?_, ?_, Hq, ?_, ?_⟩ <;> omega
    · refine ⟨q, 2, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  | succ p =>
    have hp0 : p = 0 := by omega
    subst hp0
    rcases hard0_remainder n h (by omega) (by omega) with ⟨q, ⟨HQ, Hq, Hq'⟩ | ⟨HQ, Hq⟩⟩
    · refine ⟨q, 0, ?_, ?_, Hq', ?_, ?_⟩ <;> omega
    · refine ⟨q, 2, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

lemma HardScan (n h p : Nat) {l : ListBlank (Fin 2)}
    (Hp : p ≤ 1) (HC : 6 * 3 ^ h + p ≤ 2 ^ n)
    (Hl : LC outer (n + 2) (2 ^ (n + 2) - (6 - 4 * p)) l) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (RBar l ((e0 ^ h) +> ([0, 1] +> default))) [target_tm]⊢⁺ (RBar l' default) := by
  have Hd : 6 - 4 * p = 2 ∨ 6 - 4 * p = 6 := by omega
  have HC3 : 3 * 3 ^ h ≤ 2 ^ n := by omega
  rcases Zero26 n h (6 - 4 * p) ([0, 1] +> default) Hd HC3 Hl with ⟨l1, H1, S1⟩
  have HK : 2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h + (12 - (6 - 4 * p))) =
      2 ^ (1 + h) * (1 + (2 ^ n - 3 * 3 ^ h + 1 + p) * 2) := by
    have h1 : 4 * 2 ^ n - 12 * 3 ^ h + (12 - (6 - 4 * p)) = 2 * (1 + (2 ^ n - 3 * 3 ^ h + 1 + p) * 2) := by omega
    have h2 : 2 ^ (1 + h) = 2 ^ h * 2 := by rw [Nat.add_comm 1 h, Nat.pow_succ]
    rw [h1, h2]
    ring
  by_cases HT : 9 * 3 ^ h ≤ 2 ^ n + 1 + p
  · have HG : 4 * 6 ^ (1 + h) < 2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h + (12 - (6 - 4 * p))) := by
      rw [HK]
      apply (normal_budget (1 + h) (2 ^ n - 3 * 3 ^ h + 1 + p)).mpr
      have : 3 ^ (1 + h) = 3 * 3 ^ h := by rw [Nat.add_comm 1 h, Nat.pow_succ]; ring
      (try omega)
    rcases terminal (1 + h) (2 ^ n - 3 * 3 ^ h + 1 + p) EndTail.End01 H1 HK HG with ⟨l2, u, HL, HB, HS⟩
    have hn_eq : (n + h + 2) + 1 = n + h + 3 := by omega
    rw [hn_eq] at HL HB
    exact ⟨l2, u, HL, HB, stepStar_stepPlus_stepPlus S1 HS⟩
  · have HT' : 2 ^ n + 1 + p < 9 * 3 ^ h := by omega
    have HB : LC outer (n + h + 2) (2 ^ (1 + h) * (1 + (1 + 3 * 3 ^ h + (2 ^ n - 6 * 3 ^ h + p)) * 2)) l1 := by
      have hk_eq : 2 ^ h * (4 * 2 ^ n - 12 * 3 ^ h + (12 - (6 - 4 * p))) =
          2 ^ (1 + h) * (1 + (1 + 3 * 3 ^ h + (2 ^ n - 6 * 3 ^ h + p)) * 2) := by
        rw [HK]
        have : 1 + 3 * 3 ^ h + (2 ^ n - 6 * 3 ^ h + p) = 2 ^ n - 3 * 3 ^ h + 1 + p := by omega
        rw [this]
      rw [← hk_eq]; exact H1
    rcases HardEntry n h (2 ^ n - 6 * 3 ^ h + p) HB with ⟨l2, H2, S2⟩
    rcases remaining_safe n h p Hp HC HT' with ⟨q, b, HQ, Hb, Hq, H0, Htwo⟩
    have HL : LC outer n (3 * q + b) l2 := by rw [← HQ]; exact H2
    rcases RemainderReturn n h q b HL Hb Hq H0 Htwo HC3 with ⟨l3, u, H3, H4, S3⟩
    exact ⟨l3, u, H3, H4, stepStar_stepPlus_stepPlus S1 (S2 ⋙ S3)⟩

lemma Hard0 (n : Nat) {l : ListBlank (Fin 2)} (h : Nat) {r : ListBlank (Fin 2)}
    (Hl : LC outer n 0 l) (Hr : TC ([0, 1] +> default) h 0 r) (HC : 6 * 3 ^ h + 1 ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  rw [TC_zero_unique Hr]
  rcases clear0 ((e0 ^ h) +> ([0, 1] +> default)) Hl with ⟨l1, H1, S1⟩
  rcases HardScan n h 1 (by omega) HC H1 with ⟨l2, u, H2, H3, S2⟩
  exact ⟨l2, u, H2, H3, S1 ⋙ S2⟩

lemma Hard2 (n : Nat) {l : ListBlank (Fin 2)} (h : Nat) {r : ListBlank (Fin 2)}
    (Hl : LC outer n 2 l) (Hr : TC ([1, 1] +> default) h (3 ^ h - 1) r) (HC : 6 * 3 ^ h ≤ 2 ^ n) :
    ∃ l' u, LC outer (n + h + 3) (3 + u * 2) l' ∧ 6 + u * 2 ≤ 2 ^ (n + h + 3) ∧
      (QBar l (e0 +> r)) [target_tm]⊢⁺ (RBar l' default) := by
  rcases clear2_full default Hl Hr with ⟨l1, r1, H1, T1, S1⟩
  rw [TC_zero_unique T1] at S1
  rcases HardScan n h 0 (by omega) (by omega) H1 with ⟨l2, u, H2, H3, S2⟩
  exact ⟨l2, u, H2, H3, S1 ⋙ S2⟩

lemma Bo_return (n : Nat) (c : Cfg (Fin 2) (Fin 6))
    (H : ∃ l u, LC outer n (3 + u * 2) l ∧ 6 + u * 2 ≤ 2 ^ n ∧ c [target_tm]⊢⁺ (RBar l default)) :
    ∃ c', (c [target_tm]⊢⁺ c') ∧ Allowed c' := by
  rcases H with ⟨l, u, Hl, Hg, HS⟩
  exact ⟨RBar l default, HS, Allowed.Bo n u l Hl Hg⟩

lemma S11_all (n k h v : Nat) (l r : ListBlank (Fin 2))
    (Hl : LC outer n k l) (Hr : TC ([1, 1] +> default) h v r)
    (Hg : k + v * 3 + 3 * 3 ^ h + 1 ≤ 2 ^ n) :
    ∃ c', ((QBar l (e0 +> r)) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  rcases k with _ | _ | _ | k
  · cases v with
    | zero => exact Bo_return (n + h + 3) _ (Zero11 n h Hl Hr (by omega))
    | succ v => exact Bo_return (n + h + 3) _ (Good0 n h (v + 1) Hl Hr EndTail.End11 (by omega) (by omega))
  · exact Bo_return (n + h + 3) _ (Good1 n h v Hl Hr EndTail.End11 (by omega))
  · by_cases Hv : v + 1 < 3 ^ h
    · exact Bo_return (n + h + 3) _ (Good2 n h v Hl Hr EndTail.End11 Hv (by omega))
    · have hb := TC_bound Hr
      have Ev : v = 3 ^ h - 1 := by omega
      subst Ev
      exact Bo_return (n + h + 3) _ (Hard2 n h Hl Hr (by omega))
  · have Hl' : LC outer n (3 + k) l := by
      have : 3 + k = k + 3 := by omega
      rw [this]; exact Hl
    exact S11_step n k h v l r Hl' Hr (by omega)

lemma S01_all (n k h v : Nat) (l r : ListBlank (Fin 2))
    (Hl : LC outer n k l) (Hr : TC ([0, 1] +> default) h v r)
    (Hg : k + v * 3 + 6 * 3 ^ h + 1 ≤ 2 ^ n) :
    ∃ c', ((QBar l (e0 +> r)) [target_tm]⊢⁺ c') ∧ Allowed c' := by
  rcases k with _ | _ | _ | k
  · cases v with
    | zero => exact Bo_return (n + h + 3) _ (Hard0 n h Hl Hr (by omega))
    | succ v => exact Bo_return (n + h + 3) _ (Good0 n h (v + 1) Hl Hr EndTail.End01 (by omega) (by omega))
  · exact Bo_return (n + h + 3) _ (Good1 n h v Hl Hr EndTail.End01 (by omega))
  · by_cases Hv : v + 1 < 3 ^ h
    · exact Bo_return (n + h + 3) _ (Good2 n h v Hl Hr EndTail.End01 Hv (by omega))
    · have hb := TC_bound Hr
      have Ev : v = 3 ^ h - 1 := by omega
      subst Ev
      exact S01_exit n 0 h l r Hl Hr (by omega)
  · have Hl' : LC outer n (3 + k) l := by
      have : 3 + k = k + 3 := by omega
      rw [this]; exact Hl
    exact S01_step n k h v l r Hl' Hr (by omega)

lemma Allowed_step (c : Cfg (Fin 2) (Fin 6)) (H : Allowed c) :
    ∃ c', (c [target_tm]⊢⁺ c') ∧ Allowed c' := by
  cases H with
  | Bo n v l Hl Hg => exact Bo_step n v l Hl Hg
  | Be m a u l Hl Hg => exact Be_step m a u l Hl Hg
  | S11 n k h v l r Hl Hr Hg => exact S11_all n k h v l r Hl Hr Hg
  | S01 n k h v l r Hl Hr Hg => exact S01_all n k h v l r Hl Hr Hg

-- ============================================================================
-- Section 17: Computable `CCfg` 333-Step Startup & Nonhalt Theorem
-- ============================================================================

open Counter in
def ccfg_init : CCfg (Fin 2) (Fin 6) := ⟨A, 0, [], []⟩
open Counter in
def ccfg_333 : CCfg (Fin 2) (Fin 6) :=
  ⟨B, 0, [1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩

open Counter in
set_option maxRecDepth 4000000 in
lemma bmultiStep_333 : bmultiStep target_tm 333 ccfg_init = some ccfg_333 := by decide

def l_init : ListBlank (Fin 2) :=
  w011 +> (w011 +> (w111 +> (w011 +> (w011 +> outer))))

lemma l_init_LC : LC outer 5 27 l_init :=
  LC.d1 4 13 _ (LC.d1 3 6 _ (LC.d0 2 3 _ (LC.d1 1 1 _ (LC.d1 0 0 outer (LC.nil : LC outer 0 0 outer)))))

open Counter in
lemma entry_tm7 : (init []) [target_tm]⊢* (RBar l_init default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = evalBCfg ccfg_init := rfl
  have h_end : evalBCfg ccfg_333 = RBar l_init default := by
    unfold evalBCfg evalWindow ccfg_333 RBar l_init w011 w111 outer
    simp only [cons_append_lb, append_nil_lb]
    rfl
  rw [h_init, ← h_end]
  exact ⟨333, bmultiStep_sound 333 ccfg_init ccfg_333 bmultiStep_333⟩

end Solution

open Counter

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
theorem is_does_not_halt : IsNotHalt target_tm :=
  does_not_halt_of_invariant Allowed
    ⟨RBar l_init default, entry_tm7, Allowed.Bo 5 12 l_init l_init_LC (by decide)⟩
    Allowed_step

end BusyBeaver.M_1RB1RC_1LC1RE_HHH1LD_0LE0LD_1RA0RF_1LD1RB
