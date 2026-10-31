/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC0LF_0RA---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC0LF_0RA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC0LF_0RAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC0LF_0RA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 800000
variable {α β γ : Type*} [Inhabited α] [Inhabited β] [Inhabited γ]

namespace Solution
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 800000

set_option autoImplicit true
set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

def tm15 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 1 => none

def perm_0365 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 5

def map_cfg_0365 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map perm_0365, ⟨c.tape.1, c.tape.right, c.tape.left⟩⟩

lemma step_map_0365 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (map_cfg_0365 c) = (step tm15 c).map map_cfg_0365 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;> try rfl
  all_goals omega

@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma multiStep_map_0365 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (map_cfg_0365 c) n = (multiStep tm15 c n).map map_cfg_0365 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zMs, zMs, ih]
    cases multiStep tm15 c n with
    | none => rfl
    | some c' => exact step_map_0365 c'

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
set_option linter.unusedSectionVars false
@[simp] lemma zPz (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z0j (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
lemma z0k (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [z0j, Nat.succ_add, ih, List.append_assoc]
lemma z0l (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) := by
  induction n with
  | zero => simp [z0j]
  | succ n ih => simp [z0j, List.append_assoc, ih]
def z0o (d0 d1 : zF) : Nat → Nat → zB → zB
  | 0, _, r => r
  | len + 1, n, r => (if n % 2 = 0 then d1 else d0) +> z0o d0 d1 len (n / 2) r

def MC : Nat → Nat → zB → zB
  | 0, n, r => (if n % 2 = 0 then [1] else [0]) +> r
  | h + 1, n, r => (if n % 2 = 0 then [1, 0, 0] else [0, 0, 0]) +> MC h (n / 2) r

lemma z0s (d0 d1 : zF) (len n : Nat) (r : zB) :
    z0o d0 d1 (len + 1) (n * 2) r = d1 +> z0o d0 d1 len n r := by
  simp only [z0o]
  have h1 : (n * 2) % 2 = 0 := by omega
  have h2 : (n * 2) / 2 = n := by omega
  simp [h1, h2]
lemma z0t (d0 d1 : zF) (len n : Nat) (r : zB) :
    z0o d0 d1 (len + 1) (n * 2 + 1) r = d0 +> z0o d0 d1 len n r := by
  simp only [z0o]
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1, h2]
lemma z0u (d0 d1 : zF) (len : Nat) (r : zB) :
    z0o d0 d1 len 0 r = (d1 ^ len) +> r := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have h := z0s d0 d1 len 0 r
    simp only [Nat.zero_mul] at h
    rw [h, ih, z0j, append_assoc]
lemma z0v (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n
lemma z0w (d0 d1 : zF) (len : Nat) (r : zB) :
    z0o d0 d1 len (2 ^ len - 1) r = (d0 ^ len) +> r := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hp := z0v len
    have h1 : 2 ^ (len + 1) - 1 = (2 ^ len - 1) * 2 + 1 := by
      rw [Nat.pow_succ]; omega
    rw [h1, z0t, ih, z0j, append_assoc]
lemma z0x (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0o d0 d1 (len + i) (n * 2 ^ i) r = (d1 ^ i) +> z0o d0 d1 len n r := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : len + (i + 1) = (len + i) + 1 := by omega
    have h2 : n * 2 ^ (i + 1) = (n * 2 ^ i) * 2 := by rw [Nat.pow_succ, ← Nat.mul_assoc]
    rw [h1, h2, z0s, ih, z0j, append_assoc]
lemma z0y' (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0o d0 d1 (len + i) ((n + 1) * 2 ^ i - 1) r =
    (d0 ^ i) +> z0o d0 d1 len n r := by
  induction i with
  | zero =>
    have h1 : (n + 1) * 2 ^ 0 - 1 = n := by omega
    simp [h1]
  | succ i ih =>
    have hp := z0v i
    have hpos : 1 ≤ (n + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : len + (i + 1) = (len + i) + 1 := by omega
    have h2 : (n + 1) * 2 ^ (i + 1) - 1 = ((n + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [h1, h2, z0t, ih, z0j, append_assoc]

abbrev ld0 : zF := [0, 1, 1, 1]
abbrev ld1 : zF := [1, 1, 1, 1]
abbrev rd0 : zF := [0, 0, 0]
abbrev rd1 : zF := [1, 0, 0]

lemma MC_s (h n : Nat) (r : zB) :
    MC (h + 1) (n * 2) r = rd1 +> MC h n r := by
  simp only [MC, rd1]
  have h1 : (n * 2) % 2 = 0 := by omega
  have h2 : (n * 2) / 2 = n := by omega
  simp [h1, h2]
lemma MC_t (h n : Nat) (r : zB) :
    MC (h + 1) (n * 2 + 1) r = rd0 +> MC h n r := by
  simp only [MC, rd0]
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1, h2]
lemma MC_lsb_0 (h n i : Nat) (r : zB) :
    MC (h + i) (n * 2 ^ i) r = (rd1 ^ i) +> MC h n r := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : h + (i + 1) = (h + i) + 1 := by omega
    have h2 : n * 2 ^ (i + 1) = (n * 2 ^ i) * 2 := by rw [Nat.pow_succ, ← Nat.mul_assoc]
    rw [h1, h2, MC_s, ih, z0j, append_assoc]
lemma MC_lsb_1 (h n i : Nat) (r : zB) :
    MC (h + i) ((n + 1) * 2 ^ i - 1) r = (rd0 ^ i) +> MC h n r := by
  induction i with
  | zero =>
    have h1 : (n + 1) * 2 ^ 0 - 1 = n := by omega
    simp [h1]
  | succ i ih =>
    have hp := z0v i
    have hpos : 1 ≤ (n + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : h + (i + 1) = (h + i) + 1 := by omega
    have h2 : (n + 1) * 2 ^ (i + 1) - 1 = ((n + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [h1, h2, MC_t, ih, z0j, append_assoc]
lemma MC_base_0 (h : Nat) (r : zB) :
    MC h 0 r = (rd1 ^ h) +> [1] +> r := by
  have := MC_lsb_0 0 0 h r
  simp only [Nat.zero_add, Nat.zero_mul] at this
  rw [this]; rfl
lemma MC_base_1 (h : Nat) (r : zB) :
    MC h (2 ^ (h + 1) - 1) r = (rd0 ^ h) +> [0] +> r := by
  have hp := z0v h
  have h1 : 2 ^ (h + 1) - 1 = (1 + 1) * 2 ^ h - 1 := by rw [Nat.pow_succ]; omega
  rw [h1]
  have := MC_lsb_1 0 1 h r
  simp only [Nat.zero_add] at this
  rw [this]; rfl

lemma z0M (d0 d1 : zF) (len n : Nat) (r : zB)
    (h : 1 + n < 2 ^ len) :
    ∃ (i : Nat) (s : zB),
      z0o d0 d1 len (1 + n) r = (d1 ^ i) +> d0 +> s ∧
      z0o d0 d1 len n r = (d0 ^ i) +> d1 +> s := by
  induction len generalizing n with
  | zero => simp at h
  | succ len ih =>
    have hp : 2 ^ (len + 1) = 2 ^ len * 2 := Nat.pow_succ 2 len
    let k := n / 2
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have h_even : n = k * 2 := by omega
      have h_odd : 1 + n = k * 2 + 1 := by omega
      refine ⟨0, z0o d0 d1 len k r, ?_, ?_⟩
      · rw [h_odd, z0t]; rfl
      · rw [h_even, z0s]; rfl
    · have h_odd : n = k * 2 + 1 := by omega
      have h_even : 1 + n = (1 + k) * 2 := by omega
      have h_lt : 1 + k < 2 ^ len := by omega
      rcases ih k h_lt with ⟨i, s, hi1, hi0⟩
      refine ⟨i + 1, s, ?_, ?_⟩
      · rw [h_even, z0s, hi1, z0j, append_assoc]
      · rw [h_odd, z0t, hi0, z0j, append_assoc]

lemma MC_dec (h n : Nat) (r : zB) (hn : 1 + n < 2 ^ (h + 1)) :
    ∃ (i : Nat) (s : zB),
      MC h (1 + n) r = (rd1 ^ i) +> [0] +> s ∧
      MC h n r = (rd0 ^ i) +> [1] +> s := by
  induction h generalizing n with
  | zero =>
    have hn0 : n = 0 := by simp at hn; omega
    subst hn0
    exact ⟨0, r, rfl, rfl⟩
  | succ h ih =>
    have hp : 2 ^ (h + 1 + 1) = 2 ^ (h + 1) * 2 := Nat.pow_succ 2 (h + 1)
    let k := n / 2
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have h_even : n = k * 2 := by omega
      have h_odd : 1 + n = k * 2 + 1 := by omega
      refine ⟨0, [0, 0] +> MC h k r, ?_, ?_⟩
      · rw [h_odd, MC_t]; rfl
      · rw [h_even, MC_s]; rfl
    · have h_odd : n = k * 2 + 1 := by omega
      have h_even : 1 + n = (1 + k) * 2 := by omega
      have h_lt : 1 + k < 2 ^ (h + 1) := by omega
      rcases ih k h_lt with ⟨i, s, hi1, hi0⟩
      refine ⟨i + 1, s, ?_, ?_⟩
      · rw [h_even, MC_s, hi1, z0j, append_assoc]
      · rw [h_odd, MC_t, hi0, z0j, append_assoc]

lemma zSm (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z0P (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1, zSm tm c_1 c_2 h⟩
lemma z0Q (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa (tm : Machine Γ Λ) (c_1 : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt (tm : Machine Γ Λ) (c_1 c_2 c_3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPs {tm : Machine Γ Λ} {c_1 c_2 : Cfg Γ Λ} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma z0R {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z0S {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z0T {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z0R (z0Q tm c_1 c_2 h₁) h₂

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step_tm" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z0T (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z0i, zDh, zDt])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)

lemma sh_0_sound (n : Nat) (l r : zB) :
    (l {{A}}> ((rd1 ^ n) +> r)) [tm15]⊢* ((([1, 1, 1] ^ n) +> l) {{A}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{A}}> (rd1 +> (rd1 ^ n) +> r)) [tm15]⊢*
        (([1, 1, 1] +> l) {{A}}> ((rd1 ^ n) +> r)) := by
      dsimp [rd1, ListBlank.append]; execute
    have h2 := ih ([1, 1, 1] +> l) r
    rw [<- append_assoc ([1, 1, 1] ^ n) [1, 1, 1] l, z0l] at h2
    exact zSt h1 h2

lemma sh_1_sound (n : Nat) (l r : zB) :
    ((([1] ^ n) +> l) <{{B}} r) [tm15]⊢* (l <{{B}} (([0] ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (([1] +> ([1] ^ n) +> l) <{{B}} r) [tm15]⊢*
        ((([1] ^ n) +> l) <{{B}} ([0] +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([0] +> r)
    rw [<- append_assoc ([0] ^ n) [0] r, z0l] at h2
    exact zSt h1 h2

lemma sh_2_sound (n : Nat) (l r : zB) :
    ((([1, 1] ^ n) +> l) <{{C}} r) [tm15]⊢* (l <{{C}} (([1, 0] ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (([1, 1] +> ([1, 1] ^ n) +> l) <{{C}} r) [tm15]⊢*
        ((([1, 1] ^ n) +> l) <{{C}} ([1, 0] +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih l ([1, 0] +> r)
    rw [<- append_assoc ([1, 0] ^ n) [1, 0] r, z0l] at h2
    exact zSt h1 h2

lemma sh_3_sound (n : Nat) (l r : zB) :
    (l {{D}}> (([1] ^ n) +> r)) [tm15]⊢* ((([0] ^ n) +> l) {{D}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{D}}> ([1] +> ([1] ^ n) +> r)) [tm15]⊢*
        (([0] +> l) {{D}}> (([1] ^ n) +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih ([0] +> l) r
    rw [<- append_assoc ([0] ^ n) [0] l, z0l] at h2
    exact zSt h1 h2

lemma sh_4_sound (n : Nat) (l r : zB) :
    (l {{D}}> (([0, 1, 0] ^ n) +> r)) [tm15]⊢* ((([1, 1, 1] ^ n) +> l) {{D}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{D}}> ([0, 1, 0] +> ([0, 1, 0] ^ n) +> r)) [tm15]⊢*
        (([1, 1, 1] +> l) {{D}}> (([0, 1, 0] ^ n) +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih ([1, 1, 1] +> l) r
    rw [<- append_assoc ([1, 1, 1] ^ n) [1, 1, 1] l, z0l] at h2
    exact zSt h1 h2

lemma sh_5_sound (n : Nat) (l r : zB) :
    (l {{D}}> (([0, 1, 0, 1] ^ n) +> r)) [tm15]⊢* (((ld0 ^ n) +> l) {{D}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{D}}> ([0, 1, 0, 1] +> ([0, 1, 0, 1] ^ n) +> r)) [tm15]⊢*
        ((ld0 +> l) {{D}}> (([0, 1, 0, 1] ^ n) +> r)) := by
      dsimp [ld0, ListBlank.append]; execute
    have h2 := ih (ld0 +> l) r
    rw [<- append_assoc (ld0 ^ n) ld0 l, z0l] at h2
    exact zSt h1 h2

lemma sh_6_sound (n : Nat) (l r : zB) :
    (l {{D}}> (([1, 0, 1, 0] ^ n) +> r)) [tm15]⊢* ((([1, 1, 1, 0] ^ n) +> l) {{D}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (l {{D}}> ([1, 0, 1, 0] +> ([1, 0, 1, 0] ^ n) +> r)) [tm15]⊢*
        (([1, 1, 1, 0] +> l) {{D}}> (([1, 0, 1, 0] ^ n) +> r)) := by
      dsimp [ListBlank.append]; execute
    have h2 := ih ([1, 1, 1, 0] +> l) r
    rw [<- append_assoc ([1, 1, 1, 0] ^ n) [1, 1, 1, 0] l, z0l] at h2
    exact zSt h1 h2

def z0U (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  ([1] +> l) <{{C}} ([1, 0, 1, 0] +> r)
def z0V (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  ([1, 0, 1, 1, 1] +> l) {{A}}> r

lemma z10 (n : Nat) (l r : zB) :
    ((([1, 1, 1] ^ n) +> l) <{{B}} r) [tm15]⊢* (l <{{B}} ((rd0 ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (([1, 1, 1] +> ([1, 1, 1] ^ n) +> l) <{{B}} r) [tm15]⊢*
        ((([1, 1, 1] ^ n) +> l) <{{B}} (rd0 +> r)) := by
      dsimp [rd0, ListBlank.append]; execute
    have h2 := ih l (rd0 +> r)
    rw [<- append_assoc (rd0 ^ n) rd0 r, z0l] at h2
    exact zSt h1 h2

lemma z11 (n : Nat) (l r : zB) :
    (([1] +> (ld1 ^ n) +> l) <{{C}} r) [tm15]⊢*
    (([1] +> l) <{{C}} (([1, 0, 1, 0] ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (([1] +> ld1 +> (ld1 ^ n) +> l) <{{C}} r) [tm15]⊢*
        (([1] +> (ld1 ^ n) +> l) <{{C}} ([1, 0, 1, 0] +> r)) := by
      dsimp [ld1, ListBlank.append]; execute
    have h2 := ih l ([1, 0, 1, 0] +> r)
    rw [<- append_assoc ([1, 0, 1, 0] ^ n) [1, 0, 1, 0] r, z0l] at h2
    exact zSt h1 h2

lemma z13 (n : Nat) (l r : zB) :
    (([1, 0, 1, 1, 1] +> l) {{A}}> (([1, 0, 1, 0] ^ n) +> r)) [tm15]⊢*
    (([1, 0, 1, 1, 1] +> (ld0 ^ n) +> l) {{A}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [z0j, append_assoc]
    have h1 : (([1, 0, 1, 1, 1] +> l) {{A}}> ([1, 0, 1, 0] +> ([1, 0, 1, 0] ^ n) +> r)) [tm15]⊢*
        (([1, 0, 1, 1, 1] +> ld0 +> l) {{A}}> (([1, 0, 1, 0] ^ n) +> r)) := by
      dsimp [ld0, ListBlank.append]; execute
    have h2 := ih (ld0 +> l) r
    rw [<- append_assoc (ld0 ^ n) ld0 l, z0l] at h2
    exact zSt h1 h2

lemma z15 (l r : zB) (n : Nat) :
    (z0U ((ld1 ^ n) +> ld0 +> l) r) [tm15]⊢⁺
    (z0V ((ld0 ^ n) +> ld1 +> l) r) := by
  unfold z0U z0V
  have h1 := z11 n (ld0 +> l) ([1, 0, 1, 0] +> r)
  have h_eq : (([1, 0, 1, 0] ^ n) +> [1, 0, 1, 0] +> r) = ([1, 0, 1, 0] +> ([1, 0, 1, 0] ^ n) +> r) := by
    rw [<- append_assoc ([1, 0, 1, 0] ^ n) [1, 0, 1, 0] r, z0l, z0j, append_assoc]
  rw [h_eq] at h1
  have h2 : (([1] +> ld0 +> l) <{{C}} ([1, 0, 1, 0] +> ([1, 0, 1, 0] ^ n) +> r)) [tm15]⊢⁺
      (([1, 0, 1, 1, 1] +> ld1 +> l) {{A}}> (([1, 0, 1, 0] ^ n) +> r)) := by
    dsimp [ld0, ld1, ListBlank.append]; execute
  have h3 := z13 n (ld1 +> l) r
  exact z0R (z0S h1 h2) h3

lemma z15_absorb (l r : zB) (n : Nat) :
    (z0U ((ld1 ^ n) +> [1, 0, 1, 1] +> l) r) [tm15]⊢⁺
    (z0V ((ld0 ^ (n + 1)) +> l) r) := by
  unfold z0U z0V
  have h1 := z11 n ([1, 0, 1, 1] +> l) ([1, 0, 1, 0] +> r)
  have h_eq : (([1, 0, 1, 0] ^ n) +> [1, 0, 1, 0] +> r) = ([1, 0, 1, 0] +> ([1, 0, 1, 0] ^ n) +> r) := by
    rw [<- append_assoc ([1, 0, 1, 0] ^ n) [1, 0, 1, 0] r, z0l, z0j, append_assoc]
  rw [h_eq] at h1
  have h2 : (([1] +> [1, 0, 1, 1] +> l) <{{C}} ([1, 0, 1, 0] +> ([1, 0, 1, 0] ^ n) +> r)) [tm15]⊢⁺
      (([1, 0, 1, 1, 1] +> ld0 +> l) {{A}}> (([1, 0, 1, 0] ^ n) +> r)) := by
    dsimp [ld0, ListBlank.append]; execute
  have h3 := z13 n (ld0 +> l) r
  rw [<- append_assoc (ld0 ^ n) ld0 l, z0l] at h3
  exact z0R (z0S h1 h2) h3

lemma z16 (l r : zB) (n : Nat) :
    (z0V l ((rd1 ^ n) +> [0] +> r)) [tm15]⊢⁺
    (z0U l ((rd0 ^ n) +> [1] +> r)) := by
  unfold z0V z0U
  have h1 := sh_0_sound n ([1, 0, 1, 1, 1] +> l) ([0] +> r)
  have h2 : ((([1, 1, 1] ^ n) +> [1, 0, 1, 1, 1] +> l) {{A}}> ([0] +> r)) [tm15]⊢⁺
      ((([1, 1, 1] ^ n) +> [1, 0, 1, 1, 1] +> l) <{{B}} ([1] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h3 := z10 n ([1, 0, 1, 1, 1] +> l) ([1] +> r)
  have h4 : (([1, 0, 1, 1, 1] +> l) <{{B}} ((rd0 ^ n) +> [1] +> r)) [tm15]⊢*
      (([1] +> l) <{{C}} ([1, 0, 1, 0] +> (rd0 ^ n) +> [1] +> r)) := by
    dsimp [ListBlank.append]; execute
  exact z0R (z0R (z0S h1 h2) h3) h4

lemma z1H (len k : Nat) (l r : zB) (h : 1 + k < 2 ^ len) :
    (z0U (z0o ld0 ld1 len (1 + k) l) r) [tm15]⊢⁺ (z0V (z0o ld0 ld1 len k l) r) := by
  rcases z0M ld0 ld1 len k l h with ⟨i, s, hi1, hi0⟩
  rw [hi1, hi0]
  exact z15 s r i

lemma z1J (h n : Nat) (l r : zB) (hn : 1 + n < 2 ^ (h + 1)) :
    (z0V l (MC h (1 + n) r)) [tm15]⊢⁺ (z0U l (MC h n r)) := by
  rcases MC_dec h n r hn with ⟨i, s, hi1, hi0⟩
  rw [hi1, hi0]
  exact z16 l s i

lemma pair_general (len val_l h val_r c : Nat) (l r : zB)
    (hl : val_l + c < 2 ^ len) (hr : val_r + c < 2 ^ (h + 1)) :
    (z0V (z0o ld0 ld1 len (val_l + c) l) (MC h (val_r + c) r)) [tm15]⊢*
    (z0V (z0o ld0 ld1 len val_l l) (MC h val_r r)) := by
  induction c with
  | zero => exact ⟨0, rfl⟩
  | succ c ih =>
    have h1 : val_r + (c + 1) = 1 + (val_r + c) := by omega
    have h2 : val_l + (c + 1) = 1 + (val_l + c) := by omega
    rw [h1, h2]
    have s1 := zPs (z1J h (val_r + c) (z0o ld0 ld1 len (1 + (val_l + c)) l) r (by omega))
    have s2 := zPs (z1H len (val_l + c) l (MC h (val_r + c) r) (by omega))
    have s3 := ih (by omega) (by omega)
    exact zSt (zSt s1 s2) s3

lemma absorb_step (L h val_r : Nat) (l r : zB) (hr : val_r + 2 ^ L < 2 ^ (h + 1)) :
    (z0V ((ld0 ^ L) +> [1, 0, 1, 1] +> l) (MC h (val_r + 2 ^ L) r)) [tm15]⊢*
    (z0V ((ld0 ^ (L + 1)) +> l) (MC h val_r r)) := by
  have hp := z0v L
  have h1 : (ld0 ^ L) +> [1, 0, 1, 1] +> l = z0o ld0 ld1 L (0 + (2 ^ L - 1)) ([1, 0, 1, 1] +> l) := by
    rw [Nat.zero_add, z0w]
  have h2 : val_r + 2 ^ L = (1 + val_r) + (2 ^ L - 1) := by omega
  rw [h1, h2]
  have s1 := pair_general L 0 h (1 + val_r) (2 ^ L - 1) ([1, 0, 1, 1] +> l) r (by omega) (by omega)
  rw [z0u] at s1
  have s2 := zPs (z1J h val_r ((ld1 ^ L) +> [1, 0, 1, 1] +> l) r (by omega))
  have s3 := zPs (z15_absorb l (MC h val_r r) L)
  exact zSt (zSt s1 s2) s3

lemma absorb_loop (L m' h val_r : Nat) (l r : zB)
    (hr : val_r + (2 ^ m' - 1) * 2 ^ L < 2 ^ (h + 1)) :
    (z0V ((ld0 ^ L) +> ([1, 0, 1, 1] ^ m') +> l) (MC h (val_r + (2 ^ m' - 1) * 2 ^ L) r)) [tm15]⊢*
    (z0V ((ld0 ^ (L + m')) +> l) (MC h val_r r)) := by
  induction m' generalizing L val_r with
  | zero =>
    have h0 : (2 ^ 0 - 1) * 2 ^ L = 0 := by simp
    simp only [h0, Nat.add_zero, zPz, append_nil]
    exact ⟨0, rfl⟩
  | succ m' ih =>
    have hm := z0v m'
    have hLpos := z0v L
    have halg : (2 ^ (m' + 1) - 1) * 2 ^ L = (2 ^ m' - 1) * 2 ^ (L + 1) + 2 ^ L := by
      have h1 : 2 ^ (m' + 1) - 1 = (2 ^ m' - 1) * 2 + 1 := by rw [Nat.pow_succ]; omega
      rw [h1, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ L), ← Nat.pow_succ]
    have hsum : val_r + (2 ^ (m' + 1) - 1) * 2 ^ L = (val_r + (2 ^ m' - 1) * 2 ^ (L + 1)) + 2 ^ L := by
      omega
    rw [z0j, append_assoc, hsum]
    have s1 := absorb_step L h (val_r + (2 ^ m' - 1) * 2 ^ (L + 1)) (([1, 0, 1, 1] ^ m') +> l) r (by omega)
    have s2 := ih (L + 1) val_r (by omega)
    have hL : L + 1 + m' = L + (m' + 1) := by omega
    rw [hL] at s2
    exact zSt s1 s2

lemma absorb_general (n m' h val_r : Nat) (l r : zB)
    (hr : val_r + (1 + (2 ^ m' - 1) * 2 ^ (n + 1)) < 2 ^ (h + 1)) :
    (z0V ((ld1 ^ n) +> ([1, 0, 1, 1] ^ (m' + 1)) +> l)
      (MC h (val_r + (1 + (2 ^ m' - 1) * 2 ^ (n + 1))) r)) [tm15]⊢*
    (z0V ((ld0 ^ (n + (m' + 1))) +> l) (MC h val_r r)) := by
  rw [z0j, append_assoc]
  have hsum : val_r + (1 + (2 ^ m' - 1) * 2 ^ (n + 1)) = 1 + (val_r + (2 ^ m' - 1) * 2 ^ (n + 1)) := by omega
  rw [hsum]
  have s1 := zPs (z1J h (val_r + (2 ^ m' - 1) * 2 ^ (n + 1)) ((ld1 ^ n) +> [1, 0, 1, 1] +> ([1, 0, 1, 1] ^ m') +> l) r (by omega))
  have s2 := zPs (z15_absorb (([1, 0, 1, 1] ^ m') +> l) (MC h (val_r + (2 ^ m' - 1) * 2 ^ (n + 1)) r) n)
  have s3 := absorb_loop (n + 1) m' h val_r l r (by omega)
  have hL : n + 1 + m' = n + (m' + 1) := by omega
  rw [hL] at s3
  exact zSt (zSt s1 s2) s3

-- ============================================================================
-- Section 2: Block / Stack / PartList Engine & Soundness
-- ============================================================================

structure Block where
  pat : Nat
  width : Nat
  len : Nat
  deriving DecidableEq

abbrev Stack := List Block

def rot1 (w p : Nat) : Nat :=
  p / 2 + (p % 2) * (2 ^ (w - 1))

def rot_k (w : Nat) : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => rot_k w k (rot1 w p)

def rot_mod (w n p : Nat) : Nat :=
  if (p == 0 || (w == 1 && p == 1)) = true then p
  else if rot_k w w p = p then rot_k w (n % w) p else rot_k w n p

lemma rot_k_add (w a b p : Nat) : rot_k w (a + b) p = rot_k w b (rot_k w a p) := by
  induction a generalizing p with
  | zero => simp [rot_k]
  | succ a ih => simp [rot_k, Nat.succ_add, ih]

lemma rot_k_period (w p : Nat) (h : rot_k w w p = p) (q r : Nat) :
    rot_k w (w * q + r) p = rot_k w r p := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : w * (q + 1) + r = w + (w * q + r) := by
      rw [Nat.mul_succ]; omega
    rw [h1, rot_k_add, h, ih]

lemma rot_k_zero (w n : Nat) : rot_k w n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rot_k, rot1] using! ih

lemma rot_k_one_one (n : Nat) : rot_k 1 n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rot_k, rot1] using! ih

lemma rot_mod_eq (w n p : Nat) : rot_mod w n p = rot_k w n p := by
  unfold rot_mod
  split_ifs with h0 h
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h0
    rcases h0 with rfl | ⟨rfl, rfl⟩
    · exact (rot_k_zero w n).symm
    · exact (rot_k_one_one n).symm
  · have hdiv := Nat.div_add_mod n w
    conv_rhs => rw [← hdiv]
    exact (rot_k_period w p h (n / w) (n % w)).symm
  · rfl

def bit_of (x : Nat) : Fin 2 := if x % 2 = 1 then 1 else 0

def expand_pat (w p : Nat) : Nat → zB → zB
  | 0, r => r
  | n + 1, r => bit_of p >> expand_pat w (rot1 w p) n r

def stack_to_tape : Stack → zB
  | [] => default
  | b :: rest => expand_pat b.width b.pat b.len (stack_to_tape rest)

lemma expand_pat_add (w p a b : Nat) (r : zB) :
    expand_pat w p (a + b) r = expand_pat w p a (expand_pat w (rot_k w a p) b r) := by
  induction a generalizing p with
  | zero => simp [expand_pat, rot_k]
  | succ a ih => simp only [Nat.succ_add, expand_pat, rot_k, ih]

lemma expand_pat_zero_pat (w n : Nat) : expand_pat w 0 n default = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : rot1 w 0 = 0 := by simp [rot1]
    have h2 : bit_of 0 = 0 := rfl
    simp only [expand_pat, h1, h2, ih, z0i]

def with_nat {α : Type} (e : Nat) (f : Nat → α) : α :=
  Nat.casesOn e (f 0) (fun n => f (Nat.succ n))

@[simp] lemma with_nat_eq {α : Type} (e : Nat) (f : Nat → α) : with_nat e f = f e := by
  cases e <;> rfl

def with_list {α β : Type} (xs : List β) (f : List β → α) : α :=
  List.casesOn xs (f []) (fun h t => f (h :: t))

@[simp] lemma with_list_eq {α β : Type} (xs : List β) (f : List β → α) : with_list xs f = f xs := by
  cases xs <;> rfl

def with_prod {α β γ : Type} (p : α × β) (f : α × β → γ) : γ :=
  Prod.casesOn p (fun a b => f (a, b))

@[simp] lemma with_prod_eq {α β γ : Type} (p : α × β) (f : α × β → γ) : with_prod p f = f p := by
  cases p; rfl

def with_block {α : Type} (b : Block) (f : Block → α) : α :=
  Block.casesOn b (fun pat width len =>
    with_nat pat (fun p =>
      with_nat width (fun w =>
        with_nat len (fun l =>
          f ⟨p, w, l⟩))))

@[simp] lemma with_block_eq {α : Type} (b : Block) (f : Block → α) : with_block b f = f b := by
  cases b; simp [with_block]

def with_stack {α : Type} (s : Stack) (f : Stack → α) : α :=
  List.casesOn s (f []) (fun top rest =>
    with_block top (fun top' => f (top' :: rest)))

@[simp] lemma with_stack_eq {α : Type} (s : Stack) (f : Stack → α) : with_stack s f = f s := by
  cases s <;> simp [with_stack]

def push_stack_aux (b : Block) : Stack → Stack
  | [] => if b.pat = 0 then [] else [b]
  | top :: rest =>
    if (b.width == top.width && rot_mod b.width b.len b.pat == top.pat) = true then
      with_nat (b.len + top.len) (fun new_len =>
        push_stack_aux ⟨b.pat, b.width, new_len⟩ rest)
    else
      b :: top :: rest

def push_stack (pat width len : Nat) (s : Stack) : Stack :=
  with_stack s (fun s' =>
    if len = 0 then s'
    else
      with_nat pat (fun p =>
        with_nat width (fun w =>
          with_nat len (fun l =>
            push_stack_aux ⟨p, w, l⟩ s'))))

lemma push_stack_aux_sound (b : Block) (s : Stack) :
    stack_to_tape (push_stack_aux b s) = expand_pat b.width b.pat b.len (stack_to_tape s) := by
  induction s generalizing b with
  | nil =>
    unfold push_stack_aux
    split_ifs with h
    · simp only [stack_to_tape, h, expand_pat_zero_pat]
    · rfl
  | cons top rest ih =>
    unfold push_stack_aux
    simp only [with_nat_eq]
    split_ifs with h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [ih, stack_to_tape, expand_pat_add, ← rot_mod_eq, h.2, ← h.1]
    · rfl

lemma push_stack_sound (pat width len : Nat) (s : Stack) :
    stack_to_tape (push_stack pat width len s) = expand_pat width pat len (stack_to_tape s) := by
  unfold push_stack
  simp only [with_stack_eq, with_nat_eq]
  split_ifs with h
  · subst h; rfl
  · exact push_stack_aux_sound ⟨pat, width, len⟩ s

def drop_stack (n : Nat) : Stack → Stack
  | [] => []
  | top :: rest =>
    if n = 0 then top :: rest
    else if top.len ≤ n then
      with_nat (n - top.len) (fun rem => drop_stack rem rest)
    else
      with_nat (rot_mod top.width n top.pat) (fun p' =>
        with_nat (top.len - n) (fun l' =>
          ⟨p', top.width, l'⟩ :: rest))

lemma drop_stack_zero (s : Stack) : drop_stack 0 s = s := by
  cases s <;> rfl

lemma drop_stack_top_le (top : Block) (rest : Stack) (k : Nat) (hk : k ≤ top.len) :
    stack_to_tape (top :: rest) =
      expand_pat top.width top.pat k (stack_to_tape (drop_stack k (top :: rest))) := by
  unfold drop_stack
  simp only [with_nat_eq]
  split_ifs with h0 hle
  · subst h0; rfl
  · have heq : k = top.len := by omega
    subst heq
    simp only [Nat.sub_self, drop_stack_zero, stack_to_tape]
  · simp only [stack_to_tape, rot_mod_eq]
    rw [← expand_pat_add]
    have hlen : k + (top.len - k) = top.len := by omega
    rw [hlen]

def pop1 : Stack → Fin 2 × Stack
  | [] => (0, [])
  | top :: rest =>
    if top.len = 0 then
      pop1 rest
    else
      let bit := bit_of top.pat
      if top.len = 1 then
        (bit, rest)
      else
        with_nat (rot1 top.width top.pat) (fun p' =>
          with_nat (top.len - 1) (fun l' =>
            (bit, ⟨p', top.width, l'⟩ :: rest)))

lemma pop1_sound (s : Stack) :
    stack_to_tape s = (pop1 s).1 >> stack_to_tape (pop1 s).2 := by
  induction s with
  | nil => exact z0i.symm
  | cons top rest ih =>
    unfold pop1
    simp only [with_nat_eq]
    split_ifs with h0 h1
    · simp only [stack_to_tape, h0, expand_pat, ih]
    · simp only [stack_to_tape, h1, expand_pat]
    · simp only [stack_to_tape]
      have hlen : top.len = (top.len - 1) + 1 := by omega
      conv_lhs => rw [hlen, expand_pat]

def word_of : Nat → Nat → zF
  | _, 0 => []
  | pat, w + 1 => bit_of pat :: word_of (pat / 2) w

def pop_word : Nat → Nat → Stack → Option Stack
  | _, 0, s => some s
  | pat, w + 1, s =>
    with_prod (pop1 s) (fun res =>
      if res.1 = bit_of pat then
        pop_word (pat / 2) w res.2
      else
        none)

lemma pop_word_sound (pat w : Nat) (s s' : Stack) (h : pop_word pat w s = some s') :
    stack_to_tape s = word_of pat w +> stack_to_tape s' := by
  induction w generalizing pat s with
  | zero =>
    simp [pop_word] at h
    subst h; rfl
  | succ w ih =>
    simp only [pop_word, with_prod_eq] at h
    split_ifs at h with hb
    rw [pop1_sound s, hb, ih (pat / 2) (pop1 s).2 h, word_of, append_cons]

def pat_word (bw : Nat) : Nat → Nat → zF
  | _, 0 => []
  | bp, w + 1 => bit_of bp :: pat_word bw (rot1 bw bp) w

lemma expand_pat_word (bw bp w : Nat) (r : zB) :
    expand_pat bw bp w r = pat_word bw bp w +> r := by
  induction w generalizing bp with
  | zero => rfl
  | succ w ih => simp [expand_pat, pat_word, ih]

lemma expand_pat_bulk (bw bp pat w bulk : Nat) (r : zB)
    (hrot : rot_k bw w bp = bp) (hw : pat_word bw bp w = word_of pat w) :
    expand_pat bw bp (bulk * w) r = ((word_of pat w) ^ bulk) +> r := by
  induction bulk with
  | zero => simp [expand_pat]
  | succ bulk ih =>
    have h1 : (bulk + 1) * w = w + bulk * w := by rw [Nat.succ_mul, Nat.add_comm]
    rw [h1, expand_pat_add, hrot, ih, expand_pat_word, hw, z0j, append_assoc]

def count_stack_mut (pat w : Nat) : Nat → Nat → Stack → Nat × Stack
  | 0, _, s => (0, s)
  | fuel + 1, limit, s =>
    if limit = 0 then (0, s)
    else
      match s with
      | [] => (0, [])
      | top :: rest =>
        if (0 < w && w ≤ top.len && rot_k top.width w top.pat == top.pat &&
            pat_word top.width top.pat w == word_of pat w) = true then
          let div := top.len / w
          with_nat (min limit div) (fun bulk =>
            with_stack (drop_stack (bulk * w) (top :: rest)) (fun s1 =>
              with_prod (count_stack_mut pat w fuel (limit - bulk) s1) (fun res =>
                with_nat res.1 (fun c1 =>
                  with_stack res.2 (fun s2 => (bulk + c1, s2))))))
        else
          match pop_word pat w (top :: rest) with
          | some s1 =>
            with_prod (count_stack_mut pat w fuel (limit - 1) s1) (fun res =>
              with_nat res.1 (fun c1 =>
                with_stack res.2 (fun s2 => (1 + c1, s2))))
          | none => (0, top :: rest)

lemma count_stack_mut_sound (pat w fuel limit : Nat) (s : Stack) :
    (count_stack_mut pat w fuel limit s).1 ≤ limit ∧
    stack_to_tape s = ((word_of pat w) ^ (count_stack_mut pat w fuel limit s).1) +>
      stack_to_tape (count_stack_mut pat w fuel limit s).2 := by
  induction fuel generalizing limit s with
  | zero => simp [count_stack_mut]
  | succ fuel ih =>
    by_cases hlim : limit = 0
    · simp [count_stack_mut, hlim]
    · cases s with
      | nil => simp [count_stack_mut, hlim]
      | cons top rest =>
        simp only [count_stack_mut, hlim, ↓reduceIte, with_nat_eq, with_stack_eq, with_prod_eq]
        split_ifs with h
        · dsimp only
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          rcases h with ⟨⟨⟨hw0, hwlen⟩, hrot⟩, hpat⟩
          have hbulk_le_div : min limit (top.len / w) ≤ top.len / w :=
            Nat.min_le_right limit (top.len / w)
          have hbulk_le_lim : min limit (top.len / w) ≤ limit :=
            Nat.min_le_left limit (top.len / w)
          have hmul_le : min limit (top.len / w) * w ≤ top.len :=
            Nat.le_trans (Nat.mul_le_mul_right w hbulk_le_div) (Nat.div_mul_le_self top.len w)
          have hdrop := drop_stack_top_le top rest (min limit (top.len / w) * w) hmul_le
          rw [expand_pat_bulk top.width top.pat pat w (min limit (top.len / w)) _ hrot hpat] at hdrop
          rcases ih (limit - min limit (top.len / w))
              (drop_stack (min limit (top.len / w) * w) (top :: rest)) with ⟨hrem_le, hrem_eq⟩
          refine ⟨by omega, ?_⟩
          rw [hdrop, hrem_eq, z0k, append_assoc]
        · cases hpop : pop_word pat w (top :: rest) with
          | none => simp
          | some s1 =>
            dsimp only
            have hpw := pop_word_sound pat w (top :: rest) s1 hpop
            rcases ih (limit - 1) s1 with ⟨hrem_le, hrem_eq⟩
            refine ⟨by omega, ?_⟩
            rw [hpw, hrem_eq, Nat.add_comm 1, z0j, append_assoc]

-- PartList & Parser / Subtractor
abbrev PartList := List (Bool × Nat)

def bsize_parts : PartList → Nat
  | [] => 0
  | (_, k) :: xs => k + bsize_parts xs

def eval_lsb : PartList → Nat
  | [] => 0
  | (b, k) :: xs => (if b then 2 ^ k - 1 else 0) + eval_lsb xs * 2 ^ k

def cons_lsb (b : Bool) (k : Nat) (xs : PartList) : PartList :=
  with_list xs (fun xs' =>
    if k = 0 then xs'
    else if !b && xs'.isEmpty then []
    else (b, k) :: xs')

lemma eval_cons_lsb (b : Bool) (k : Nat) (xs : PartList) :
    eval_lsb (cons_lsb b k xs) = (if b then 2 ^ k - 1 else 0) + eval_lsb xs * 2 ^ k := by
  cases k with
  | zero => simp [cons_lsb]
  | succ k => cases b <;> cases xs <;> simp [cons_lsb, eval_lsb]

lemma bsize_cons_lsb_le (b : Bool) (k : Nat) (xs : PartList) :
    bsize_parts (cons_lsb b k xs) ≤ k + bsize_parts xs := by
  cases k with
  | zero => simp [cons_lsb]
  | succ k => cases b <;> cases xs <;> simp [cons_lsb, bsize_parts]

lemma eval_lsb_lt (xs : PartList) : eval_lsb xs < 2 ^ (bsize_parts xs) := by
  induction xs with
  | nil => simp [eval_lsb, bsize_parts]
  | cons p xs ih =>
    rcases p with ⟨b, k⟩
    simp only [eval_lsb, bsize_parts]
    have hk := z0v k
    have hd : (if b then 2 ^ k - 1 else 0) < 2 ^ k := by split_ifs <;> omega
    have hmul : (eval_lsb xs + 1) * 2 ^ k ≤ 2 ^ (bsize_parts xs) * 2 ^ k :=
      Nat.mul_le_mul_right (2 ^ k) ih
    have hpow : 2 ^ (k + bsize_parts xs) = 2 ^ (bsize_parts xs) * 2 ^ k := by
      rw [Nat.add_comm, Nat.pow_add]
    have hadd : (eval_lsb xs + 1) * 2 ^ k = 2 ^ k + eval_lsb xs * 2 ^ k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

lemma z0o_part (b : Bool) (k len n : Nat) (r : zB) :
    z0o ld0 ld1 (k + len) ((if b then 2 ^ k - 1 else 0) + n * 2 ^ k) r =
      ((if b then ld0 else ld1) ^ k) +> z0o ld0 ld1 len n r := by
  rw [Nat.add_comm k len]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact z0x ld0 ld1 len n k r
  · simp only [↓reduceIte]
    have hp := z0v k
    have h1 : 2 ^ k - 1 + n * 2 ^ k = (n + 1) * 2 ^ k - 1 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [h1]
    exact z0y' ld0 ld1 len n k r

lemma MC_part (b : Bool) (k h n : Nat) (r : zB) :
    MC (h + k) ((if b then 2 ^ k - 1 else 0) + n * 2 ^ k) r =
      ((if b then rd0 else rd1) ^ k) +> MC h n r := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact MC_lsb_0 h n k r
  · simp only [↓reduceIte]
    have hp := z0v k
    have h1 : 2 ^ k - 1 + n * 2 ^ k = (n + 1) * 2 ^ k - 1 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [h1]
    exact MC_lsb_1 h n k r

lemma push_ld (b : Bool) (k : Nat) (s : Stack) :
    stack_to_tape (push_stack (if b then 14 else 1) (if b then 4 else 1) (k * 4) s) =
      ((if b then ld0 else ld1) ^ k) +> stack_to_tape s := by
  rw [push_stack_sound]
  cases b
  · exact expand_pat_bulk 1 1 15 4 k (stack_to_tape s) rfl rfl
  · exact expand_pat_bulk 4 14 14 4 k (stack_to_tape s) rfl rfl

lemma push_rd (b : Bool) (k : Nat) (s : Stack) :
    stack_to_tape (push_stack (if b then 0 else 1) (if b then 1 else 3) (k * 3) s) =
      ((if b then rd0 else rd1) ^ k) +> stack_to_tape s := by
  rw [push_stack_sound]
  cases b
  · exact expand_pat_bulk 3 1 1 3 k (stack_to_tape s) rfl rfl
  · exact expand_pat_bulk 1 0 0 3 k (stack_to_tape s) rfl rfl

def put_l_parts : PartList → Stack → Stack
  | [], s => s
  | (b, k) :: xs, s =>
    push_stack (if b then 14 else 1) (if b then 4 else 1) (k * 4) (put_l_parts xs s)

lemma put_l_parts_sound (xs : PartList) (s : Stack) :
    stack_to_tape (put_l_parts xs s) =
      z0o ld0 ld1 (bsize_parts xs) (eval_lsb xs) (stack_to_tape s) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨b, k⟩
    simp only [put_l_parts, bsize_parts, eval_lsb, push_ld, ih, z0o_part]

lemma z0o_pad_zero (xs : PartList) (extra : Nat) (r : zB) :
    z0o ld0 ld1 (bsize_parts xs + extra) (eval_lsb xs) r =
      z0o ld0 ld1 (bsize_parts xs) (eval_lsb xs) ((ld1 ^ extra) +> r) := by
  induction xs with
  | nil => simp [bsize_parts, eval_lsb, z0o, z0u]
  | cons p xs ih =>
    rcases p with ⟨b, k⟩
    simp only [bsize_parts, eval_lsb]
    rw [Nat.add_assoc k (bsize_parts xs) extra, z0o_part, ih, ← z0o_part]

def put_l_stack (xs : PartList) (n : Nat) (s : Stack) : Stack :=
  let bs := bsize_parts xs
  let s1 := if bs < n then push_stack 1 1 ((n - bs) * 4) s else s
  put_l_parts xs s1

lemma put_l_stack_sound (xs : PartList) (n : Nat) (s : Stack) (hn : bsize_parts xs ≤ n) :
    stack_to_tape (put_l_stack xs n s) =
      z0o ld0 ld1 n (eval_lsb xs) (stack_to_tape s) := by
  unfold put_l_stack
  dsimp only
  rw [put_l_parts_sound]
  have hlen : n = bsize_parts xs + (n - bsize_parts xs) := by omega
  conv_rhs => rw [hlen, z0o_pad_zero]
  split_ifs with hlt
  · have := push_ld false (n - bsize_parts xs) s
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this]
  · have hz : n - bsize_parts xs = 0 := by omega
    simp [hz]

lemma push_rd_base (b : Bool) (h : Nat) (s : Stack) :
    stack_to_tape (push_stack (if b then 0 else 1) (if b then 1 else 3) ((h + 1) * 3 - 2) s) =
      MC h (if b then 2 ^ (h + 1) - 1 else 0) (stack_to_tape s) := by
  have hlen : (h + 1) * 3 - 2 = h * 3 + 1 := by omega
  rw [hlen, push_stack_sound, expand_pat_add]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hrot : rot_k 3 (h * 3) 1 = 1 := by
      have := rot_k_period 3 1 rfl h 0
      simpa [Nat.mul_comm] using! this
    rw [hrot, expand_pat_bulk 3 1 1 3 h _ rfl rfl, MC_base_0]; rfl
  · simp only [↓reduceIte]
    have hrot : rot_k 1 (h * 3) 0 = 0 := by
      have := rot_k_period 1 0 rfl (h * 3) 0
      simpa using! this
    rw [hrot, expand_pat_bulk 1 0 0 3 h _ rfl rfl, MC_base_1]; rfl

def put_r_rec : PartList → Nat → Stack → Stack
  | [], k, s => push_stack 1 3 (k * 3 - 2) s
  | (bit, m) :: rest, k, s =>
    if m = 0 then
      put_r_rec rest k s
    else if k ≤ m then
      push_stack (if bit then 0 else 1) (if bit then 1 else 3) (m * 3 - 2) s
    else
      push_stack (if bit then 0 else 1) (if bit then 1 else 3) (m * 3) (put_r_rec rest (k - m) s)

def put_r_stack (xs : PartList) (k : Nat) (s : Stack) : Stack :=
  put_r_rec xs k s

lemma put_r_rec_sound (xs : PartList) (k : Nat) (s : Stack)
    (hk : 1 ≤ k) (hbs : bsize_parts xs ≤ k) :
    stack_to_tape (put_r_rec xs k s) =
      MC (k - 1) (eval_lsb xs) (stack_to_tape s) := by
  induction xs generalizing k with
  | nil =>
    simp only [put_r_rec, eval_lsb]
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    exact push_rd_base false (k - 1) s
  | cons p rest ih =>
    rcases p with ⟨bit, m⟩
    simp only [bsize_parts, eval_lsb] at hbs ⊢
    by_cases hm0 : m = 0
    · subst hm0
      have h0 : (if bit then 2 ^ 0 - 1 else 0) + eval_lsb rest * 2 ^ 0 = eval_lsb rest := by
        cases bit <;> simp
      simp only [put_r_rec, ↓reduceIte, h0]
      exact ih k hk (by omega)
    · by_cases hkm : k ≤ m
      · simp only [put_r_rec, hm0, hkm, ↓reduceIte]
        have heq : m = k := by omega
        have hrest0 : bsize_parts rest = 0 := by omega
        have hlt := eval_lsb_lt rest
        rw [hrest0] at hlt
        have heval0 : eval_lsb rest = 0 := by omega
        subst heq
        rw [heval0, Nat.zero_mul, Nat.add_zero]
        have hk1 : m = (m - 1) + 1 := by omega
        have hbase := push_rd_base bit (m - 1) s
        rw [← hk1] at hbase
        exact hbase
      · simp only [put_r_rec, hm0, hkm, ↓reduceIte]
        rw [push_rd, ih (k - m) (by omega) (by omega), ← MC_part]
        have hlen : k - m - 1 + m = k - 1 := by omega
        rw [hlen]

def parse_step_l (limit : Nat) (s : Stack) : Option (Bool × Nat × Stack) :=
  match s with
  | [] => none
  | top :: rest =>
    if (top.width == 1 && top.pat == 1 && 4 ≤ top.len) = true then
      let k := min limit (top.len / 4)
      some (false, k, drop_stack (k * 4) (top :: rest))
    else if (top.width == 4 && top.pat == 14 && 4 ≤ top.len) = true then
      let k := min limit (top.len / 4)
      some (true, k, drop_stack (k * 4) (top :: rest))
    else
      match pop_word 15 4 (top :: rest) with
      | some s1 => some (false, 1, s1)
      | none =>
        match pop_word 14 4 (top :: rest) with
        | some s1 => some (true, 1, s1)
        | none => none

lemma parse_step_l_sound (limit : Nat) (s s1 : Stack) (bit : Bool) (k : Nat)
    (h : parse_step_l limit s = some (bit, k, s1)) :
    stack_to_tape s = ((if bit then ld0 else ld1) ^ k) +> stack_to_tape s1 := by
  cases s with
  | nil => simp [parse_step_l] at h
  | cons top rest =>
    simp only [parse_step_l] at h
    split_ifs at h with h0 h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h0
      have hdiv : min limit (top.len / 4) ≤ top.len / 4 := Nat.min_le_right _ _
      have hmul : min limit (top.len / 4) * 4 ≤ top.len :=
        Nat.le_trans (Nat.mul_le_mul_right 4 hdiv) (Nat.div_mul_le_self top.len 4)
      rw [drop_stack_top_le top rest _ hmul, h0.1.1, h0.1.2]
      exact expand_pat_bulk 1 1 15 4 (min limit (top.len / 4)) _ rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      have hdiv : min limit (top.len / 4) ≤ top.len / 4 := Nat.min_le_right _ _
      have hmul : min limit (top.len / 4) * 4 ≤ top.len :=
        Nat.le_trans (Nat.mul_le_mul_right 4 hdiv) (Nat.div_mul_le_self top.len 4)
      rw [drop_stack_top_le top rest _ hmul, h1.1.1, h1.1.2]
      exact expand_pat_bulk 4 14 14 4 (min limit (top.len / 4)) _ rfl rfl
    · cases h15 : pop_word 15 4 (top :: rest) with
      | some s' =>
        rw [h15] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        simpa using! pop_word_sound 15 4 (top :: rest) s' h15
      | none =>
        rw [h15] at h
        cases h14 : pop_word 14 4 (top :: rest) with
        | some s' =>
          rw [h14] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          simpa using! pop_word_sound 14 4 (top :: rest) s' h14
        | none =>
          rw [h14] at h
          contradiction

def parse_l : Nat → Nat → Stack → PartList × Stack
  | 0, _, s => ([], s)
  | fuel + 1, limit, s =>
    if limit = 0 then ([], s)
    else
      match parse_step_l limit s with
      | none => ([], s)
      | some (bit, k, s1) =>
        with_prod (parse_l fuel (limit - k) s1) (fun res =>
          with_list res.1 (fun r1 =>
            with_stack res.2 (fun r2 =>
              if !bit && r1.isEmpty then
                ([], s)
              else
                ((bit, k) :: r1, r2))))

lemma parse_l_sound (fuel limit : Nat) (s : Stack) :
    stack_to_tape s =
      z0o ld0 ld1 (bsize_parts (parse_l fuel limit s).1) (eval_lsb (parse_l fuel limit s).1)
        (stack_to_tape (parse_l fuel limit s).2) := by
  induction fuel generalizing limit s with
  | zero => rfl
  | succ fuel ih =>
    by_cases hlim : limit = 0
    · simp [parse_l, hlim]; rfl
    · simp only [parse_l, hlim, ↓reduceIte, with_prod_eq, with_list_eq, with_stack_eq]
      cases hstep : parse_step_l limit s with
      | none => rfl
      | some val =>
        rcases val with ⟨bit, k, s1⟩
        dsimp only
        split_ifs with he
        · rfl
        · simp only [bsize_parts, eval_lsb, z0o_part, ← ih (limit - k) s1]
          exact parse_step_l_sound limit s s1 bit k hstep

def parse_step_r (limit : Nat) (s : Stack) : Option (Bool × Nat × Stack) :=
  match s with
  | [] => none
  | top :: rest =>
    if (top.width == 3 && top.pat == 1 && 3 ≤ top.len) = true then
      let k := min limit (top.len / 3)
      some (false, k, drop_stack (k * 3) (top :: rest))
    else if (top.width == 1 && top.pat == 0 && 3 ≤ top.len) = true then
      let k := min limit (top.len / 3)
      some (true, k, drop_stack (k * 3) (top :: rest))
    else
      match pop_word 1 3 (top :: rest) with
      | some s1 => some (false, 1, s1)
      | none =>
        match pop_word 0 3 (top :: rest) with
        | some s1 => some (true, 1, s1)
        | none => none

lemma parse_step_r_sound (limit : Nat) (s s1 : Stack) (bit : Bool) (k : Nat)
    (hlim : 1 ≤ limit) (h : parse_step_r limit s = some (bit, k, s1)) :
    1 ≤ k ∧ stack_to_tape s = ((if bit then rd0 else rd1) ^ k) +> stack_to_tape s1 := by
  cases s with
  | nil => simp [parse_step_r] at h
  | cons top rest =>
    simp only [parse_step_r] at h
    split_ifs at h with h0 h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h0
      have hdiv : min limit (top.len / 3) ≤ top.len / 3 := Nat.min_le_right _ _
      have hmul : min limit (top.len / 3) * 3 ≤ top.len :=
        Nat.le_trans (Nat.mul_le_mul_right 3 hdiv) (Nat.div_mul_le_self top.len 3)
      refine ⟨by omega, ?_⟩
      rw [drop_stack_top_le top rest _ hmul, h0.1.1, h0.1.2]
      exact expand_pat_bulk 3 1 1 3 (min limit (top.len / 3)) _ rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      have hdiv : min limit (top.len / 3) ≤ top.len / 3 := Nat.min_le_right _ _
      have hmul : min limit (top.len / 3) * 3 ≤ top.len :=
        Nat.le_trans (Nat.mul_le_mul_right 3 hdiv) (Nat.div_mul_le_self top.len 3)
      refine ⟨by omega, ?_⟩
      rw [drop_stack_top_le top rest _ hmul, h1.1.1, h1.1.2]
      exact expand_pat_bulk 1 0 0 3 (min limit (top.len / 3)) _ rfl rfl
    · cases h01 : pop_word 1 3 (top :: rest) with
      | some s' =>
        rw [h01] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact ⟨by omega, by simpa using! pop_word_sound 1 3 (top :: rest) s' h01⟩
      | none =>
        rw [h01] at h
        cases h00 : pop_word 0 3 (top :: rest) with
        | some s' =>
          rw [h00] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨by omega, by simpa using! pop_word_sound 0 3 (top :: rest) s' h00⟩
        | none =>
          rw [h00] at h
          contradiction

def parse_r : Nat → Nat → Stack → PartList × Stack
  | 0, _, s => ([], s)
  | fuel + 1, limit, s =>
    if limit = 0 then ([], s)
    else
      match s with
      | [] => ([(true, limit)], [])
      | top :: rest =>
        match parse_step_r limit (top :: rest) with
        | none =>
          with_prod (pop1 (top :: rest)) (fun p =>
            if p.1 = 0 then
              with_stack p.2 (fun p2 => ([(true, 1)], p2))
            else
              ([], top :: rest))
        | some (bit, k, s1) =>
          with_prod (parse_r fuel (limit - k) s1) (fun res =>
            with_list res.1 (fun r1 =>
              with_stack res.2 (fun r2 =>
                if r1.isEmpty then
                  if bit then
                    with_stack (push_stack 0 1 2 s1) (fun r2' => ([(true, k)], r2'))
                  else
                    ([], top :: rest)
                else
                  ((bit, k) :: r1, r2))))

lemma rd0_default (n : Nat) : (rd0 ^ n) +> (default : zB) = default := by
  induction n with
  | zero => rfl
  | succ n ih => simp [z0j, rd0, ih]

lemma parse_r_sound (fuel limit : Nat) (s : Stack)
    (hne : (parse_r fuel limit s).1 ≠ []) :
    1 ≤ bsize_parts (parse_r fuel limit s).1 ∧
    stack_to_tape s =
      MC (bsize_parts (parse_r fuel limit s).1 - 1) (eval_lsb (parse_r fuel limit s).1)
        (stack_to_tape (parse_r fuel limit s).2) := by
  induction fuel generalizing limit s with
  | zero => simp [parse_r] at hne
  | succ fuel ih =>
    by_cases hlim : limit = 0
    · simp [parse_r, hlim] at hne
    · cases s with
      | nil =>
        simp only [parse_r, hlim, ↓reduceIte, bsize_parts, eval_lsb, Nat.add_zero, Nat.zero_mul,
           stack_to_tape]
        refine ⟨by omega, ?_⟩
        have hlim_eq : limit = (limit - 1) + 1 := by omega
        conv_rhs => rw [hlim_eq]
        simp only [Nat.add_sub_cancel, MC_base_1 (limit - 1)]
        simp [rd0_default]
      | cons top rest =>
        simp only [parse_r, hlim, ↓reduceIte, with_prod_eq, with_list_eq, with_stack_eq] at hne ⊢
        cases hstep : parse_step_r limit (top :: rest) with
        | none =>
          rw [hstep] at hne
          dsimp only at hne ⊢
          by_cases hp0 : (pop1 (top :: rest)).1 = 0
          · simp only [hp0, ↓reduceIte, bsize_parts, eval_lsb, MC]
            refine ⟨by omega, ?_⟩
            rw [pop1_sound (top :: rest), hp0]; rfl
          · simp [hp0] at hne
        | some val =>
          rcases val with ⟨bit, k, s1⟩
          rw [hstep] at hne
          dsimp only at hne ⊢
          rcases parse_step_r_sound limit (top :: rest) s1 bit k (by omega) hstep with ⟨hk1, hseq⟩
          by_cases he : (parse_r fuel (limit - k) s1).1.isEmpty
          · by_cases hbit : bit
            · subst hbit
              simp only [he, ↓reduceIte, bsize_parts, eval_lsb, Nat.add_zero, Nat.zero_mul]
              refine ⟨hk1, ?_⟩
              have hk_eq : k = (k - 1) + 1 := by omega
              conv_rhs => rw [hk_eq]
              simp only [Nat.add_sub_cancel, MC_base_1 (k - 1)]
              rw [push_stack_sound, expand_pat_word]
              change stack_to_tape (top :: rest) = (rd0 ^ (k - 1)) +> [0] +> [0, 0] +> stack_to_tape s1
              have hrd : [0] +> [0, 0] +> stack_to_tape s1 = rd0 +> stack_to_tape s1 := rfl
              rw [hrd, ← append_assoc, z0l, ← hk_eq, hseq]; rfl
            · simp [he, hbit] at hne
          · simp only [he, Bool.false_eq_true, ↓reduceIte, bsize_parts, eval_lsb]
            have hne_res : (parse_r fuel (limit - k) s1).1 ≠ [] := by
              intro hc; simp [hc] at he
            rcases ih (limit - k) s1 hne_res with ⟨hbs1, hmc⟩
            refine ⟨by omega, ?_⟩
            have hsub : k + bsize_parts (parse_r fuel (limit - k) s1).1 - 1 =
                (bsize_parts (parse_r fuel (limit - k) s1).1 - 1) + k := by omega
            rw [hsub, MC_part, ← hmc, hseq]

-- Subtractor & soundness
def subbit (a b borrow : Bool) : Bool × Bool :=
  (xor (xor a b) borrow, (!a && (b || borrow)) || (b && borrow))

def next_x (px : Bool) (kx n : Nat) (xs : PartList) : PartList :=
  if n < kx then (px, kx - n) :: xs else xs

def next_y (n : Nat) : PartList → PartList
  | [] => []
  | (q, l) :: yrest => if n < l then (q, l - n) :: yrest else yrest

def head_q : PartList → Bool
  | [] => false
  | (q, _) :: _ => q

def head_l (kx : Nat) : PartList → Nat
  | [] => kx
  | (_, l) :: _ => l

def sub_chunk_c (px qy c : Bool) (n : Nat) : Bool :=
  if 1 < n then (subbit px qy (subbit px qy c).2).2 else (subbit px qy c).2

def sub_chunk_out (px qy c : Bool) (n : Nat) (out : PartList) : PartList :=
  cons_lsb (subbit px qy c).1 1
    (if 1 < n then cons_lsb (subbit px qy (subbit px qy c).2).1 (n - 1) out else out)

def sub_lsb : Nat → Bool → PartList → PartList → Option PartList
  | 0, _, _, _ => none
  | _ + 1, c, [], ys =>
    if ys.isEmpty && !c then some [] else none
  | fuel + 1, c, (px, kx) :: xs, ys =>
    let qy := head_q ys
    let ly := head_l kx ys
    with_nat (min kx ly) (fun n =>
      with_list (next_x px kx n xs) (fun nx =>
        with_list (next_y n ys) (fun ny =>
          if n = 0 then
            sub_lsb fuel c nx ny
          else
            match sub_lsb fuel (sub_chunk_c px qy c n) nx ny with
            | none => none
            | some out => some (sub_chunk_out px qy c n out))))

lemma eval_split_part (p : Bool) (k n : Nat) (rest : PartList) (hn : n ≤ k) :
    eval_lsb ((p, k) :: rest) =
      (if p then 2 ^ n - 1 else 0) + eval_lsb (next_x p k n rest) * 2 ^ n := by
  unfold next_x
  by_cases hlt : n < k
  · simp only [hlt, ↓reduceIte, eval_lsb, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
    have hk : k - n + n = k := by omega
    rw [hk]
    cases p
    · simp
    · simp only [↓reduceIte]
      have hp1 := z0v n
      have hp2 := z0v (k - n)
      have hpow : 2 ^ (k - n) * 2 ^ n = 2 ^ k := by rw [← Nat.pow_add, hk]
      have hle : 2 ^ n ≤ 2 ^ k := by rw [← hpow]; exact Nat.le_mul_of_pos_left _ hp2
      have hd : (2 ^ (k - n) - 1) * 2 ^ n = 2 ^ k - 2 ^ n := by
        rw [Nat.sub_mul, Nat.one_mul, hpow]
      rw [hd]; omega
  · have heq : k = n := by omega
    subst heq
    simp [hlt, eval_lsb]

lemma bsize_sub_chunk_out (px qy c : Bool) (n : Nat) (out : PartList) (hn : 1 ≤ n) :
    bsize_parts (sub_chunk_out px qy c n out) ≤ n + bsize_parts out := by
  unfold sub_chunk_out
  have h1 := bsize_cons_lsb_le (subbit px qy c).1 1
    (if 1 < n then cons_lsb (subbit px qy (subbit px qy c).2).1 (n - 1) out else out)
  have h2 : bsize_parts (if 1 < n then cons_lsb (subbit px qy (subbit px qy c).2).1 (n - 1) out else out) ≤
      (n - 1) + bsize_parts out := by
    by_cases h1n : 1 < n
    · simp only [h1n, ↓reduceIte]
      exact bsize_cons_lsb_le _ (n - 1) out
    · simp only [h1n, ↓reduceIte]
      omega
  omega

lemma eval_sub_chunk_out (px qy c : Bool) (n : Nat) (out : PartList) (hn : 1 ≤ n) :
    eval_lsb (sub_chunk_out px qy c n out) + (if qy then 2 ^ n - 1 else 0) + (if c then 1 else 0) =
      (if px then 2 ^ n - 1 else 0) +
      (eval_lsb out + (if sub_chunk_c px qy c n then 1 else 0)) * 2 ^ n := by
  unfold sub_chunk_out sub_chunk_c
  rw [eval_cons_lsb]
  have hpos := z0v (n - 1)
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    have hn1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn1, Nat.pow_succ]
  by_cases h1n : 1 < n
  · simp only [h1n, ↓reduceIte, eval_cons_lsb]
    have hmul : ((if (subbit px qy (subbit px qy c).2).1 then 2 ^ (n - 1) - 1 else 0) +
        eval_lsb out * 2 ^ (n - 1)) * 2 ^ 1 =
        (if (subbit px qy (subbit px qy c).2).1 then 2 ^ (n - 1) - 1 else 0) * 2 +
        eval_lsb out * 2 ^ n := by
      simp only [Nat.pow_one, Nat.add_mul, Nat.mul_assoc, ← hpow]
    have hmul2 : (eval_lsb out + (if (subbit px qy (subbit px qy c).2).2 then 1 else 0)) * 2 ^ n =
        eval_lsb out * 2 ^ n + (if (subbit px qy (subbit px qy c).2).2 then 1 else 0) * 2 ^ n := by
      rw [Nat.add_mul]
    rw [hmul, hmul2]
    cases px <;> cases qy <;> cases c <;> dsimp [subbit] <;> omega
  · have hn_eq : n = 1 := by omega
    subst hn_eq
    simp only [Nat.lt_irrefl, ↓reduceIte, Nat.pow_one]
    have hmul2 : (eval_lsb out + (if (subbit px qy c).2 then 1 else 0)) * 2 =
        eval_lsb out * 2 + (if (subbit px qy c).2 then 1 else 0) * 2 := by
      rw [Nat.add_mul]
    rw [hmul2]
    cases px <;> cases qy <;> cases c <;> dsimp [subbit] <;> omega

lemma sub_lsb_sound (fuel : Nat) (c : Bool) (xs ys out : PartList)
    (h : sub_lsb fuel c xs ys = some out) :
    bsize_parts out ≤ bsize_parts xs ∧
    eval_lsb out + eval_lsb ys + (if c then 1 else 0) = eval_lsb xs := by
  induction fuel generalizing c xs ys out with
  | zero => simp [sub_lsb] at h
  | succ fuel ih =>
    cases xs with
    | nil =>
      simp only [sub_lsb] at h
      split_ifs at h with hyc
      simp only [Option.some.injEq] at h
      subst h
      cases ys <;> cases c <;> simp [eval_lsb, bsize_parts] at hyc ⊢
    | cons xhead xrest =>
      rcases xhead with ⟨px, kx⟩
      simp only [sub_lsb, with_nat_eq, with_list_eq] at h
      have hn_kx : min kx (head_l kx ys) ≤ kx := Nat.min_le_left kx (head_l kx ys)
      have hsplit_x : eval_lsb ((px, kx) :: xrest) =
          (if px then 2 ^ (min kx (head_l kx ys)) - 1 else 0) +
          eval_lsb (next_x px kx (min kx (head_l kx ys)) xrest) * 2 ^ (min kx (head_l kx ys)) :=
        eval_split_part px kx (min kx (head_l kx ys)) xrest hn_kx
      have hsplit_y : eval_lsb ys =
          (if head_q ys then 2 ^ (min kx (head_l kx ys)) - 1 else 0) +
          eval_lsb (next_y (min kx (head_l kx ys)) ys) * 2 ^ (min kx (head_l kx ys)) := by
        cases ys with
        | nil => simp [head_q, next_y, eval_lsb]
        | cons yh yr =>
          rcases yh with ⟨q, l⟩
          exact eval_split_part q l (min kx l) yr (Nat.min_le_right kx l)
      have hbs_nx : min kx (head_l kx ys) + bsize_parts (next_x px kx (min kx (head_l kx ys)) xrest) =
          bsize_parts ((px, kx) :: xrest) := by
        dsimp [next_x, bsize_parts]
        split_ifs with hlt <;> simp [bsize_parts] <;> omega
      by_cases hn0 : min kx (head_l kx ys) = 0
      · rw [if_pos hn0] at h
        rcases ih c (next_x px kx (min kx (head_l kx ys)) xrest) (next_y (min kx (head_l kx ys)) ys) out h with ⟨hbs_out, heval_out⟩
        rw [hn0] at hsplit_x hsplit_y hbs_nx hbs_out heval_out
        simp only [Nat.pow_zero, Nat.sub_self, ite_self, Nat.zero_add, Nat.mul_one] at hsplit_x hsplit_y hbs_nx
        exact ⟨by omega, by omega⟩
      · rw [if_neg hn0] at h
        cases hrec : sub_lsb fuel (sub_chunk_c px (head_q ys) c (min kx (head_l kx ys)))
            (next_x px kx (min kx (head_l kx ys)) xrest) (next_y (min kx (head_l kx ys)) ys) with
        | none => rw [hrec] at h; contradiction
        | some out_rec =>
          rw [hrec] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases ih (sub_chunk_c px (head_q ys) c (min kx (head_l kx ys)))
              (next_x px kx (min kx (head_l kx ys)) xrest) (next_y (min kx (head_l kx ys)) ys) out_rec hrec with ⟨hbs_rec, heval_rec⟩
          have hn1 : 1 ≤ min kx (head_l kx ys) := by omega
          have hbs1 := bsize_sub_chunk_out px (head_q ys) c (min kx (head_l kx ys)) out_rec hn1
          have hev1 := eval_sub_chunk_out px (head_q ys) c (min kx (head_l kx ys)) out_rec hn1
          have h_assoc : eval_lsb out_rec + (if sub_chunk_c px (head_q ys) c (min kx (head_l kx ys)) then 1 else 0) +
              eval_lsb (next_y (min kx (head_l kx ys)) ys) =
              eval_lsb out_rec + eval_lsb (next_y (min kx (head_l kx ys)) ys) +
              (if sub_chunk_c px (head_q ys) c (min kx (head_l kx ys)) then 1 else 0) := by omega
          have hmul_rec : (eval_lsb out_rec + (if sub_chunk_c px (head_q ys) c (min kx (head_l kx ys)) then 1 else 0)) *
              2 ^ (min kx (head_l kx ys)) +
              eval_lsb (next_y (min kx (head_l kx ys)) ys) * 2 ^ (min kx (head_l kx ys)) =
              eval_lsb (next_x px kx (min kx (head_l kx ys)) xrest) * 2 ^ (min kx (head_l kx ys)) := by
            rw [← Nat.add_mul, h_assoc, heval_rec]
          exact ⟨by omega, by omega⟩

-- ============================================================================
-- Section 3: Macro Step Engine (step_m / run_m) & Soundness
-- ============================================================================

structure MState where
  q : Fin 6
  l : Stack
  r : Stack
  deriving DecidableEq

def mstate_to_cfg (s : MState) : Cfg (Fin 2) (Fin 6) :=
  (stack_to_tape s.l) {{s.q}}> (stack_to_tape s.r)

lemma cfg_right_eq_left (q : Fin 6) (b : Fin 2) (l r : zB) :
    (l {{q}}> (b >> r)) = ((b >> l) <{{q}} r) := by
  simp [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

def choose_limit_r_loop (n : Nat) : Nat → Nat → Stack → Nat
  | 0, _, _ => n + 1
  | _ + 1, done, [] => if done ≤ n then n + 1 else done + 1
  | fuel + 1, done, top :: rest =>
    if (top.width == 3 && top.pat == 1 && 3 ≤ top.len) = true then
      let div := top.len / 3
      choose_limit_r_loop n fuel (done + div) (drop_stack (div * 3) (top :: rest))
    else if (top.width == 1 && top.pat == 0 && 3 ≤ top.len) = true then
      let div := top.len / 3
      let next_done := done + div
      if n < next_done then
        min (max (n + 2) (done + 2)) next_done
      else
        choose_limit_r_loop n fuel next_done (drop_stack (div * 3) (top :: rest))
    else
      match pop_word 1 3 (top :: rest) with
      | some r1 => choose_limit_r_loop n fuel (done + 1) r1
      | none =>
        match pop_word 0 3 (top :: rest) with
        | some r1 =>
          if n < done + 1 then done + 1
          else choose_limit_r_loop n fuel (done + 1) r1
        | none =>
          if (pop1 (top :: rest)).1 = 0 then done + 1 else done

def choose_limit_r (kfuel : Nat) (n : Nat) (r : Stack) : Nat :=
  choose_limit_r_loop n kfuel 0 r

def push_prefix_l (l : Stack) : Stack :=
  push_stack 1 1 1 (push_stack 0 1 1 (push_stack 1 1 3 l))

lemma push_prefix_l_sound (l : Stack) :
    stack_to_tape (push_prefix_l l) = [1, 0, 1, 1, 1] +> stack_to_tape l := by
  unfold push_prefix_l
  rw [push_stack_sound, push_stack_sound, push_stack_sound]
  rfl

def build_vprime (n m_use : Nat) : PartList :=
  let v0 : PartList := if 1 < m_use then cons_lsb true (m_use - 1) [] else []
  let v1 : PartList := if 1 < m_use then cons_lsb false n v0 else v0
  cons_lsb true 1 v1

lemma eval_build_vprime (n m' : Nat) :
    eval_lsb (build_vprime n (m' + 1)) = 1 + (2 ^ m' - 1) * 2 ^ (n + 1) := by
  unfold build_vprime
  dsimp only
  by_cases h1 : 1 < m' + 1
  · simp only [h1, ↓reduceIte, eval_cons_lsb, eval_lsb, Nat.add_sub_cancel,
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Bool.false_eq_true, Nat.zero_add, Nat.pow_one]
    rw [Nat.mul_assoc, ← Nat.pow_succ]
  · have hm0 : m' = 0 := by omega
    subst hm0
    simp [eval_cons_lsb, eval_lsb]

def some_mstate (q : Fin 6) (l r : Stack) : Option MState :=
  with_nat q.val (fun _ =>
    with_stack l (fun l' =>
      with_stack r (fun r' =>
        some ⟨q, l', r'⟩)))

@[simp] lemma some_mstate_eq (q : Fin 6) (l r : Stack) :
    some_mstate q l r = some ⟨q, l, r⟩ := by
  simp [some_mstate]

def do_shift_right (sq : Fin 6) (sw sin sout sout_w : Nat) (s : MState) : Option MState :=
  if s.q = sq then
    let target2 := sin + sin * (2 ^ sw)
    if (pop_word target2 (2 * sw) s.r).isSome then
      with_prod (count_stack_mut sin sw 8 100000000 s.r) (fun res =>
        let l' := push_stack sout sout_w (res.1 * sw) s.l
        some_mstate sq l' res.2)
    else none
  else none

lemma do_shift_right_sound (sq : Fin 6) (sw sin sout sout_w pat_out : Nat) (s s' : MState)
    (hrot : rot_k sout_w sw sout = sout)
    (hw : pat_word sout_w sout sw = word_of pat_out sw)
    (hsh : ∀ (n : Nat) (l r : zB),
      (l {{sq}}> (((word_of sin sw) ^ n) +> r)) [tm15]⊢*
      ((((word_of pat_out sw) ^ n) +> l) {{sq}}> r))
    (h : do_shift_right sq sw sin sout sout_w s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold do_shift_right at h
  simp only [with_prod_eq] at h
  split_ifs at h with hq hpw
  simp only [some_mstate_eq, Option.some.injEq] at h
  subst h
  rcases count_stack_mut_sound sin sw 8 100000000 s.r with ⟨_, hcnt⟩
  unfold mstate_to_cfg
  dsimp only
  rw [hq, hcnt, push_stack_sound, expand_pat_bulk sout_w sout pat_out sw _ _ hrot hw]
  exact hsh _ _ _

def bit_pat (b : Fin 2) : Nat := if b = 1 then 1 else 0

lemma push_bit_sound (b : Fin 2) (s : Stack) :
    stack_to_tape (push_stack (bit_pat b) 1 1 s) = b >> stack_to_tape s := by
  rw [push_stack_sound]
  rcases b with ⟨_ | _ | b, hb⟩ <;> try rfl
  omega

def do_shift_left (sq : Fin 6) (sw sin sout sout_w : Nat) (s : MState) : Option MState :=
  if s.q = sq then
    let target2 := sin + sin * (2 ^ sw)
    with_prod (pop1 s.r) (fun p_r =>
      if (p_r.1 == bit_of target2 && (pop_word (target2 / 2) (2 * sw - 1) s.l).isSome) = true then
        let l1 := push_stack (bit_pat p_r.1) 1 1 s.l
        with_prod (count_stack_mut sin sw 8 100000000 l1) (fun res =>
          with_prod (pop1 res.2) (fun p_l =>
            let r1 := push_stack sout sout_w (res.1 * sw) p_r.2
            let r2 := push_stack (bit_pat p_l.1) 1 1 r1
            some_mstate sq p_l.2 r2))
      else none)
  else none

lemma do_shift_left_sound (sq : Fin 6) (sw sin sout sout_w pat_out : Nat) (s s' : MState)
    (hrot : rot_k sout_w sw sout = sout)
    (hw : pat_word sout_w sout sw = word_of pat_out sw)
    (hsh : ∀ (n : Nat) (l r : zB),
      ((((word_of sin sw) ^ n) +> l) <{{sq}} r) [tm15]⊢*
      (l <{{sq}} (((word_of pat_out sw) ^ n) +> r)))
    (h : do_shift_left sq sw sin sout sout_w s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold do_shift_left at h
  simp only [with_prod_eq] at h
  split_ifs at h with hq hguard
  simp only [some_mstate_eq, Option.some.injEq] at h
  subst h
  let l1 := push_stack (bit_pat (pop1 s.r).1) 1 1 s.l
  let res := count_stack_mut sin sw 8 100000000 l1
  rcases count_stack_mut_sound sin sw 8 100000000 l1 with ⟨_, hcnt⟩
  unfold mstate_to_cfg
  dsimp only
  rw [hq, pop1_sound s.r, cfg_right_eq_left, ← push_bit_sound (pop1 s.r).1 s.l]
  change (stack_to_tape l1 <{{sq}} stack_to_tape (pop1 s.r).2) [tm15]⊢* _
  rw [hcnt, push_bit_sound (pop1 res.2).1, cfg_right_eq_left, ← pop1_sound res.2,
    push_stack_sound, expand_pat_bulk sout_w sout pat_out sw _ _ hrot hw]
  exact hsh _ _ _

def try_pair_stack (kfuel : Nat) (s : MState) : Option MState :=
  if s.q = 0 then
    match pop_word 29 5 s.l with
    | none => none
    | some lc =>
      with_prod (parse_l kfuel 100000000 lc) (fun res_l =>
        with_list res_l.1 (fun a =>
          if a.isEmpty then none
          else
            with_nat (bsize_parts a) (fun n =>
              with_nat (choose_limit_r kfuel n s.r) (fun lim_r =>
                if lim_r = 0 then none
                else
                  with_prod (parse_r kfuel lim_r s.r) (fun res_r =>
                    with_list res_r.1 (fun b =>
                      if b.isEmpty then none
                      else
                        with_nat (bsize_parts b) (fun k =>
                          match sub_lsb kfuel false a b with
                          | some out =>
                            let l1 := push_prefix_l (put_l_stack out n res_l.2)
                            let r1 := put_r_stack [] k res_r.2
                            some_mstate 0 l1 r1
                          | none =>
                            match sub_lsb kfuel false b a with
                            | some out =>
                              let l1 := push_prefix_l (put_l_stack [] n res_l.2)
                              let r1 := put_r_stack out k res_r.2
                              some_mstate 0 l1 r1
                            | none => none)))))))
  else none

lemma try_pair_stack_sound (kfuel : Nat) (s s' : MState) (h : try_pair_stack kfuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold try_pair_stack at h
  split_ifs at h with hq
  cases hpw : pop_word 29 5 s.l with
  | none => rw [hpw] at h; contradiction
  | some lc =>
    rw [hpw] at h
    simp only [with_prod_eq, with_list_eq, with_nat_eq] at h
    split_ifs at h with ha_empty hlim0 hb_empty
    have hpw_eq := pop_word_sound 29 5 s.l lc hpw
    have hw29 : word_of 29 5 = [1, 0, 1, 1, 1] := rfl
    rw [hw29] at hpw_eq
    have hpl := parse_l_sound kfuel 100000000 lc
    let a := (parse_l kfuel 100000000 lc).1
    let lc1 := (parse_l kfuel 100000000 lc).2
    let n := bsize_parts a
    let b := (parse_r kfuel (choose_limit_r kfuel n s.r) s.r).1
    let rc1 := (parse_r kfuel (choose_limit_r kfuel n s.r) s.r).2
    let k := bsize_parts b
    have hne_b : b ≠ [] := by
      dsimp [b, n, a]
      intro hc; simp [hc] at hb_empty
    rcases parse_r_sound kfuel (choose_limit_r kfuel n s.r) s.r hne_b with ⟨hk1, hpr⟩
    have hal := eval_lsb_lt a
    have hbl := eval_lsb_lt b
    have hk_eq : k - 1 + 1 = k := by dsimp [k, b] at hk1 ⊢; omega
    cases hsub1 : sub_lsb kfuel false a b with
    | some out =>
      rw [hsub1] at h; simp only [some_mstate_eq, Option.some.injEq] at h; subst h
      rcases sub_lsb_sound kfuel false a b out hsub1 with ⟨hbs_out, heval_out⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at heval_out
      unfold mstate_to_cfg; dsimp only
      rw [hq, hpw_eq, hpl, hpr, push_prefix_l_sound, put_l_stack_sound out n lc1 hbs_out,
        put_r_stack, put_r_rec_sound [] k rc1 hk1 (by simp [bsize_parts])]
      change (z0V (z0o ld0 ld1 n (eval_lsb a) (stack_to_tape lc1))
        (MC (k - 1) (eval_lsb b) (stack_to_tape rc1))) [tm15]⊢*
        (z0V (z0o ld0 ld1 n (eval_lsb out) (stack_to_tape lc1))
        (MC (k - 1) 0 (stack_to_tape rc1)))
      have hpg := pair_general n (eval_lsb out) (k - 1) 0 (eval_lsb b) (stack_to_tape lc1) (stack_to_tape rc1)
        (by dsimp [n] at hal ⊢; omega) (by rw [hk_eq]; dsimp [k] at hbl ⊢; omega)
      rw [heval_out, Nat.zero_add] at hpg
      exact hpg
    | none =>
      rw [hsub1] at h; dsimp only at h
      cases hsub2 : sub_lsb kfuel false b a with
      | none => rw [hsub2] at h; contradiction
      | some out =>
        rw [hsub2] at h; simp only [some_mstate_eq, Option.some.injEq] at h; subst h
        rcases sub_lsb_sound kfuel false b a out hsub2 with ⟨hbs_out, heval_out⟩
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at heval_out
        unfold mstate_to_cfg; dsimp only
        rw [hq, hpw_eq, hpl, hpr, push_prefix_l_sound,
          put_l_stack_sound [] n lc1 (by simp [bsize_parts]),
          put_r_stack, put_r_rec_sound out k rc1 hk1 hbs_out]
        change (z0V (z0o ld0 ld1 n (eval_lsb a) (stack_to_tape lc1))
          (MC (k - 1) (eval_lsb b) (stack_to_tape rc1))) [tm15]⊢*
          (z0V (z0o ld0 ld1 n 0 (stack_to_tape lc1))
          (MC (k - 1) (eval_lsb out) (stack_to_tape rc1)))
        have hpg := pair_general n 0 (k - 1) (eval_lsb out) (eval_lsb a) (stack_to_tape lc1) (stack_to_tape rc1)
          (by dsimp [n] at hal ⊢; omega) (by rw [hk_eq]; dsimp [k] at hbl ⊢; omega)
        rw [Nat.zero_add, heval_out] at hpg
        exact hpg

def try_absorb_sub (kfuel : Nat) (n m_use : Nat) (b : PartList) : Option (Nat × PartList) :=
  match sub_lsb kfuel false b (build_vprime n m_use) with
  | some out => some (m_use, out)
  | none =>
    if m_use ≤ 1 then none
    else
      match sub_lsb kfuel false b (build_vprime n (m_use - 1)) with
      | some out => some (m_use - 1, out)
      | none => none

lemma try_absorb_sub_sound (kfuel : Nat) (n m_init m_use : Nat) (b out : PartList)
    (hm : 1 ≤ m_init) (h : try_absorb_sub kfuel n m_init b = some (m_use, out)) :
    1 ≤ m_use ∧ sub_lsb kfuel false b (build_vprime n m_use) = some out := by
  unfold try_absorb_sub at h
  cases h1 : sub_lsb kfuel false b (build_vprime n m_init) with
  | some out1 =>
    rw [h1] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨hm, h1⟩
  | none =>
    rw [h1] at h; dsimp only at h
    split_ifs at h with hle1
    cases h2 : sub_lsb kfuel false b (build_vprime n (m_init - 1)) with
    | none => rw [h2] at h; contradiction
    | some out2 =>
      rw [h2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by omega, h2⟩

def calc_m_init (m n k : Nat) : Nat :=
  min m (if n < k then k - n else 1)

def try_absorb_stack (kfuel : Nat) (s : MState) : Option MState :=
  if s.q = 0 then
    match pop_word 29 5 s.l with
    | none => none
    | some lc0 =>
      with_prod (count_stack_mut 15 4 kfuel 100000000 lc0) (fun res1 =>
        with_prod (count_stack_mut 13 4 kfuel 100000000 res1.2) (fun res_m =>
          if res_m.1 = 0 then none
          else
            with_nat (choose_limit_r kfuel (res1.1 + res_m.1) s.r) (fun lim_r =>
              if lim_r = 0 then none
              else
                with_prod (parse_r kfuel lim_r s.r) (fun res_r =>
                  with_list res_r.1 (fun b =>
                    if b.isEmpty then none
                    else
                      with_nat (bsize_parts b) (fun k =>
                        with_nat (calc_m_init res_m.1 res1.1 k) (fun m_init =>
                          if m_init = 0 then none
                          else
                            match try_absorb_sub kfuel res1.1 m_init b with
                            | none => none
                            | some (m_use, out) =>
                              with_prod (count_stack_mut 13 4 kfuel m_use res1.2) (fun res2 =>
                                if res2.1 = m_use then
                                  let l_new := push_prefix_l (push_stack 14 4 ((res1.1 + res2.1) * 4) res2.2)
                                  let r_new := put_r_stack out k res_r.2
                                  some_mstate 0 l_new r_new
                                else none))))))))
  else none

lemma try_absorb_stack_sound (kfuel : Nat) (s s' : MState) (h : try_absorb_stack kfuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold try_absorb_stack at h
  split_ifs at h with hq
  cases hpw : pop_word 29 5 s.l with
  | none => rw [hpw] at h; contradiction
  | some lc0 =>
    rw [hpw] at h
    simp only [with_prod_eq, with_list_eq, with_nat_eq] at h
    split_ifs at h with hm0 hlim0 hb_empty hmin0
    let res1 := count_stack_mut 15 4 kfuel 100000000 lc0
    let res_m := count_stack_mut 13 4 kfuel 100000000 res1.2
    let lim_r := choose_limit_r kfuel (res1.1 + res_m.1) s.r
    let res_r := parse_r kfuel lim_r s.r
    let k := bsize_parts res_r.1
    let m_init := calc_m_init res_m.1 res1.1 k
    cases habs : try_absorb_sub kfuel res1.1 m_init res_r.1 with
    | none => rw [habs] at h; contradiction
    | some pair_out =>
      rcases pair_out with ⟨m_use, out⟩
      rw [habs] at h
      simp only [with_prod_eq, with_list_eq, with_nat_eq] at h
      split_ifs at h with hm_act
      simp only [some_mstate_eq, Option.some.injEq] at h; subst h
      have hmin_pos : 1 ≤ m_init := by dsimp [m_init, k, res_r, lim_r, res_m, res1] at hmin0 ⊢; omega
      rcases try_absorb_sub_sound kfuel res1.1 m_init m_use res_r.1 out hmin_pos habs with ⟨hm_use1, hsub⟩
      rcases sub_lsb_sound kfuel false res_r.1 (build_vprime res1.1 m_use) out hsub with ⟨hbs_out, heval_out⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at heval_out
      have hpw_eq := pop_word_sound 29 5 s.l lc0 hpw
      have hw29 : word_of 29 5 = [1, 0, 1, 1, 1] := rfl
      rw [hw29] at hpw_eq
      rcases count_stack_mut_sound 15 4 kfuel 100000000 lc0 with ⟨_, hcnt15⟩
      have hw15 : word_of 15 4 = ld1 := rfl
      rw [hw15] at hcnt15
      let res2 := count_stack_mut 13 4 kfuel m_use res1.2
      rcases count_stack_mut_sound 13 4 kfuel m_use res1.2 with ⟨_, hcnt13⟩
      have hw13 : word_of 13 4 = [1, 0, 1, 1] := rfl
      rw [hw13] at hcnt13
      have hne_b : res_r.1 ≠ [] := by
        dsimp [res_r, lim_r, res_m, res1]
        intro hc; simp [hc] at hb_empty
      rcases parse_r_sound kfuel lim_r s.r hne_b with ⟨hk1, hpr⟩
      have hbl := eval_lsb_lt res_r.1
      have hk_eq : k - 1 + 1 = k := by dsimp [k, res_r] at hk1 ⊢; omega
      have hm_eq : res2.1 = (m_use - 1) + 1 := by rw [show res2.1 = m_use from hm_act]; omega
      have hv_eq : eval_lsb (build_vprime res1.1 m_use) = 1 + (2 ^ (m_use - 1) - 1) * 2 ^ (res1.1 + 1) := by
        have hmu : m_use = (m_use - 1) + 1 := by omega
        conv_lhs => rw [hmu]
        exact eval_build_vprime res1.1 (m_use - 1)
      rw [hv_eq] at heval_out
      unfold mstate_to_cfg; dsimp only
      rw [hq, hpw_eq, hcnt15, hcnt13, hpr, push_prefix_l_sound]
      have hpush14 := push_ld true (res1.1 + res2.1) res2.2
      simp only [↓reduceIte] at hpush14
      rw [hpush14, put_r_stack, put_r_rec_sound out k res_r.2 hk1 hbs_out]
      change (z0V ((ld1 ^ res1.1) +> ([1, 0, 1, 1] ^ res2.1) +> stack_to_tape res2.2)
        (MC (k - 1) (eval_lsb res_r.1) (stack_to_tape res_r.2))) [tm15]⊢*
        (z0V ((ld0 ^ (res1.1 + res2.1)) +> stack_to_tape res2.2)
        (MC (k - 1) (eval_lsb out) (stack_to_tape res_r.2)))
      rw [hm_eq, ← heval_out]
      exact absorb_general res1.1 (m_use - 1) (k - 1) (eval_lsb out)
        (stack_to_tape res2.2) (stack_to_tape res_r.2) (by rw [hk_eq]; dsimp [k] at hbl ⊢; omega)

def step_prim (s : MState) : Option MState :=
  with_prod (pop1 s.r) (fun pr =>
    match tm15 s.q pr.1 with
    | none => none
    | some (none, _) => none
    | some (some q', Stmt.write w d) =>
      let b_bit := bit_pat w
      match d with
      | Dir.right =>
        some_mstate q' (push_stack b_bit 1 1 s.l) pr.2
      | Dir.left =>
        with_prod (pop1 s.l) (fun pl =>
          let r1 := push_stack b_bit 1 1 pr.2
          let r2 := push_stack (bit_pat pl.1) 1 1 r1
          some_mstate q' pl.2 r2))

lemma step_prim_sound (s s' : MState) (h : step_prim s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold step_prim at h
  simp only [with_prod_eq] at h
  cases htm : tm15 s.q (pop1 s.r).1 with
  | none => rw [htm] at h; contradiction
  | some val =>
    rcases val with ⟨oq, stmt⟩
    cases oq with
    | none => rw [htm] at h; contradiction
    | some q' =>
      rcases stmt with ⟨w, d⟩
      rw [htm] at h
      cases d with
      | left =>
        simp only [with_prod_eq, some_mstate_eq, Option.some.injEq] at h
        subst h
        refine z0P tm15 _ _ ?_
        unfold mstate_to_cfg step
        dsimp only
        rw [pop1_sound s.r, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, htm]
        dsimp [Tape.move, Tape.write]
        rw [push_bit_sound (pop1 s.l).1, push_bit_sound w, Turing.ListBlank.head_cons,
          Turing.ListBlank.tail_cons, pop1_sound s.l, Turing.ListBlank.head_cons,
          Turing.ListBlank.tail_cons]
      | right =>
        simp only [some_mstate_eq, Option.some.injEq] at h
        subst h
        refine z0P tm15 _ _ ?_
        unfold mstate_to_cfg step
        dsimp only
        rw [pop1_sound s.r, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, htm]
        dsimp [Tape.move, Tape.write]
        rw [push_bit_sound w]

def step_m_q0 (s : MState) : Option MState :=
  let kbig := Nat.add (Nat.add s.l.length s.r.length) 4
  match try_pair_stack kbig s with
  | some s' => some s'
  | none =>
  match try_absorb_stack kbig s with
  | some s' => some s'
  | none =>
  match do_shift_right 0 3 1 1 1 s with
  | some s' => some s'
  | none => step_prim s

def step_m_q1 (s : MState) : Option MState :=
  match do_shift_left 1 1 1 0 1 s with
  | some s' => some s'
  | none => step_prim s

def step_m_q2 (s : MState) : Option MState :=
  match do_shift_left 2 2 3 1 2 s with
  | some s' => some s'
  | none => step_prim s

def step_m_q3 (s : MState) : Option MState :=
  match do_shift_right 3 1 1 0 1 s with
  | some s' => some s'
  | none =>
  match do_shift_right 3 3 2 1 1 s with
  | some s' => some s'
  | none =>
  match do_shift_right 3 4 10 14 4 s with
  | some s' => some s'
  | none =>
  match do_shift_right 3 4 5 7 4 s with
  | some s' => some s'
  | none => step_prim s

def step_m (s : MState) : Option MState :=
  match s.q.val with
  | 0 => step_m_q0 s
  | 1 => step_m_q1 s
  | 2 => step_m_q2 s
  | 3 => step_m_q3 s
  | _ => step_prim s

lemma step_m_sound (s s' : MState) (h : step_m s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold step_m at h
  rcases hq : s.q.val with _ | _ | _ | _ | n <;> rw [hq] at h
  · unfold step_m_q0 at h; dsimp only at h
    cases hp : try_pair_stack (Nat.add (Nat.add s.l.length s.r.length) 4) s with
    | some s1 => rw [hp] at h; simp only [Option.some.injEq] at h; subst h; exact try_pair_stack_sound _ s s1 hp
    | none =>
    rw [hp] at h; dsimp only at h
    cases ha : try_absorb_stack (Nat.add (Nat.add s.l.length s.r.length) 4) s with
    | some s1 => rw [ha] at h; simp only [Option.some.injEq] at h; subst h; exact try_absorb_stack_sound _ s s1 ha
    | none =>
    rw [ha] at h; dsimp only at h
    cases hs : do_shift_right 0 3 1 1 1 s with
    | some s1 => rw [hs] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_right_sound 0 3 1 1 1 7 s s1 rfl rfl sh_0_sound hs
    | none => rw [hs] at h; dsimp only at h; exact step_prim_sound s s' h
  · unfold step_m_q1 at h
    cases hs : do_shift_left 1 1 1 0 1 s with
    | some s1 => rw [hs] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_left_sound 1 1 1 0 1 0 s s1 rfl rfl sh_1_sound hs
    | none => rw [hs] at h; dsimp only at h; exact step_prim_sound s s' h
  · unfold step_m_q2 at h
    cases hs : do_shift_left 2 2 3 1 2 s with
    | some s1 => rw [hs] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_left_sound 2 2 3 1 2 1 s s1 rfl rfl sh_2_sound hs
    | none => rw [hs] at h; dsimp only at h; exact step_prim_sound s s' h
  · unfold step_m_q3 at h
    cases h3 : do_shift_right 3 1 1 0 1 s with
    | some s1 => rw [h3] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_right_sound 3 1 1 0 1 0 s s1 rfl rfl sh_3_sound h3
    | none =>
    rw [h3] at h; dsimp only at h
    cases h4 : do_shift_right 3 3 2 1 1 s with
    | some s1 => rw [h4] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_right_sound 3 3 2 1 1 7 s s1 rfl rfl sh_4_sound h4
    | none =>
    rw [h4] at h; dsimp only at h
    cases h5 : do_shift_right 3 4 10 14 4 s with
    | some s1 => rw [h5] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_right_sound 3 4 10 14 4 14 s s1 rfl rfl sh_5_sound h5
    | none =>
    rw [h5] at h; dsimp only at h
    cases h6 : do_shift_right 3 4 5 7 4 s with
    | some s1 => rw [h6] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_right_sound 3 4 5 7 4 7 s s1 rfl rfl sh_6_sound h6
    | none => rw [h6] at h; dsimp only at h; exact step_prim_sound s s' h
  · exact step_prim_sound s s' h

def forceStackCPS {α : Type} : Stack → (Stack → α) → α
  | [], k => k []
  | b :: rest, k =>
    with_block b (fun b' =>
      forceStackCPS rest (fun rest' =>
        k (b' :: rest')))

@[simp] lemma forceStackCPS_eq {α : Type} (s : Stack) (k : Stack → α) : forceStackCPS s k = k s := by
  induction s generalizing k with
  | nil => rfl
  | cons b rest ih => simp only [forceStackCPS, with_block_eq, ih]

def norm_mstate (s : MState) : MState :=
  with_nat s.q.val (fun _ =>
    forceStackCPS s.l (fun l' =>
      forceStackCPS s.r (fun r' =>
        ⟨s.q, l', r'⟩)))

@[simp] lemma norm_mstate_eq (s : MState) : norm_mstate s = s := by
  rcases s with ⟨q, l, r⟩
  simp only [norm_mstate, with_nat_eq, forceStackCPS_eq]

def maybe_norm (fuel : Nat) (s : MState) : MState :=
  if fuel % 16 = 0 then norm_mstate s else s

@[simp] lemma maybe_norm_eq (fuel : Nat) (s : MState) : maybe_norm fuel s = s := by
  unfold maybe_norm; split_ifs <;> simp

def run_m : Nat → MState → Option MState
  | 0, s => some s
  | fuel + 1, s =>
    match step_m s with
    | none => none
    | some s' => run_m fuel (maybe_norm fuel s')

lemma run_m_sound (fuel : Nat) (s s' : MState) (h : run_m fuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  induction fuel generalizing s with
  | zero =>
    simp [run_m] at h; subst h; exact ⟨0, rfl⟩
  | succ fuel ih =>
    simp only [run_m, maybe_norm_eq] at h
    cases hs : step_m s with
    | none => rw [hs] at h; contradiction
    | some s1 =>
      rw [hs] at h
      exact zSt (step_m_sound s s1 hs) (ih s1 h)

def is_halt_m (s : MState) : Bool :=
  s.q = 5 && (pop1 s.r).1 = 1

lemma is_halt_m_sound (s : MState) (h : is_halt_m s = true) :
    step tm15 (mstate_to_cfg s) = none := by
  unfold is_halt_m at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hq, hr⟩
  unfold mstate_to_cfg step
  dsimp only
  rw [hq, pop1_sound s.r, hr, Turing.ListBlank.head_cons]
  rfl

def cfg_0 : MState := ⟨1, [], []⟩
lemma run_m_trans {m n : Nat} {s1 s2 s3 : MState}
    (h1 : run_m m s1 = some s2) (h2 : run_m n s2 = some s3) :
    run_m (m + n) s1 = some s3 := by
  induction m generalizing s1 with
  | zero =>
    simp [run_m] at h1; subst h1; simpa using! h2
  | succ m ih =>
    simp only [run_m, Nat.succ_add] at h1 ⊢
    cases hs : step_m s1 with
    | none => simp [hs] at h1
    | some s' => simp [hs, maybe_norm_eq] at h1 ⊢; exact ih h1

def MReach (s1 s2 : MState) : Prop :=
  ∃ fuel, run_m fuel s1 = some s2

noncomputable def mkBlock_f_p  : Nat → Nat → Nat → Block :=
fun p w l =>
  @Nat.rec (fun _ => Block) ⟨0, 0, 0⟩ (fun p' _ =>
    @Nat.rec (fun _ => Block) ⟨0, 0, 0⟩ (fun w' _ =>
      @Nat.rec (fun _ => Block) ⟨0, 0, 0⟩ (fun l' _ =>
        ⟨p', w', l'⟩) (Nat.add 1 l)) (Nat.add 1 w)) (Nat.add 1 p)
noncomputable def rot1_f_p  : Nat → Nat → Nat :=
fun w p => Nat.add (Nat.shiftRight p 1) (Nat.mul (Nat.land p 1) (Nat.shiftLeft 1 (Nat.sub w 1)))
noncomputable def rot_mod_f_p  : Nat → Nat → Nat → Nat :=
fun w n p =>
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat)
      (rot_k w n p)
      (let r := Nat.mod n w
       @Bool.rec (fun _ => Nat)
         (Nat.add (Nat.shiftRight p r) (Nat.shiftLeft (Nat.land p (Nat.sub (Nat.shiftLeft 1 r) 1)) (Nat.sub w r)))
         p
         (Nat.beq r 0))
      (Bool.and (Nat.ble 2 w) (Bool.and (Nat.ble w 4) (Bool.and (Nat.ble p 15) (Nat.ble p (Nat.sub (Nat.shiftLeft 1 w) 1))))))
    p
    (Bool.or (Nat.beq p 0) (Bool.and (Nat.beq w 1) (Nat.beq p 1)))
noncomputable def bit_of_bool_f_p  : Nat → Bool :=
fun x => Nat.beq (Nat.land x 1) 1
noncomputable def push_stack_aux_f_p (mkBlock_f : Nat → Nat → Nat → Block) (rot_mod_f : Nat → Nat → Nat → Nat) : Block → Stack → Stack :=
fun b s =>
  @List.rec Block (fun _ => Block → Stack)
    (fun b => @Bool.rec (fun _ => Stack) [b] [] (Nat.beq b.pat 0))
    (fun top rest ih b =>
      @Bool.rec (fun _ => Stack)
        (b :: top :: rest)
        (ih (mkBlock_f b.pat b.width (Nat.add b.len top.len)))
        (Bool.and (Nat.beq b.width top.width) (Nat.beq (rot_mod_f b.width b.len b.pat) top.pat)))
    s b
noncomputable def push_stack_f_p (mkBlock_f : Nat → Nat → Nat → Block) (push_stack_aux_f : Block → Stack → Stack) : Nat → Nat → Nat → Stack → Stack :=
fun pat width len s =>
  @Bool.rec (fun _ => Stack) (push_stack_aux_f (mkBlock_f pat width len) s) s (Nat.beq len 0)
noncomputable def drop_stack_f_p (mkBlock_f : Nat → Nat → Nat → Block) (rot_mod_f : Nat → Nat → Nat → Nat) : Nat → Stack → Stack :=
fun n s =>
  @List.rec Block (fun _ => Nat → Stack)
    (fun _ => [])
    (fun top rest ih n =>
      @Bool.rec (fun _ => Stack)
        (@Bool.rec (fun _ => Stack)
          (mkBlock_f (rot_mod_f top.width n top.pat) top.width (Nat.sub top.len n) :: rest)
          (ih (Nat.sub n top.len))
          (Nat.ble top.len n))
        (top :: rest)
        (Nat.beq n 0))
    s n
noncomputable def pop1_b_f_p (mkBlock_f : Nat → Nat → Nat → Block) (rot1_f : Nat → Nat → Nat) (bit_of_bool_f : Nat → Bool) : Stack → Bool × Stack :=
fun s =>
  @List.rec Block (fun _ => Bool × Stack)
    (false, [])
    (fun top rest ih =>
      @Bool.rec (fun _ => Bool × Stack)
        (let bit := bit_of_bool_f top.pat
         @Bool.rec (fun _ => Bool × Stack)
           (bit, mkBlock_f (rot1_f top.width top.pat) top.width (Nat.sub top.len 1) :: rest)
           (bit, rest)
           (Nat.beq top.len 1))
        ih
        (Nat.beq top.len 0))
    s
noncomputable def pop_word_f_p (bit_of_bool_f : Nat → Bool) (pop1_b_f : Stack → Bool × Stack) : Nat → Nat → Stack → Option Stack :=
fun pat w s =>
  @Nat.rec (fun _ => Nat → Stack → Option Stack)
    (fun _ s => some s)
    (fun _ ih pat s =>
      let res := pop1_b_f s
      @Bool.rec (fun _ => Option Stack) none (ih (Nat.shiftRight pat 1) res.2)
        (Bool.not (Bool.xor res.1 (bit_of_bool_f pat))))
    w pat s
noncomputable def fast_match_f_p  : Nat → Nat → Block → Bool :=
fun pat w top =>
  @Bool.rec (fun _ => Bool)
    (0 < w && w ≤ top.len && rot_k top.width w top.pat == top.pat &&
     pat_word top.width top.pat w == word_of pat w)
    (Bool.and (Nat.ble w top.len)
      (let mul := match top.width with | 1 => 4095 | 2 => 1365 | 3 => 585 | _ => 273
       Bool.and (Nat.beq (Nat.land (Nat.shiftRight (Nat.mul top.pat mul) w) (Nat.sub (Nat.shiftLeft 1 top.width) 1)) top.pat)
         (Nat.beq (Nat.land (Nat.mul top.pat mul) (Nat.sub (Nat.shiftLeft 1 w) 1)) pat)))
    (Bool.and (Nat.ble 1 w)
      (Bool.and (Nat.ble w 4)
        (Bool.and (Nat.ble 1 top.width)
          (Bool.and (Nat.ble top.width 4)
            (Bool.and (Nat.ble top.pat (Nat.sub (Nat.shiftLeft 1 top.width) 1))
              (Nat.ble pat (Nat.sub (Nat.shiftLeft 1 w) 1)))))))
noncomputable def count_stack_mut_f_p (drop_stack_f : Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (fast_match_f : Nat → Nat → Block → Bool) : Nat → Nat → Nat → Nat → Stack → Nat × Stack :=
fun pat w fuel limit s =>
  @Nat.rec (fun _ => Nat → Stack → Nat × Stack)
    (fun _ s => (0, s))
    (fun _ ih limit s =>
      @Bool.rec (fun _ => Nat × Stack)
        (match s with
         | [] => (0, [])
         | top :: rest =>
           @Bool.rec (fun _ => Nat × Stack)
             (match pop_word_f pat w (top :: rest) with
              | some s1 =>
                let res := ih (Nat.sub limit 1) s1
                (Nat.add 1 res.1, res.2)
              | none => (0, top :: rest))
             (let bulk := Nat.min limit (Nat.div top.len w)
              let res := ih (Nat.sub limit bulk) (drop_stack_f (Nat.mul bulk w) (top :: rest))
              (Nat.add bulk res.1, res.2))
             (fast_match_f pat w top))
        (0, s)
        (Nat.beq limit 0))
    fuel limit s
noncomputable def mkPart_f_p  : Bool → Nat → PartList → PartList :=
fun b k xs =>
  @Nat.rec (fun _ => PartList) xs (fun k' _ =>
    @Bool.rec (fun _ => PartList) ((b, Nat.add 1 k') :: xs) []
      (Bool.and (Bool.not b) (match xs with | [] => true | _ => false))) k
noncomputable def bsize_parts_f_p  : PartList → Nat :=
@List.rec (Bool × Nat) (fun _ => Nat) 0 (fun hd _ ih => Nat.add hd.2 ih)
noncomputable def put_l_parts_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) : PartList → Stack → Stack :=
@List.rec (Bool × Nat) (fun _ => Stack → Stack)
  (fun s => s)
  (fun hd _ ih s =>
    push_stack_f (@Bool.rec (fun _ => Nat) 1 14 hd.1) (@Bool.rec (fun _ => Nat) 1 4 hd.1) (Nat.mul hd.2 4) (ih s))
noncomputable def put_l_stack_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (bsize_parts_f : PartList → Nat) (put_l_parts_f : PartList → Stack → Stack) : PartList → Nat → Stack → Stack :=
fun xs n s =>
  let bs := bsize_parts_f xs
  let s1 := @Bool.rec (fun _ => Stack) s (push_stack_f 1 1 (Nat.mul (Nat.sub n bs) 4) s) (Nat.ble (Nat.add bs 1) n)
  put_l_parts_f xs s1
noncomputable def put_r_rec_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) : PartList → Nat → Stack → Stack :=
@List.rec (Bool × Nat) (fun _ => Nat → Stack → Stack)
  (fun k s => push_stack_f 1 3 (Nat.sub (Nat.mul k 3) 2) s)
  (fun hd _ ih k s =>
    @Bool.rec (fun _ => Stack)
      (@Bool.rec (fun _ => Stack)
        (push_stack_f (@Bool.rec (fun _ => Nat) 1 0 hd.1) (@Bool.rec (fun _ => Nat) 3 1 hd.1) (Nat.mul hd.2 3) (ih (Nat.sub k hd.2) s))
        (push_stack_f (@Bool.rec (fun _ => Nat) 1 0 hd.1) (@Bool.rec (fun _ => Nat) 3 1 hd.1) (Nat.sub (Nat.mul hd.2 3) 2) s)
        (Nat.ble k hd.2))
      (ih k s)
      (Nat.beq hd.2 0))
noncomputable def parse_step_l_f_p (drop_stack_f : Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) : Nat → Stack → Option (Bool × Nat × Stack) :=
fun limit s =>
  match s with
  | [] => none
  | top :: rest =>
    @Bool.rec (fun _ => Option (Bool × Nat × Stack))
      (@Bool.rec (fun _ => Option (Bool × Nat × Stack))
        (match pop_word_f 15 4 (top :: rest) with
         | some s1 => some (false, 1, s1)
         | none =>
           match pop_word_f 14 4 (top :: rest) with
           | some s1 => some (true, 1, s1)
           | none => none)
        (let k := Nat.min limit (Nat.div top.len 4)
         some (true, k, drop_stack_f (Nat.mul k 4) (top :: rest)))
        (Bool.and (Nat.beq top.width 4) (Bool.and (Nat.beq top.pat 14) (Nat.ble 4 top.len))))
      (let k := Nat.min limit (Nat.div top.len 4)
       some (false, k, drop_stack_f (Nat.mul k 4) (top :: rest)))
      (Bool.and (Nat.beq top.width 1) (Bool.and (Nat.beq top.pat 1) (Nat.ble 4 top.len)))
noncomputable def parse_l_f_p (parse_step_l_f : Nat → Stack → Option (Bool × Nat × Stack)) : Nat → Nat → Stack → PartList × Stack :=
@Nat.rec (fun _ => Nat → Stack → PartList × Stack)
  (fun _ s => ([], s))
  (fun _ ih limit s =>
    @Bool.rec (fun _ => PartList × Stack)
      (match parse_step_l_f limit s with
       | none => ([], s)
       | some (bit, k, s1) =>
         let res := ih (Nat.sub limit k) s1
         @Bool.rec (fun _ => PartList × Stack)
           ((bit, k) :: res.1, res.2)
           ([], s)
           (Bool.and (Bool.not bit) (match res.1 with | [] => true | _ => false)))
      ([], s)
      (Nat.beq limit 0))
noncomputable def parse_step_r_f_p (drop_stack_f : Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) : Nat → Stack → Option (Bool × Nat × Stack) :=
fun limit s =>
  match s with
  | [] => none
  | top :: rest =>
    @Bool.rec (fun _ => Option (Bool × Nat × Stack))
      (@Bool.rec (fun _ => Option (Bool × Nat × Stack))
        (match pop_word_f 1 3 (top :: rest) with
         | some s1 => some (false, 1, s1)
         | none =>
           match pop_word_f 0 3 (top :: rest) with
           | some s1 => some (true, 1, s1)
           | none => none)
        (let k := Nat.min limit (Nat.div top.len 3)
         some (true, k, drop_stack_f (Nat.mul k 3) (top :: rest)))
        (Bool.and (Nat.beq top.width 1) (Bool.and (Nat.beq top.pat 0) (Nat.ble 3 top.len))))
      (let k := Nat.min limit (Nat.div top.len 3)
       some (false, k, drop_stack_f (Nat.mul k 3) (top :: rest)))
      (Bool.and (Nat.beq top.width 3) (Bool.and (Nat.beq top.pat 1) (Nat.ble 3 top.len)))
noncomputable def parse_r_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) (parse_step_r_f : Nat → Stack → Option (Bool × Nat × Stack)) : Nat → Nat → Stack → PartList × Stack :=
@Nat.rec (fun _ => Nat → Stack → PartList × Stack)
  (fun _ s => ([], s))
  (fun _ ih limit s =>
    @Bool.rec (fun _ => PartList × Stack)
      (match s with
       | [] => ([(true, limit)], [])
       | top :: rest =>
         match parse_step_r_f limit (top :: rest) with
         | none =>
           let p := pop1_b_f (top :: rest)
           @Bool.rec (fun _ => PartList × Stack) ([], top :: rest) ([(true, 1)], p.2) (Bool.not p.1)
         | some (bit, k, s1) =>
           let res := ih (Nat.sub limit k) s1
           match res.1 with
           | [] => @Bool.rec (fun _ => PartList × Stack) ([], top :: rest) ([(true, k)], push_stack_f 0 1 2 s1) bit
           | _ => ((bit, k) :: res.1, res.2))
      ([], s)
      (Nat.beq limit 0))
noncomputable def sub_lsb_f_p (mkPart_f : Bool → Nat → PartList → PartList) : Nat → Bool → PartList → PartList → Option PartList :=
@Nat.rec (fun _ => Bool → PartList → PartList → Option PartList)
  (fun _ _ _ => none)
  (fun _ ih c xs ys =>
    match xs with
    | [] =>
      @Bool.rec (fun _ => Option PartList) none (some [])
        (Bool.and (match ys with | [] => true | _ => false) (Bool.not c))
    | (px, kx) :: xrest =>
      let qy := match ys with | [] => false | (q, _) :: _ => q
      let ly := match ys with | [] => kx | (_, l) :: _ => l
      let n := Nat.min kx ly
      let nx := @Bool.rec (fun _ => PartList) xrest ((px, Nat.sub kx n) :: xrest) (Nat.ble (Nat.add n 1) kx)
      let ny := match ys with | [] => [] | (q, l) :: yrest => @Bool.rec (fun _ => PartList) yrest ((q, Nat.sub l n) :: yrest) (Nat.ble (Nat.add n 1) l)
      @Bool.rec (fun _ => Option PartList)
        (let s1_1 := Bool.xor (Bool.xor px qy) c
         let s1_2 := Bool.or (Bool.and (Bool.not px) (Bool.or qy c)) (Bool.and qy c)
         let s2_1 := Bool.xor (Bool.xor px qy) s1_2
         let s2_2 := Bool.or (Bool.and (Bool.not px) (Bool.or qy s1_2)) (Bool.and qy s1_2)
         let next_c := @Bool.rec (fun _ => Bool) s1_2 s2_2 (Nat.ble 2 n)
         match ih next_c nx ny with
         | none => none
         | some out => some (mkPart_f s1_1 1 (@Bool.rec (fun _ => PartList) out (mkPart_f s2_1 (Nat.sub n 1) out) (Nat.ble 2 n))))
        (ih c nx ny)
        (Nat.beq n 0))
noncomputable def choose_limit_r_f_p (drop_stack_f : Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) : Nat → Nat → Nat → Stack → Nat :=
fun n fuel done r =>
  @Nat.rec (fun _ => Nat → Stack → Nat)
    (fun _ _ => Nat.add n 1)
    (fun _ ih done s =>
      match s with
      | [] => @Bool.rec (fun _ => Nat) (Nat.add done 1) (Nat.add n 1) (Nat.ble done n)
      | top :: rest =>
        @Bool.rec (fun _ => Nat)
          (@Bool.rec (fun _ => Nat)
            (match pop_word_f 1 3 (top :: rest) with
             | some r1 => ih (Nat.add done 1) r1
             | none =>
               match pop_word_f 0 3 (top :: rest) with
               | some r1 =>
                 @Bool.rec (fun _ => Nat)
                   (ih (Nat.add done 1) r1)
                   (Nat.add done 1)
                   (Nat.ble n done)
               | none =>
                 @Bool.rec (fun _ => Nat) done (Nat.add done 1) (Bool.not (pop1_b_f (top :: rest)).1))
            (let div := Nat.div top.len 3
             let next_done := Nat.add done div
             @Bool.rec (fun _ => Nat)
               (ih next_done (drop_stack_f (Nat.mul div 3) (top :: rest)))
               (Nat.min (Nat.max (Nat.add n 2) (Nat.add done 2)) next_done)
               (Nat.ble (Nat.add n 1) next_done))
            (Bool.and (Nat.beq top.width 1) (Bool.and (Nat.beq top.pat 0) (Nat.ble 3 top.len))))
          (let div := Nat.div top.len 3
           ih (Nat.add done div) (drop_stack_f (Nat.mul div 3) (top :: rest)))
          (Bool.and (Nat.beq top.width 3) (Bool.and (Nat.beq top.pat 1) (Nat.ble 3 top.len))))
    fuel done r
noncomputable def push_prefix_l_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) : Stack → Stack :=
fun l => push_stack_f 1 1 1 (push_stack_f 0 1 1 (push_stack_f 1 1 3 l))
noncomputable def build_vprime_f_p (mkPart_f : Bool → Nat → PartList → PartList) : Nat → Nat → PartList :=
fun n m_use =>
  @Bool.rec (fun _ => PartList)
    (mkPart_f true 1 [])
    (mkPart_f true 1 (mkPart_f false n (mkPart_f true (Nat.sub m_use 1) [])))
    (Nat.ble 2 m_use)
noncomputable def do_shift_right_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack) : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState :=
fun k128 =>
fun sq sw sin sout sout_w s =>
  @Bool.rec (fun _ => Option MState) none
    (let target2 := Nat.add sin (Nat.mul sin (Nat.shiftLeft 1 sw))
     match pop_word_f target2 (Nat.mul 2 sw) s.r with
     | none => none
     | some _ =>
       let res := count_stack_mut_f sin sw k128 100000000 s.r
       some ⟨sq, push_stack_f sout sout_w (Nat.mul res.1 sw) s.l, res.2⟩)
    (Nat.beq s.q.val sq.val)
noncomputable def do_shift_left_f_p (bit_of_bool_f : Nat → Bool) (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack) : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState :=
fun k128 =>
fun sq sw sin sout sout_w s =>
  @Bool.rec (fun _ => Option MState) none
    (let target2 := Nat.add sin (Nat.mul sin (Nat.shiftLeft 1 sw))
     let p_r := pop1_b_f s.r
     @Bool.rec (fun _ => Option MState) none
       (@Bool.rec (fun _ => Option MState) none
         (let l1 := push_stack_f (@Bool.rec (fun _ => Nat) 0 1 p_r.1) 1 1 s.l
          let res := count_stack_mut_f sin sw k128 100000000 l1
          let p_l := pop1_b_f res.2
          some ⟨sq, p_l.2, push_stack_f (@Bool.rec (fun _ => Nat) 0 1 p_l.1) 1 1 (push_stack_f sout sout_w (Nat.mul res.1 sw) p_r.2)⟩)
         (match pop_word_f (Nat.shiftRight target2 1) (Nat.sub (Nat.mul 2 sw) 1) s.l with | some _ => true | none => false))
       (Bool.not (Bool.xor p_r.1 (bit_of_bool_f target2))))
    (Nat.beq s.q.val sq.val)
noncomputable def try_pair_stack_f_p (pop_word_f : Nat → Nat → Stack → Option Stack) (bsize_parts_f : PartList → Nat) (put_l_stack_f : PartList → Nat → Stack → Stack) (put_r_rec_f : PartList → Nat → Stack → Stack) (parse_l_f : Nat → Nat → Stack → PartList × Stack) (parse_r_f : Nat → Nat → Stack → PartList × Stack) (sub_lsb_f : Nat → Bool → PartList → PartList → Option PartList) (choose_limit_r_f : Nat → Nat → Nat → Stack → Nat) (push_prefix_l_f : Stack → Stack) : Nat → MState → Option MState :=
fun k128 =>
fun s =>
  @Bool.rec (fun _ => Option MState) none
    (match pop_word_f 29 5 s.l with
     | none => none
     | some lc =>
       let res_l := parse_l_f k128 100000000 lc
       match res_l.1 with
       | [] => none
       | a_hd :: a_tl =>
         let a := a_hd :: a_tl
         let n := bsize_parts_f a
         let lim_r := choose_limit_r_f n k128 0 s.r
         @Bool.rec (fun _ => Option MState)
           (let res_r := parse_r_f k128 lim_r s.r
            match res_r.1 with
            | [] => none
            | b_hd :: b_tl =>
              let b := b_hd :: b_tl
              let k := bsize_parts_f b
              match sub_lsb_f k128 false a b with
              | some out => some ⟨0, push_prefix_l_f (put_l_stack_f out n res_l.2), put_r_rec_f [] k res_r.2⟩
              | none =>
                match sub_lsb_f k128 false b a with
                | some out => some ⟨0, push_prefix_l_f (put_l_stack_f [] n res_l.2), put_r_rec_f out k res_r.2⟩
                | none => none)
           none
           (Nat.beq lim_r 0))
    (Nat.beq s.q.val 0)
noncomputable def try_absorb_stack_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack) (bsize_parts_f : PartList → Nat) (put_r_rec_f : PartList → Nat → Stack → Stack) (parse_r_f : Nat → Nat → Stack → PartList × Stack) (sub_lsb_f : Nat → Bool → PartList → PartList → Option PartList) (choose_limit_r_f : Nat → Nat → Nat → Stack → Nat) (push_prefix_l_f : Stack → Stack) (build_vprime_f : Nat → Nat → PartList) : Nat → MState → Option MState :=
fun k128 =>
fun s =>
  @Bool.rec (fun _ => Option MState) none
    (match pop_word_f 29 5 s.l with
     | none => none
     | some lc0 =>
       let res1 := count_stack_mut_f 15 4 k128 100000000 lc0
       let res_m := count_stack_mut_f 13 4 k128 100000000 res1.2
       @Bool.rec (fun _ => Option MState)
         (let lim_r := choose_limit_r_f (Nat.add res1.1 res_m.1) k128 0 s.r
          @Bool.rec (fun _ => Option MState)
            (let res_r := parse_r_f k128 lim_r s.r
             match res_r.1 with
             | [] => none
             | b_hd :: b_tl =>
               let b := b_hd :: b_tl
               let k := bsize_parts_f b
               let m_init := Nat.min res_m.1 (@Bool.rec (fun _ => Nat) 1 (Nat.sub k res1.1) (Nat.ble (Nat.add res1.1 1) k))
               @Bool.rec (fun _ => Option MState)
                 (let try1 := sub_lsb_f k128 false b (build_vprime_f res1.1 m_init)
                  let res_sub : Option (Nat × PartList) :=
                    match try1 with
                    | some out => some (m_init, out)
                    | none =>
                      @Bool.rec (fun _ => Option (Nat × PartList))
                        (match sub_lsb_f k128 false b (build_vprime_f res1.1 (Nat.sub m_init 1)) with
                         | some out => some (Nat.sub m_init 1, out)
                         | none => none)
                        none
                        (Nat.ble m_init 1)
                  match res_sub with
                  | none => none
                  | some (m_use, out) =>
                    let res2 := count_stack_mut_f 13 4 k128 m_use res1.2
                    @Bool.rec (fun _ => Option MState) none
                      (some ⟨0, push_prefix_l_f (push_stack_f 14 4 (Nat.mul (Nat.add res1.1 res2.1) 4) res2.2), put_r_rec_f out k res_r.2⟩)
                      (Nat.beq res2.1 m_use))
                 none
                 (Nat.beq m_init 0))
            none
            (Nat.beq lim_r 0))
         none
         (Nat.beq res_m.1 0))
    (Nat.beq s.q.val 0)
noncomputable def step_prim_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) : MState → Option MState :=
fun s =>
  let pr := pop1_b_f s.r
  let (has_next, next_q, use_l, b_r) : Bool × Fin 6 × Bool × Nat :=
    match s.q.val, pr.1 with
    | 0, false => (true, 1, true, 1)
    | 0, true  => (true, 4, false, 1)
    | 1, false => (true, 2, true, 1)
    | 1, true  => (true, 1, true, 0)
    | 2, false => (true, 3, false, 1)
    | 2, true  => (true, 4, true, 0)
    | 3, false => (true, 0, false, 1)
    | 3, true  => (true, 3, false, 0)
    | 4, false => (true, 3, false, 1)
    | 4, true  => (true, 5, false, 0)
    | 5, false => (true, 1, true, 0)
    | _, _     => (false, 0, false, 0)
  @Bool.rec (fun _ => Option MState)
    none
    (@Bool.rec (fun _ => Option MState)
      (some ⟨next_q, push_stack_f b_r 1 1 s.l, pr.2⟩)
      (let pl := pop1_b_f s.l
       some ⟨next_q, pl.2, push_stack_f (@Bool.rec (fun _ => Nat) 0 1 pl.1) 1 1 (push_stack_f b_r 1 1 pr.2)⟩)
      use_l)
    has_next
noncomputable def step_m_f_p (do_shift_right_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState) (do_shift_left_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState) (try_pair_stack_f : Nat → MState → Option MState) (try_absorb_stack_f : Nat → MState → Option MState) (step_prim_f : MState → Option MState) : Nat → MState → Option MState :=
fun _ =>
fun s =>
  let macro_res : Option MState :=
    match s.q.val with
    | 0 =>
      let kbig := Nat.add (Nat.add s.l.length s.r.length) 4
      match (try_pair_stack_f kbig) s with
      | some s' => some s'
      | none =>
        match (try_absorb_stack_f kbig) s with
        | some s' => some s'
        | none => (do_shift_right_f 8) 0 3 1 1 1 s
    | 1 => (do_shift_left_f 8) 1 1 1 0 1 s
    | 2 => (do_shift_left_f 8) 2 2 3 1 2 s
    | 3 =>
      match (do_shift_right_f 8) 3 1 1 0 1 s with
      | some s' => some s'
      | none =>
        match (do_shift_right_f 8) 3 3 2 1 1 s with
        | some s' => some s'
        | none =>
          match (do_shift_right_f 8) 3 4 10 14 4 s with
          | some s' => some s'
          | none => (do_shift_right_f 8) 3 4 5 7 4 s
    | _ => none
  match macro_res with
  | some s' => some s'
  | none => step_prim_f s


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false

@[simp] lemma if_true_eq_true {α : Type} (t e : α) : (if true = true then t else e) = t := rfl
@[simp] lemma if_false_eq_true {α : Type} (t e : α) : (if false = true then t else e) = e := rfl
@[simp] lemma bool_true_and_b (b : Bool) : (true && b) = b := rfl
@[simp] lemma nat_add_1_succ {α : Type} (z : α) (f : Nat → α) (x : Nat) :
    @Nat.rec (fun _ => α) z (fun p _ => f p) (Nat.add 1 x) = f x := by
  have h : Nat.add 1 x = Nat.succ x := Nat.add_comm 1 x
  rw [h]

@[simp] lemma bool_rec_eq {α : Type} (f t : α) (b : Bool) :
    @Bool.rec (fun _ => α) f t b = if b then t else f := by
  cases b <;> rfl

@[simp] lemma nat_beq_def (x y : Nat) : x.beq y = (x == y) := by
  cases h1 : x.beq y <;> cases h2 : (x == y) <;> simp_all [Nat.beq_eq]
@[simp] lemma nat_ble_def (x y : Nat) : x.ble y = decide (x ≤ y) := by
  by_cases h : x ≤ y
  · rw [Nat.ble_eq.mpr h, decide_eq_true h]
  · cases hb : x.ble y
    · exact (decide_eq_false h).symm
    · exact False.elim (h (Nat.ble_eq.mp hb))
@[simp] lemma nat_add_def (x y : Nat) : x.add y = x + y := rfl
@[simp] lemma nat_sub_def (x y : Nat) : x.sub y = x - y := rfl
@[simp] lemma nat_mul_def (x y : Nat) : x.mul y = x * y := rfl
@[simp] lemma nat_div_def (x y : Nat) : x.div y = x / y := rfl
@[simp] lemma nat_mod_def (x y : Nat) : x.mod y = x % y := rfl
@[simp] lemma nat_min_def (x y : Nat) : x.min y = min x y := rfl
@[simp] lemma nat_max_def (x y : Nat) : x.max y = max x y := rfl
@[simp] lemma nat_land_def (x y : Nat) : x.land y = x &&& y := rfl
@[simp] lemma nat_shiftRight_def (x y : Nat) : x.shiftRight y = x >>> y := rfl
@[simp] lemma nat_shiftLeft_def (x y : Nat) : x.shiftLeft y = x <<< y := rfl

lemma mkBlock_p_eq : mkBlock_f_p = Block.mk := by
  funext p w l; unfold mkBlock_f_p; simp only [nat_add_1_succ]

lemma rot1_p_eq : rot1_f_p = rot1 := by
  funext w p; unfold rot1_f_p rot1
  simp only [nat_shiftRight_def, nat_land_def, nat_shiftLeft_def, nat_sub_def, nat_mul_def, nat_add_def,
    Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.one_mul]

lemma rot_mod_fin_eq :
    ∀ (w : Fin 5) (p : Fin 16) (r : Fin 5),
      1 ≤ w.val → p.val ≤ (Nat.shiftLeft 1 w.val) - 1 → 1 ≤ r.val → r.val < w.val →
      Nat.add (Nat.shiftRight p.val r.val)
        (Nat.shiftLeft (Nat.land p.val (Nat.sub (Nat.shiftLeft 1 r.val) 1)) (Nat.sub w.val r.val)) ==
      rot_k w.val r.val p.val := by decide +kernel

lemma rot_k_period_fin :
    ∀ (w : Fin 5) (p : Fin 16),
      1 ≤ w.val → p.val ≤ (Nat.shiftLeft 1 w.val) - 1 → rot_k w.val w.val p.val = p.val := by decide +kernel

lemma rot_mod_p_eq : rot_mod_f_p = rot_mod := by
  funext w n p
  rw [rot_mod_eq]
  unfold rot_mod_f_p
  simp only [bool_rec_eq, nat_beq_def, nat_ble_def]
  split_ifs with h0 hw hr
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h0
    rcases h0 with rfl | ⟨rfl, rfl⟩
    · exact (rot_k_zero w n).symm
    · exact (rot_k_one_one n).symm
  · simp only [Bool.and_eq_true, decide_eq_true_eq, nat_sub_def] at hw
    rcases hw with ⟨hw2, hw4, hp15, hp⟩
    have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw2
    have hper := rot_k_period_fin ⟨w, Nat.lt_succ_of_le hw4⟩ ⟨p, Nat.lt_succ_of_le hp15⟩ hw1 hp
    simp only [nat_mod_def, beq_iff_eq] at hr
    have hdiv := Nat.div_add_mod n w
    conv_rhs => rw [← hdiv]
    rw [rot_k_period w p hper (n / w) (n % w), hr]; rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq, nat_sub_def] at hw
    rcases hw with ⟨hw2, hw4, hp15, hp⟩
    have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw2
    have hw0 : 0 < w := Nat.lt_of_lt_of_le (by decide : 0 < 1) hw1
    have hper := rot_k_period_fin ⟨w, Nat.lt_succ_of_le hw4⟩ ⟨p, Nat.lt_succ_of_le hp15⟩ hw1 hp
    have hdiv := Nat.div_add_mod n w
    conv_rhs => rw [← hdiv]
    rw [rot_k_period w p hper (n / w) (n % w)]
    have hrmod : n % w < w := Nat.mod_lt n hw0
    have hr1 : 1 ≤ n % w := by
      simp only [nat_mod_def] at hr
      cases hc : (n % w == 0)
      · rw [beq_eq_false_iff_ne] at hc; exact Nat.pos_of_ne_zero hc
      · exact False.elim (hr hc)
    have hfin := rot_mod_fin_eq ⟨w, Nat.lt_succ_of_le hw4⟩ ⟨p, Nat.lt_succ_of_le hp15⟩
      ⟨n % w, Nat.lt_trans hrmod (Nat.lt_succ_of_le hw4)⟩ hw1 hp hr1 hrmod
    exact of_decide_eq_true hfin
  · rfl

lemma bit_of_bool_p_eq : bit_of_bool_f_p = (fun x => bit_of x == 1) := by
  funext x; unfold bit_of_bool_f_p bit_of
  simp only [nat_land_def, nat_beq_def, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h2 | h2 <;> rw [h2] <;> rfl

lemma push_stack_aux_p_eq
    {mkBlock_f} (h1 : mkBlock_f = Block.mk)
    {rot_mod_f} (h2 : rot_mod_f = rot_mod) :
    push_stack_aux_f_p mkBlock_f rot_mod_f = push_stack_aux := by
  subst h1; subst h2; funext b s
  unfold push_stack_aux_f_p
  induction s generalizing b with
  | nil =>
    unfold push_stack_aux
    simp only [bool_rec_eq, nat_beq_def]
    by_cases hp : b.pat = 0 <;> simp [hp]
  | cons top rest ih =>
    unfold push_stack_aux
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_add_def, with_nat_eq]

lemma push_stack_p_eq
    {mkBlock_f} (h1 : mkBlock_f = Block.mk)
    {push_stack_aux_f} (h2 : push_stack_aux_f = push_stack_aux) :
    push_stack_f_p mkBlock_f push_stack_aux_f = push_stack := by
  subst h1; subst h2; funext pat width len s
  unfold push_stack_f_p push_stack
  simp only [bool_rec_eq, nat_beq_def, with_stack_eq, with_nat_eq]
  by_cases hlen : len = 0 <;> simp [hlen]

lemma drop_stack_p_eq
    {mkBlock_f} (h1 : mkBlock_f = Block.mk)
    {rot_mod_f} (h2 : rot_mod_f = rot_mod) :
    drop_stack_f_p mkBlock_f rot_mod_f = drop_stack := by
  subst h1; subst h2; funext n s
  unfold drop_stack_f_p
  induction s generalizing n with
  | nil => rfl
  | cons top rest ih =>
    unfold drop_stack
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_sub_def, with_nat_eq]
    by_cases hn : n = 0
    · simp only [hn, beq_self_eq_true, if_true_eq_true, ↓reduceIte]
    · have hne : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
      rw [hne]; simp only [if_false_eq_true, hn, ↓reduceIte]
      by_cases hle : top.len ≤ n
      · simp only [hle, decide_true, if_true_eq_true, ↓reduceIte]
      · simp only [hle, decide_false, if_false_eq_true, ↓reduceIte]

lemma pop1_b_p_eq
    {mkBlock_f} (h1 : mkBlock_f = Block.mk)
    {rot1_f} (h2 : rot1_f = rot1)
    {bit_of_bool_f} (h3 : bit_of_bool_f = fun x => bit_of x == 1) :
    pop1_b_f_p mkBlock_f rot1_f bit_of_bool_f = fun s => ((pop1 s).1 == 1, (pop1 s).2) := by
  subst h1; subst h2; subst h3; funext s
  unfold pop1_b_f_p
  induction s with
  | nil => rfl
  | cons top rest ih =>
    unfold pop1
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_sub_def, with_nat_eq]
    by_cases h0 : top.len = 0
    · simp only [h0, beq_self_eq_true, if_true_eq_true, ↓reduceIte]
    · have hne0 : (top.len == 0) = false := beq_eq_false_iff_ne.mpr h0
      rw [hne0]; simp only [if_false_eq_true, h0, ↓reduceIte]
      by_cases h1 : top.len = 1
      · simp only [h1, beq_self_eq_true, if_true_eq_true, ↓reduceIte]
      · have hne1 : (top.len == 1) = false := beq_eq_false_iff_ne.mpr h1
        rw [hne1]; simp only [if_false_eq_true, h1, ↓reduceIte]

lemma sym_xnor_eq : ∀ (a b : Fin 2), ((!(a == 1 ^^ b == 1)) = true) = (a = b) := by decide

lemma pop_word_p_eq
    {bit_of_bool_f} (h1 : bit_of_bool_f = fun x => bit_of x == 1)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2)) :
    pop_word_f_p bit_of_bool_f pop1_b_f = pop_word := by
  subst h1; subst h2; funext pat w s
  unfold pop_word_f_p
  induction w generalizing pat s with
  | zero => rfl
  | succ w ih =>
    unfold pop_word
    simp only [ih]
    simp only [bool_rec_eq, with_prod_eq, sym_xnor_eq, nat_shiftRight_def]
    have hsh : ∀ x : Nat, x >>> 1 = x / 2 := fun _ => rfl
    simp only [hsh]

lemma fast_match_core_fin :
    ∀ (w : Fin 5) (tw : Fin 5) (tp : Fin 16) (pat : Fin 16),
      1 ≤ w.val → 1 ≤ tw.val → tp.val ≤ (Nat.shiftLeft 1 tw.val) - 1 → pat.val ≤ (Nat.shiftLeft 1 w.val) - 1 →
      (let mul := match tw.val with | 1 => 4095 | 2 => 1365 | 3 => 585 | _ => 273
       Bool.and (Nat.beq (Nat.land (Nat.shiftRight (Nat.mul tp.val mul) w.val) (Nat.sub (Nat.shiftLeft 1 tw.val) 1)) tp.val)
         (Nat.beq (Nat.land (Nat.mul tp.val mul) (Nat.sub (Nat.shiftLeft 1 w.val) 1)) pat.val)) =
      (rot_k tw.val w.val tp.val == tp.val && pat_word tw.val tp.val w.val == word_of pat.val w.val) := by
  decide +kernel

lemma fast_match_p_eq :
    fast_match_f_p = fun pat w top =>
      (0 < w && w ≤ top.len && rot_k top.width w top.pat == top.pat &&
       pat_word top.width top.pat w == word_of pat w) := by
  funext pat w top
  unfold fast_match_f_p
  simp only [bool_rec_eq, nat_ble_def]
  split_ifs with hg
  · simp only [Bool.and_eq_true, decide_eq_true_eq, nat_sub_def] at hg
    rcases hg with ⟨hw1, hw4, htw1, htw4, htp, hpat⟩
    have h15 : ∀ (k : Fin 5), (Nat.shiftLeft 1 k.val).sub 1 ≤ 15 := by decide
    have htp16 : (Nat.shiftLeft 1 top.width).sub 1 ≤ 15 := h15 ⟨top.width, by omega⟩
    have hpat16 : (Nat.shiftLeft 1 w).sub 1 ≤ 15 := h15 ⟨w, by omega⟩
    simp only [nat_sub_def] at htp16 hpat16
    have hcore := fast_match_core_fin ⟨w, by omega⟩ ⟨top.width, by omega⟩ ⟨top.pat, by omega⟩ ⟨pat, by omega⟩
      hw1 htw1 htp hpat
    dsimp only at hcore
    rw [hcore]
    have hw_pos : decide (0 < w) = true := decide_eq_true (by omega)
    rw [hw_pos, Bool.true_and]
    cases decide (w ≤ top.len) <;> cases (rot_k top.width w top.pat == top.pat) <;>
      cases (pat_word top.width top.pat w == word_of pat w) <;> rfl
  · rfl


lemma count_stack_mut_p_eq
    {drop_stack_f} (h1 : drop_stack_f = drop_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word)
    {fast_match_f} (h3 : fast_match_f = fun pat w top =>
      (0 < w && w ≤ top.len && rot_k top.width w top.pat == top.pat &&
       pat_word top.width top.pat w == word_of pat w)) :
    count_stack_mut_f_p drop_stack_f pop_word_f fast_match_f = count_stack_mut := by
  subst h1; subst h2; subst h3
  funext pat w fuel limit s
  unfold count_stack_mut_f_p
  induction fuel generalizing limit s with
  | zero => rfl
  | succ fuel ih =>
    unfold count_stack_mut
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_div_def, nat_mul_def, nat_sub_def, nat_add_def,
      nat_min_def, with_nat_eq, with_stack_eq, with_prod_eq]
    by_cases hlim : limit = 0
    · simp [hlim]
    · have hne : (limit == 0) = false := beq_eq_false_iff_ne.mpr hlim
      rw [hne]; simp only [if_false_eq_true, hlim, ↓reduceIte]

lemma mkPart_p_eq : mkPart_f_p = cons_lsb := by
  funext b k xs
  unfold mkPart_f_p cons_lsb
  cases k <;> cases xs <;> simp only [bool_rec_eq, nat_add_def, with_list_eq, Nat.add_comm 1 _] <;> cases b <;> rfl

lemma bsize_parts_p_eq : bsize_parts_f_p = bsize_parts := by
  funext xs; unfold bsize_parts_f_p
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨b, k⟩
    simp only [ih]
    simp only [bsize_parts, nat_add_def]

lemma put_l_parts_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack) :
    put_l_parts_f_p push_stack_f = put_l_parts := by
  subst h1; funext xs s; unfold put_l_parts_f_p
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨b, k⟩
    simp only [ih]
    simp only [put_l_parts, bool_rec_eq, nat_mul_def]

lemma put_l_stack_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {bsize_parts_f} (h2 : bsize_parts_f = bsize_parts)
    {put_l_parts_f} (h3 : put_l_parts_f = put_l_parts) :
    put_l_stack_f_p push_stack_f bsize_parts_f put_l_parts_f = put_l_stack := by
  subst h1; subst h2; subst h3; funext xs n s
  unfold put_l_stack_f_p put_l_stack
  simp only [bool_rec_eq, nat_ble_def, nat_add_def, nat_sub_def, nat_mul_def]
  congr 1
  by_cases hlt : bsize_parts xs < n
  · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
  · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]

lemma put_r_rec_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack) :
    put_r_rec_f_p push_stack_f = put_r_rec := by
  subst h1; funext xs k s; unfold put_r_rec_f_p
  induction xs generalizing k s with
  | nil => simp only [put_r_rec, nat_sub_def, nat_mul_def]
  | cons hd tl ih =>
    rcases hd with ⟨b, m⟩
    unfold put_r_rec
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_sub_def, nat_mul_def]
    by_cases hm : m = 0
    · simp [hm]
    · have hne : (m == 0) = false := beq_eq_false_iff_ne.mpr hm
      rw [hne]; simp only [if_false_eq_true, hm, ↓reduceIte]
      by_cases hle : k ≤ m <;> simp [hle]

lemma parse_step_l_p_eq
    {drop_stack_f} (h1 : drop_stack_f = drop_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word) :
    parse_step_l_f_p drop_stack_f pop_word_f = parse_step_l := by
  subst h1; subst h2; funext limit s
  unfold parse_step_l_f_p parse_step_l
  cases s with
  | nil => rfl
  | cons top rest =>
    simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_div_def, nat_mul_def, nat_min_def, Bool.and_assoc]

lemma parse_l_p_eq
    {parse_step_l_f} (h1 : parse_step_l_f = parse_step_l) :
    parse_l_f_p parse_step_l_f = parse_l := by
  subst h1; funext fuel limit s; unfold parse_l_f_p
  induction fuel generalizing limit s with
  | zero => rfl
  | succ fuel ih =>
    unfold parse_l
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_sub_def, with_prod_eq, with_list_eq, with_stack_eq]
    by_cases hlim : limit = 0
    · simp [hlim]
    · have hne : (limit == 0) = false := beq_eq_false_iff_ne.mpr hlim
      rw [hne]; simp only [if_false_eq_true, hlim, ↓reduceIte]
      cases parse_step_l limit s with
      | none => rfl
      | some val =>
        rcases val with ⟨b, k, s1⟩; dsimp only
        cases b <;> cases (parse_l fuel (limit - k) s1).1 <;> rfl

lemma parse_step_r_p_eq
    {drop_stack_f} (h1 : drop_stack_f = drop_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word) :
    parse_step_r_f_p drop_stack_f pop_word_f = parse_step_r := by
  subst h1; subst h2; funext limit s
  unfold parse_step_r_f_p parse_step_r
  cases s with
  | nil => rfl
  | cons top rest =>
    simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_div_def, nat_mul_def, nat_min_def, Bool.and_assoc]

lemma sym_not_eq_one : ∀ (x : Fin 2), ((!(x == 1)) = true) = (x = 0) := by decide

lemma parse_r_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2))
    {parse_step_r_f} (h3 : parse_step_r_f = parse_step_r) :
    parse_r_f_p push_stack_f pop1_b_f parse_step_r_f = parse_r := by
  subst h1; subst h2; subst h3; funext fuel limit s; unfold parse_r_f_p
  induction fuel generalizing limit s with
  | zero => rfl
  | succ fuel ih =>
    unfold parse_r
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_sub_def, with_prod_eq, with_list_eq, with_stack_eq]
    by_cases hlim : limit = 0
    · simp [hlim]
    · have hne : (limit == 0) = false := beq_eq_false_iff_ne.mpr hlim
      rw [hne]; simp only [if_false_eq_true, hlim, ↓reduceIte]
      cases s with
      | nil => rfl
      | cons top rest =>
        dsimp only
        rcases parse_step_r limit (top :: rest) with _ | ⟨b, k, s1⟩
        · simp only [sym_not_eq_one]
        · dsimp only
          cases (parse_r fuel (limit - k) s1).1 <;> cases b <;> rfl

lemma sub_lsb_p_eq
    {mkPart_f} (h1 : mkPart_f = cons_lsb) :
    sub_lsb_f_p mkPart_f = sub_lsb := by
  subst h1; funext fuel c xs ys; unfold sub_lsb_f_p
  induction fuel generalizing c xs ys with
  | zero => rfl
  | succ fuel ih =>
    unfold sub_lsb
    simp only [ih]
    cases xs with
    | nil =>
      simp only [bool_rec_eq]
      cases ys <;> cases c <;> rfl
    | cons xhd xrest =>
      rcases xhd with ⟨px, kx⟩
      cases ys with
      | nil =>
        simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_add_def, nat_sub_def,
          nat_min_def, with_nat_eq, with_list_eq, head_q, head_l, next_x, next_y]
        have hmink : min kx kx = kx := Nat.min_self kx
        simp only [hmink, Nat.sub_self]
        by_cases hlt : kx < kx
        · exact False.elim (Nat.lt_irrefl kx hlt)
        · simp only [hlt, ↓reduceIte]
          have hfalse : decide (kx + 1 ≤ kx) = false := decide_eq_false (by omega)
          rw [hfalse, if_false_eq_true]
          by_cases hk0 : kx = 0
          · simp [hk0]
          · have hne0 : (kx == 0) = false := beq_eq_false_iff_ne.mpr hk0
            rw [hne0]; simp only [if_false_eq_true, hk0, ↓reduceIte]
            have hc_eq : (if decide (2 ≤ kx) then
                (!px && (false || ((!px && (false || c)) || (false && c)))) ||
                  (false && ((!px && (false || c)) || (false && c)))
                else (!px && (false || c)) || (false && c)) =
                sub_chunk_c px false c kx := by
              unfold sub_chunk_c subbit
              by_cases h1 : 1 < kx
              · rw [if_pos h1, decide_eq_true (by omega), if_true_eq_true]
              · rw [if_neg h1, decide_eq_false (by omega), if_false_eq_true]
            rw [hc_eq]
            cases sub_lsb fuel (sub_chunk_c px false c kx) xrest [] with
            | none => rfl
            | some out =>
              dsimp only; unfold sub_chunk_out subbit
              by_cases h1 : 1 < kx
              · rw [if_pos h1, decide_eq_true (by omega), if_true_eq_true]
              · rw [if_neg h1, decide_eq_false (by omega), if_false_eq_true]
      | cons yhd yrest =>
        rcases yhd with ⟨qy, ly⟩
        simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_add_def, nat_sub_def,
          nat_min_def, with_nat_eq, with_list_eq, head_q, head_l]
        have hnx : (if decide (min kx ly + 1 ≤ kx) then (px, kx - min kx ly) :: xrest else xrest) =
                   next_x px kx (min kx ly) xrest := by
          unfold next_x
          by_cases hlt : min kx ly < kx
          · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
          · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]
        have hny : (if decide (min kx ly + 1 ≤ ly) then (qy, ly - min kx ly) :: yrest else yrest) =
                   next_y (min kx ly) ((qy, ly) :: yrest) := by
          dsimp only [next_y]
          by_cases hlt : min kx ly < ly
          · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
          · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]
        rw [hnx, hny]
        by_cases hn0 : min kx ly = 0
        · simp [hn0]
        · have hne0 : (min kx ly == 0) = false := beq_eq_false_iff_ne.mpr hn0
          rw [hne0]; simp only [if_false_eq_true, hn0, ↓reduceIte]
          have hc_eq : (if decide (2 ≤ min kx ly) then
              (!px && (qy || ((!px && (qy || c)) || (qy && c)))) ||
                (qy && ((!px && (qy || c)) || (qy && c)))
              else (!px && (qy || c)) || (qy && c)) =
              sub_chunk_c px qy c (min kx ly) := by
            unfold sub_chunk_c subbit
            by_cases h1 : 1 < min kx ly
            · rw [if_pos h1, decide_eq_true (by omega), if_true_eq_true]
            · rw [if_neg h1, decide_eq_false (by omega), if_false_eq_true]
          rw [hc_eq]
          cases sub_lsb fuel (sub_chunk_c px qy c (min kx ly))
              (next_x px kx (min kx ly) xrest) (next_y (min kx ly) ((qy, ly) :: yrest)) with
          | none => rfl
          | some out =>
            dsimp only; unfold sub_chunk_out subbit
            by_cases h1 : 1 < min kx ly
            · rw [if_pos h1, decide_eq_true (by omega), if_true_eq_true]
            · rw [if_neg h1, decide_eq_false (by omega), if_false_eq_true]

lemma choose_limit_r_p_eq
    {drop_stack_f} (h1 : drop_stack_f = drop_stack)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2))
    {pop_word_f} (h3 : pop_word_f = pop_word) :
    choose_limit_r_f_p drop_stack_f pop1_b_f pop_word_f = choose_limit_r_loop := by
  subst h1; subst h2; subst h3; funext n fuel done r
  unfold choose_limit_r_f_p
  induction fuel generalizing done r with
  | zero => rfl
  | succ fuel ih =>
    unfold choose_limit_r_loop
    simp only [ih]
    cases r with
    | nil =>
      simp only [bool_rec_eq, nat_ble_def, nat_add_def]
      by_cases hle : done ≤ n <;> simp [hle]
    | cons top rest =>
      simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_add_def, nat_div_def, nat_mul_def,
        nat_min_def, nat_max_def, Bool.and_assoc]
      by_cases c1 : (top.width == 3 && (top.pat == 1 && decide (3 ≤ top.len))) = true
      · simp only [c1, ↓reduceIte]
      · have hc1f : (top.width == 3 && (top.pat == 1 && decide (3 ≤ top.len))) = false :=
          Bool.eq_false_iff.mpr c1
        simp only [hc1f, Bool.false_eq_true, ↓reduceIte]
        by_cases c2 : (top.width == 1 && (top.pat == 0 && decide (3 ≤ top.len))) = true
        · simp only [c2, ↓reduceIte]
          by_cases hlt : n < done + top.len / 3
          · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
          · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]
        · have hc2f : (top.width == 1 && (top.pat == 0 && decide (3 ≤ top.len))) = false :=
            Bool.eq_false_iff.mpr c2
          simp only [hc2f, Bool.false_eq_true, ↓reduceIte]
          cases pop_word 1 3 (top :: rest) with
          | some r1 => rfl
          | none =>
            cases pop_word 0 3 (top :: rest) with
            | some r1 =>
              dsimp only
              by_cases hlt : n < done + 1
              · have hd : decide (n ≤ done) = true := decide_eq_true (by omega)
                simp only [hd, hlt, ↓reduceIte]
              · have hd : decide (n ≤ done) = false := decide_eq_false (by omega)
                simp only [hd, hlt, Bool.false_eq_true, ↓reduceIte]
            | none =>
              dsimp only
              simp only [sym_not_eq_one]

lemma push_prefix_l_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack) :
    push_prefix_l_f_p push_stack_f = push_prefix_l := by
  subst h1; rfl

lemma build_vprime_p_eq
    {mkPart_f} (h1 : mkPart_f = cons_lsb) :
    build_vprime_f_p mkPart_f = build_vprime := by
  subst h1; funext n m_use
  unfold build_vprime_f_p build_vprime
  simp only [bool_rec_eq, nat_ble_def, nat_sub_def]
  by_cases hlt : 1 < m_use
  · rw [if_pos hlt, if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
  · rw [if_neg hlt, if_neg hlt, decide_eq_false (by omega), if_false_eq_true]

lemma do_shift_right_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word)
    {count_stack_mut_f} (h3 : count_stack_mut_f = count_stack_mut) :
    do_shift_right_f_p push_stack_f pop_word_f count_stack_mut_f 8 = do_shift_right := by
  subst h1; subst h2; subst h3; funext sq sw sin sout sout_w s
  unfold do_shift_right_f_p do_shift_right
  simp only [bool_rec_eq, nat_beq_def, nat_add_def, nat_mul_def, nat_shiftLeft_def,
    Nat.shiftLeft_eq, Nat.one_mul, with_prod_eq, some_mstate_eq]
  have hq : ((s.q.val == sq.val) = true) = (s.q = sq) := by
    cases h : (s.q.val == sq.val)
    · simp only [beq_eq_false_iff_ne] at h; simp [Fin.ext_iff, h]
    · simp only [beq_iff_eq] at h; simp [Fin.ext_iff, h]
  simp only [hq]
  by_cases hsq : s.q = sq
  · simp only [hsq, ↓reduceIte]
    cases pop_word (sin + sin * 2 ^ sw) (2 * sw) s.r <;> rfl
  · simp only [hsq, ↓reduceIte]

lemma bit_pat_eq : ∀ (x : Fin 2), (if x == 1 then 1 else 0) = bit_pat x := by decide

lemma do_shift_left_p_eq
    {bit_of_bool_f} (h1 : bit_of_bool_f = fun x => bit_of x == 1)
    {push_stack_f} (h2 : push_stack_f = push_stack)
    {pop1_b_f} (h3 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2))
    {pop_word_f} (h4 : pop_word_f = pop_word)
    {count_stack_mut_f} (h5 : count_stack_mut_f = count_stack_mut) :
    do_shift_left_f_p bit_of_bool_f push_stack_f pop1_b_f pop_word_f count_stack_mut_f 8 = do_shift_left := by
  subst h1; subst h2; subst h3; subst h4; subst h5
  funext sq sw sin sout sout_w s
  unfold do_shift_left_f_p do_shift_left
  simp only [bool_rec_eq, nat_beq_def, nat_add_def, nat_mul_def, nat_sub_def,
    nat_shiftLeft_def, nat_shiftRight_def, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.shiftRight_eq_div_pow, Nat.pow_one, with_prod_eq, some_mstate_eq, bit_pat_eq,
    sym_xnor_eq]
  have hq : ((s.q.val == sq.val) = true) = (s.q = sq) := by
    cases h : (s.q.val == sq.val)
    · simp only [beq_eq_false_iff_ne] at h; simp [Fin.ext_iff, h]
    · simp only [beq_iff_eq] at h; simp [Fin.ext_iff, h]
  simp only [hq]
  by_cases hsq : s.q = sq
  · simp only [hsq, ↓reduceIte]
    by_cases heq : (pop1 s.r).1 = bit_of (sin + sin * 2 ^ sw)
    · simp only [heq, beq_self_eq_true, Bool.true_and, ↓reduceIte]
      cases pop_word ((sin + sin * 2 ^ sw) / 2) (2 * sw - 1) s.l <;> rfl
    · have hne : ((pop1 s.r).1 == bit_of (sin + sin * 2 ^ sw)) = false := beq_eq_false_iff_ne.mpr heq
      rw [hne]; simp only [Bool.false_and, Bool.false_eq_true, heq, ↓reduceIte]
  · simp only [hsq, ↓reduceIte]

lemma try_pair_stack_p_eq
    {pop_word_f} (h1 : pop_word_f = pop_word)
    {bsize_parts_f} (h2 : bsize_parts_f = bsize_parts)
    {put_l_stack_f} (h3 : put_l_stack_f = put_l_stack)
    {put_r_rec_f} (h4 : put_r_rec_f = put_r_rec)
    {parse_l_f} (h5 : parse_l_f = parse_l)
    {parse_r_f} (h6 : parse_r_f = parse_r)
    {sub_lsb_f} (h7 : sub_lsb_f = sub_lsb)
    {choose_limit_r_f} (h8 : choose_limit_r_f = choose_limit_r_loop)
    {push_prefix_l_f} (h9 : push_prefix_l_f = push_prefix_l) :
    try_pair_stack_f_p pop_word_f bsize_parts_f put_l_stack_f put_r_rec_f
      parse_l_f parse_r_f sub_lsb_f choose_limit_r_f push_prefix_l_f = try_pair_stack := by
  funext kfuel;
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9
  funext s
  unfold try_pair_stack_f_p try_pair_stack put_r_stack choose_limit_r
  have hq : ((s.q.val == 0) = true) = (s.q = 0) := by
    cases h : (s.q.val == 0)
    · simp only [beq_eq_false_iff_ne] at h; simp [Fin.ext_iff, h]
    · simp only [beq_iff_eq] at h; simp [Fin.ext_iff, h]
  simp only [bool_rec_eq, nat_beq_def, hq]
  split_ifs with hq0
  · cases pop_word 29 5 s.l with
    | none => rfl
    | some lc =>
      dsimp only
      generalize parse_l kfuel 100000000 lc = res_l
      rcases res_l with ⟨a_list, l_tail⟩
      rw [with_prod_eq]; dsimp only
      rw [with_list_eq]
      cases a_list with
      | nil => rfl
      | cons a_hd a_tl =>
        dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
        generalize bsize_parts (a_hd :: a_tl) = n
        rw [with_nat_eq]
        generalize choose_limit_r_loop n kfuel 0 s.r = lim_r
        rw [with_nat_eq]
        by_cases hlim : lim_r = 0
        · simp [hlim]
        · have hne : (lim_r == 0) = false := beq_eq_false_iff_ne.mpr hlim
          rw [hne]; simp only [if_false_eq_true, hlim, ↓reduceIte]
          generalize parse_r kfuel lim_r s.r = res_r
          rcases res_r with ⟨b_list, r_tail⟩
          rw [with_prod_eq]; dsimp only
          rw [with_list_eq]
          cases b_list with
          | nil => rfl
          | cons b_hd b_tl =>
            dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
            rw [with_nat_eq]
            simp only [some_mstate_eq]
            cases sub_lsb kfuel false (a_hd :: a_tl) (b_hd :: b_tl) with
            | some out => rfl
            | none =>
              cases sub_lsb kfuel false (b_hd :: b_tl) (a_hd :: a_tl) <;> rfl
  · rfl

lemma try_absorb_stack_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word)
    {count_stack_mut_f} (h3 : count_stack_mut_f = count_stack_mut)
    {bsize_parts_f} (h4 : bsize_parts_f = bsize_parts)
    {put_r_rec_f} (h5 : put_r_rec_f = put_r_rec)
    {parse_r_f} (h6 : parse_r_f = parse_r)
    {sub_lsb_f} (h7 : sub_lsb_f = sub_lsb)
    {choose_limit_r_f} (h8 : choose_limit_r_f = choose_limit_r_loop)
    {push_prefix_l_f} (h9 : push_prefix_l_f = push_prefix_l)
    {build_vprime_f} (h10 : build_vprime_f = build_vprime) :
    try_absorb_stack_f_p push_stack_f pop_word_f count_stack_mut_f bsize_parts_f
      put_r_rec_f parse_r_f sub_lsb_f choose_limit_r_f push_prefix_l_f build_vprime_f =
    try_absorb_stack := by
  funext kfuel;
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9; subst h10
  funext s
  unfold try_absorb_stack_f_p try_absorb_stack put_r_stack choose_limit_r
  have hq : ((s.q.val == 0) = true) = (s.q = 0) := by
    cases h : (s.q.val == 0)
    · simp only [beq_eq_false_iff_ne] at h; simp [Fin.ext_iff, h]
    · simp only [beq_iff_eq] at h; simp [Fin.ext_iff, h]
  simp only [bool_rec_eq, nat_beq_def, nat_ble_def, nat_add_def, nat_sub_def, nat_mul_def,
    nat_min_def, hq]
  split_ifs with hq0
  · cases pop_word 29 5 s.l with
    | none => rfl
    | some lc0 =>
      dsimp only
      generalize count_stack_mut 15 4 kfuel 100000000 lc0 = res1
      rcases res1 with ⟨n1, r1⟩
      rw [with_prod_eq]; dsimp only
      generalize count_stack_mut 13 4 kfuel 100000000 r1 = res_m
      rcases res_m with ⟨nm, rm⟩
      rw [with_prod_eq]; dsimp only
      by_cases hm0 : nm = 0
      · simp [hm0]
      · have hne_m : (nm == 0) = false := beq_eq_false_iff_ne.mpr hm0
        rw [hne_m]; simp only [if_false_eq_true, hm0, ↓reduceIte]
        generalize choose_limit_r_loop (n1 + nm) kfuel 0 s.r = lim_r
        rw [with_nat_eq]
        by_cases hlim0 : lim_r = 0
        · simp [hlim0]
        · have hne_l : (lim_r == 0) = false := beq_eq_false_iff_ne.mpr hlim0
          rw [hne_l]; simp only [if_false_eq_true, hlim0, ↓reduceIte]
          generalize parse_r kfuel lim_r s.r = res_r
          rcases res_r with ⟨b_list, r_tail⟩
          rw [with_prod_eq]; dsimp only
          rw [with_list_eq]
          cases b_list with
          | nil => rfl
          | cons b_hd b_tl =>
            dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
            generalize bsize_parts (b_hd :: b_tl) = k
            rw [with_nat_eq]
            have hmin_eq : min nm (if decide (n1 + 1 ≤ k) then k - n1 else 1) =
                           calc_m_init nm n1 k := by
              unfold calc_m_init
              by_cases hlt : n1 < k
              · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
              · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]
            rw [hmin_eq]
            generalize calc_m_init nm n1 k = m_init
            rw [with_nat_eq]
            by_cases hmi0 : m_init = 0
            · simp [hmi0]
            · have hne_i : (m_init == 0) = false := beq_eq_false_iff_ne.mpr hmi0
              rw [hne_i]; simp only [if_false_eq_true, hmi0, ↓reduceIte]
              have hsub_eq : (match sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 m_init) with
                  | some out => some (m_init, out)
                  | none =>
                    if decide (m_init ≤ 1) then none
                    else match sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 (m_init - 1)) with
                      | some out => some (m_init - 1, out)
                      | none => none) =
                  try_absorb_sub kfuel n1 m_init (b_hd :: b_tl) := by
                unfold try_absorb_sub
                cases sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 m_init) with
                | some out => rfl
                | none =>
                  dsimp only
                  by_cases hle1 : m_init ≤ 1
                  · rw [if_pos hle1, decide_eq_true hle1, if_true_eq_true]
                  · rw [if_neg hle1, decide_eq_false hle1, if_false_eq_true]
              rw [hsub_eq]
              cases try_absorb_sub kfuel n1 m_init (b_hd :: b_tl) with
              | none => rfl
              | some pair_out =>
                rcases pair_out with ⟨m_use, out⟩
                dsimp only
                generalize count_stack_mut 13 4 kfuel m_use r1 = res2
                rcases res2 with ⟨n2, r2⟩
                rw [with_prod_eq]; dsimp only
                simp only [some_mstate_eq]
                by_cases hres2 : n2 = m_use
                · simp [hres2]
                · have hne2 : (n2 == m_use) = false := beq_eq_false_iff_ne.mpr hres2
                  rw [hne2]; simp [hres2]
  · rfl

lemma step_prim_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2)) :
    step_prim_f_p push_stack_f pop1_b_f = step_prim := by
  subst h1; subst h2; funext s
  unfold step_prim_f_p step_prim
  rcases s with ⟨q, l, r⟩
  simp only [bool_rec_eq, with_prod_eq, some_mstate_eq, bit_pat_eq]
  rcases hpr : pop1 r with ⟨b_r, r_rest⟩
  dsimp only
  rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases b_r with ⟨_ | _ | b_r, hb⟩ <;> (try rfl) <;> (try omega)

lemma step_m_p_eq
    {do_shift_right_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState} (h1 : do_shift_right_f 8 = do_shift_right)
    {do_shift_left_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState} (h2 : do_shift_left_f 8 = do_shift_left)
    {try_pair_stack_f : Nat → MState → Option MState} (h3 : try_pair_stack_f = try_pair_stack)
    {try_absorb_stack_f : Nat → MState → Option MState} (h4 : try_absorb_stack_f = try_absorb_stack)
    {step_prim_f} (h5 : step_prim_f = step_prim) :
    step_m_f_p do_shift_right_f do_shift_left_f try_pair_stack_f try_absorb_stack_f step_prim_f 8 = step_m := by
  subst h5; funext s; unfold step_m_f_p; rw [h1, h2, h3, h4]; unfold step_m
  rcases hq : s.q.val with _ | _ | _ | _ | n
  · unfold step_m_q0; dsimp only
    cases try_pair_stack (Nat.add (Nat.add s.l.length s.r.length) 4) s <;>
      cases try_absorb_stack (Nat.add (Nat.add s.l.length s.r.length) 4) s <;>
      cases do_shift_right 0 3 1 1 1 s <;> rfl
  · unfold step_m_q1
    cases do_shift_left 1 1 1 0 1 s <;> rfl
  · unfold step_m_q2
    cases do_shift_left 2 2 3 1 2 s <;> rfl
  · unfold step_m_q3
    cases do_shift_right 3 1 1 0 1 s <;>
      cases do_shift_right 3 3 2 1 1 s <;>
        cases do_shift_right 3 4 10 14 4 s <;>
          cases do_shift_right 3 4 5 7 4 s <;> rfl
  · rfl


noncomputable def step_m_f_inst (k128 : Nat) : MState → Option MState :=
(fun (mkBlock_f : Nat → Nat → Nat → Block) =>
(fun (rot1_f : Nat → Nat → Nat) =>
(fun (rot_mod_f : Nat → Nat → Nat → Nat) =>
(fun (bit_of_bool_f : Nat → Bool) =>
(fun (push_stack_aux_f : Block → Stack → Stack) =>
(fun (push_stack_f : Nat → Nat → Nat → Stack → Stack) =>
(fun (drop_stack_f : Nat → Stack → Stack) =>
(fun (pop1_b_f : Stack → Bool × Stack) =>
(fun (pop_word_f : Nat → Nat → Stack → Option Stack) =>
(fun (fast_match_f : Nat → Nat → Block → Bool) =>
(fun (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack) =>
(fun (mkPart_f : Bool → Nat → PartList → PartList) =>
(fun (bsize_parts_f : PartList → Nat) =>
(fun (put_l_parts_f : PartList → Stack → Stack) =>
(fun (put_l_stack_f : PartList → Nat → Stack → Stack) =>
(fun (put_r_rec_f : PartList → Nat → Stack → Stack) =>
(fun (parse_step_l_f : Nat → Stack → Option (Bool × Nat × Stack)) =>
(fun (parse_l_f : Nat → Nat → Stack → PartList × Stack) =>
(fun (parse_step_r_f : Nat → Stack → Option (Bool × Nat × Stack)) =>
(fun (parse_r_f : Nat → Nat → Stack → PartList × Stack) =>
(fun (sub_lsb_f : Nat → Bool → PartList → PartList → Option PartList) =>
(fun (choose_limit_r_f : Nat → Nat → Nat → Stack → Nat) =>
(fun (push_prefix_l_f : Stack → Stack) =>
(fun (build_vprime_f : Nat → Nat → PartList) =>
(fun (do_shift_right_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState) =>
(fun (do_shift_left_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState) =>
(fun (try_pair_stack_f : Nat → MState → Option MState) =>
(fun (try_absorb_stack_f : Nat → MState → Option MState) =>
(fun (step_prim_f : MState → Option MState) =>
(fun (step_m_f : Nat → MState → Option MState) =>
step_m_f k128
) (step_m_f_p do_shift_right_f do_shift_left_f try_pair_stack_f try_absorb_stack_f step_prim_f)
) (step_prim_f_p push_stack_f pop1_b_f)
) (try_absorb_stack_f_p push_stack_f pop_word_f count_stack_mut_f bsize_parts_f put_r_rec_f parse_r_f sub_lsb_f choose_limit_r_f push_prefix_l_f build_vprime_f)
) (try_pair_stack_f_p pop_word_f bsize_parts_f put_l_stack_f put_r_rec_f parse_l_f parse_r_f sub_lsb_f choose_limit_r_f push_prefix_l_f)
) (do_shift_left_f_p bit_of_bool_f push_stack_f pop1_b_f pop_word_f count_stack_mut_f)
) (do_shift_right_f_p push_stack_f pop_word_f count_stack_mut_f)
) (build_vprime_f_p mkPart_f)
) (push_prefix_l_f_p push_stack_f)
) (choose_limit_r_f_p drop_stack_f pop1_b_f pop_word_f)
) (sub_lsb_f_p mkPart_f)
) (parse_r_f_p push_stack_f pop1_b_f parse_step_r_f)
) (parse_step_r_f_p drop_stack_f pop_word_f)
) (parse_l_f_p parse_step_l_f)
) (parse_step_l_f_p drop_stack_f pop_word_f)
) (put_r_rec_f_p push_stack_f)
) (put_l_stack_f_p push_stack_f bsize_parts_f put_l_parts_f)
) (put_l_parts_f_p push_stack_f)
) bsize_parts_f_p
) mkPart_f_p
) (count_stack_mut_f_p drop_stack_f pop_word_f fast_match_f)
) fast_match_f_p
) (pop_word_f_p bit_of_bool_f pop1_b_f)
) (pop1_b_f_p mkBlock_f rot1_f bit_of_bool_f)
) (drop_stack_f_p mkBlock_f rot_mod_f)
) (push_stack_f_p mkBlock_f push_stack_aux_f)
) (push_stack_aux_f_p mkBlock_f rot_mod_f)
) bit_of_bool_f_p
) rot_mod_f_p
) rot1_f_p
) mkBlock_f_p




noncomputable def consBlock1 (p w l : Nat) (rest : Stack) : Stack :=
  let p0 : Nat := match p with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7
    | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | 13 => 13 | 14 => 14 | 15 => 15 | n => n
  let w0 : Nat := match w with
    | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | n => n
  @Nat.rec (fun _ => Stack) [] (fun l1 _ => ⟨p0, w0, l1⟩ :: rest) (Nat.add 1 l)

lemma consBlock1_eq (p w l : Nat) (rest : Stack) :
    consBlock1 p w l rest = ⟨p, w, l⟩ :: rest := by
  unfold consBlock1
  have hp : (match p with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7
    | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | 13 => 13 | 14 => 14 | 15 => 15 | n => n) = p := by
    match p with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | n + 16 => rfl
  have hw : (match w with
    | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | n => n) = w := by
    match w with
    | 0 | 1 | 2 | 3 | 4 | n + 5 => rfl
  have hl : Nat.add 1 l = Nat.succ l := Nat.add_comm 1 l
  rw [hp, hw, hl]

lemma mkBlock_f_p_eq (p w l : Nat) :
    mkBlock_f_p p w l = ⟨p, w, l⟩ := by
  unfold mkBlock_f_p
  have hp : Nat.add 1 p = Nat.succ p := Nat.add_comm 1 p
  have hw : Nat.add 1 w = Nat.succ w := Nat.add_comm 1 w
  have hl : Nat.add 1 l = Nat.succ l := Nat.add_comm 1 l
  rw [hp, hw, hl]

noncomputable def push_stack_aux_fast_fuel (fuel : Nat) : Nat → Nat → Nat → Stack → Stack :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Stack → Stack)
    (fun p w l rest => consBlock1 p w l rest)
    (fun _ ih p w l s =>
      match s with
      | [] => @Bool.rec (fun _ => Stack) (consBlock1 p w l []) [] (Nat.beq p 0)
      | top :: rest =>
        @Bool.rec (fun _ => Stack)
          (consBlock1 p w l (top :: rest))
          (ih p w (Nat.add l top.len) rest)
          (Bool.and (Nat.beq w top.width) (Nat.beq (rot_mod_f_p w l p) top.pat)))
    fuel

lemma push_stack_aux_fast_fuel_eq (fuel : Nat) (s : Stack) (hs : s.length < fuel) (p w l : Nat) :
    push_stack_aux_fast_fuel fuel p w l s =
      push_stack_aux_f_p mkBlock_f_p rot_mod_f_p ⟨p, w, l⟩ s := by
  induction fuel generalizing s p w l with
  | zero => cases hs
  | succ k ih =>
    cases s with
    | nil =>
      change @Bool.rec (fun _ => Stack) (consBlock1 p w l []) [] (Nat.beq p 0) =
             @Bool.rec (fun _ => Stack) [⟨p, w, l⟩] [] (Nat.beq p 0)
      cases Nat.beq p 0 <;> simp [consBlock1_eq]
    | cons top rest =>
      have hlen : rest.length < k := by simp at hs; omega
      change @Bool.rec (fun _ => Stack)
               (consBlock1 p w l (top :: rest))
               (push_stack_aux_fast_fuel k p w (Nat.add l top.len) rest)
               (Bool.and (Nat.beq w top.width) (Nat.beq (rot_mod_f_p w l p) top.pat)) =
             @Bool.rec (fun _ => Stack)
               (⟨p, w, l⟩ :: top :: rest)
               (push_stack_aux_f_p mkBlock_f_p rot_mod_f_p (mkBlock_f_p p w (Nat.add l top.len)) rest)
               (Bool.and (Nat.beq w top.width) (Nat.beq (rot_mod_f_p w l p) top.pat))
      cases Bool.and (Nat.beq w top.width) (Nat.beq (rot_mod_f_p w l p) top.pat) <;>
        simp [consBlock1_eq, mkBlock_f_p_eq, ih rest hlen]

noncomputable def push_stack_fast (p w l : Nat) (s : Stack) : Stack :=
  @Bool.rec (fun _ => Stack) (push_stack_aux_fast_fuel (Nat.add (List.length s) 1) p w l s) s (Nat.beq l 0)

lemma push_stack_fast_eq :
    push_stack_fast = push_stack_f_p mkBlock_f_p (push_stack_aux_f_p mkBlock_f_p rot_mod_f_p) := by
  funext p w l s
  unfold push_stack_fast push_stack_f_p
  cases Nat.beq l 0 <;> simp [mkBlock_f_p_eq, push_stack_aux_fast_fuel_eq (s.length + 1) s (Nat.lt_succ_self s.length)]

noncomputable def drop_stack_fast_fuel (fuel : Nat) : Nat → Stack → Stack :=
  @Nat.rec (fun _ => Nat → Stack → Stack)
    (fun _ s => s)
    (fun _ ih n s =>
      @Bool.rec (fun _ => Stack)
        (match s with
         | [] => []
         | top :: rest =>
           @Bool.rec (fun _ => Stack)
             (consBlock1 (rot_mod_f_p top.width n top.pat) top.width (Nat.sub top.len n) rest)
             (ih (Nat.sub n top.len) rest)
             (Nat.ble top.len n))
        s
        (Nat.beq n 0))
    fuel

lemma drop_stack_fast_fuel_eq (fuel : Nat) (s : Stack) (hs : s.length < fuel) (n : Nat) :
    drop_stack_fast_fuel fuel n s = drop_stack_f_p mkBlock_f_p rot_mod_f_p n s := by
  induction fuel generalizing s n with
  | zero => cases hs
  | succ k ih =>
    cases s with
    | nil =>
      change @Bool.rec (fun _ => Stack) [] [] (Nat.beq n 0) = []
      cases Nat.beq n 0 <;> rfl
    | cons top rest =>
      have hlen : rest.length < k := by simp at hs; omega
      change @Bool.rec (fun _ => Stack)
               (@Bool.rec (fun _ => Stack)
                 (consBlock1 (rot_mod_f_p top.width n top.pat) top.width (Nat.sub top.len n) rest)
                 (drop_stack_fast_fuel k (Nat.sub n top.len) rest)
                 (Nat.ble top.len n))
               (top :: rest)
               (Nat.beq n 0) =
             @Bool.rec (fun _ => Stack)
               (@Bool.rec (fun _ => Stack)
                 (mkBlock_f_p (rot_mod_f_p top.width n top.pat) top.width (Nat.sub top.len n) :: rest)
                 (drop_stack_f_p mkBlock_f_p rot_mod_f_p (Nat.sub n top.len) rest)
                 (Nat.ble top.len n))
               (top :: rest)
               (Nat.beq n 0)
      cases Nat.beq n 0 <;> cases Nat.ble top.len n <;> simp [consBlock1_eq, mkBlock_f_p_eq, ih rest hlen]

noncomputable def drop_stack_fast (n : Nat) (s : Stack) : Stack :=
  drop_stack_fast_fuel (Nat.add (List.length s) 1) n s

lemma drop_stack_fast_eq :
    drop_stack_fast = drop_stack_f_p mkBlock_f_p rot_mod_f_p := by
  funext n s
  exact drop_stack_fast_fuel_eq (s.length + 1) s (Nat.lt_succ_self s.length) n

noncomputable def pop1_b_fast_fuel (fuel : Nat) : Stack → Bool × Stack :=
  @Nat.rec (fun _ => Stack → Bool × Stack)
    (fun _ => (false, []))
    (fun _ ih s =>
      match s with
      | [] => (false, [])
      | top :: rest =>
        @Bool.rec (fun _ => Bool × Stack)
          (let bit := bit_of_bool_f_p top.pat
           @Bool.rec (fun _ => Bool × Stack)
             (bit, consBlock1 (rot1_f_p top.width top.pat) top.width (Nat.sub top.len 1) rest)
             (bit, rest)
             (Nat.beq top.len 1))
          (ih rest)
          (Nat.beq top.len 0))
    fuel

lemma pop1_b_fast_fuel_eq (fuel : Nat) (s : Stack) (hs : s.length < fuel) :
    pop1_b_fast_fuel fuel s = pop1_b_f_p mkBlock_f_p rot1_f_p bit_of_bool_f_p s := by
  induction fuel generalizing s with
  | zero => cases hs
  | succ k ih =>
    cases s with
    | nil => rfl
    | cons top rest =>
      have hlen : rest.length < k := by simp at hs; omega
      change @Bool.rec (fun _ => Bool × Stack)
               (@Bool.rec (fun _ => Bool × Stack)
                 (bit_of_bool_f_p top.pat, consBlock1 (rot1_f_p top.width top.pat) top.width (Nat.sub top.len 1) rest)
                 (bit_of_bool_f_p top.pat, rest)
                 (Nat.beq top.len 1))
               (pop1_b_fast_fuel k rest)
               (Nat.beq top.len 0) =
             @Bool.rec (fun _ => Bool × Stack)
               (@Bool.rec (fun _ => Bool × Stack)
                 (bit_of_bool_f_p top.pat, mkBlock_f_p (rot1_f_p top.width top.pat) top.width (Nat.sub top.len 1) :: rest)
                 (bit_of_bool_f_p top.pat, rest)
                 (Nat.beq top.len 1))
               (pop1_b_f_p mkBlock_f_p rot1_f_p bit_of_bool_f_p rest)
               (Nat.beq top.len 0)
      cases Nat.beq top.len 0 <;> cases Nat.beq top.len 1 <;> simp [consBlock1_eq, mkBlock_f_p_eq, ih rest hlen]

noncomputable def pop1_b_fast (s : Stack) : Bool × Stack :=
  pop1_b_fast_fuel (Nat.add (List.length s) 1) s

lemma pop1_b_fast_eq :
    pop1_b_fast = pop1_b_f_p mkBlock_f_p rot1_f_p bit_of_bool_f_p := by
  funext s
  exact pop1_b_fast_fuel_eq (s.length + 1) s (Nat.lt_succ_self s.length)


noncomputable def bit_of_bool_f0 : Nat → Bool := bit_of_bool_f_p
noncomputable def push_stack_f0 : Nat → Nat → Nat → Stack → Stack := push_stack_fast
noncomputable def drop_stack_f0 : Nat → Stack → Stack := drop_stack_fast
noncomputable def pop1_b_f0 : Stack → Bool × Stack := pop1_b_fast
noncomputable def pop_word_f0 : Nat → Nat → Stack → Option Stack := pop_word_f_p bit_of_bool_f0 pop1_b_f0
noncomputable def fast_match_f0 : Nat → Nat → Block → Bool := fast_match_f_p
noncomputable def count_stack_mut_f0 : Nat → Nat → Nat → Nat → Stack → Nat × Stack := count_stack_mut_f_p drop_stack_f0 pop_word_f0 fast_match_f0
noncomputable def mkPart_f0 : Bool → Nat → PartList → PartList := mkPart_f_p
noncomputable def bsize_parts_f0 : PartList → Nat := bsize_parts_f_p
noncomputable def put_l_parts_f0 : PartList → Stack → Stack := put_l_parts_f_p push_stack_f0
noncomputable def put_l_stack_f0 : PartList → Nat → Stack → Stack := put_l_stack_f_p push_stack_f0 bsize_parts_f0 put_l_parts_f0
noncomputable def put_r_rec_f0 : PartList → Nat → Stack → Stack := put_r_rec_f_p push_stack_f0
noncomputable def parse_step_l_f0 : Nat → Stack → Option (Bool × Nat × Stack) := parse_step_l_f_p drop_stack_f0 pop_word_f0
noncomputable def parse_l_f0 : Nat → Nat → Stack → PartList × Stack := parse_l_f_p parse_step_l_f0
noncomputable def parse_step_r_f0 : Nat → Stack → Option (Bool × Nat × Stack) := parse_step_r_f_p drop_stack_f0 pop_word_f0
noncomputable def parse_r_f0 : Nat → Nat → Stack → PartList × Stack := parse_r_f_p push_stack_f0 pop1_b_f0 parse_step_r_f0
noncomputable def sub_lsb_f0 : Nat → Bool → PartList → PartList → Option PartList := sub_lsb_f_p mkPart_f0
noncomputable def choose_limit_r_f0 : Nat → Nat → Nat → Stack → Nat := choose_limit_r_f_p drop_stack_f0 pop1_b_f0 pop_word_f0
noncomputable def push_prefix_l_f0 : Stack → Stack := push_prefix_l_f_p push_stack_f0
noncomputable def build_vprime_f0 : Nat → Nat → PartList := build_vprime_f_p mkPart_f0
noncomputable def do_shift_right_f0 : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState := do_shift_right_f_p push_stack_f0 pop_word_f0 count_stack_mut_f0
noncomputable def do_shift_left_f0 : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState := do_shift_left_f_p bit_of_bool_f0 push_stack_f0 pop1_b_f0 pop_word_f0 count_stack_mut_f0
noncomputable def try_pair_stack_f0 : Nat → MState → Option MState := try_pair_stack_f_p pop_word_f0 bsize_parts_f0 put_l_stack_f0 put_r_rec_f0 parse_l_f0 parse_r_f0 sub_lsb_f0 choose_limit_r_f0 push_prefix_l_f0
noncomputable def try_absorb_stack_f0 : Nat → MState → Option MState := try_absorb_stack_f_p push_stack_f0 pop_word_f0 count_stack_mut_f0 bsize_parts_f0 put_r_rec_f0 parse_r_f0 sub_lsb_f0 choose_limit_r_f0 push_prefix_l_f0 build_vprime_f0
noncomputable def step_prim_f0 : MState → Option MState := step_prim_f_p push_stack_f0 pop1_b_f0
noncomputable def step_m_c0 : MState → Option MState := step_m_f_p do_shift_right_f0 do_shift_left_f0 try_pair_stack_f0 try_absorb_stack_f0 step_prim_f0 8

lemma step_m_c0_eq : step_m_c0 = step_m :=
  let h01 := mkBlock_p_eq
  let h02 := rot1_p_eq
  let h03 := rot_mod_p_eq
  let h04 := bit_of_bool_p_eq
  let h05 := push_stack_aux_p_eq h01 h03
  let h06 := push_stack_fast_eq.trans (push_stack_p_eq h01 h05)
  let h07 := drop_stack_fast_eq.trans (drop_stack_p_eq h01 h03)
  let h08 := pop1_b_fast_eq.trans (pop1_b_p_eq h01 h02 h04)
  let h09 := pop_word_p_eq h04 h08
  let h10 := fast_match_p_eq
  let h11 := count_stack_mut_p_eq h07 h09 h10
  let h12 := mkPart_p_eq
  let h13 := bsize_parts_p_eq
  let h14 := put_l_parts_p_eq h06
  let h15 := put_l_stack_p_eq h06 h13 h14
  let h16 := put_r_rec_p_eq h06
  let h17 := parse_step_l_p_eq h07 h09
  let h18 := parse_l_p_eq h17
  let h19 := parse_step_r_p_eq h07 h09
  let h20 := parse_r_p_eq h06 h08 h19
  let h21 := sub_lsb_p_eq h12
  let h22 := choose_limit_r_p_eq h07 h08 h09
  let h23 := push_prefix_l_p_eq h06
  let h24 := build_vprime_p_eq h12
  let h25 := do_shift_right_p_eq h06 h09 h11
  let h26 := do_shift_left_p_eq h04 h06 h08 h09 h11
  let h27 := try_pair_stack_p_eq h09 h13 h15 h16 h18 h20 h21 h22 h23
  let h28 := try_absorb_stack_p_eq h06 h09 h11 h13 h16 h20 h21 h22 h23 h24
  let h29 := step_prim_p_eq h06 h08
  step_m_p_eq h25 h26 h27 h28 h29

noncomputable def run_m_fast (fuel : Nat) (s0 : MState) : Option MState :=
  @Nat.rec (fun _ => MState → Option MState)
    (fun s => some s)
    (fun _ ih s =>
      match step_m_c0 s with
      | none => none
      | some s1 => ih s1)
    fuel s0

lemma run_m_loop_eq {step_f : MState → Option MState}
    (hstep : step_f = step_m) (fuel : Nat) (s0 : MState) :
    @Nat.rec (fun _ => MState → Option MState)
      (fun s => some s)
      (fun _ ih s =>
        match step_f s with
        | none => none
        | some s1 => ih s1)
      fuel s0 = run_m fuel s0 := by
  subst hstep
  induction fuel generalizing s0 with
  | zero => rfl
  | succ i ih =>
    unfold run_m
    simp only [maybe_norm_eq]
    cases hs : step_m s0 with
    | none => rfl
    | some s1 => exact ih s1

lemma run_m_fast_eq (fuel : Nat) (s0 : MState) :
    run_m_fast fuel s0 = run_m fuel s0 :=
  run_m_loop_eq step_m_c0_eq fuel s0

noncomputable def block_beq (a b : Block) : Bool :=
  Bool.and (Nat.beq a.pat b.pat) (Bool.and (Nat.beq a.width b.width) (Nat.beq a.len b.len))

lemma block_beq_eq {a b : Block} (h : block_beq a b = true) : a = b := by
  rcases a with ⟨p1, w1, l1⟩; rcases b with ⟨p2, w2, l2⟩
  simp only [block_beq, Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

noncomputable def stack_beq : Stack → Stack → Bool :=
  @List.rec Block (fun _ => Stack → Bool)
    (fun ys => @List.rec Block (fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun x _ ih ys =>
      @List.rec Block (fun _ => Bool) false (fun y ys2 _ => Bool.and (block_beq x y) (ih ys2)) ys)

lemma stack_beq_eq : ∀ {xs ys : Stack}, stack_beq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [stack_beq, Bool.and_eq_true] at h
    rw [block_beq_eq h.1, stack_beq_eq h.2]

noncomputable def opt_mstate_beq (o : Option MState) (target : MState) : Bool :=
  match o with
  | none => false
  | some s =>
    Bool.and (Nat.beq s.q.val target.q.val)
      (Bool.and (stack_beq s.l target.l) (stack_beq s.r target.r))

lemma opt_mstate_beq_eq {o : Option MState} {t : MState} (h : opt_mstate_beq o t = true) :
    o = some t := by
  cases o with
  | none => cases h
  | some s =>
    rcases s with ⟨q1, l1, r1⟩; rcases t with ⟨q2, l2, r2⟩
    simp only [opt_mstate_beq, Bool.and_eq_true, Nat.beq_eq] at h
    rcases h with ⟨hq, hl, hr⟩
    rw [Fin.ext hq, stack_beq_eq hl, stack_beq_eq hr]

lemma mreach_base_fast {k : Nat} {s1 s2 : MState} (h : opt_mstate_beq (run_m_fast k s1) s2 = true) : MReach s1 s2 :=
  ⟨k, (run_m_fast_eq k s1).symm.trans (opt_mstate_beq_eq h)⟩

lemma mreach_step_fast {k : Nat} {s1 s2 s3 : MState}
    (h1 : opt_mstate_beq (run_m_fast k s1) s2 = true) (h2 : MReach s2 s3) : MReach s1 s3 :=
  let ⟨n, hn⟩ := h2
  ⟨k + n, run_m_trans ((run_m_fast_eq k s1).symm.trans (opt_mstate_beq_eq h1)) hn⟩


def cfg_p0 : MState := cfg_0
def cfg_p20 : MState := ⟨0, [⟨1, 1, 4⟩, ⟨0, 1, 1⟩, ⟨1, 1, 3⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 20⟩, ⟨1, 1, 12⟩, ⟨14, 4, 16⟩, ⟨1, 1, 4⟩, ⟨14, 4, 8⟩, ⟨13, 4, 229⟩, ⟨1, 1, 1⟩], [⟨1, 3, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨0, 1, 5⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 84⟩, ⟨0, 1, 6⟩, ⟨1, 3, 1⟩]⟩
def cfg_p40 : MState := ⟨0, [⟨1, 1, 7⟩, ⟨0, 1, 1⟩, ⟨1, 1, 11⟩, ⟨13, 4, 1⟩, ⟨1, 1, 9⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 692⟩, ⟨1, 1, 1⟩], [⟨0, 1, 18⟩, ⟨1, 1, 1⟩, ⟨0, 1, 14⟩, ⟨1, 3, 9⟩, ⟨0, 1, 9⟩, ⟨1, 3, 57⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 1⟩]⟩
def cfg_p60 : MState := ⟨2, [⟨1, 1, 1⟩, ⟨7, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 24⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨13, 4, 1377⟩, ⟨1, 1, 1⟩], [⟨1, 1, 2⟩, ⟨0, 1, 13⟩, ⟨1, 1, 1⟩, ⟨0, 1, 26⟩, ⟨1, 1, 1⟩, ⟨0, 1, 8⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 72⟩, ⟨1, 3, 6⟩, ⟨0, 1, 99⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 12⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 54⟩, ⟨0, 1, 6⟩, ⟨1, 3, 589⟩]⟩
def cfg_p80 : MState := ⟨3, [⟨1, 1, 6⟩, ⟨0, 1, 1⟩, ⟨1, 1, 3⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 28⟩, ⟨1, 1, 4⟩, ⟨14, 4, 92⟩, ⟨1, 1, 4⟩, ⟨14, 4, 464⟩, ⟨1, 1, 4⟩, ⟨14, 4, 1372⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨0, 1, 5⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 126⟩, ⟨1, 3, 27⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 234⟩, ⟨1, 3, 1⟩]⟩
def cfg_p100 : MState := ⟨4, [⟨1, 1, 3⟩, ⟨7, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 4⟩, ⟨13, 4, 9⟩, ⟨1, 1, 8⟩, ⟨14, 4, 2292⟩, ⟨1, 1, 1⟩], [⟨2, 2, 3⟩, ⟨1, 1, 1⟩, ⟨0, 1, 16⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 51⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 348⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1029⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 90⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩
def cfg_p120 : MState := ⟨4, [⟨1, 1, 5⟩, ⟨0, 1, 1⟩, ⟨1, 1, 3⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 876⟩, ⟨1, 1, 132⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 156⟩, ⟨1, 1, 4⟩, ⟨14, 4, 24⟩, ⟨1, 1, 40⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 40⟩, ⟨1, 1, 4⟩, ⟨14, 4, 20⟩, ⟨1, 1, 4⟩, ⟨14, 4, 16⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 76⟩, ⟨1, 1, 4⟩, ⟨14, 4, 588⟩, ⟨13, 4, 1817⟩, ⟨1, 1, 1⟩], [⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 87⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 159⟩, ⟨1, 3, 1⟩]⟩
def cfg_p140 : MState := ⟨0, [⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨7, 4, 8⟩, ⟨1, 1, 25⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 48⟩, ⟨13, 4, 2⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 8⟩, ⟨13, 4, 1⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4368⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 42⟩, ⟨1, 3, 75⟩, ⟨0, 1, 54⟩, ⟨1, 3, 99⟩, ⟨0, 1, 3⟩, ⟨1, 3, 579⟩, ⟨0, 1, 99⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 117⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 30⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 57⟩, ⟨0, 1, 3⟩, ⟨1, 3, 441⟩, ⟨0, 1, 6⟩, ⟨1, 3, 1360⟩]⟩
def cfg_p160 : MState := ⟨3, [⟨7, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4824⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 93⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 141⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 261⟩, ⟨0, 1, 99⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 117⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 30⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 57⟩, ⟨0, 1, 3⟩, ⟨1, 3, 441⟩, ⟨0, 1, 6⟩, ⟨1, 3, 1362⟩, ⟨0, 1, 762⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩
def cfg_p180 : MState := ⟨0, [⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 23⟩, ⟨13, 4, 1⟩, ⟨1, 1, 8⟩, ⟨14, 4, 80⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 36⟩, ⟨13, 4, 177⟩, ⟨1, 1, 4⟩, ⟨14, 4, 20⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 80⟩, ⟨14, 4, 100⟩, ⟨1, 1, 4⟩, ⟨14, 4, 44⟩, ⟨1, 1, 12⟩, ⟨14, 4, 12⟩, ⟨1, 1, 16⟩, ⟨14, 4, 24⟩, ⟨1, 1, 4⟩, ⟨14, 4, 36⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨13, 4, 4841⟩, ⟨1, 1, 1⟩], [⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 57⟩, ⟨0, 1, 3⟩, ⟨1, 3, 441⟩, ⟨0, 1, 6⟩, ⟨1, 3, 1362⟩, ⟨0, 1, 762⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩
def cfg_p200 : MState := ⟨4, [⟨1, 1, 3⟩, ⟨7, 4, 7⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 120⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 9⟩, ⟨14, 4, 8⟩, ⟨1, 1, 12⟩, ⟨14, 4, 72⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 20⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 40⟩, ⟨14, 4, 5688⟩, ⟨1, 1, 1⟩], [⟨2, 2, 3⟩, ⟨1, 1, 1⟩, ⟨0, 1, 22⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 39⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1356⟩, ⟨0, 1, 762⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1431⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 1⟩]⟩
def cfg_p220 : MState := ⟨4, [⟨7, 4, 3⟩, ⟨13, 4, 1⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 48⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 32⟩, ⟨14, 4, 8⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨13, 4, 9⟩, ⟨1, 1, 4⟩, ⟨14, 4, 6200⟩, ⟨1, 1, 1⟩], [⟨0, 1, 2⟩, ⟨1, 2, 20⟩, ⟨1, 1, 1⟩, ⟨0, 1, 4⟩, ⟨1, 1, 1⟩, ⟨0, 1, 11⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1209⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1431⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 90⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩
def cfg_p240 : MState := ⟨1, [⟨1, 1, 2⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨7, 4, 8⟩, ⟨1, 1, 16⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 2044⟩, ⟨1, 1, 4⟩, ⟨14, 4, 7916⟩, ⟨1, 1, 1⟩], [⟨0, 1, 2⟩, ⟨2, 3, 13⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 72⟩, ⟨0, 1, 3⟩, ⟨1, 3, 228⟩, ⟨0, 1, 270⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 45⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 84⟩, ⟨1, 3, 96⟩, ⟨0, 1, 12⟩, ⟨1, 3, 12⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 411⟩, ⟨0, 1, 3255⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩
def cfg_p260 : MState := ⟨3, [⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 10292⟩, ⟨1, 1, 1⟩], [⟨0, 1, 1⟩, ⟨1, 2, 8⟩, ⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨0, 1, 6⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 39⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 270⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 45⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 84⟩, ⟨1, 3, 96⟩, ⟨0, 1, 12⟩, ⟨1, 3, 12⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 411⟩, ⟨0, 1, 174⟩, ⟨1, 3, 3081⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 1⟩]⟩
def cfg_p280 : MState := ⟨3, [⟨7, 4, 8⟩, ⟨1, 1, 13⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 10748⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 54⟩, ⟨0, 1, 3⟩, ⟨1, 3, 93⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 411⟩, ⟨0, 1, 174⟩, ⟨1, 3, 3081⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩
def cfg_p300 : MState := ⟨1, [⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨7, 4, 8⟩, ⟨1, 1, 13⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 28⟩, ⟨1, 1, 1⟩, ⟨7, 4, 3⟩, ⟨1, 1, 20⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 16⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 88⟩, ⟨1, 1, 4⟩, ⟨14, 4, 10912⟩, ⟨1, 1, 1⟩], [⟨0, 1, 2⟩, ⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨2, 3, 406⟩, ⟨0, 1, 174⟩, ⟨1, 3, 3081⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 1⟩]⟩
def cfg_p320 : MState := ⟨2, [⟨1, 1, 3⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 36⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨13, 4, 11917⟩, ⟨1, 1, 1⟩], [⟨0, 1, 1⟩, ⟨1, 2, 6⟩, ⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 132⟩, ⟨0, 1, 303⟩, ⟨1, 3, 2316⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 1⟩]⟩
def cfg_p340 : MState := ⟨1, [⟨1, 1, 2⟩, ⟨0, 1, 1⟩, ⟨1, 1, 13⟩, ⟨0, 1, 1⟩, ⟨1, 1, 3⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 8⟩, ⟨1, 1, 1⟩, ⟨14, 4, 4⟩, ⟨1, 1, 20⟩, ⟨14, 4, 60⟩, ⟨1, 1, 4⟩, ⟨14, 4, 32⟩, ⟨1, 1, 4⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 56⟩, ⟨1, 1, 96⟩, ⟨14, 4, 120⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 260⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12200⟩, ⟨1, 1, 1⟩], [⟨0, 1, 2⟩, ⟨2, 3, 1⟩, ⟨0, 1, 47⟩, ⟨1, 1, 1⟩, ⟨0, 1, 5⟩, ⟨1, 3, 1779⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 1⟩]⟩
def cfg_p360 : MState := ⟨3, [⟨7, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 80⟩, ⟨1, 1, 4⟩, ⟨14, 4, 13228⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨1, 3, 15⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 30⟩, ⟨1, 1, 1⟩, ⟨0, 1, 8⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 195⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1170⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 3⟩, ⟨0, 1, 930⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩
def cfg_p380 : MState := ⟨3, [⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 44⟩, ⟨1, 1, 1⟩, ⟨7, 4, 3⟩, ⟨1, 1, 8⟩, ⟨13, 4, 5⟩, ⟨1, 1, 12⟩, ⟨14, 4, 112⟩, ⟨13, 4, 1⟩, ⟨1, 1, 20⟩, ⟨14, 4, 4⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 13548⟩, ⟨1, 1, 1⟩], [⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 996⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 3⟩, ⟨0, 1, 930⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩
def cfg_p400 : MState := ⟨3, [⟨1, 1, 1⟩], [⟨0, 1, 1⟩, ⟨1, 2, 14108⟩, ⟨1, 1, 1⟩, ⟨0, 1, 10⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 96⟩, ⟨0, 1, 9⟩, ⟨1, 3, 558⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2775⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 3⟩, ⟨0, 1, 930⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 1⟩]⟩
def cfg_p420 : MState := ⟨0, [⟨1, 1, 28⟩, ⟨0, 1, 1⟩, ⟨1, 1, 11⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨13, 4, 14873⟩, ⟨1, 1, 1⟩], [⟨1, 3, 1⟩, ⟨0, 1, 1⟩, ⟨1, 3, 3⟩, ⟨0, 1, 51⟩, ⟨1, 3, 264⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 12⟩, ⟨0, 1, 57⟩, ⟨1, 3, 63⟩, ⟨0, 1, 3⟩, ⟨1, 3, 243⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1989⟩, ⟨0, 1, 153⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 3⟩, ⟨0, 1, 930⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 1242⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩
def cfg_p440 : MState := ⟨0, [⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 11⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 24⟩, ⟨14, 4, 44⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 280⟩, ⟨1, 1, 4⟩, ⟨14, 4, 76⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 24⟩, ⟨13, 4, 85⟩, ⟨1, 1, 1⟩, ⟨7, 4, 3⟩, ⟨13, 4, 14873⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨2, 3, 1⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 36⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 93⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1989⟩, ⟨0, 1, 153⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 3⟩, ⟨0, 1, 930⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 1242⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩
def cfg_p460 : MState := ⟨3, [⟨7, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 15920⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 27⟩, ⟨1, 3, 18⟩, ⟨0, 1, 6⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 12⟩, ⟨0, 1, 18⟩, ⟨1, 3, 21⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1581⟩, ⟨0, 1, 153⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1350⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 948⟩, ⟨1, 3, 3⟩, ⟨0, 1, 930⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 1242⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩
def cfg_p480 : MState := ⟨5, [⟨0, 1, 1⟩, ⟨1, 1, 2⟩, ⟨0, 1, 1⟩, ⟨1, 1, 7⟩, ⟨14, 4, 16⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨13, 4, 18873⟩, ⟨1, 1, 1⟩], [⟨4, 3, 245⟩, ⟨0, 1, 105⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 105⟩, ⟨0, 1, 24⟩, ⟨1, 3, 6⟩, ⟨0, 1, 90⟩, ⟨1, 3, 33⟩, ⟨0, 1, 54⟩, ⟨1, 3, 258⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 609⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 180⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 42⟩, ⟨1, 3, 39⟩, ⟨0, 1, 18⟩, ⟨1, 3, 864⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 375⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 1242⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4962⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩
def cfg_p498 : MState := ⟨5, [⟨0, 1, 1⟩, ⟨1, 1, 8⟩, ⟨0, 1, 1⟩, ⟨1, 1, 3⟩, ⟨14, 4, 4⟩, ⟨1, 1, 9⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 19220⟩, ⟨1, 1, 1⟩], [⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 105⟩, ⟨0, 1, 24⟩, ⟨1, 3, 6⟩, ⟨0, 1, 90⟩, ⟨1, 3, 33⟩, ⟨0, 1, 54⟩, ⟨1, 3, 258⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 609⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 180⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 42⟩, ⟨1, 3, 39⟩, ⟨0, 1, 18⟩, ⟨1, 3, 864⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 375⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 675⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 1242⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4962⟩, ⟨1, 3, 6⟩, ⟨0, 1, 255⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩
def cfg_end : MState := cfg_p498

lemma step_ckpt_p20 : opt_mstate_beq (run_m_fast 1000 cfg_p0) cfg_p20 = true := by decide +kernel
lemma step_ckpt_p40 : opt_mstate_beq (run_m_fast 1000 cfg_p20) cfg_p40 = true := by decide +kernel
lemma step_ckpt_p60 : opt_mstate_beq (run_m_fast 1000 cfg_p40) cfg_p60 = true := by decide +kernel
lemma step_ckpt_p80 : opt_mstate_beq (run_m_fast 1000 cfg_p60) cfg_p80 = true := by decide +kernel
lemma step_ckpt_p100 : opt_mstate_beq (run_m_fast 1000 cfg_p80) cfg_p100 = true := by decide +kernel
lemma step_ckpt_p120 : opt_mstate_beq (run_m_fast 1000 cfg_p100) cfg_p120 = true := by decide +kernel
lemma step_ckpt_p140 : opt_mstate_beq (run_m_fast 1000 cfg_p120) cfg_p140 = true := by decide +kernel
lemma step_ckpt_p160 : opt_mstate_beq (run_m_fast 1000 cfg_p140) cfg_p160 = true := by decide +kernel
lemma step_ckpt_p180 : opt_mstate_beq (run_m_fast 1000 cfg_p160) cfg_p180 = true := by decide +kernel
lemma step_ckpt_p200 : opt_mstate_beq (run_m_fast 1000 cfg_p180) cfg_p200 = true := by decide +kernel
lemma step_ckpt_p220 : opt_mstate_beq (run_m_fast 1000 cfg_p200) cfg_p220 = true := by decide +kernel
lemma step_ckpt_p240 : opt_mstate_beq (run_m_fast 1000 cfg_p220) cfg_p240 = true := by decide +kernel
lemma step_ckpt_p260 : opt_mstate_beq (run_m_fast 1000 cfg_p240) cfg_p260 = true := by decide +kernel
lemma step_ckpt_p280 : opt_mstate_beq (run_m_fast 1000 cfg_p260) cfg_p280 = true := by decide +kernel
lemma step_ckpt_p300 : opt_mstate_beq (run_m_fast 1000 cfg_p280) cfg_p300 = true := by decide +kernel
lemma step_ckpt_p320 : opt_mstate_beq (run_m_fast 1000 cfg_p300) cfg_p320 = true := by decide +kernel
lemma step_ckpt_p340 : opt_mstate_beq (run_m_fast 1000 cfg_p320) cfg_p340 = true := by decide +kernel
lemma step_ckpt_p360 : opt_mstate_beq (run_m_fast 1000 cfg_p340) cfg_p360 = true := by decide +kernel
lemma step_ckpt_p380 : opt_mstate_beq (run_m_fast 1000 cfg_p360) cfg_p380 = true := by decide +kernel
lemma step_ckpt_p400 : opt_mstate_beq (run_m_fast 1000 cfg_p380) cfg_p400 = true := by decide +kernel
lemma step_ckpt_p420 : opt_mstate_beq (run_m_fast 1000 cfg_p400) cfg_p420 = true := by decide +kernel
lemma step_ckpt_p440 : opt_mstate_beq (run_m_fast 1000 cfg_p420) cfg_p440 = true := by decide +kernel
lemma step_ckpt_p460 : opt_mstate_beq (run_m_fast 1000 cfg_p440) cfg_p460 = true := by decide +kernel
lemma step_ckpt_p480 : opt_mstate_beq (run_m_fast 1000 cfg_p460) cfg_p480 = true := by decide +kernel
lemma step_ckpt_p498 : opt_mstate_beq (run_m_fast 900 cfg_p480) cfg_p498 = true := by decide +kernel
lemma halt_cfg_end : is_halt_m cfg_end = true := by decide +kernel

lemma reach_p480 : MReach cfg_p480 cfg_end := mreach_base_fast step_ckpt_p498
lemma reach_p460 : MReach cfg_p460 cfg_end := mreach_step_fast step_ckpt_p480 reach_p480
lemma reach_p440 : MReach cfg_p440 cfg_end := mreach_step_fast step_ckpt_p460 reach_p460
lemma reach_p420 : MReach cfg_p420 cfg_end := mreach_step_fast step_ckpt_p440 reach_p440
lemma reach_p400 : MReach cfg_p400 cfg_end := mreach_step_fast step_ckpt_p420 reach_p420
lemma reach_p380 : MReach cfg_p380 cfg_end := mreach_step_fast step_ckpt_p400 reach_p400
lemma reach_p360 : MReach cfg_p360 cfg_end := mreach_step_fast step_ckpt_p380 reach_p380
lemma reach_p340 : MReach cfg_p340 cfg_end := mreach_step_fast step_ckpt_p360 reach_p360
lemma reach_p320 : MReach cfg_p320 cfg_end := mreach_step_fast step_ckpt_p340 reach_p340
lemma reach_p300 : MReach cfg_p300 cfg_end := mreach_step_fast step_ckpt_p320 reach_p320
lemma reach_p280 : MReach cfg_p280 cfg_end := mreach_step_fast step_ckpt_p300 reach_p300
lemma reach_p260 : MReach cfg_p260 cfg_end := mreach_step_fast step_ckpt_p280 reach_p280
lemma reach_p240 : MReach cfg_p240 cfg_end := mreach_step_fast step_ckpt_p260 reach_p260
lemma reach_p220 : MReach cfg_p220 cfg_end := mreach_step_fast step_ckpt_p240 reach_p240
lemma reach_p200 : MReach cfg_p200 cfg_end := mreach_step_fast step_ckpt_p220 reach_p220
lemma reach_p180 : MReach cfg_p180 cfg_end := mreach_step_fast step_ckpt_p200 reach_p200
lemma reach_p160 : MReach cfg_p160 cfg_end := mreach_step_fast step_ckpt_p180 reach_p180
lemma reach_p140 : MReach cfg_p140 cfg_end := mreach_step_fast step_ckpt_p160 reach_p160
lemma reach_p120 : MReach cfg_p120 cfg_end := mreach_step_fast step_ckpt_p140 reach_p140
lemma reach_p100 : MReach cfg_p100 cfg_end := mreach_step_fast step_ckpt_p120 reach_p120
lemma reach_p80 : MReach cfg_p80 cfg_end := mreach_step_fast step_ckpt_p100 reach_p100
lemma reach_p60 : MReach cfg_p60 cfg_end := mreach_step_fast step_ckpt_p80 reach_p80
lemma reach_p40 : MReach cfg_p40 cfg_end := mreach_step_fast step_ckpt_p60 reach_p60
lemma reach_p20 : MReach cfg_p20 cfg_end := mreach_step_fast step_ckpt_p40 reach_p40
lemma reach_0 : MReach cfg_0 cfg_end := mreach_step_fast step_ckpt_p20 reach_p20
end Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 800000

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

open Solution in
theorem is_halt : IsHalt target_tm := by
  rcases reach_0 with ⟨fuel, hfuel⟩
  rcases run_m_sound fuel cfg_0 cfg_end hfuel with ⟨n, hn⟩
  refine ⟨map_cfg_0365 (mstate_to_cfg cfg_end), ⟨n, ?_⟩, ?_⟩
  · have hinit : (init [] : Cfg (Fin 2) (Fin 6)) = map_cfg_0365 (mstate_to_cfg cfg_0) := rfl
    rw [hinit, multiStep_map_0365, hn]
    rfl
  · rw [step_map_0365, is_halt_m_sound cfg_end halt_cfg_end]
    rfl

end BusyBeaver.M_1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC0LF_0RAHHH
