/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LD---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option autoImplicit true

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5


local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

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

def perm_0155 : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 0
  | 5 => 5

def map_cfg_0155 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map perm_0155, c.tape⟩

lemma step_map_0155 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (map_cfg_0155 c) = (step tm15 c).map map_cfg_0155 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;> try rfl
  all_goals omega

@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma multiStep_map_0155 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (map_cfg_0155 c) n = (multiStep tm15 c n).map map_cfg_0155 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zMs, zMs, ih]
    cases multiStep tm15 c n with
    | none => rfl
    | some c' => exact step_map_0155 c'

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
lemma z0m (a b : List α) (n : Nat) : (a ++ b) ^ n ++ a = a ++ (b ++ a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [z0j, List.append_assoc, ih, z0j]
    simp only [List.append_assoc]
lemma z0n (a b : zF) (i : Nat) (s : zB) :
    a +> ((b ++ a) ^ i) +> (b +> s) = ((a ++ b) ^ (i + 1)) +> s := by
  rw [<- append_assoc, <- append_assoc, <- z0m, List.append_assoc, z0l]

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
lemma zPt {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, _, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
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
  if w ≤ 1 then p else p / 2 + (p % 2) * (2 ^ (w - 1))

def rot_k (w : Nat) : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => rot_k w k (rot1 w p)

def rot_mod (w n p : Nat) : Nat :=
  if w ≤ 1 then p
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

lemma rot_mod_eq (w n p : Nat) : rot_mod w n p = rot_k w n p := by
  unfold rot_mod
  split_ifs with hw h
  · induction n generalizing p with
    | zero => rfl
    | succ n ih => rw [rot_k, rot1, if_pos hw, ← ih p]
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

def with_nat (e : Nat) (f : Nat → α) : α :=
  Nat.casesOn e (f 0) (fun n => f (Nat.succ n))

@[simp] lemma with_nat_eq (e : Nat) (f : Nat → α) : with_nat e f = f e := by
  cases e <;> rfl

def with_list (xs : List β) (f : List β → α) : α :=
  List.casesOn xs (f []) (fun h t => f (h :: t))

@[simp] lemma with_list_eq (xs : List β) (f : List β → α) : with_list xs f = f xs := by
  cases xs <;> rfl

def with_prod (p : α × β) (f : α × β → γ) : γ :=
  Prod.casesOn p (fun a b => f (a, b))

@[simp] lemma with_prod_eq (p : α × β) (f : α × β → γ) : with_prod p f = f p := by
  cases p; rfl

def with_block (b : Block) (f : Block → α) : α :=
  Block.casesOn b (fun pat width len =>
    with_nat pat (fun p =>
      with_nat width (fun w =>
        with_nat len (fun l =>
          f ⟨p, w, l⟩))))

@[simp] lemma with_block_eq (b : Block) (f : Block → α) : with_block b f = f b := by
  cases b; simp [with_block]

def with_stack (s : Stack) (f : Stack → α) : α :=
  List.casesOn s (f []) (fun top rest =>
    with_block top (fun top' => f (top' :: rest)))

@[simp] lemma with_stack_eq (s : Stack) (f : Stack → α) : with_stack s f = f s := by
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

def with_bool (b : Bool) (f : Bool → α) : α :=
  Bool.casesOn b (f false) (f true)

@[simp] lemma with_bool_eq (b : Bool) (f : Bool → α) : with_bool b f = f b := by
  cases b <;> rfl

def cons_lsb (b : Bool) (k : Nat) (xs : PartList) : PartList :=
  with_bool b (fun b' =>
    with_nat k (fun k' =>
      with_list xs (fun xs' =>
        if k' = 0 then xs'
        else match xs' with
        | [] => if b' then [(true, k')] else []
        | (b2, k2) :: rest =>
          if b' == b2 then
            with_nat (k' + k2) (fun kk => (b', kk) :: rest)
          else (b', k') :: (b2, k2) :: rest)))

lemma eval_cons_lsb (b : Bool) (k : Nat) (xs : PartList) :
    eval_lsb (cons_lsb b k xs) = (if b then 2 ^ k - 1 else 0) + eval_lsb xs * 2 ^ k := by
  unfold cons_lsb
  simp only [with_bool_eq, with_nat_eq, with_list_eq]
  by_cases hk : k = 0
  · subst hk; simp [eval_lsb]
  · simp only [hk, ↓reduceIte]
    cases xs with
    | nil => cases b <;> simp [eval_lsb]
    | cons head rest =>
      rcases head with ⟨b2, k2⟩
      dsimp only
      by_cases hbb : (b == b2) = true
      · simp only [hbb, ↓reduceIte, eval_lsb]
        simp only [beq_iff_eq] at hbb
        subst hbb
        rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm k2 k]
        cases b
        · simp
        · simp only [↓reduceIte]
          have hp1 := z0v k
          have hp2 := z0v k2
          have hpow : 2 ^ k2 * 2 ^ k = 2 ^ (k + k2) := by rw [← Nat.pow_add, Nat.add_comm]
          have hle : 2 ^ k ≤ 2 ^ (k + k2) := by rw [← hpow]; exact Nat.le_mul_of_pos_left _ hp2
          have hd : (2 ^ k2 - 1) * 2 ^ k = 2 ^ (k + k2) - 2 ^ k := by
            rw [Nat.sub_mul, Nat.one_mul, hpow]
          rw [hd]; omega
      · simp [hbb, eval_lsb]

lemma bsize_cons_lsb_le (b : Bool) (k : Nat) (xs : PartList) :
    bsize_parts (cons_lsb b k xs) ≤ k + bsize_parts xs := by
  unfold cons_lsb
  simp only [with_bool_eq, with_nat_eq, with_list_eq]
  by_cases hk : k = 0
  · subst hk; simp [bsize_parts]
  · simp only [hk, ↓reduceIte]
    cases xs with
    | nil => cases b <;> simp [bsize_parts]
    | cons head rest =>
      rcases head with ⟨b2, k2⟩
      dsimp only
      by_cases hbb : (b == b2) = true <;> simp [hbb, bsize_parts, Nat.add_assoc]

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
    if ys.isEmpty && !c then some ((px, kx) :: xs)
    else
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
      if hyc : (ys.isEmpty && !c) = true then
        rw [if_pos hyc] at h
        simp only [Option.some.injEq] at h
        subst h
        cases ys <;> cases c <;> simp [eval_lsb] at hyc ⊢
      else
      rw [if_neg hyc] at h
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

def drop_mult3 (top : Block) (rest : Stack) : Stack :=
  let rem := top.len % 3
  if rem = 0 then rest else ⟨top.pat, top.width, rem⟩ :: rest

def choose_limit_r_loop (n : Nat) : Nat → Nat → Stack → Nat
  | 0, _, _ => n + 1
  | _ + 1, done, [] => if done ≤ n then n + 1 else done + 1
  | fuel + 1, done, top :: rest =>
    if (top.width == 3 && top.pat == 1 && 3 ≤ top.len) = true then
      with_nat (done + top.len / 3) (fun next_done =>
        choose_limit_r_loop n fuel next_done (drop_mult3 top rest))
    else if (top.width == 1 && top.pat == 0 && 3 ≤ top.len) = true then
      with_nat (done + top.len / 3) (fun next_done =>
        if n < next_done then
          min (max (n + 2) (done + 2)) next_done
        else
          choose_limit_r_loop n fuel next_done (drop_mult3 top rest))
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


def can_pair : Stack → Bool
  | [] => false
  | top :: rest =>
    if (top.width == 1 && top.pat == 1) = true then
      if rest.isEmpty then false
      else if top.len % 4 = 0 then can_pair rest
      else true
    else if (top.width == 4 && top.pat == 14 && 4 ≤ top.len) = true then true
    else if (top.width == 4 && top.pat == 13 && 4 ≤ top.len) = true then false
    else true

def can_absorb : Stack → Bool
  | [] => false
  | top :: rest =>
    if (top.width == 1 && top.pat == 1) = true then
      if rest.isEmpty then false
      else if top.len % 4 = 0 then can_absorb rest
      else true
    else if (top.width == 4 && top.pat == 13 && 4 ≤ top.len) = true then true
    else if (top.width == 4 && top.pat == 14 && 4 ≤ top.len) = true then false
    else true

def pre_pair_l : Stack → Bool
  | b1 :: b2 :: b3 :: rest =>
    if b1.pat == 1 && b1.width == 1 && b1.len == 1 then
      if b2.pat == 0 && b2.width == 1 && b2.len == 1 then
        if b3.pat == 1 && b3.width == 1 && 3 ≤ b3.len then
          let rem := b3.len - 3
          can_pair (if rem == 0 then rest else ⟨1, 1, rem⟩ :: rest)
        else true
      else true
    else false
  | b1 :: _ :: [] => b1.pat == 1 && b1.width == 1 && b1.len == 1
  | _ => false

def pre_absorb_l : Stack → Bool
  | b1 :: b2 :: b3 :: rest =>
    if b1.pat == 1 && b1.width == 1 && b1.len == 1 then
      if b2.pat == 0 && b2.width == 1 && b2.len == 1 then
        if b3.pat == 1 && b3.width == 1 && 3 ≤ b3.len then
          let rem := b3.len - 3
          can_absorb (if rem == 0 then rest else ⟨1, 1, rem⟩ :: rest)
        else true
      else true
    else false
  | b1 :: _ :: [] => b1.pat == 1 && b1.width == 1 && b1.len == 1
  | _ => false

def can_parse_r : Stack → Bool
  | top :: _ => !(top.width == 3 && top.pat == 1 && top.len % 3 == 1)
  | [] => true

def sub_lsb_checked (fuel n k : Nat) (a b : PartList) : Option PartList :=
  if n < k then none else sub_lsb fuel false a b

lemma sub_lsb_checked_sound (fuel n k : Nat) (a b out : PartList)
    (h : sub_lsb_checked fuel n k a b = some out) :
    bsize_parts out ≤ bsize_parts a ∧
    eval_lsb out + eval_lsb b + (if false then 1 else 0) = eval_lsb a := by
  unfold sub_lsb_checked at h
  split_ifs at h
  exact sub_lsb_sound fuel false a b out h

def try_pair_stack (kfuel : Nat) (s : MState) : Option MState :=
  if s.q = 0 then
    if (pre_pair_l s.l && can_parse_r s.r) = true then
      match pop_word 29 5 s.l with
      | none => none
      | some lc =>
        if can_pair lc then
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
                              match sub_lsb_checked kfuel n k a b with
                              | some out =>
                                let l1 := push_prefix_l (put_l_stack out n res_l.2)
                                let r1 := put_r_stack [] k res_r.2
                                some_mstate 0 l1 r1
                              | none =>
                                match sub_lsb_checked kfuel k n b a with
                                | some out =>
                                  let l1 := push_prefix_l (put_l_stack [] n res_l.2)
                                  let r1 := put_r_stack out k res_r.2
                                  some_mstate 0 l1 r1
                                | none => none)))))))
        else none
    else none
  else none

lemma try_pair_stack_sound (kfuel : Nat) (s s' : MState) (h : try_pair_stack kfuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold try_pair_stack at h
  split_ifs at h with hq hpre
  cases hpw : pop_word 29 5 s.l with
  | none => rw [hpw] at h; contradiction
  | some lc =>
    rw [hpw] at h
    simp only [with_prod_eq, with_list_eq, with_nat_eq] at h
    split_ifs at h with hcp ha_empty hlim0 hb_empty
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
    change ¬b.isEmpty = true at hb_empty
    have hne_b : b ≠ [] := by intro hc; simp [hc] at hb_empty
    rcases parse_r_sound kfuel (choose_limit_r kfuel n s.r) s.r hne_b with ⟨hk1, hpr⟩
    have hal := eval_lsb_lt a
    have hbl := eval_lsb_lt b
    have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    cases hsub1 : sub_lsb_checked kfuel n k a b with
    | some out =>
      rw [hsub1] at h; simp only [some_mstate_eq, Option.some.injEq] at h; subst h
      rcases sub_lsb_checked_sound kfuel n k a b out hsub1 with ⟨hbs_out, heval_out⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at heval_out
      unfold mstate_to_cfg; dsimp only
      rw [hq, hpw_eq, hpl, hpr, push_prefix_l_sound, put_l_stack_sound out n lc1 hbs_out,
        put_r_stack, put_r_rec_sound [] k rc1 hk1 (by simp [bsize_parts])]
      change (z0V (z0o ld0 ld1 n (eval_lsb a) (stack_to_tape lc1))
        (MC (k - 1) (eval_lsb b) (stack_to_tape rc1))) [tm15]⊢*
        (z0V (z0o ld0 ld1 n (eval_lsb out) (stack_to_tape lc1))
        (MC (k - 1) 0 (stack_to_tape rc1)))
      have hpg := pair_general n (eval_lsb out) (k - 1) 0 (eval_lsb b) (stack_to_tape lc1) (stack_to_tape rc1)
        (by rw [heval_out]; exact hal) (by rw [Nat.zero_add, hk_eq]; exact hbl)
      rw [heval_out, Nat.zero_add] at hpg
      exact hpg
    | none =>
      rw [hsub1] at h; dsimp only at h
      cases hsub2 : sub_lsb_checked kfuel k n b a with
      | none => rw [hsub2] at h; contradiction
      | some out =>
        rw [hsub2] at h; simp only [some_mstate_eq, Option.some.injEq] at h; subst h
        rcases sub_lsb_checked_sound kfuel k n b a out hsub2 with ⟨hbs_out, heval_out⟩
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
          (by rw [Nat.zero_add]; exact hal) (by rw [heval_out, hk_eq]; exact hbl)
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
    if (pre_absorb_l s.l && can_parse_r s.r) = true then
      match pop_word 29 5 s.l with
      | none => none
      | some lc0 =>
        if can_absorb lc0 then
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
    else none
  else none

lemma try_absorb_stack_sound (kfuel : Nat) (s s' : MState) (h : try_absorb_stack kfuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold try_absorb_stack at h
  split_ifs at h with hq hpre
  cases hpw : pop_word 29 5 s.l with
  | none => rw [hpw] at h; contradiction
  | some lc0 =>
    rw [hpw] at h
    simp only [with_prod_eq, with_list_eq, with_nat_eq] at h
    split_ifs at h with hca hm0 hlim0 hb_empty hmin0
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
      dsimp only [with_prod_eq, with_list_eq, with_nat_eq] at h
      split_ifs at h with hm_act
      simp only [some_mstate_eq, Option.some.injEq] at h; subst h
      change ¬m_init = 0 at hmin0
      have hmin_pos : 1 ≤ m_init := Nat.pos_of_ne_zero hmin0
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
      change ¬res_r.1.isEmpty = true at hb_empty
      have hne_b : res_r.1 ≠ [] := by intro hc; simp [hc] at hb_empty
      rcases parse_r_sound kfuel lim_r s.r hne_b with ⟨hk1, hpr⟩
      have hbl := eval_lsb_lt res_r.1
      have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk1
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
        (stack_to_tape res2.2) (stack_to_tape res_r.2) (by rw [heval_out, hk_eq]; exact hbl)

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

def has_head_bit1 : Stack → Bool
  | [] => false
  | top :: _ => top.pat % 2 == 1

def can_any_macro (s : MState) : Bool :=
  if s.q == 0 then
    (match s.r with
     | top :: _ => top.pat % 2 == 1 && !(top.width == 1 && 2 ≤ top.len)
     | [] => false) ||
    ((pre_pair_l s.l || pre_absorb_l s.l) && can_parse_r s.r)
  else if s.q == 1 || s.q == 2 then
    has_head_bit1 s.l && has_head_bit1 s.r
  else if s.q == 3 then
    match s.r with
    | [] => false
    | top :: rest =>
      if top.width == 1 && top.pat == 0 then
        if 1 < top.len then false else has_head_bit1 rest
      else if top.width == 1 && top.pat == 1 && top.len == 1 then
        match rest with
        | [] => false
        | b2 :: _ => !(b2.width == 1 && b2.pat == 0 && 2 ≤ b2.len)
      else true
  else false

def run_prim : Nat → MState → Option MState
  | 0, s => some s
  | fuel + 1, s =>
    if (s.q = 5 && (pop1 s.r).1 = 1) || can_any_macro s then some s
    else
      match step_prim s with
      | none => some s
      | some s' => run_prim fuel s'

lemma run_prim_sound (fuel : Nat) (s s' : MState) (h : run_prim fuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  induction fuel generalizing s with
  | zero => simp [run_prim] at h; subst h; exact ⟨0, rfl⟩
  | succ fuel ih =>
    unfold run_prim at h
    split_ifs at h with hstop
    · simp only [Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
    · cases hp : step_prim s with
      | none => rw [hp] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
      | some s1 =>
        rw [hp] at h
        exact zSt (step_prim_sound s s1 hp) (ih s1 h)

def step_prim_plus (s : MState) : Option MState :=
  match step_prim s with
  | none => none
  | some s1 => run_prim 24 s1

lemma step_prim_plus_sound (s s' : MState) (h : step_prim_plus s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  unfold step_prim_plus at h
  cases hpr : step_prim s with
  | none => rw [hpr] at h; contradiction
  | some s1 =>
    rw [hpr] at h
    exact zSt (step_prim_sound s s1 hpr) (run_prim_sound 24 s1 s' h)

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
  | none => step_prim_plus s

def step_m_q1 (s : MState) : Option MState :=
  match do_shift_left 1 1 1 0 1 s with
  | some s' => some s'
  | none => step_prim_plus s

def step_m_q2 (s : MState) : Option MState :=
  match do_shift_left 2 2 3 1 2 s with
  | some s' => some s'
  | none => step_prim_plus s

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
  | none => step_prim_plus s

def step_m (s : MState) : Option MState :=
  match s.q.val with
  | 0 => step_m_q0 s
  | 1 => step_m_q1 s
  | 2 => step_m_q2 s
  | 3 => step_m_q3 s
  | _ => step_prim_plus s

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
    | none => rw [hs] at h; dsimp only at h; exact step_prim_plus_sound s s' h
  · unfold step_m_q1 at h
    cases hs : do_shift_left 1 1 1 0 1 s with
    | some s1 => rw [hs] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_left_sound 1 1 1 0 1 0 s s1 rfl rfl sh_1_sound hs
    | none => rw [hs] at h; dsimp only at h; exact step_prim_plus_sound s s' h
  · unfold step_m_q2 at h
    cases hs : do_shift_left 2 2 3 1 2 s with
    | some s1 => rw [hs] at h; simp only [Option.some.injEq] at h; subst h; exact do_shift_left_sound 2 2 3 1 2 1 s s1 rfl rfl sh_2_sound hs
    | none => rw [hs] at h; dsimp only at h; exact step_prim_plus_sound s s' h
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
    | none => rw [h6] at h; dsimp only at h; exact step_prim_plus_sound s s' h
  · exact step_prim_plus_sound s s' h

def run_m : Nat → MState → Option MState
  | 0, s => some s
  | fuel + 1, s =>
    match step_m s with
    | none => none
    | some s' => run_m fuel s'

lemma run_m_sound (fuel : Nat) (s s' : MState) (h : run_m fuel s = some s') :
    (mstate_to_cfg s) [tm15]⊢* (mstate_to_cfg s') := by
  induction fuel generalizing s with
  | zero =>
    simp [run_m] at h; subst h; exact ⟨0, rfl⟩
  | succ fuel ih =>
    simp only [run_m] at h
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







set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxHeartbeats 2000000

noncomputable def bnot_fast (x : Bool) : Bool :=
  @Bool.rec (fun _ => Bool) true false x

noncomputable def band_fast (x y : Bool) : Bool :=
  @Bool.rec (fun _ => Bool) false y x

noncomputable def bor_fast (x y : Bool) : Bool :=
  @Bool.rec (fun _ => Bool) y true x

noncomputable def bxor_fast (x y : Bool) : Bool :=
  @Bool.rec (fun _ => Bool) y (@Bool.rec (fun _ => Bool) true false y) x

noncomputable def nat_min_fast (x y : Nat) : Nat :=
  @Bool.rec (fun _ => Nat) y x (Nat.ble x y)

noncomputable def nat_max_fast (x y : Nat) : Nat :=
  @Bool.rec (fun _ => Nat) x y (Nat.ble x y)

noncomputable def withOptionFast {α β : Type} (o : Option α) (onNone : β) (onSome : α → β) : β :=
  @Option.rec α (fun _ => β) onNone onSome o

noncomputable def matchStackFast {α : Type} (s : Stack) (onNil : α) (onCons : Block → Stack → α) : α :=
  @List.rec Block (fun _ => α) onNil (fun hd tl _ => onCons hd tl) s

noncomputable def matchPartListFast {α : Type} (xs : PartList) (onNil : α) (onCons : Bool → Nat → PartList → α) : α :=
  @List.rec (Bool × Nat) (fun _ => α) onNil (fun hd tl _ => @Prod.rec Bool Nat (fun _ => α) (fun b k => onCons b k tl) hd) xs

noncomputable def isEmptyPartListFast (xs : PartList) : Bool :=
  @List.rec (Bool × Nat) (fun _ => Bool) true (fun _ _ _ => false) xs

def fin6_0 : Fin 6 := ⟨0, by decide⟩
def fin6_1 : Fin 6 := ⟨1, by decide⟩
def fin6_2 : Fin 6 := ⟨2, by decide⟩
def fin6_3 : Fin 6 := ⟨3, by decide⟩
def fin6_4 : Fin 6 := ⟨4, by decide⟩
def fin6_5 : Fin 6 := ⟨5, by decide⟩

noncomputable def consBlock1 (p w l : Nat) (rest : Stack) : Stack :=
  @Nat.rec (fun _ => Stack) [] (fun p0 _ =>
    @Nat.rec (fun _ => Stack) [] (fun w0 _ =>
      @Nat.rec (fun _ => Stack) [] (fun l0 _ =>
        ⟨p0, w0, l0⟩ :: rest) (Nat.add 1 l)) (Nat.add 1 w)) (Nat.add 1 p)

noncomputable def withProdFast {α β γ : Type} (p : α × β) (f : α → β → γ) : γ :=
  @Prod.rec α β (fun _ => γ) f p

noncomputable def withProd3Fast {α β γ δ : Type} (p : α × β × γ) (f : α → β → γ → δ) : δ :=
  @Prod.rec α (β × γ) (fun _ => δ) (fun a bc => @Prod.rec β γ (fun _ => δ) (fun b c => f a b c) bc) p

noncomputable def withNatFast {α : Type} (x : Nat) (f : Nat → α) : α :=
  @Nat.rec (fun _ => α) (f 0) (fun x0 _ => f x0) (Nat.add 1 x)

noncomputable def withBoolFast {α : Type} (b : Bool) (f : Bool → α) : α :=
  @Bool.rec (fun _ => α) (f false) (f true) b

noncomputable def withStackFast {α : Type} (s : Stack) (f : Stack → α) : α :=
  @List.rec Block (fun _ => α) (f []) (fun top rest _ => f (top :: rest)) s

noncomputable def withPartFast {α : Type} (p : Bool × Nat) (f : Bool → Nat → α) : α :=
  @Prod.rec Bool Nat (fun _ => α) (fun b n => withBoolFast b (fun b0 => withNatFast n (fun n0 => f b0 n0))) p

noncomputable def withPartListFast {α : Type} (xs : PartList) (f : PartList → α) : α :=
  @List.rec (Bool × Nat) (fun _ => α) (f []) (fun hd tl _ => withPartFast hd (fun b0 n0 => f ((b0, n0) :: tl))) xs

noncomputable def someMStateFast (q : Fin 6) (l r : Stack) : Option MState :=
  withStackFast l (fun l' => withStackFast r (fun r' => some ⟨q, l', r'⟩))

noncomputable def stack_len_fast : Stack → Nat :=
  @List.rec Block (fun _ => Nat) 0 (fun _ _ ih => Nat.add ih 1)

noncomputable def mkBlock_f_p : Nat → Nat → Nat → Block :=
fun p w l =>
  @Nat.rec (fun _ => Block) ⟨0, 0, 0⟩ (fun p' _ =>
    @Nat.rec (fun _ => Block) ⟨0, 0, 0⟩ (fun w' _ =>
      @Nat.rec (fun _ => Block) ⟨0, 0, 0⟩ (fun l' _ =>
        ⟨p', w', l'⟩) (Nat.add 1 l)) (Nat.add 1 w)) (Nat.add 1 p)

noncomputable def rot1_f_p : Nat → Nat → Nat :=
fun w p =>
  @Bool.rec (fun _ => Nat)
    (Nat.add (Nat.shiftRight p 1) (Nat.mul (Nat.land p 1) (Nat.shiftLeft 1 (Nat.sub w 1))))
    p
    (Nat.ble w 1)

noncomputable def rot_mod_f_p : Nat → Nat → Nat → Nat :=
fun w n p =>
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat)
      (rot_k w n p)
      (withNatFast (Nat.mod n w) (fun r =>
        @Bool.rec (fun _ => Nat)
          (Nat.add (Nat.shiftRight p r) (Nat.shiftLeft (Nat.land p (Nat.sub (Nat.shiftLeft 1 r) 1)) (Nat.sub w r)))
          p
          (Nat.beq r 0)))
      (band_fast (Nat.ble 2 w) (band_fast (Nat.ble w 4) (band_fast (Nat.ble p 15) (Nat.ble p (Nat.sub (Nat.shiftLeft 1 w) 1))))))
    p
    (bor_fast (Nat.beq p 0) (band_fast (Nat.beq w 1) (Nat.beq p 1)))

noncomputable def bit_of_bool_f_p : Nat → Bool :=
fun x => Nat.beq (Nat.land x 1) 1

noncomputable def push_stack_aux_fast : Stack → Nat → Nat → Nat → Stack :=
  @List.rec Block (fun _ => Nat → Nat → Nat → Stack)
    (fun p w l => @Bool.rec (fun _ => Stack) (⟨p, w, l⟩ :: []) [] (Nat.beq p 0))
    (fun top rest ih p w l =>
      @Bool.rec (fun _ => Stack)
        (⟨p, w, l⟩ :: top :: rest)
        (withNatFast (Nat.add l top.len) (fun nl => ih p w nl))
        (band_fast (Nat.beq w top.width) (Nat.beq (rot_mod_f_p w l p) top.pat)))

noncomputable def push_stack_fast (p w l : Nat) (s : Stack) : Stack :=
  withNatFast l (fun l0 =>
    @Bool.rec (fun _ => Stack)
      (withNatFast p (fun p0 => withNatFast w (fun w0 => push_stack_aux_fast s p0 w0 l0)))
      s
      (Nat.beq l0 0))

noncomputable def drop_stack_aux_fast : Stack → Nat → Stack :=
  @List.rec Block (fun _ => Nat → Stack)
    (fun _ => [])
    (fun top rest ih n =>
      @Bool.rec (fun _ => Stack)
        (consBlock1 (rot_mod_f_p top.width n top.pat) top.width (Nat.sub top.len n) rest)
        (withNatFast (Nat.sub n top.len) (fun rem =>
          @Bool.rec (fun _ => Stack) (ih rem) rest (Nat.beq rem 0)))
        (Nat.ble top.len n))

noncomputable def drop_stack_fast : Nat → Stack → Stack :=
fun n s =>
  withNatFast n (fun n0 =>
    @Bool.rec (fun _ => Stack) (drop_stack_aux_fast s n0) s (Nat.beq n0 0))

noncomputable def pop1_b_fast : Stack → Bool × Stack :=
fun s =>
  @List.rec Block (fun _ => Bool × Stack)
    (false, [])
    (fun top rest ih =>
      @Bool.rec (fun _ => Bool × Stack)
        (bit_of_bool_f_p top.pat,
         @Bool.rec (fun _ => Stack)
           (consBlock1 (rot1_f_p top.width top.pat) top.width (Nat.sub top.len 1) rest)
           rest
           (Nat.beq top.len 1))
        ih
        (Nat.beq top.len 0))
    s

noncomputable def pop_word_f_p (bit_of_bool_f : Nat → Bool) (pop1_b_f : Stack → Bool × Stack) : Nat → Nat → Stack → Option Stack :=
fun pat w s =>
  @Nat.rec (fun _ => Nat → Stack → Option Stack)
    (fun _ s => withStackFast s some)
    (fun _ ih pat s =>
      withProdFast (pop1_b_f s) (fun r1 r2 =>
        @Bool.rec (fun _ => Option Stack) none (withNatFast (Nat.shiftRight pat 1) (fun np => ih np r2))
          (bnot_fast (bxor_fast r1 (bit_of_bool_f pat)))))
    w pat s

noncomputable def fast_match_f_p : Nat → Nat → Block → Bool :=
fun pat w top =>
  @Bool.rec (fun _ => Bool)
    (0 < w && w ≤ top.len && rot_k top.width w top.pat == top.pat &&
     pat_word top.width top.pat w == word_of pat w)
    (band_fast (Nat.ble w top.len)
      (let mul := @Bool.rec (fun _ => Nat)
        (@Bool.rec (fun _ => Nat)
          (@Bool.rec (fun _ => Nat) 273 585 (Nat.beq top.width 3))
          1365 (Nat.beq top.width 2))
        4095 (Nat.beq top.width 1)
       withNatFast (Nat.mul top.pat mul) (fun pm =>
         band_fast (Nat.beq (Nat.land (Nat.shiftRight pm w) (Nat.sub (Nat.shiftLeft 1 top.width) 1)) top.pat)
           (Nat.beq (Nat.land pm (Nat.sub (Nat.shiftLeft 1 w) 1)) pat))))
    (band_fast (Nat.ble 1 w)
      (band_fast (Nat.ble w 4)
        (band_fast (Nat.ble 1 top.width)
          (band_fast (Nat.ble top.width 4)
            (band_fast (Nat.ble top.pat (Nat.sub (Nat.shiftLeft 1 top.width) 1))
              (Nat.ble pat (Nat.sub (Nat.shiftLeft 1 w) 1)))))))

noncomputable def count_stack_mut_f_p (drop_stack_f : Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (fast_match_f : Nat → Nat → Block → Bool) : Nat → Nat → Nat → Nat → Stack → Nat × Stack :=
fun pat w fuel limit s =>
  @Nat.rec (fun _ => Nat → Stack → Nat × Stack)
    (fun _ s => (0, s))
    (fun _ ih limit s =>
      @Bool.rec (fun _ => Nat × Stack)
        (matchStackFast s
          (0, [])
          (fun top rest =>
            @Bool.rec (fun _ => Nat × Stack)
              (withOptionFast (pop_word_f pat w (top :: rest))
                (0, top :: rest)
                (fun s1 =>
                  withNatFast (Nat.sub limit 1) (fun nlim =>
                    withProdFast (ih nlim s1) (fun r1 r2 =>
                      withNatFast (Nat.add 1 r1) (fun c => (c, r2))))))
              (withNatFast (nat_min_fast limit (Nat.div top.len w)) (fun bulk =>
                withNatFast (Nat.sub limit bulk) (fun nlim =>
                  withStackFast (drop_stack_f (Nat.mul bulk w) (top :: rest)) (fun s_drop =>
                    withProdFast (ih nlim s_drop) (fun r1 r2 =>
                      withNatFast (Nat.add bulk r1) (fun c => (c, r2)))))))
              (fast_match_f pat w top)))
        (0, s)
        (Nat.beq limit 0))
    fuel limit s

noncomputable def mkPart_f_p : Bool → Nat → PartList → PartList :=
fun b k xs =>
  withNatFast k (fun k0 =>
    @Bool.rec (fun _ => PartList)
      (withBoolFast b (fun b0 =>
        matchPartListFast xs
          (@Bool.rec (fun _ => PartList) [] [(true, k0)] b0)
          (fun b2 k2 rest =>
            @Bool.rec (fun _ => PartList)
              ((b0, k0) :: (b2, k2) :: rest)
              (withNatFast (Nat.add k0 k2) (fun nk => (b0, nk) :: rest))
              (bnot_fast (bxor_fast b0 b2)))))
      xs
      (Nat.beq k0 0))

noncomputable def bsize_parts_f_p : PartList → Nat :=
@List.rec (Bool × Nat) (fun _ => Nat) 0 (fun hd _ ih => @Prod.rec Bool Nat (fun _ => Nat) (fun _ d => Nat.add d ih) hd)

noncomputable def put_l_parts_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) : PartList → Stack → Stack :=
@List.rec (Bool × Nat) (fun _ => Stack → Stack)
  (fun s => s)
  (fun hd _ ih s =>
    @Prod.rec Bool Nat (fun _ => Stack) (fun b d =>
      push_stack_f (@Bool.rec (fun _ => Nat) 1 14 b) (@Bool.rec (fun _ => Nat) 1 4 b) (Nat.mul d 4) (ih s)) hd)

noncomputable def put_l_stack_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (bsize_parts_f : PartList → Nat) (put_l_parts_f : PartList → Stack → Stack) : PartList → Nat → Stack → Stack :=
fun xs n s =>
  withNatFast (bsize_parts_f xs) (fun bs =>
    withStackFast (@Bool.rec (fun _ => Stack) s (push_stack_f 1 1 (Nat.mul (Nat.sub n bs) 4) s) (Nat.ble (Nat.add bs 1) n)) (fun s1 =>
      put_l_parts_f xs s1))

noncomputable def put_r_rec_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) : PartList → Nat → Stack → Stack :=
@List.rec (Bool × Nat) (fun _ => Nat → Stack → Stack)
  (fun k s => push_stack_f 1 3 (Nat.sub (Nat.mul k 3) 2) s)
  (fun hd _ ih k s =>
    @Prod.rec Bool Nat (fun _ => Stack) (fun b d =>
      @Bool.rec (fun _ => Stack)
        (@Bool.rec (fun _ => Stack)
          (withNatFast (Nat.sub k d) (fun nk =>
            push_stack_f (@Bool.rec (fun _ => Nat) 1 0 b) (@Bool.rec (fun _ => Nat) 3 1 b) (Nat.mul d 3) (ih nk s)))
          (push_stack_f (@Bool.rec (fun _ => Nat) 1 0 b) (@Bool.rec (fun _ => Nat) 3 1 b) (Nat.sub (Nat.mul d 3) 2) s)
          (Nat.ble k d))
        (ih k s)
        (Nat.beq d 0)) hd)

noncomputable def parse_step_l_f_p (drop_stack_f : Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) : Nat → Stack → Option (Bool × Nat × Stack) :=
fun limit s =>
  matchStackFast s
    none
    (fun top rest =>
      @Bool.rec (fun _ => Option (Bool × Nat × Stack))
        (@Bool.rec (fun _ => Option (Bool × Nat × Stack))
          (withOptionFast (pop_word_f 15 4 (top :: rest))
            (withOptionFast (pop_word_f 14 4 (top :: rest))
              none
              (fun s1 => some (true, 1, s1)))
            (fun s1 => some (false, 1, s1)))
          (withNatFast (nat_min_fast limit (Nat.div top.len 4)) (fun k =>
            withStackFast (drop_stack_f (Nat.mul k 4) (top :: rest)) (fun s_drop =>
              some (true, k, s_drop))))
          (band_fast (Nat.beq top.width 4) (band_fast (Nat.beq top.pat 14) (Nat.ble 4 top.len))))
        (withNatFast (nat_min_fast limit (Nat.div top.len 4)) (fun k =>
          withStackFast (drop_stack_f (Nat.mul k 4) (top :: rest)) (fun s_drop =>
            some (false, k, s_drop))))
        (band_fast (Nat.beq top.width 1) (band_fast (Nat.beq top.pat 1) (Nat.ble 4 top.len))))

noncomputable def parse_l_f_p (parse_step_l_f : Nat → Stack → Option (Bool × Nat × Stack)) : Nat → Nat → Stack → PartList × Stack :=
@Nat.rec (fun _ => Nat → Stack → PartList × Stack)
  (fun _ s => ([], s))
  (fun _ ih limit s =>
    @Bool.rec (fun _ => PartList × Stack)
      (withOptionFast (parse_step_l_f limit s)
        ([], s)
        (fun p =>
          withProd3Fast p (fun bit k s1 =>
            withNatFast (Nat.sub limit k) (fun nlim =>
              withProdFast (ih nlim s1) (fun r1 r2 =>
                @Bool.rec (fun _ => PartList × Stack)
                  ((bit, k) :: r1, r2)
                  ([], s)
                  (band_fast (bnot_fast bit) (isEmptyPartListFast r1)))))))
      ([], s)
      (Nat.beq limit 0))

noncomputable def parse_step_r_f_p (drop_stack_f : Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) : Nat → Stack → Option (Bool × Nat × Stack) :=
fun limit s =>
  matchStackFast s
    none
    (fun top rest =>
      @Bool.rec (fun _ => Option (Bool × Nat × Stack))
        (@Bool.rec (fun _ => Option (Bool × Nat × Stack))
          (withOptionFast (pop_word_f 1 3 (top :: rest))
            (withOptionFast (pop_word_f 0 3 (top :: rest))
              none
              (fun s1 => some (true, 1, s1)))
            (fun s1 => some (false, 1, s1)))
          (withNatFast (nat_min_fast limit (Nat.div top.len 3)) (fun k =>
            withStackFast (drop_stack_f (Nat.mul k 3) (top :: rest)) (fun s_drop =>
              some (true, k, s_drop))))
          (band_fast (Nat.beq top.width 1) (band_fast (Nat.beq top.pat 0) (Nat.ble 3 top.len))))
        (withNatFast (nat_min_fast limit (Nat.div top.len 3)) (fun k =>
          withStackFast (drop_stack_f (Nat.mul k 3) (top :: rest)) (fun s_drop =>
            some (false, k, s_drop))))
        (band_fast (Nat.beq top.width 3) (band_fast (Nat.beq top.pat 1) (Nat.ble 3 top.len))))

noncomputable def parse_r_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) (parse_step_r_f : Nat → Stack → Option (Bool × Nat × Stack)) : Nat → Nat → Stack → PartList × Stack :=
@Nat.rec (fun _ => Nat → Stack → PartList × Stack)
  (fun _ s => ([], s))
  (fun _ ih limit s =>
    @Bool.rec (fun _ => PartList × Stack)
      (matchStackFast s
        ([(true, limit)], [])
        (fun top rest =>
          withOptionFast (parse_step_r_f limit (top :: rest))
            (withProdFast (pop1_b_f (top :: rest)) (fun p1 p2 =>
              @Bool.rec (fun _ => PartList × Stack) ([], top :: rest) (withStackFast p2 (fun p2' => ([(true, 1)], p2'))) (bnot_fast p1)))
            (fun p =>
              withProd3Fast p (fun bit k s1 =>
                withNatFast (Nat.sub limit k) (fun nlim =>
                  withProdFast (ih nlim s1) (fun r1 r2 =>
                    @Bool.rec (fun _ => PartList × Stack)
                      ((bit, k) :: r1, r2)
                      (@Bool.rec (fun _ => PartList × Stack) ([], top :: rest) (withStackFast (push_stack_f 0 1 2 s1) (fun sp => ([(true, k)], sp))) bit)
                      (isEmptyPartListFast r1)))))))
      ([], s)
      (Nat.beq limit 0))

noncomputable def sub_lsb_f_p(mkPart_f : Bool → Nat → PartList → PartList) : Nat → Bool → PartList → PartList → Option PartList :=
@Nat.rec (fun _ => Bool → PartList → PartList → Option PartList)
  (fun _ _ _ => none)
  (fun _ ih c xs ys =>
    matchPartListFast xs
      (@Bool.rec (fun _ => Option PartList) none (some [])
        (band_fast (isEmptyPartListFast ys) (bnot_fast c)))
      (fun px kx xrest =>
        matchPartListFast ys
          (@Bool.rec (fun _ => Option PartList)
            (@Bool.rec (fun _ => Option PartList)
              (withBoolFast (bxor_fast px c) (fun s1_1 =>
                withBoolFast (band_fast (bnot_fast px) c) (fun s1_2 =>
                  @Bool.rec (fun _ => Option PartList)
                    (withOptionFast (ih s1_2 xrest [])
                      none
                      (fun out => some (mkPart_f s1_1 1 out)))
                    (withBoolFast (bxor_fast px s1_2) (fun s2_1 =>
                      withBoolFast (band_fast (bnot_fast px) s1_2) (fun s2_2 =>
                        withOptionFast (ih s2_2 xrest [])
                          none
                          (fun out => some (mkPart_f s1_1 1 (mkPart_f s2_1 (Nat.sub kx 1) out))))))
                    (Nat.ble 2 kx))))
              (ih c xrest [])
              (Nat.beq kx 0))
            (some ((px, kx) :: xrest))
            (bnot_fast c))
          (fun qy ly yrest =>
            withNatFast (nat_min_fast kx ly) (fun n =>
              withPartListFast (@Bool.rec (fun _ => PartList) xrest ((px, Nat.sub kx n) :: xrest) (Nat.ble (Nat.add n 1) kx)) (fun nx =>
                withPartListFast (@Bool.rec (fun _ => PartList) yrest ((qy, Nat.sub ly n) :: yrest) (Nat.ble (Nat.add n 1) ly)) (fun ny =>
                  @Bool.rec (fun _ => Option PartList)
                    (withBoolFast (bxor_fast px qy) (fun pxq =>
                      withBoolFast (bxor_fast pxq c) (fun s1_1 =>
                        withBoolFast (bor_fast (band_fast (bnot_fast px) (bor_fast qy c)) (band_fast qy c)) (fun s1_2 =>
                          @Bool.rec (fun _ => Option PartList)
                            (withOptionFast (ih s1_2 nx ny)
                              none
                              (fun out => some (mkPart_f s1_1 1 out)))
                            (withBoolFast (bxor_fast pxq s1_2) (fun s2_1 =>
                              withBoolFast (bor_fast (band_fast (bnot_fast px) (bor_fast qy s1_2)) (band_fast qy s1_2)) (fun s2_2 =>
                                withOptionFast (ih s2_2 nx ny)
                                  none
                                  (fun out => some (mkPart_f s1_1 1 (mkPart_f s2_1 (Nat.sub n 1) out))))))
                            (Nat.ble 2 n)))))
                    (ih c nx ny)
                    (Nat.beq n 0)))))))

noncomputable def sub_lsb_checked_f_p (sub_lsb_f : Nat → Bool → PartList → PartList → Option PartList) :
    Nat → Nat → Nat → PartList → PartList → Option PartList :=
fun fuel n k a b =>
  @Bool.rec (fun _ => Option PartList) (sub_lsb_f fuel false a b) none (Nat.ble (Nat.add n 1) k)

noncomputable def drop_mult3_fast (top : Block) (rest : Stack) : Stack :=
  withNatFast (Nat.mod top.len 3) (fun rem =>
    @Bool.rec (fun _ => Stack) (consBlock1 top.pat top.width rem rest) rest (Nat.beq rem 0))

noncomputable def choose_limit_r_f_p (drop_mult3_f : Block → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) : Nat → Nat → Nat → Stack → Nat :=
fun n fuel done r =>
  @Nat.rec (fun _ => Nat → Stack → Nat)
    (fun _ _ => Nat.add n 1)
    (fun _ ih done s =>
      matchStackFast s
        (@Bool.rec (fun _ => Nat) (Nat.add done 1) (Nat.add n 1) (Nat.ble done n))
        (fun top rest =>
          @Bool.rec (fun _ => Nat)
            (@Bool.rec (fun _ => Nat)
              (withOptionFast (pop_word_f 1 3 (top :: rest))
                (withOptionFast (pop_word_f 0 3 (top :: rest))
                  (@Bool.rec (fun _ => Nat) done (Nat.add done 1) (bnot_fast (pop1_b_f (top :: rest)).1))
                  (fun r1 =>
                    @Bool.rec (fun _ => Nat)
                      (withNatFast (Nat.add done 1) (fun nd => ih nd r1))
                      (Nat.add done 1)
                      (Nat.ble n done)))
                (fun r1 => withNatFast (Nat.add done 1) (fun nd => ih nd r1)))
              (withNatFast (Nat.add done (Nat.div top.len 3)) (fun next_done =>
                @Bool.rec (fun _ => Nat)
                  (ih next_done (drop_mult3_f top rest))
                  (nat_min_fast (nat_max_fast (Nat.add n 2) (Nat.add done 2)) next_done)
                  (Nat.ble (Nat.add n 1) next_done)))
              (band_fast (Nat.beq top.width 1) (band_fast (Nat.beq top.pat 0) (Nat.ble 3 top.len))))
            (withNatFast (Nat.add done (Nat.div top.len 3)) (fun next_done =>
              ih next_done (drop_mult3_f top rest)))
            (band_fast (Nat.beq top.width 3) (band_fast (Nat.beq top.pat 1) (Nat.ble 3 top.len)))))
    fuel done r

noncomputable def push_prefix_l_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) : Stack → Stack :=
fun l => push_stack_f 1 1 1 (push_stack_f 0 1 1 (push_stack_f 1 1 3 l))

noncomputable def build_vprime_f_p (mkPart_f : Bool → Nat → PartList → PartList) : Nat → Nat → PartList :=
fun n m_use =>
  @Bool.rec (fun _ => PartList)
    (mkPart_f true 1 [])
    (mkPart_f true 1 (mkPart_f false n (mkPart_f true (Nat.sub m_use 1) [])))
    (Nat.ble 2 m_use)

noncomputable def can_pair_f : Stack → Bool :=
  @List.rec Block (fun _ => Bool)
    false
    (fun top rest ih =>
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool)
            true
            false
            (band_fast (Nat.beq top.width 4) (band_fast (Nat.beq top.pat 13) (Nat.ble 4 top.len))))
          true
          (band_fast (Nat.beq top.width 4) (band_fast (Nat.beq top.pat 14) (Nat.ble 4 top.len))))
        (matchStackFast rest
          false
          (fun _ _ => @Bool.rec (fun _ => Bool) true ih (Nat.beq (Nat.mod top.len 4) 0)))
        (band_fast (Nat.beq top.width 1) (Nat.beq top.pat 1)))

noncomputable def can_absorb_f : Stack → Bool :=
  @List.rec Block (fun _ => Bool)
    false
    (fun top rest ih =>
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool)
            true
            false
            (band_fast (Nat.beq top.width 4) (band_fast (Nat.beq top.pat 14) (Nat.ble 4 top.len))))
          true
          (band_fast (Nat.beq top.width 4) (band_fast (Nat.beq top.pat 13) (Nat.ble 4 top.len))))
        (matchStackFast rest
          false
          (fun _ _ => @Bool.rec (fun _ => Bool) true ih (Nat.beq (Nat.mod top.len 4) 0)))
        (band_fast (Nat.beq top.width 1) (Nat.beq top.pat 1)))

noncomputable def pre_pair_l_f (can_pair_fn : Stack → Bool) (s : Stack) : Bool :=
  matchStackFast s false (fun b1 r1 =>
    matchStackFast r1 false (fun b2 r2 =>
      matchStackFast r2
        (band_fast (Nat.beq b1.pat 1) (band_fast (Nat.beq b1.width 1) (Nat.beq b1.len 1)))
        (fun b3 rest =>
          @Bool.rec (fun _ => Bool) false
            (@Bool.rec (fun _ => Bool) true
              (@Bool.rec (fun _ => Bool) true
                (withNatFast (Nat.sub b3.len 3) (fun rem =>
                  can_pair_fn (@Bool.rec (fun _ => Stack) (consBlock1 1 1 rem rest) rest (Nat.beq rem 0))))
                (band_fast (Nat.beq b3.pat 1) (band_fast (Nat.beq b3.width 1) (Nat.ble 3 b3.len))))
              (band_fast (Nat.beq b2.pat 0) (band_fast (Nat.beq b2.width 1) (Nat.beq b2.len 1))))
            (band_fast (Nat.beq b1.pat 1) (band_fast (Nat.beq b1.width 1) (Nat.beq b1.len 1))))))

noncomputable def pre_absorb_l_f (can_absorb_fn : Stack → Bool) (s : Stack) : Bool :=
  matchStackFast s false (fun b1 r1 =>
    matchStackFast r1 false (fun b2 r2 =>
      matchStackFast r2
        (band_fast (Nat.beq b1.pat 1) (band_fast (Nat.beq b1.width 1) (Nat.beq b1.len 1)))
        (fun b3 rest =>
          @Bool.rec (fun _ => Bool) false
            (@Bool.rec (fun _ => Bool) true
              (@Bool.rec (fun _ => Bool) true
                (withNatFast (Nat.sub b3.len 3) (fun rem =>
                  can_absorb_fn (@Bool.rec (fun _ => Stack) (consBlock1 1 1 rem rest) rest (Nat.beq rem 0))))
                (band_fast (Nat.beq b3.pat 1) (band_fast (Nat.beq b3.width 1) (Nat.ble 3 b3.len))))
              (band_fast (Nat.beq b2.pat 0) (band_fast (Nat.beq b2.width 1) (Nat.beq b2.len 1))))
            (band_fast (Nat.beq b1.pat 1) (band_fast (Nat.beq b1.width 1) (Nat.beq b1.len 1))))))

noncomputable def can_parse_r_f (s : Stack) : Bool :=
  matchStackFast s true (fun top _ =>
    bnot_fast (band_fast (Nat.beq top.width 3) (band_fast (Nat.beq top.pat 1) (Nat.beq (Nat.mod top.len 3) 1))))

noncomputable def do_shift_right_f_p (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack) : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState :=
fun k128 =>
fun sq sw sin sout sout_w s =>
  @Bool.rec (fun _ => Option MState) none
    (let target2 := Nat.add sin (Nat.mul sin (Nat.shiftLeft 1 sw))
     withOptionFast (pop_word_f target2 (Nat.mul 2 sw) s.r)
       none
       (fun _ =>
         withProdFast (count_stack_mut_f sin sw k128 100000000 s.r) (fun r1 r2 =>
           someMStateFast sq (push_stack_f sout sout_w (Nat.mul r1 sw) s.l) r2)))
    (Nat.beq s.q.val sq.val)

noncomputable def do_shift_left_f_p (bit_of_bool_f : Nat → Bool) (push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) (pop_word_f : Nat → Nat → Stack → Option Stack) (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack) : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState :=
fun k128 =>
fun sq sw sin sout sout_w s =>
  @Bool.rec (fun _ => Option MState) none
    (let target2 := Nat.add sin (Nat.mul sin (Nat.shiftLeft 1 sw))
     withProdFast (pop1_b_f s.r) (fun pr1 pr2 =>
       @Bool.rec (fun _ => Option MState) none
         (@Bool.rec (fun _ => Option MState) none
           (let l1 := push_stack_f (@Bool.rec (fun _ => Nat) 0 1 pr1) 1 1 s.l
            withProdFast (count_stack_mut_f sin sw k128 100000000 l1) (fun r1 r2 =>
              withProdFast (pop1_b_f r2) (fun pl1 pl2 =>
                someMStateFast sq pl2 (push_stack_f (@Bool.rec (fun _ => Nat) 0 1 pl1) 1 1 (push_stack_f sout sout_w (Nat.mul r1 sw) pr2)))))
           (withOptionFast (pop_word_f (Nat.shiftRight target2 1) (Nat.sub (Nat.mul 2 sw) 1) s.l) false (fun _ => true)))
         (bnot_fast (bxor_fast pr1 (bit_of_bool_f target2)))))
    (Nat.beq s.q.val sq.val)

noncomputable def try_pair_stack_f_p
    (pre_pair_l_fn : Stack → Bool)
    (can_parse_r_fn : Stack → Bool)
    (can_pair_fn : Stack → Bool)
    (pop_word_f : Nat → Nat → Stack → Option Stack)
    (bsize_parts_f : PartList → Nat)
    (put_l_stack_f : PartList → Nat → Stack → Stack)
    (put_r_rec_f : PartList → Nat → Stack → Stack)
    (parse_l_f : Nat → Nat → Stack → PartList × Stack)
    (parse_r_f : Nat → Nat → Stack → PartList × Stack)
    (sub_lsb_checked_f : Nat → Nat → Nat → PartList → PartList → Option PartList)
    (choose_limit_r_f : Nat → Nat → Nat → Stack → Nat)
    (push_prefix_l_f : Stack → Stack) : Nat → MState → Option MState :=
fun k128 =>
fun s =>
  @Bool.rec (fun _ => Option MState) none
    (@Bool.rec (fun _ => Option MState) none
      (withOptionFast (pop_word_f 29 5 s.l)
        none
        (fun lc =>
          @Bool.rec (fun _ => Option MState) none
            (withNatFast k128 (fun k128 =>
              withProdFast (parse_l_f k128 100000000 lc) (fun rl1 rl2 =>
                @Bool.rec (fun _ => Option MState)
                  (withNatFast (bsize_parts_f rl1) (fun n =>
                    withNatFast (choose_limit_r_f n k128 0 s.r) (fun lim_r =>
                      @Bool.rec (fun _ => Option MState)
                        (withProdFast (parse_r_f k128 lim_r s.r) (fun rr1 rr2 =>
                          @Bool.rec (fun _ => Option MState)
                            (withNatFast (bsize_parts_f rr1) (fun k =>
                              withOptionFast (sub_lsb_checked_f k128 n k rl1 rr1)
                                (withOptionFast (sub_lsb_checked_f k128 k n rr1 rl1)
                                  none
                                  (fun out => someMStateFast fin6_0 (push_prefix_l_f (put_l_stack_f [] n rl2)) (put_r_rec_f out k rr2)))
                                (fun out => someMStateFast fin6_0 (push_prefix_l_f (put_l_stack_f out n rl2)) (put_r_rec_f [] k rr2))))
                            none
                            (isEmptyPartListFast rr1)))
                        none
                        (Nat.beq lim_r 0))))
                  none
                  (isEmptyPartListFast rl1))))
            (can_pair_fn lc)))
      (band_fast (pre_pair_l_fn s.l) (can_parse_r_fn s.r)))
    (Nat.beq s.q.val 0)

noncomputable def try_absorb_stack_f_p
    (pre_absorb_l_fn : Stack → Bool)
    (can_parse_r_fn : Stack → Bool)
    (can_absorb_fn : Stack → Bool)
    (push_stack_f : Nat → Nat → Nat → Stack → Stack)
    (pop_word_f : Nat → Nat → Stack → Option Stack)
    (count_stack_mut_f : Nat → Nat → Nat → Nat → Stack → Nat × Stack)
    (bsize_parts_f : PartList → Nat)
    (put_r_rec_f : PartList → Nat → Stack → Stack)
    (parse_r_f : Nat → Nat → Stack → PartList × Stack)
    (sub_lsb_f : Nat → Bool → PartList → PartList → Option PartList)
    (choose_limit_r_f : Nat → Nat → Nat → Stack → Nat)
    (push_prefix_l_f : Stack → Stack)
    (build_vprime_f : Nat → Nat → PartList) : Nat → MState → Option MState :=
fun k128 =>
fun s =>
  @Bool.rec (fun _ => Option MState) none
    (@Bool.rec (fun _ => Option MState) none
      (withOptionFast (pop_word_f 29 5 s.l)
        none
        (fun lc0 =>
          @Bool.rec (fun _ => Option MState) none
            (withNatFast k128 (fun k128 =>
              withProdFast (count_stack_mut_f 15 4 k128 100000000 lc0) (fun r1_1 r1_2 =>
                withProdFast (count_stack_mut_f 13 4 k128 100000000 r1_2) (fun rm_1 _ =>
                  @Bool.rec (fun _ => Option MState)
                    (withNatFast (choose_limit_r_f (Nat.add r1_1 rm_1) k128 0 s.r) (fun lim_r =>
                      @Bool.rec (fun _ => Option MState)
                        (withProdFast (parse_r_f k128 lim_r s.r) (fun rr_1 rr_2 =>
                          @Bool.rec (fun _ => Option MState)
                            (withNatFast (bsize_parts_f rr_1) (fun k =>
                              withNatFast (nat_min_fast rm_1 (@Bool.rec (fun _ => Nat) 1 (Nat.sub k r1_1) (Nat.ble (Nat.add r1_1 1) k))) (fun m_init =>
                                @Bool.rec (fun _ => Option MState)
                                  (let res_sub : Option (Nat × PartList) :=
                                    withOptionFast (sub_lsb_f k128 false rr_1 (build_vprime_f r1_1 m_init))
                                      (@Bool.rec (fun _ => Option (Nat × PartList))
                                        (withNatFast (Nat.sub m_init 1) (fun m_m1 =>
                                          withOptionFast (sub_lsb_f k128 false rr_1 (build_vprime_f r1_1 m_m1))
                                            none
                                            (fun out => some (m_m1, out))))
                                        none
                                        (Nat.ble m_init 1))
                                      (fun out => some (m_init, out))
                                   withOptionFast res_sub
                                     none
                                     (fun pair_out =>
                                       withProdFast pair_out (fun m_use out =>
                                         withProdFast (count_stack_mut_f 13 4 k128 m_use r1_2) (fun r2_1 r2_2 =>
                                           @Bool.rec (fun _ => Option MState) none
                                             (someMStateFast fin6_0 (push_prefix_l_f (push_stack_f 14 4 (Nat.mul (Nat.add r1_1 r2_1) 4) r2_2)) (put_r_rec_f out k rr_2))
                                             (Nat.beq r2_1 m_use)))))
                                  none
                                  (Nat.beq m_init 0))))
                            none
                            (isEmptyPartListFast rr_1)))
                        none
                        (Nat.beq lim_r 0)))
                    none
                    (Nat.beq rm_1 0)))))
            (can_absorb_fn lc0)))
      (band_fast (pre_absorb_l_fn s.l) (can_parse_r_fn s.r)))
    (Nat.beq s.q.val 0)

noncomputable def step_prim_f_p(push_stack_f : Nat → Nat → Nat → Stack → Stack) (pop1_b_f : Stack → Bool × Stack) : MState → Option MState :=
fun s =>
  withProdFast (pop1_b_f s.r) (fun pr1 pr2 =>
    let step_r := fun (nq : Fin 6) (br : Nat) =>
      someMStateFast nq (push_stack_f br 1 1 s.l) pr2
    let step_l := fun (nq : Fin 6) (br : Nat) =>
      withProdFast (pop1_b_f s.l) (fun pl1 pl2 =>
        someMStateFast nq pl2 (push_stack_f (@Bool.rec (fun _ => Nat) 0 1 pl1) 1 1 (push_stack_f br 1 1 pr2)))
    let qv := s.q.val
    @Bool.rec (fun _ => Option MState)
      (@Bool.rec (fun _ => Option MState)
        (@Bool.rec (fun _ => Option MState)
          (@Bool.rec (fun _ => Option MState)
            (@Bool.rec (fun _ => Option MState)
              (@Bool.rec (fun _ => Option MState)
                none
                (@Bool.rec (fun _ => Option MState) (step_l fin6_1 0) none pr1)
                (Nat.beq qv 5))
              (@Bool.rec (fun _ => Option MState) (step_r fin6_3 1) (step_r fin6_5 0) pr1)
              (Nat.beq qv 4))
            (@Bool.rec (fun _ => Option MState) (step_r fin6_0 1) (step_r fin6_3 0) pr1)
            (Nat.beq qv 3))
          (@Bool.rec (fun _ => Option MState) (step_r fin6_3 1) (step_l fin6_4 0) pr1)
          (Nat.beq qv 2))
        (@Bool.rec (fun _ => Option MState) (step_l fin6_2 1) (step_l fin6_1 0) pr1)
        (Nat.beq qv 1))
      (@Bool.rec (fun _ => Option MState) (step_l fin6_1 1) (step_r fin6_4 1) pr1)
      (Nat.beq qv 0))

noncomputable def has_head_bit1_f (s : Stack) : Bool :=
  matchStackFast s false (fun top _ => Nat.beq (Nat.land top.pat 1) 1)

noncomputable def can_any_macro_f
    (pre_pair_l_fn : Stack → Bool)
    (pre_absorb_l_fn : Stack → Bool)
    (can_parse_r_fn : Stack → Bool)
    (s : MState) : Bool :=
  let qv := s.q.val
  @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          false
          (matchStackFast s.r false (fun top rest =>
            @Bool.rec (fun _ => Bool)
              (@Bool.rec (fun _ => Bool)
                true
                (matchStackFast rest false (fun b2 _ =>
                  bnot_fast (band_fast (Nat.beq b2.width 1) (band_fast (Nat.beq b2.pat 0) (Nat.ble 2 b2.len)))))
                (band_fast (Nat.beq top.width 1) (band_fast (Nat.beq top.pat 1) (Nat.beq top.len 1))))
              (@Bool.rec (fun _ => Bool) (has_head_bit1_f rest) false (Nat.ble 2 top.len))
              (band_fast (Nat.beq top.width 1) (Nat.beq top.pat 0))))
          (Nat.beq qv 3))
        (band_fast (has_head_bit1_f s.l) (has_head_bit1_f s.r))
        (Nat.beq qv 2))
      (band_fast (has_head_bit1_f s.l) (has_head_bit1_f s.r))
      (Nat.beq qv 1))
    (bor_fast
      (matchStackFast s.r false (fun top _ =>
        band_fast (Nat.beq (Nat.land top.pat 1) 1) (bnot_fast (band_fast (Nat.beq top.width 1) (Nat.ble 2 top.len)))))
      (band_fast (bor_fast (pre_pair_l_fn s.l) (pre_absorb_l_fn s.l)) (can_parse_r_fn s.r)))
    (Nat.beq qv 0)

noncomputable def run_prim_f_p
    (pop1_b_f : Stack → Bool × Stack)
    (can_any_macro_fn : MState → Bool)
    (step_prim_f : MState → Option MState) : Nat → MState → Option MState :=
@Nat.rec (fun _ => MState → Option MState)
  (fun s => some s)
  (fun _ ih s =>
    @Bool.rec (fun _ => Option MState)
      (withOptionFast (step_prim_f s) (some s) ih)
      (some s)
      (bor_fast (band_fast (Nat.beq s.q.val 5) (pop1_b_f s.r).1) (can_any_macro_fn s)))

noncomputable def step_prim_plus_f_p
    (step_prim_f : MState → Option MState)
    (run_prim_f : Nat → MState → Option MState) : MState → Option MState :=
fun s =>
  withOptionFast (step_prim_f s) none (run_prim_f 24)

noncomputable def step_m_f_p
    (do_shift_right_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState)
    (do_shift_left_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState)
    (try_pair_stack_f : Nat → MState → Option MState)
    (try_absorb_stack_f : Nat → MState → Option MState)
    (step_prim_plus_f : MState → Option MState) : Nat → MState → Option MState :=
fun _ =>
fun s =>
  let qv := s.q.val
  let macro_res : Option MState :=
    @Bool.rec (fun _ => Option MState)
      (@Bool.rec (fun _ => Option MState)
        (@Bool.rec (fun _ => Option MState)
          (@Bool.rec (fun _ => Option MState)
            none
            (withOptionFast ((do_shift_right_f 8) fin6_3 1 1 0 1 s)
              (withOptionFast ((do_shift_right_f 8) fin6_3 3 2 1 1 s)
                (withOptionFast ((do_shift_right_f 8) fin6_3 4 10 14 4 s)
                  ((do_shift_right_f 8) fin6_3 4 5 7 4 s)
                  some)
                some)
              some)
            (Nat.beq qv 3))
          ((do_shift_left_f 8) fin6_2 2 3 1 2 s)
          (Nat.beq qv 2))
        ((do_shift_left_f 8) fin6_1 1 1 0 1 s)
        (Nat.beq qv 1))
      (let kbig := Nat.add (Nat.add (stack_len_fast s.l) (stack_len_fast s.r)) 4
       withOptionFast ((try_pair_stack_f kbig) s)
         (withOptionFast ((try_absorb_stack_f kbig) s)
           ((do_shift_right_f 8) fin6_0 3 1 1 1 s)
           some)
         some)
      (Nat.beq qv 0)
  withOptionFast macro_res (step_prim_plus_f s) some


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

@[simp] lemma bnot_fast_eq (x : Bool) : bnot_fast x = !x := by cases x <;> rfl
@[simp] lemma band_fast_eq (x y : Bool) : band_fast x y = (x && y) := by cases x <;> rfl
@[simp] lemma bor_fast_eq (x y : Bool) : bor_fast x y = (x || y) := by cases x <;> rfl
@[simp] lemma bxor_fast_eq (x y : Bool) : bxor_fast x y = (x ^^ y) := by cases x <;> cases y <;> rfl

@[simp] lemma nat_min_fast_eq (x y : Nat) : nat_min_fast x y = min x y := by
  unfold nat_min_fast
  simp only [bool_rec_eq, nat_ble_def]
  by_cases h : x ≤ y
  · simp [h, Nat.min_eq_left h]
  · have h2 : y ≤ x := by omega
    simp [h, Nat.min_eq_right h2]

@[simp] lemma nat_max_fast_eq (x y : Nat) : nat_max_fast x y = max x y := by
  unfold nat_max_fast
  simp only [bool_rec_eq, nat_ble_def]
  by_cases h : x ≤ y
  · simp [h, Nat.max_eq_right h]
  · have h2 : y ≤ x := by omega
    simp [h, Nat.max_eq_left h2]

@[simp] lemma withOptionFast_eq {α β : Type} (o : Option α) (onNone : β) (onSome : α → β) :
    withOptionFast o onNone onSome = match o with | none => onNone | some a => onSome a := by
  cases o <;> rfl

@[simp] lemma matchStackFast_eq {α : Type} (s : Stack) (onNil : α) (onCons : Block → Stack → α) :
    matchStackFast s onNil onCons = match s with | [] => onNil | hd :: tl => onCons hd tl := by
  cases s <;> rfl

@[simp] lemma matchPartListFast_eq {α : Type} (xs : PartList) (onNil : α) (onCons : Bool → Nat → PartList → α) :
    matchPartListFast xs onNil onCons = match xs with | [] => onNil | (b, k) :: tl => onCons b k tl := by
  cases xs with
  | nil => rfl
  | cons hd tl => cases hd; rfl

@[simp] lemma isEmptyPartListFast_eq (xs : PartList) :
    isEmptyPartListFast xs = xs.isEmpty := by
  cases xs <;> rfl

@[simp] lemma fin6_0_eq : fin6_0 = 0 := rfl
@[simp] lemma fin6_1_eq : fin6_1 = 1 := rfl
@[simp] lemma fin6_2_eq : fin6_2 = 2 := rfl
@[simp] lemma fin6_3_eq : fin6_3 = 3 := rfl
@[simp] lemma fin6_4_eq : fin6_4 = 4 := rfl
@[simp] lemma fin6_5_eq : fin6_5 = 5 := rfl

lemma consBlock1_eq (p w l : Nat) (rest : Stack) :
    consBlock1 p w l rest = ⟨p, w, l⟩ :: rest := by
  unfold consBlock1
  have hp : Nat.add 1 p = Nat.succ p := Nat.add_comm 1 p
  have hw : Nat.add 1 w = Nat.succ w := Nat.add_comm 1 w
  have hl : Nat.add 1 l = Nat.succ l := Nat.add_comm 1 l
  rw [hp, hw, hl]

@[simp] lemma withProdFast_eq {α β γ : Type} (p : α × β) (f : α → β → γ) :
    withProdFast p f = f p.1 p.2 := by
  cases p; rfl

@[simp] lemma withProd3Fast_eq {α β γ δ : Type} (p : α × β × γ) (f : α → β → γ → δ) :
    withProd3Fast p f = f p.1 p.2.1 p.2.2 := by
  rcases p with ⟨a, b, c⟩; rfl

@[simp] lemma withNatFast_eq {α : Type} (x : Nat) (f : Nat → α) :
    withNatFast x f = f x := by
  unfold withNatFast
  have hx : Nat.add 1 x = Nat.succ x := Nat.add_comm 1 x
  rw [hx]

@[simp] lemma withBoolFast_eq {α : Type} (b : Bool) (f : Bool → α) :
    withBoolFast b f = f b := by
  cases b <;> rfl

@[simp] lemma withStackFast_eq {α : Type} (s : Stack) (f : Stack → α) :
    withStackFast s f = f s := by
  cases s <;> rfl

@[simp] lemma withPartFast_eq {α : Type} (p : Bool × Nat) (f : Bool → Nat → α) :
    withPartFast p f = f p.1 p.2 := by
  rcases p with ⟨b, n⟩
  simp [withPartFast]

@[simp] lemma withPartListFast_eq {α : Type} (xs : PartList) (f : PartList → α) :
    withPartListFast xs f = f xs := by
  cases xs with
  | nil => rfl
  | cons hd tl =>
    rcases hd with ⟨b, n⟩
    simp [withPartListFast]

@[simp] lemma someMStateFast_eq (q : Fin 6) (l r : Stack) :
    someMStateFast q l r = some ⟨q, l, r⟩ := by
  simp [someMStateFast]

@[simp] lemma stack_len_fast_eq (s : Stack) :
    stack_len_fast s = s.length := by
  induction s with
  | nil => rfl
  | cons hd tl ih =>
    change Nat.add (stack_len_fast tl) 1 = (hd :: tl).length
    simp [ih]

lemma mkBlock_p_eq : mkBlock_f_p = Block.mk := by
  funext p w l; unfold mkBlock_f_p; simp only [nat_add_1_succ]

lemma rot1_p_eq : rot1_f_p = rot1 := by
  funext w p; unfold rot1_f_p rot1
  simp only [bool_rec_eq, nat_ble_def, nat_shiftRight_def, nat_land_def, nat_shiftLeft_def,
    nat_sub_def, nat_mul_def, nat_add_def,
    Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.one_mul]
  by_cases hw : w ≤ 1 <;> simp [hw]

lemma rot_k_zero (w n : Nat) : rot_k w n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : rot1 w 0 = 0 := by simp [rot1]
    simp [rot_k, h1, ih]

lemma rot_k_one_one (n : Nat) : rot_k 1 n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : rot1 1 1 = 1 := by simp [rot1]
    simp [rot_k, h1, ih]

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
  simp only [bool_rec_eq, band_fast_eq, bor_fast_eq, withNatFast_eq, nat_beq_def, nat_ble_def]
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

lemma push_stack_aux_fast_eq (s : Stack) (p w l : Nat) :
    push_stack_aux_fast s p w l = push_stack_aux ⟨p, w, l⟩ s := by
  induction s generalizing p w l with
  | nil =>
    change @Bool.rec (fun _ => Stack) (⟨p, w, l⟩ :: []) [] (Nat.beq p 0) =
           push_stack_aux ⟨p, w, l⟩ []
    unfold push_stack_aux
    simp only [bool_rec_eq, nat_beq_def]
    by_cases hp : p = 0 <;> simp [hp]
  | cons top rest ih =>
    change @Bool.rec (fun _ => Stack)
        (⟨p, w, l⟩ :: top :: rest)
        (withNatFast (Nat.add l top.len) (fun nl => push_stack_aux_fast rest p w nl))
        (band_fast (Nat.beq w top.width) (Nat.beq (rot_mod_f_p w l p) top.pat)) =
      push_stack_aux ⟨p, w, l⟩ (top :: rest)
    unfold push_stack_aux
    simp only [ih, bool_rec_eq, band_fast_eq, nat_beq_def, nat_add_def, withNatFast_eq, with_nat_eq, rot_mod_p_eq]

lemma push_stack_fast_eq : push_stack_fast = push_stack := by
  funext p w l s
  unfold push_stack_fast push_stack
  simp only [withNatFast_eq, bool_rec_eq, nat_beq_def, push_stack_aux_fast_eq, with_stack_eq, with_nat_eq]
  by_cases hl : l = 0 <;> simp [hl]

lemma drop_stack_aux_fast_eq (s : Stack) (n : Nat) (hn : n ≠ 0) :
    drop_stack_aux_fast s n = drop_stack n s := by
  induction s generalizing n with
  | nil => rfl
  | cons top rest ih =>
    change @Bool.rec (fun _ => Stack)
        (consBlock1 (rot_mod_f_p top.width n top.pat) top.width (Nat.sub top.len n) rest)
        (withNatFast (Nat.sub n top.len) (fun rem =>
          @Bool.rec (fun _ => Stack) (drop_stack_aux_fast rest rem) rest (Nat.beq rem 0)))
        (Nat.ble top.len n) = drop_stack n (top :: rest)
    unfold drop_stack
    simp only [bool_rec_eq, nat_ble_def, nat_beq_def, nat_sub_def, withNatFast_eq, with_nat_eq,
      consBlock1_eq, rot_mod_p_eq, hn, ↓reduceIte]
    by_cases hle : top.len ≤ n
    · simp only [hle, decide_true, if_true_eq_true, ↓reduceIte]
      by_cases hrem : n - top.len = 0
      · simp [hrem, drop_stack_zero]
      · have hne : (n - top.len == 0) = false := beq_eq_false_iff_ne.mpr hrem
        rw [hne, if_false_eq_true]
        exact ih (n - top.len) hrem
    · simp only [hle, decide_false, if_false_eq_true, ↓reduceIte]

lemma drop_stack_fast_eq : drop_stack_fast = drop_stack := by
  funext n s
  unfold drop_stack_fast
  simp only [withNatFast_eq, bool_rec_eq, nat_beq_def]
  by_cases hn : n = 0
  · simp [hn, drop_stack_zero]
  · have hne : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
    rw [hne, if_false_eq_true]
    exact drop_stack_aux_fast_eq s n hn

lemma pop1_b_fast_eq : pop1_b_fast = fun s => ((pop1 s).1 == 1, (pop1 s).2) := by
  funext s
  induction s with
  | nil => rfl
  | cons top rest ih =>
    change @Bool.rec (fun _ => Bool × Stack)
        (bit_of_bool_f_p top.pat,
         @Bool.rec (fun _ => Stack)
           (consBlock1 (rot1_f_p top.width top.pat) top.width (Nat.sub top.len 1) rest)
           rest
           (Nat.beq top.len 1))
        (pop1_b_fast rest)
        (Nat.beq top.len 0) = ((pop1 (top :: rest)).1 == 1, (pop1 (top :: rest)).2)
    unfold pop1
    simp only [ih, bool_rec_eq, nat_beq_def, nat_sub_def, consBlock1_eq, rot1_p_eq, bit_of_bool_p_eq, with_nat_eq]
    by_cases h0 : top.len = 0
    · simp [h0]
    · have hne0 : (top.len == 0) = false := beq_eq_false_iff_ne.mpr h0
      rw [hne0]; simp only [if_false_eq_true, h0, ↓reduceIte]
      by_cases h1 : top.len = 1
      · simp [h1]
      · have hne1 : (top.len == 1) = false := beq_eq_false_iff_ne.mpr h1
        rw [hne1]; simp [h1]

lemma sym_xnor_eq : ∀ (a b : Fin 2), ((!(a == 1 ^^ b == 1)) = true) = (a = b) := by decide

lemma pop_word_p_eq
    {bit_of_bool_f} (h1 : bit_of_bool_f = fun x => bit_of x == 1)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2)) :
    pop_word_f_p bit_of_bool_f pop1_b_f = pop_word := by
  subst h1; subst h2; funext pat w s
  unfold pop_word_f_p
  induction w generalizing pat s with
  | zero => simp [pop_word]
  | succ w ih =>
    unfold pop_word
    simp only [ih]
    simp only [bool_rec_eq, bnot_fast_eq, bxor_fast_eq, with_prod_eq, withProdFast_eq,
      withNatFast_eq, sym_xnor_eq, nat_shiftRight_def]
    have hsh : ∀ x : Nat, x >>> 1 = x / 2 := fun _ => rfl
    simp only [hsh]

lemma fast_match_core_fin :
    ∀ (w : Fin 5) (tw : Fin 5) (tp : Fin 16) (pat : Fin 16),
      1 ≤ w.val → 1 ≤ tw.val → tp.val ≤ (Nat.shiftLeft 1 tw.val) - 1 → pat.val ≤ (Nat.shiftLeft 1 w.val) - 1 →
      (let mul := @Bool.rec (fun _ => Nat)
        (@Bool.rec (fun _ => Nat)
          (@Bool.rec (fun _ => Nat) 273 585 (Nat.beq tw.val 3))
          1365 (Nat.beq tw.val 2))
        4095 (Nat.beq tw.val 1)
       withNatFast (Nat.mul tp.val mul) (fun pm =>
         band_fast (Nat.beq (Nat.land (Nat.shiftRight pm w.val) (Nat.sub (Nat.shiftLeft 1 tw.val) 1)) tp.val)
           (Nat.beq (Nat.land pm (Nat.sub (Nat.shiftLeft 1 w.val) 1)) pat.val))) =
      (rot_k tw.val w.val tp.val == tp.val && pat_word tw.val tp.val w.val == word_of pat.val w.val) := by
  decide +kernel

lemma fast_match_p_eq :
    fast_match_f_p = fun pat w top =>
      (0 < w && w ≤ top.len && rot_k top.width w top.pat == top.pat &&
       pat_word top.width top.pat w == word_of pat w) := by
  funext pat w top
  unfold fast_match_f_p
  have hguard :
      band_fast (Nat.ble 1 w)
        (band_fast (Nat.ble w 4)
          (band_fast (Nat.ble 1 top.width)
            (band_fast (Nat.ble top.width 4)
              (band_fast (Nat.ble top.pat (Nat.sub (Nat.shiftLeft 1 top.width) 1))
                (Nat.ble pat (Nat.sub (Nat.shiftLeft 1 w) 1)))))) =
      (decide (1 ≤ w) && (decide (w ≤ 4) && (decide (1 ≤ top.width) && (decide (top.width ≤ 4) &&
        (decide (top.pat ≤ (Nat.shiftLeft 1 top.width) - 1) && decide (pat ≤ (Nat.shiftLeft 1 w) - 1)))))) := by
    simp only [band_fast_eq, nat_ble_def, nat_sub_def]
  rw [hguard, bool_rec_eq]
  split_ifs with hg
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    rcases hg with ⟨hw1, hw4, htw1, htw4, htp, hpat⟩
    have h15 : ∀ (k : Fin 5), (Nat.shiftLeft 1 k.val) - 1 ≤ 15 := by decide
    have htp16 : (Nat.shiftLeft 1 top.width) - 1 ≤ 15 := h15 ⟨top.width, by omega⟩
    have hpat16 : (Nat.shiftLeft 1 w) - 1 ≤ 15 := h15 ⟨w, by omega⟩
    have hcore := fast_match_core_fin ⟨w, by omega⟩ ⟨top.width, by omega⟩ ⟨top.pat, by omega⟩ ⟨pat, by omega⟩
      hw1 htw1 htp hpat
    dsimp only at hcore
    rw [band_fast_eq, hcore, nat_ble_def]
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
      nat_min_fast_eq, matchStackFast_eq, withOptionFast_eq, withStackFast_eq,
      with_nat_eq, with_stack_eq, with_prod_eq, withProdFast_eq, withNatFast_eq]
    by_cases hlim : limit = 0
    · simp [hlim]
    · have hne : (limit == 0) = false := beq_eq_false_iff_ne.mpr hlim
      rw [hne]; simp only [if_false_eq_true, hlim, ↓reduceIte]
      cases s with
      | nil => rfl
      | cons top rest =>
        dsimp only
        split_ifs with hfm
        · rfl
        · cases pop_word pat w (top :: rest) <;> rfl

lemma mkPart_p_eq : mkPart_f_p = cons_lsb := by
  funext b k xs
  unfold mkPart_f_p cons_lsb
  simp only [withNatFast_eq, withBoolFast_eq, matchPartListFast_eq, bool_rec_eq,
    nat_beq_def, nat_add_def, bnot_fast_eq, bxor_fast_eq,
    with_bool_eq, with_nat_eq, with_list_eq]
  cases k with
  | zero => rfl
  | succ k' =>
    have hne : (Nat.succ k' == 0) = false := rfl
    rw [hne, if_false_eq_true]
    cases xs with
    | nil => cases b <;> rfl
    | cons hd rest =>
      rcases hd with ⟨b2, k2⟩
      cases b <;> cases b2 <;> rfl

lemma bsize_parts_p_eq : bsize_parts_f_p = bsize_parts := by
  funext xs; unfold bsize_parts_f_p
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨b, k⟩
    simp only [ih]
    rfl

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
  simp only [withNatFast_eq, withStackFast_eq, bool_rec_eq, nat_ble_def, nat_add_def, nat_sub_def, nat_mul_def]
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
    simp only [bool_rec_eq, withNatFast_eq, nat_beq_def, nat_ble_def, nat_sub_def, nat_mul_def]
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
    simp only [matchStackFast_eq, withOptionFast_eq, withNatFast_eq, withStackFast_eq,
      band_fast_eq, nat_min_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, nat_div_def, nat_mul_def, Bool.and_assoc]
    split_ifs with c1 c2
    · rfl
    · rfl
    · cases pop_word 15 4 (top :: rest) with
      | some s1 => rfl
      | none => cases pop_word 14 4 (top :: rest) <;> rfl

lemma parse_l_p_eq
    {parse_step_l_f} (h1 : parse_step_l_f = parse_step_l) :
    parse_l_f_p parse_step_l_f = parse_l := by
  subst h1; funext fuel limit s; unfold parse_l_f_p
  induction fuel generalizing limit s with
  | zero => rfl
  | succ fuel ih =>
    unfold parse_l
    simp only [ih]
    simp only [bool_rec_eq, nat_beq_def, nat_sub_def, withOptionFast_eq, withProd3Fast_eq,
      withNatFast_eq, withProdFast_eq, band_fast_eq, bnot_fast_eq, isEmptyPartListFast_eq,
      with_prod_eq, with_list_eq, with_stack_eq]
    by_cases hlim : limit = 0
    · simp [hlim]
    · have hne : (limit == 0) = false := beq_eq_false_iff_ne.mpr hlim
      rw [hne]; simp only [if_false_eq_true, hlim, ↓reduceIte]
      cases parse_step_l limit s with
      | none => rfl
      | some val =>
        rcases val with ⟨b, k, s1⟩; dsimp only

lemma parse_step_r_p_eq
    {drop_stack_f} (h1 : drop_stack_f = drop_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word) :
    parse_step_r_f_p drop_stack_f pop_word_f = parse_step_r := by
  subst h1; subst h2; funext limit s
  unfold parse_step_r_f_p parse_step_r
  cases s with
  | nil => rfl
  | cons top rest =>
    simp only [matchStackFast_eq, withOptionFast_eq, withNatFast_eq, withStackFast_eq,
      band_fast_eq, nat_min_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, nat_div_def, nat_mul_def, Bool.and_assoc]
    split_ifs with c1 c2
    · rfl
    · rfl
    · cases pop_word 1 3 (top :: rest) with
      | some s1 => rfl
      | none => cases pop_word 0 3 (top :: rest) <;> rfl

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
    simp only [bool_rec_eq, nat_beq_def, nat_sub_def, matchStackFast_eq, withOptionFast_eq,
      withProd3Fast_eq, withNatFast_eq, withProdFast_eq, withStackFast_eq,
      bnot_fast_eq, isEmptyPartListFast_eq, with_prod_eq, with_list_eq, with_stack_eq]
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
      simp only [matchPartListFast_eq, bool_rec_eq, band_fast_eq, isEmptyPartListFast_eq, bnot_fast_eq]
    | cons xhd xrest =>
      rcases xhd with ⟨px, kx⟩
      cases ys with
      | nil =>
        cases c with
        | false => rfl
        | true =>
          simp only [matchPartListFast_eq, bool_rec_eq, withBoolFast_eq, withOptionFast_eq,
            bnot_fast_eq, bxor_fast_eq, band_fast_eq,
            nat_beq_def, nat_ble_def, nat_add_def, nat_sub_def,
            with_nat_eq, with_list_eq, head_q, head_l, next_x, next_y,
            List.isEmpty, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          have hmink : min kx kx = kx := Nat.min_self kx
          simp only [hmink, Nat.sub_self]
          by_cases hlt : kx < kx
          · exact False.elim (Nat.lt_irrefl kx hlt)
          · simp only [hlt, ↓reduceIte]
            by_cases hk0 : kx = 0
            · simp [hk0]
            · have hne0 : (kx == 0) = false := beq_eq_false_iff_ne.mpr hk0
              rw [hne0]; simp only [if_false_eq_true, hk0, ↓reduceIte]
              by_cases h1 : 1 < kx
              · have hd2 : decide (2 ≤ kx) = true := decide_eq_true (by omega)
                rw [hd2, if_true_eq_true]
                have hc2 : (!px && (!px && true)) = sub_chunk_c px false true kx := by
                  unfold sub_chunk_c subbit; rw [if_pos h1]; cases px <;> rfl
                rw [hc2]
                cases sub_lsb fuel (sub_chunk_c px false true kx) xrest [] with
                | none => rfl
                | some out =>
                  dsimp only; unfold sub_chunk_out subbit; rw [if_pos h1]
                  cases px <;> rfl
              · have hd2 : decide (2 ≤ kx) = false := decide_eq_false (by omega)
                rw [hd2, if_false_eq_true]
                have hc1 : (!px && true) = sub_chunk_c px false true kx := by
                  unfold sub_chunk_c subbit; rw [if_neg h1]; cases px <;> rfl
                rw [hc1]
                cases sub_lsb fuel (sub_chunk_c px false true kx) xrest [] with
                | none => rfl
                | some out =>
                  dsimp only; unfold sub_chunk_out subbit; rw [if_neg h1]
                  cases px <;> rfl
      | cons yhd yrest =>
        rcases yhd with ⟨qy, ly⟩
        simp only [matchPartListFast_eq, withNatFast_eq, withPartListFast_eq, withBoolFast_eq,
          withOptionFast_eq, nat_min_fast_eq, bool_rec_eq,
          bnot_fast_eq, bxor_fast_eq, band_fast_eq, bor_fast_eq,
          nat_beq_def, nat_ble_def, nat_add_def, nat_sub_def,
          with_nat_eq, with_list_eq, head_q, head_l,
          List.isEmpty, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
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
          by_cases h1 : 1 < min kx ly
          · have hd2 : decide (2 ≤ min kx ly) = true := decide_eq_true (by omega)
            rw [hd2, if_true_eq_true]
            have hc2 : ((!px && (qy || ((!px && (qy || c)) || (qy && c)))) ||
                        (qy && ((!px && (qy || c)) || (qy && c)))) =
                       sub_chunk_c px qy c (min kx ly) := by
              unfold sub_chunk_c subbit; rw [if_pos h1]
            rw [hc2]
            cases sub_lsb fuel (sub_chunk_c px qy c (min kx ly))
                (next_x px kx (min kx ly) xrest) (next_y (min kx ly) ((qy, ly) :: yrest)) with
            | none => rfl
            | some out =>
              dsimp only; unfold sub_chunk_out subbit; rw [if_pos h1]
          · have hd2 : decide (2 ≤ min kx ly) = false := decide_eq_false (by omega)
            rw [hd2, if_false_eq_true]
            have hc1 : ((!px && (qy || c)) || (qy && c)) =
                       sub_chunk_c px qy c (min kx ly) := by
              unfold sub_chunk_c subbit; rw [if_neg h1]
            rw [hc1]
            cases sub_lsb fuel (sub_chunk_c px qy c (min kx ly))
                (next_x px kx (min kx ly) xrest) (next_y (min kx ly) ((qy, ly) :: yrest)) with
            | none => rfl
            | some out =>
              dsimp only; unfold sub_chunk_out subbit; rw [if_neg h1]

lemma sub_lsb_checked_p_eq
    {sub_lsb_f} (h1 : sub_lsb_f = sub_lsb) :
    sub_lsb_checked_f_p sub_lsb_f = sub_lsb_checked := by
  subst h1; funext fuel n k a b
  unfold sub_lsb_checked_f_p sub_lsb_checked
  simp only [bool_rec_eq, nat_ble_def, nat_add_def]
  by_cases hlt : n < k
  · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
  · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]

lemma drop_mult3_fast_eq : drop_mult3_fast = drop_mult3 := by
  funext top rest
  unfold drop_mult3_fast drop_mult3
  simp only [withNatFast_eq, bool_rec_eq, nat_beq_def, nat_mod_def, consBlock1_eq]
  by_cases h : top.len % 3 = 0 <;> simp [h]

lemma choose_limit_r_p_eq
    {drop_mult3_f} (h1 : drop_mult3_f = drop_mult3)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2))
    {pop_word_f} (h3 : pop_word_f = pop_word) :
    choose_limit_r_f_p drop_mult3_f pop1_b_f pop_word_f = choose_limit_r_loop := by
  subst h1; subst h2; subst h3; funext n fuel done r
  unfold choose_limit_r_f_p
  induction fuel generalizing done r with
  | zero => rfl
  | succ fuel ih =>
    unfold choose_limit_r_loop
    simp only [ih]
    cases r with
    | nil =>
      simp only [matchStackFast_eq, bool_rec_eq, nat_ble_def, nat_add_def]
      by_cases hle : done ≤ n <;> simp [hle]
    | cons top rest =>
      simp only [matchStackFast_eq, withOptionFast_eq, withNatFast_eq, band_fast_eq, bnot_fast_eq,
        nat_min_fast_eq, nat_max_fast_eq,
        bool_rec_eq, nat_beq_def, nat_ble_def, nat_add_def, nat_div_def,
        with_nat_eq, Bool.and_assoc]
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

lemma can_pair_f_eq : can_pair_f = can_pair := by
  funext s; unfold can_pair_f
  induction s with
  | nil => rfl
  | cons top rest ih =>
    unfold can_pair
    simp only [ih]
    simp only [matchStackFast_eq, band_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, nat_mod_def, Bool.and_assoc]
    by_cases c1 : (top.width == 1 && top.pat == 1) = true
    · simp only [c1, ↓reduceIte]
      cases rest with
      | nil => rfl
      | cons rhd rtl =>
        dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
        by_cases hm : top.len % 4 = 0
        · simp [hm]
        · have hne : (top.len % 4 == 0) = false := beq_eq_false_iff_ne.mpr hm
          rw [hne]; simp [hm]
    · have hc1f : (top.width == 1 && top.pat == 1) = false := Bool.eq_false_iff.mpr c1
      simp only [hc1f, Bool.false_eq_true, ↓reduceIte]

lemma can_absorb_f_eq : can_absorb_f = can_absorb := by
  funext s; unfold can_absorb_f
  induction s with
  | nil => rfl
  | cons top rest ih =>
    unfold can_absorb
    simp only [ih]
    simp only [matchStackFast_eq, band_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, nat_mod_def, Bool.and_assoc]
    by_cases c1 : (top.width == 1 && top.pat == 1) = true
    · simp only [c1, ↓reduceIte]
      cases rest with
      | nil => rfl
      | cons rhd rtl =>
        dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
        by_cases hm : top.len % 4 = 0
        · simp [hm]
        · have hne : (top.len % 4 == 0) = false := beq_eq_false_iff_ne.mpr hm
          rw [hne]; simp [hm]
    · have hc1f : (top.width == 1 && top.pat == 1) = false := Bool.eq_false_iff.mpr c1
      simp only [hc1f, Bool.false_eq_true, ↓reduceIte]

lemma pre_pair_l_f_eq {can_pair_fn} (h1 : can_pair_fn = can_pair) :
    pre_pair_l_f can_pair_fn = pre_pair_l := by
  subst h1; funext s; unfold pre_pair_l_f
  match s with
  | b1 :: b2 :: b3 :: rest =>
    dsimp only [pre_pair_l]
    simp only [matchStackFast_eq, withNatFast_eq, band_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, nat_sub_def, consBlock1_eq, Bool.and_assoc]
  | b1 :: _ :: [] =>
    dsimp only [pre_pair_l]
    simp only [matchStackFast_eq, band_fast_eq, nat_beq_def, Bool.and_assoc]
  | [] => rfl
  | [_] => rfl

lemma pre_absorb_l_f_eq {can_absorb_fn} (h1 : can_absorb_fn = can_absorb) :
    pre_absorb_l_f can_absorb_fn = pre_absorb_l := by
  subst h1; funext s; unfold pre_absorb_l_f
  match s with
  | b1 :: b2 :: b3 :: rest =>
    dsimp only [pre_absorb_l]
    simp only [matchStackFast_eq, withNatFast_eq, band_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, nat_sub_def, consBlock1_eq, Bool.and_assoc]
  | b1 :: _ :: [] =>
    dsimp only [pre_absorb_l]
    simp only [matchStackFast_eq, band_fast_eq, nat_beq_def, Bool.and_assoc]
  | [] => rfl
  | [_] => rfl

lemma can_parse_r_f_eq : can_parse_r_f = can_parse_r := by
  funext s; cases s with
  | nil => rfl
  | cons top rest =>
    unfold can_parse_r_f can_parse_r
    simp only [matchStackFast_eq, bnot_fast_eq, band_fast_eq, nat_beq_def, nat_mod_def, Bool.and_assoc]

lemma do_shift_right_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {pop_word_f} (h2 : pop_word_f = pop_word)
    {count_stack_mut_f} (h3 : count_stack_mut_f = count_stack_mut) :
    do_shift_right_f_p push_stack_f pop_word_f count_stack_mut_f 8 = do_shift_right := by
  subst h1; subst h2; subst h3; funext sq sw sin sout sout_w s
  unfold do_shift_right_f_p do_shift_right
  simp only [bool_rec_eq, withOptionFast_eq, someMStateFast_eq, nat_beq_def, nat_add_def, nat_mul_def, nat_shiftLeft_def,
    Nat.shiftLeft_eq, Nat.one_mul, with_prod_eq, withProdFast_eq, some_mstate_eq]
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
  simp only [bool_rec_eq, withOptionFast_eq, someMStateFast_eq, bnot_fast_eq, bxor_fast_eq,
    nat_beq_def, nat_add_def, nat_mul_def, nat_sub_def,
    nat_shiftLeft_def, nat_shiftRight_def, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.shiftRight_eq_div_pow, Nat.pow_one, with_prod_eq, withProdFast_eq, some_mstate_eq, bit_pat_eq,
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
    {pre_pair_l_fn} (h0a : pre_pair_l_fn = pre_pair_l)
    {can_parse_r_fn} (h0b : can_parse_r_fn = can_parse_r)
    {can_pair_fn} (h0c : can_pair_fn = can_pair)
    {pop_word_f} (h1 : pop_word_f = pop_word)
    {bsize_parts_f} (h2 : bsize_parts_f = bsize_parts)
    {put_l_stack_f} (h3 : put_l_stack_f = put_l_stack)
    {put_r_rec_f} (h4 : put_r_rec_f = put_r_rec)
    {parse_l_f} (h5 : parse_l_f = parse_l)
    {parse_r_f} (h6 : parse_r_f = parse_r)
    {sub_lsb_checked_f} (h7 : sub_lsb_checked_f = sub_lsb_checked)
    {choose_limit_r_f} (h8 : choose_limit_r_f = choose_limit_r_loop)
    {push_prefix_l_f} (h9 : push_prefix_l_f = push_prefix_l) :
    try_pair_stack_f_p pre_pair_l_fn can_parse_r_fn can_pair_fn
      pop_word_f bsize_parts_f put_l_stack_f put_r_rec_f
      parse_l_f parse_r_f sub_lsb_checked_f choose_limit_r_f push_prefix_l_f = try_pair_stack := by
  funext kfuel
  subst h0a; subst h0b; subst h0c; subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9
  funext s
  unfold try_pair_stack_f_p try_pair_stack put_r_stack choose_limit_r
  by_cases hq0 : s.q = 0
  · have hqb : Nat.beq s.q.val 0 = true := by rw [nat_beq_def, beq_iff_eq]; exact congrArg Fin.val hq0
    rw [hqb, if_pos hq0]; dsimp only
    by_cases hpre : (pre_pair_l s.l && can_parse_r s.r) = true
    · have hpreb : band_fast (pre_pair_l s.l) (can_parse_r s.r) = true := by rw [band_fast_eq]; exact hpre
      rw [hpreb, if_pos hpre]; dsimp only
      cases pop_word 29 5 s.l with
      | none => rfl
      | some lc =>
        dsimp only [withOptionFast]
        by_cases hcp : can_pair lc = true
        · rw [hcp, if_true_eq_true]; dsimp only
          rw [withNatFast_eq]
          generalize parse_l kfuel 100000000 lc = res_l
          rcases res_l with ⟨a_list, l_tail⟩
          rw [withProdFast_eq, with_prod_eq]; dsimp only
          rw [with_list_eq]
          cases a_list with
          | nil => rfl
          | cons a_hd a_tl =>
            dsimp only [isEmptyPartListFast, List.isEmpty, Bool.false_eq_true, ↓reduceIte]
            rw [withNatFast_eq, with_nat_eq]
            generalize bsize_parts (a_hd :: a_tl) = n
            rw [withNatFast_eq, with_nat_eq]
            generalize choose_limit_r_loop n kfuel 0 s.r = lim_r
            by_cases hlim : lim_r = 0
            · subst hlim; rfl
            · have hne : Nat.beq lim_r 0 = false := by rw [nat_beq_def, beq_eq_false_iff_ne]; exact hlim
              rw [hne, if_neg hlim]; dsimp only
              generalize parse_r kfuel lim_r s.r = res_r
              rcases res_r with ⟨b_list, r_tail⟩
              rw [withProdFast_eq, with_prod_eq]; dsimp only
              rw [with_list_eq]
              cases b_list with
              | nil => rfl
              | cons b_hd b_tl =>
                dsimp only [isEmptyPartListFast, List.isEmpty, Bool.false_eq_true, ↓reduceIte]
                rw [withNatFast_eq, with_nat_eq]
                simp only [withOptionFast_eq, someMStateFast_eq, fin6_0_eq, some_mstate_eq]
                cases sub_lsb_checked kfuel n (bsize_parts (b_hd :: b_tl)) (a_hd :: a_tl) (b_hd :: b_tl) with
                | some out => rfl
                | none =>
                  cases sub_lsb_checked kfuel (bsize_parts (b_hd :: b_tl)) n (b_hd :: b_tl) (a_hd :: a_tl) <;> rfl
        · have hcpf : can_pair lc = false := Bool.eq_false_iff.mpr hcp
          rw [hcpf, if_false_eq_true]
    · have hpreb : band_fast (pre_pair_l s.l) (can_parse_r s.r) = false := by rw [band_fast_eq]; exact Bool.eq_false_iff.mpr hpre
      rw [hpreb, if_neg hpre]
  · have hqb : Nat.beq s.q.val 0 = false := by rw [nat_beq_def, beq_eq_false_iff_ne]; intro h; exact hq0 (Fin.ext h)
    rw [hqb, if_neg hq0]

lemma try_absorb_stack_p_eq
    {pre_absorb_l_fn} (h0a : pre_absorb_l_fn = pre_absorb_l)
    {can_parse_r_fn} (h0b : can_parse_r_fn = can_parse_r)
    {can_absorb_fn} (h0c : can_absorb_fn = can_absorb)
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
    try_absorb_stack_f_p pre_absorb_l_fn can_parse_r_fn can_absorb_fn
      push_stack_f pop_word_f count_stack_mut_f bsize_parts_f
      put_r_rec_f parse_r_f sub_lsb_f choose_limit_r_f push_prefix_l_f build_vprime_f =
    try_absorb_stack := by
  funext kfuel
  subst h0a; subst h0b; subst h0c; subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9; subst h10
  funext s
  unfold try_absorb_stack_f_p try_absorb_stack put_r_stack choose_limit_r
  by_cases hq0 : s.q = 0
  · have hqb : Nat.beq s.q.val 0 = true := by rw [nat_beq_def, beq_iff_eq]; exact congrArg Fin.val hq0
    rw [hqb, if_pos hq0]; dsimp only
    by_cases hpre : (pre_absorb_l s.l && can_parse_r s.r) = true
    · have hpreb : band_fast (pre_absorb_l s.l) (can_parse_r s.r) = true := by rw [band_fast_eq]; exact hpre
      rw [hpreb, if_pos hpre]; dsimp only
      cases pop_word 29 5 s.l with
      | none => rfl
      | some lc0 =>
        rw [withOptionFast_eq]; dsimp only
        by_cases hca : can_absorb lc0 = true
        · rw [hca, if_true_eq_true]; dsimp only
          rw [withNatFast_eq]
          generalize count_stack_mut 15 4 kfuel 100000000 lc0 = res1
          rcases res1 with ⟨n1, r1⟩
          rw [withProdFast_eq, with_prod_eq]; dsimp only
          generalize count_stack_mut 13 4 kfuel 100000000 r1 = res_m
          rcases res_m with ⟨nm, rm⟩
          rw [withProdFast_eq, with_prod_eq]; dsimp only
          by_cases hm0 : nm = 0
          · subst hm0; rfl
          · have hne_m : Nat.beq nm 0 = false := by rw [nat_beq_def, beq_eq_false_iff_ne]; exact hm0
            rw [hne_m, if_neg hm0]; dsimp only
            rw [nat_add_def, withNatFast_eq, with_nat_eq]
            generalize choose_limit_r_loop (n1 + nm) kfuel 0 s.r = lim_r
            by_cases hlim0 : lim_r = 0
            · subst hlim0; rfl
            · have hne_l : Nat.beq lim_r 0 = false := by rw [nat_beq_def, beq_eq_false_iff_ne]; exact hlim0
              rw [hne_l, if_neg hlim0]; dsimp only
              generalize parse_r kfuel lim_r s.r = res_r
              rcases res_r with ⟨b_list, r_tail⟩
              rw [withProdFast_eq, with_prod_eq]; dsimp only
              rw [with_list_eq]
              cases b_list with
              | nil => rfl
              | cons b_hd b_tl =>
                rw [isEmptyPartListFast_eq]; dsimp only [List.isEmpty]; rw [if_false_eq_true]
                rw [withNatFast_eq, with_nat_eq]
                generalize bsize_parts (b_hd :: b_tl) = k
                have hmin_eq : nat_min_fast nm (@Bool.rec (fun _ => Nat) 1 (Nat.sub k n1) (Nat.ble (Nat.add n1 1) k)) =
                               calc_m_init nm n1 k := by
                  unfold calc_m_init
                  simp only [nat_min_fast_eq, bool_rec_eq, nat_ble_def, nat_add_def, nat_sub_def]
                  by_cases hlt : n1 < k
                  · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]
                  · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]
                rw [hmin_eq, withNatFast_eq, with_nat_eq]
                generalize calc_m_init nm n1 k = m_init
                by_cases hmi0 : m_init = 0
                · subst hmi0; rfl
                · have hne_i : Nat.beq m_init 0 = false := by rw [nat_beq_def, beq_eq_false_iff_ne]; exact hmi0
                  rw [hne_i, if_neg hmi0]; dsimp only
                  have hsub_eq :
                      withOptionFast (sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 m_init))
                        (@Bool.rec (fun _ => Option (Nat × PartList))
                          (withNatFast (Nat.sub m_init 1) (fun m_m1 =>
                            withOptionFast (sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 m_m1))
                              none
                              (fun out => some (m_m1, out))))
                          none
                          (Nat.ble m_init 1))
                        (fun out => some (m_init, out)) =
                      try_absorb_sub kfuel n1 m_init (b_hd :: b_tl) := by
                    unfold try_absorb_sub
                    simp only [withOptionFast_eq, withNatFast_eq, bool_rec_eq, nat_ble_def, nat_sub_def]
                    cases sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 m_init) with
                    | some out => rfl
                    | none =>
                      dsimp only
                      by_cases hle1 : m_init ≤ 1
                      · rw [if_pos hle1, decide_eq_true hle1, if_true_eq_true]
                      · rw [if_neg hle1, decide_eq_false hle1, if_false_eq_true]
                        cases sub_lsb kfuel false (b_hd :: b_tl) (build_vprime n1 (m_init - 1)) <;> rfl
                  rw [hsub_eq]
                  cases try_absorb_sub kfuel n1 m_init (b_hd :: b_tl) with
                  | none => rfl
                  | some pair_out =>
                    rcases pair_out with ⟨m_use, out⟩
                    dsimp only [withOptionFast, withProdFast]
                    generalize count_stack_mut 13 4 kfuel m_use r1 = res2
                    rcases res2 with ⟨n2, r2⟩
                    rw [with_prod_eq]; dsimp only
                    simp only [bool_rec_eq, nat_beq_def, nat_mul_def, nat_add_def, someMStateFast_eq, fin6_0_eq, some_mstate_eq]
                    by_cases hres2 : n2 = m_use
                    · simp [hres2]
                    · have hne2 : (n2 == m_use) = false := beq_eq_false_iff_ne.mpr hres2
                      rw [hne2]; simp [hres2]
        · have hcaf : can_absorb lc0 = false := Bool.eq_false_iff.mpr hca
          rw [hcaf, if_false_eq_true]
    · have hpreb : band_fast (pre_absorb_l s.l) (can_parse_r s.r) = false := by rw [band_fast_eq]; exact Bool.eq_false_iff.mpr hpre
      rw [hpreb, if_neg hpre]
  · have hqb : Nat.beq s.q.val 0 = false := by rw [nat_beq_def, beq_eq_false_iff_ne]; intro h; exact hq0 (Fin.ext h)
    rw [hqb, if_neg hq0]

lemma step_prim_p_eq
    {push_stack_f} (h1 : push_stack_f = push_stack)
    {pop1_b_f} (h2 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2)) :
    step_prim_f_p push_stack_f pop1_b_f = step_prim := by
  subst h1; subst h2; funext s
  unfold step_prim_f_p step_prim
  rcases s with ⟨q, l, r⟩
  simp only [bool_rec_eq, someMStateFast_eq, fin6_0_eq, fin6_1_eq, fin6_2_eq, fin6_3_eq, fin6_4_eq, fin6_5_eq,
    with_prod_eq, withProdFast_eq, some_mstate_eq, bit_pat_eq]
  rcases hpr : pop1 r with ⟨b_r, r_rest⟩
  dsimp only
  rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases b_r with ⟨_ | _ | b_r, hb⟩ <;> (try rfl) <;> (try omega)

lemma has_head_bit1_f_eq : has_head_bit1_f = has_head_bit1 := by
  funext s; cases s with
  | nil => rfl
  | cons top rest =>
    unfold has_head_bit1_f has_head_bit1
    simp only [matchStackFast_eq, nat_land_def, nat_beq_def, Nat.and_one_is_mod]

lemma can_any_macro_f_eq
    {pre_pair_l_fn} (h1 : pre_pair_l_fn = pre_pair_l)
    {pre_absorb_l_fn} (h2 : pre_absorb_l_fn = pre_absorb_l)
    {can_parse_r_fn} (h3 : can_parse_r_fn = can_parse_r) :
    can_any_macro_f pre_pair_l_fn pre_absorb_l_fn can_parse_r_fn = can_any_macro := by
  subst h1; subst h2; subst h3
  funext s
  unfold can_any_macro_f can_any_macro
  simp only [bool_rec_eq, nat_beq_def]
  rcases s with ⟨⟨_ | _ | _ | _ | _ | _ | q, hq⟩, l, r⟩
  · -- q = 0
    dsimp only [beq_self_eq_true, ↓reduceIte]
    cases r with
    | nil => simp [bor_fast_eq, band_fast_eq, matchStackFast_eq]
    | cons top rest =>
      simp only [matchStackFast_eq, bor_fast_eq, band_fast_eq, bnot_fast_eq, nat_land_def, nat_beq_def, nat_ble_def, Nat.and_one_is_mod]
      rfl
  · -- q = 1
    simp only [band_fast_eq, has_head_bit1_f_eq]
    rfl
  · -- q = 2
    simp only [band_fast_eq, has_head_bit1_f_eq]
    rfl
  · -- q = 3
    cases r with
    | nil => rfl
    | cons top rest =>
      simp only [matchStackFast_eq, band_fast_eq, bnot_fast_eq, bool_rec_eq, nat_beq_def, nat_ble_def, has_head_bit1_f_eq, Bool.and_assoc]
      have h30 : ((0 + 1 + 1 + 1 == 0) = true) = False := by decide
      have h31 : ((0 + 1 + 1 + 1 == 1) = true) = False := by decide
      have h32 : ((0 + 1 + 1 + 1 == 2) = true) = False := by decide
      have h33 : ((0 + 1 + 1 + 1 == 3) = true) = True := by decide
      simp only [h30, h31, h32, h33, ↓reduceIte]
      by_cases c1 : (top.width == 1 && top.pat == 0) = true
      · simp only [c1, ↓reduceIte]
        by_cases hlt : 1 < top.len
        · rw [if_pos hlt, decide_eq_true (by omega), if_true_eq_true]; rfl
        · rw [if_neg hlt, decide_eq_false (by omega), if_false_eq_true]; rfl
      · have hc1f : (top.width == 1 && top.pat == 0) = false := Bool.eq_false_iff.mpr c1
        simp only [hc1f, Bool.false_eq_true, ↓reduceIte]
        cases rest <;> rfl
  · -- q = 4
    rfl
  · -- q = 5
    rfl
  · omega

lemma fin6_beq_5 : ∀ (q : Fin 6), (q.val == 5) = decide (q = 5) := by decide
lemma fin2_beq_1 : ∀ (x : Fin 2), (x == 1) = decide (x = 1) := by decide

lemma run_prim_p_eq
    {pop1_b_f} (h1 : pop1_b_f = fun s => ((pop1 s).1 == 1, (pop1 s).2))
    {can_any_macro_fn} (h2 : can_any_macro_fn = can_any_macro)
    {step_prim_f} (h3 : step_prim_f = step_prim) :
    run_prim_f_p pop1_b_f can_any_macro_fn step_prim_f = run_prim := by
  subst h1; subst h2; subst h3
  funext fuel s
  unfold run_prim_f_p
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    unfold run_prim
    dsimp only
    rw [bool_rec_eq, bor_fast_eq, band_fast_eq, nat_beq_def, fin6_beq_5 s.q, fin2_beq_1 (pop1 s.r).1]
    split_ifs with hc
    · rfl
    · rw [withOptionFast_eq]
      cases step_prim s with
      | none => rfl
      | some s1 => exact ih s1

lemma step_prim_plus_p_eq
    {step_prim_f} (h1 : step_prim_f = step_prim)
    {run_prim_f} (h2 : run_prim_f = run_prim) :
    step_prim_plus_f_p step_prim_f run_prim_f = step_prim_plus := by
  subst h1; subst h2
  funext s
  unfold step_prim_plus_f_p step_prim_plus
  simp only [withOptionFast_eq]
  cases step_prim s <;> rfl

lemma step_m_p_eq
    {do_shift_right_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState} (h1 : do_shift_right_f 8 = do_shift_right)
    {do_shift_left_f : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState} (h2 : do_shift_left_f 8 = do_shift_left)
    {try_pair_stack_f : Nat → MState → Option MState} (h3 : try_pair_stack_f = try_pair_stack)
    {try_absorb_stack_f : Nat → MState → Option MState} (h4 : try_absorb_stack_f = try_absorb_stack)
    {step_prim_plus_f} (h5 : step_prim_plus_f = step_prim_plus) :
    step_m_f_p do_shift_right_f do_shift_left_f try_pair_stack_f try_absorb_stack_f step_prim_plus_f 8 = step_m := by
  subst h5; funext s; unfold step_m_f_p; rw [h1, h2, h3, h4]; unfold step_m
  simp only [bool_rec_eq, nat_beq_def, withOptionFast_eq, stack_len_fast_eq, fin6_0_eq, fin6_1_eq, fin6_2_eq, fin6_3_eq]
  rcases s with ⟨⟨_ | _ | _ | _ | _ | _ | q, hq⟩, l, r⟩
  · unfold step_m_q0
    have hq_eq : (⟨0, hq⟩ : Fin 6) = 0 := rfl
    have h00 : ((0 == 0) = true) = True := by decide
    rw [hq_eq]
    simp only [h00, ↓reduceIte]
    cases try_pair_stack (Nat.add (Nat.add l.length r.length) 4) ⟨0, l, r⟩ <;>
      cases try_absorb_stack (Nat.add (Nat.add l.length r.length) 4) ⟨0, l, r⟩ <;>
      cases do_shift_right 0 3 1 1 1 ⟨0, l, r⟩ <;> rfl
  · unfold step_m_q1
    have hq_eq : (⟨0 + 1, hq⟩ : Fin 6) = 1 := rfl
    have h10 : ((0 + 1 == 0) = true) = False := by decide
    have h11 : ((0 + 1 == 1) = true) = True := by decide
    rw [hq_eq]
    simp only [h10, h11, ↓reduceIte]
    cases do_shift_left 1 1 1 0 1 ⟨1, l, r⟩ <;> rfl
  · unfold step_m_q2
    have hq_eq : (⟨0 + 1 + 1, hq⟩ : Fin 6) = 2 := rfl
    have h20 : ((0 + 1 + 1 == 0) = true) = False := by decide
    have h21 : ((0 + 1 + 1 == 1) = true) = False := by decide
    have h22 : ((0 + 1 + 1 == 2) = true) = True := by decide
    rw [hq_eq]
    simp only [h20, h21, h22, ↓reduceIte]
    cases do_shift_left 2 2 3 1 2 ⟨2, l, r⟩ <;> rfl
  · unfold step_m_q3
    have hq_eq : (⟨0 + 1 + 1 + 1, hq⟩ : Fin 6) = 3 := rfl
    have h30 : ((0 + 1 + 1 + 1 == 0) = true) = False := by decide
    have h31 : ((0 + 1 + 1 + 1 == 1) = true) = False := by decide
    have h32 : ((0 + 1 + 1 + 1 == 2) = true) = False := by decide
    have h33 : ((0 + 1 + 1 + 1 == 3) = true) = True := by decide
    rw [hq_eq]
    simp only [h30, h31, h32, h33, ↓reduceIte]
    cases do_shift_right 3 1 1 0 1 ⟨3, l, r⟩ <;>
      cases do_shift_right 3 3 2 1 1 ⟨3, l, r⟩ <;>
        cases do_shift_right 3 4 10 14 4 ⟨3, l, r⟩ <;>
          cases do_shift_right 3 4 5 7 4 ⟨3, l, r⟩ <;> rfl
  · rfl
  · rfl
  · omega

noncomputable def mkBlock_f0 : Nat → Nat → Nat → Block := mkBlock_f_p
noncomputable def rot1_f0 : Nat → Nat → Nat := rot1_f_p
noncomputable def rot_mod_f0 : Nat → Nat → Nat → Nat := rot_mod_f_p
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
noncomputable def sub_lsb_checked_f0 : Nat → Nat → Nat → PartList → PartList → Option PartList := sub_lsb_checked_f_p sub_lsb_f0
noncomputable def drop_mult3_f0 : Block → Stack → Stack := drop_mult3_fast
noncomputable def choose_limit_r_f0 : Nat → Nat → Nat → Stack → Nat := choose_limit_r_f_p drop_mult3_f0 pop1_b_f0 pop_word_f0
noncomputable def push_prefix_l_f0 : Stack → Stack := push_prefix_l_f_p push_stack_f0
noncomputable def build_vprime_f0 : Nat → Nat → PartList := build_vprime_f_p mkPart_f0
noncomputable def can_pair_f0 : Stack → Bool := can_pair_f
noncomputable def can_absorb_f0 : Stack → Bool := can_absorb_f
noncomputable def pre_pair_l_f0 : Stack → Bool := pre_pair_l_f can_pair_f0
noncomputable def pre_absorb_l_f0 : Stack → Bool := pre_absorb_l_f can_absorb_f0
noncomputable def can_parse_r_f0 : Stack → Bool := can_parse_r_f
noncomputable def do_shift_right_f0 : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState := do_shift_right_f_p push_stack_f0 pop_word_f0 count_stack_mut_f0
noncomputable def do_shift_left_f0 : Nat → Fin 6 → Nat → Nat → Nat → Nat → MState → Option MState := do_shift_left_f_p bit_of_bool_f0 push_stack_f0 pop1_b_f0 pop_word_f0 count_stack_mut_f0
noncomputable def try_pair_stack_f0 : Nat → MState → Option MState := try_pair_stack_f_p pre_pair_l_f0 can_parse_r_f0 can_pair_f0 pop_word_f0 bsize_parts_f0 put_l_stack_f0 put_r_rec_f0 parse_l_f0 parse_r_f0 sub_lsb_checked_f0 choose_limit_r_f0 push_prefix_l_f0
noncomputable def try_absorb_stack_f0 : Nat → MState → Option MState := try_absorb_stack_f_p pre_absorb_l_f0 can_parse_r_f0 can_absorb_f0 push_stack_f0 pop_word_f0 count_stack_mut_f0 bsize_parts_f0 put_r_rec_f0 parse_r_f0 sub_lsb_f0 choose_limit_r_f0 push_prefix_l_f0 build_vprime_f0
noncomputable def step_prim_f0 : MState → Option MState := step_prim_f_p push_stack_f0 pop1_b_f0
noncomputable def can_any_macro_f0 : MState → Bool := can_any_macro_f pre_pair_l_f0 pre_absorb_l_f0 can_parse_r_f0
noncomputable def run_prim_f0 : Nat → MState → Option MState := run_prim_f_p pop1_b_f0 can_any_macro_f0 step_prim_f0
noncomputable def step_prim_plus_f0 : MState → Option MState := step_prim_plus_f_p step_prim_f0 run_prim_f0
noncomputable def step_m_c0 : MState → Option MState := step_m_f_p do_shift_right_f0 do_shift_left_f0 try_pair_stack_f0 try_absorb_stack_f0 step_prim_plus_f0 8

noncomputable def run_m_fast (fuel : Nat) (s0 : MState) : Option MState :=
  @Nat.rec (fun _ => MState → Option MState)
    (fun s => some s)
    (fun _ ih s =>
      withOptionFast (step_m_c0 s) none ih)
    fuel s0

noncomputable def block_beq (a b : Block) : Bool :=
  band_fast (Nat.beq a.pat b.pat) (band_fast (Nat.beq a.width b.width) (Nat.beq a.len b.len))

noncomputable def stack_beq : Stack → Stack → Bool :=
  @List.rec Block (fun _ => Stack → Bool)
    (fun ys => @List.rec Block (fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun x _ ih ys =>
      @List.rec Block (fun _ => Bool) false (fun y ys2 _ => band_fast (block_beq x y) (ih ys2)) ys)

noncomputable def opt_mstate_beq (o : Option MState) (target : MState) : Bool :=
  withOptionFast o false (fun s =>
    band_fast (Nat.beq s.q.val target.q.val)
      (band_fast (stack_beq s.l target.l) (stack_beq s.r target.r)))

noncomputable def is_some_m (o : Option MState) : Bool := withOptionFast o false (fun _ => true)


lemma step_m_c0_eq : step_m_c0 = step_m :=
  let h04 := bit_of_bool_p_eq
  let h06 := push_stack_fast_eq
  let h07 := drop_stack_fast_eq
  let h08 := pop1_b_fast_eq
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
  let h21b := sub_lsb_checked_p_eq h21
  let h22a := drop_mult3_fast_eq
  let h22 := choose_limit_r_p_eq h22a h08 h09
  let h23 := push_prefix_l_p_eq h06
  let h24 := build_vprime_p_eq h12
  let h24a := can_pair_f_eq
  let h24b := can_absorb_f_eq
  let h24c := pre_pair_l_f_eq h24a
  let h24d := pre_absorb_l_f_eq h24b
  let h24e := can_parse_r_f_eq
  let h25 := do_shift_right_p_eq h06 h09 h11
  let h26 := do_shift_left_p_eq h04 h06 h08 h09 h11
  let h27 := try_pair_stack_p_eq h24c h24e h24a h09 h13 h15 h16 h18 h20 h21b h22 h23
  let h28 := try_absorb_stack_p_eq h24d h24e h24b h06 h09 h11 h13 h16 h20 h21 h22 h23 h24
  let h29 := step_prim_p_eq h06 h08
  let h29a := can_any_macro_f_eq h24c h24d h24e
  let h29b := run_prim_p_eq h08 h29a h29
  let h29c := step_prim_plus_p_eq h29 h29b
  step_m_p_eq h25 h26 h27 h28 h29c

lemma run_m_loop_eq {step_f : MState → Option MState}
    (hstep : step_f = step_m) (fuel : Nat) (s0 : MState) :
    @Nat.rec (fun _ => MState → Option MState)
      (fun s => some s)
      (fun _ ih s =>
        withOptionFast (step_f s) none ih)
      fuel s0 = run_m fuel s0 := by
  subst hstep
  induction fuel generalizing s0 with
  | zero => rfl
  | succ i ih =>
    unfold run_m
    dsimp only
    cases hs : step_m s0 with
    | none => rfl
    | some s1 => exact ih s1

lemma run_m_fast_eq (fuel : Nat) (s0 : MState) :
    run_m_fast fuel s0 = run_m fuel s0 :=
  run_m_loop_eq step_m_c0_eq fuel s0

lemma block_beq_eq {a b : Block} (h : block_beq a b = true) : a = b := by
  rcases a with ⟨p1, w1, l1⟩; rcases b with ⟨p2, w2, l2⟩
  simp only [block_beq, band_fast_eq, Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

lemma stack_beq_eq : ∀ {xs ys : Stack}, stack_beq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    change band_fast (block_beq x y) (stack_beq xs ys) = true at h
    simp only [band_fast_eq, Bool.and_eq_true] at h
    rw [block_beq_eq h.1, stack_beq_eq h.2]

lemma opt_mstate_beq_eq {o : Option MState} {t : MState} (h : opt_mstate_beq o t = true) :
    o = some t := by
  cases o with
  | none => cases h
  | some s =>
    rcases s with ⟨q1, l1, r1⟩; rcases t with ⟨q2, l2, r2⟩
    simp only [opt_mstate_beq, withOptionFast_eq, band_fast_eq, Bool.and_eq_true, Nat.beq_eq] at h
    rcases h with ⟨hq, hl, hr⟩
    rw [Fin.ext hq, stack_beq_eq hl, stack_beq_eq hr]

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
    | some s' => simp [hs] at h1 ⊢; exact ih h1

def MReach (s1 s2 : MState) : Prop :=
  ∃ fuel, run_m fuel s1 = some s2

lemma mreach_base_fast {k : Nat} {s1 s2 : MState}
    (h : opt_mstate_beq (run_m_fast k s1) s2 = true) : MReach s1 s2 :=
  ⟨k, (run_m_fast_eq k s1).symm.trans (opt_mstate_beq_eq h)⟩

lemma mreach_step_fast {k : Nat} {s1 s2 s3 : MState}
    (h1 : opt_mstate_beq (run_m_fast k s1) s2 = true) (h2 : MReach s2 s3) : MReach s1 s3 :=
  let ⟨n, hn⟩ := h2
  ⟨k + n, run_m_trans ((run_m_fast_eq k s1).symm.trans (opt_mstate_beq_eq h1)) hn⟩


private def cfg_0 : MState := ⟨4, [], []⟩
private def cfg_1 : MState := ⟨3, [⟨0, 1, 2⟩, ⟨7, 4, 32⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 16⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 700⟩, ⟨1, 1, 1⟩], [⟨4, 3, 215⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 1⟩]⟩ -- +1100 (step 1100, blks=20)
private def cfg_2 : MState := ⟨3, [⟨1, 1, 21⟩, ⟨14, 4, 40⟩, ⟨1, 1, 16⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨13, 4, 1685⟩, ⟨1, 1, 1⟩], [⟨2, 3, 1⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 3⟩, ⟨1, 3, 363⟩, ⟨0, 1, 3⟩, ⟨1, 3, 387⟩, ⟨0, 1, 324⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1102 (step 2202, blks=25)
private def cfg_3 : MState := ⟨3, [⟨14, 4, 48⟩, ⟨1, 1, 24⟩, ⟨14, 4, 16⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨13, 4, 45⟩, ⟨1, 1, 4⟩, ⟨14, 4, 64⟩, ⟨1, 1, 4⟩, ⟨14, 4, 172⟩, ⟨1, 1, 4⟩, ⟨14, 4, 3000⟩, ⟨1, 1, 1⟩], [⟨1, 3, 945⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 867⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1305 (step 3507, blks=25)
private def cfg_4 : MState := ⟨1, [⟨1, 1, 26⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 6968⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 15⟩, ⟨0, 1, 6⟩, ⟨1, 3, 48⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 102⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 282⟩, ⟨0, 1, 3⟩, ⟨1, 3, 24⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1605⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1137⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1329⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 1⟩]⟩ -- +1360 (step 4867, blks=43)
private def cfg_5 : MState := ⟨3, [⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 136⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨13, 4, 105⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 52⟩, ⟨1, 1, 4⟩, ⟨14, 4, 7636⟩, ⟨1, 1, 1⟩], [⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 24⟩, ⟨0, 1, 3⟩, ⟨1, 3, 60⟩, ⟨0, 1, 1050⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1137⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1329⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 990⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 129⟩, ⟨1, 3, 1⟩]⟩ -- +1335 (step 6202, blks=48)
private def cfg_6 : MState := ⟨3, [⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 12488⟩, ⟨1, 1, 1⟩], [⟨0, 1, 30⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 18⟩, ⟨0, 1, 15⟩, ⟨1, 3, 9⟩, ⟨0, 1, 15⟩, ⟨1, 3, 36⟩, ⟨0, 1, 3⟩, ⟨1, 3, 189⟩, ⟨0, 1, 153⟩, ⟨1, 3, 180⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 90⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 474⟩, ⟨0, 1, 3⟩, ⟨1, 3, 150⟩, ⟨0, 1, 12⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 33⟩, ⟨1, 3, 48⟩, ⟨0, 1, 3⟩, ⟨1, 3, 150⟩, ⟨0, 1, 3⟩, ⟨1, 3, 75⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 51⟩, ⟨1, 3, 9⟩, ⟨0, 1, 9⟩, ⟨1, 3, 33⟩, ⟨0, 1, 1014⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 318⟩, ⟨0, 1, 69⟩, ⟨1, 3, 5406⟩, ⟨0, 1, 384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1165 (step 7367, blks=72)
private def cfg_7 : MState := ⟨3, [⟨7, 4, 8⟩, ⟨1, 1, 13⟩, ⟨14, 4, 4⟩, ⟨1, 1, 20⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 13812⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨1, 3, 12⟩, ⟨0, 1, 6⟩, ⟨1, 3, 87⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 81⟩, ⟨0, 1, 9⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 18⟩, ⟨0, 1, 12⟩, ⟨1, 3, 48⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 141⟩, ⟨0, 1, 3⟩, ⟨1, 3, 75⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 51⟩, ⟨1, 3, 9⟩, ⟨0, 1, 9⟩, ⟨1, 3, 33⟩, ⟨0, 1, 1014⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 318⟩, ⟨0, 1, 69⟩, ⟨1, 3, 5406⟩, ⟨0, 1, 384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1767⟩, ⟨1, 3, 3⟩, ⟨0, 1, 426⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩ -- +1198 (step 8565, blks=70)
private def cfg_8 : MState := ⟨0, [⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨1, 1, 3⟩, ⟨14, 4, 452⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 16⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨13, 4, 14129⟩, ⟨1, 1, 1⟩], [⟨0, 1, 6⟩, ⟨1, 3, 42⟩, ⟨0, 1, 3⟩, ⟨1, 3, 21⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 48⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 3⟩, ⟨0, 1, 723⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 318⟩, ⟨0, 1, 69⟩, ⟨1, 3, 5406⟩, ⟨0, 1, 384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1767⟩, ⟨1, 3, 3⟩, ⟨0, 1, 426⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩ -- +1439 (step 10004, blks=65)
private def cfg_9 : MState := ⟨0, [⟨1, 1, 7⟩, ⟨0, 1, 1⟩, ⟨1, 1, 41⟩, ⟨14, 4, 4⟩, ⟨13, 4, 5⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 15144⟩, ⟨1, 1, 1⟩], [⟨0, 1, 452⟩, ⟨1, 1, 1⟩, ⟨0, 1, 5⟩, ⟨1, 3, 318⟩, ⟨0, 1, 69⟩, ⟨1, 3, 5406⟩, ⟨0, 1, 384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1767⟩, ⟨1, 3, 3⟩, ⟨0, 1, 426⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 906⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 1⟩]⟩ -- +1105 (step 11109, blks=60)
private def cfg_10 : MState := ⟨0, [⟨1, 1, 19⟩, ⟨0, 1, 1⟩, ⟨1, 1, 51⟩, ⟨13, 4, 1⟩, ⟨13, 4, 16581⟩, ⟨1, 1, 1⟩], [⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 66⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 4689⟩, ⟨0, 1, 384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1767⟩, ⟨1, 3, 3⟩, ⟨0, 1, 426⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 906⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 906⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 552⟩, ⟨1, 3, 6⟩, ⟨0, 1, 381⟩, ⟨1, 3, 3⟩, ⟨0, 1, 549⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1323 (step 12432, blks=76)
private def cfg_11 : MState := ⟨3, [⟨14, 4, 1524⟩, ⟨1, 1, 1⟩, ⟨7, 4, 155⟩, ⟨1, 1, 4⟩, ⟨14, 4, 312⟩, ⟨1, 1, 572⟩, ⟨14, 4, 1192⟩, ⟨1, 1, 48⟩, ⟨14, 4, 4⟩, ⟨1, 1, 60⟩, ⟨14, 4, 320⟩, ⟨1, 1, 512⟩, ⟨14, 4, 1416⟩, ⟨1, 1, 4⟩, ⟨14, 4, 2724⟩, ⟨1, 1, 9⟩, ⟨14, 4, 24⟩, ⟨1, 1, 12⟩, ⟨14, 4, 32⟩, ⟨1, 1, 16⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 120⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 5944⟩, ⟨1, 1, 4⟩, ⟨14, 4, 10628⟩, ⟨1, 1, 1⟩], [⟨0, 1, 485⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 132⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 27⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 84⟩, ⟨0, 1, 51⟩, ⟨1, 3, 105⟩, ⟨0, 1, 3⟩, ⟨1, 3, 126⟩, ⟨0, 1, 624⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 552⟩, ⟨1, 3, 6⟩, ⟨0, 1, 381⟩, ⟨1, 3, 3⟩, ⟨0, 1, 549⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1227 (step 13659, blks=72)
private def cfg_12 : MState := ⟨1, [⟨1, 1, 4⟩, ⟨14, 4, 96⟩, ⟨1, 1, 9⟩, ⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 16⟩, ⟨1, 1, 12⟩, ⟨14, 4, 32⟩, ⟨1, 1, 4⟩, ⟨14, 4, 32⟩, ⟨13, 4, 45⟩, ⟨1, 1, 16⟩, ⟨14, 4, 4⟩, ⟨13, 4, 1⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 492⟩, ⟨1, 1, 1⟩, ⟨7, 4, 3⟩, ⟨1, 1, 1⟩, ⟨7, 4, 3⟩, ⟨13, 4, 1⟩, ⟨1, 1, 17⟩, ⟨14, 4, 12⟩, ⟨13, 4, 61⟩, ⟨1, 1, 4⟩, ⟨14, 4, 24⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨13, 4, 5⟩, ⟨13, 4, 309⟩, ⟨1, 1, 4⟩, ⟨14, 4, 26096⟩, ⟨1, 1, 1⟩], [⟨0, 1, 35⟩, ⟨1, 1, 1⟩, ⟨0, 1, 8⟩, ⟨1, 3, 6⟩, ⟨0, 1, 33⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 117⟩, ⟨0, 1, 3⟩, ⟨1, 3, 222⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 372⟩, ⟨1, 3, 3⟩, ⟨0, 1, 51⟩, ⟨1, 3, 498⟩, ⟨0, 1, 48⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 33⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 240⟩, ⟨0, 1, 384⟩, ⟨1, 3, 1062⟩, ⟨0, 1, 3⟩, ⟨1, 3, 2043⟩, ⟨0, 1, 9⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 90⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 4458⟩, ⟨0, 1, 3⟩, ⟨1, 3, 7971⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩ -- +1472 (step 15131, blks=95)
private def cfg_13 : MState := ⟨1, [⟨1, 1, 19⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 16⟩, ⟨1, 1, 12⟩, ⟨14, 4, 32⟩, ⟨1, 1, 4⟩, ⟨14, 4, 188⟩, ⟨1, 1, 20⟩, ⟨14, 4, 48⟩, ⟨1, 1, 4⟩, ⟨14, 4, 28688⟩, ⟨1, 1, 1⟩], [⟨0, 1, 8⟩, ⟨1, 1, 1⟩, ⟨0, 1, 59⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 9⟩, ⟨1, 3, 12⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 3⟩, ⟨1, 3, 24⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 48⟩, ⟨0, 1, 3⟩, ⟨1, 3, 237⟩, ⟨0, 1, 84⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 9⟩, ⟨0, 1, 90⟩, ⟨1, 3, 45⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 9⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 372⟩, ⟨0, 1, 6⟩, ⟨1, 3, 231⟩, ⟨0, 1, 3⟩, ⟨1, 3, 450⟩, ⟨0, 1, 3⟩, ⟨1, 3, 2043⟩, ⟨0, 1, 9⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 90⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 4458⟩, ⟨0, 1, 3⟩, ⟨1, 3, 7971⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩ -- +1449 (step 16580, blks=87)
private def cfg_14 : MState := ⟨0, [⟨1, 1, 7⟩, ⟨0, 1, 1⟩, ⟨1, 1, 63⟩, ⟨13, 4, 1⟩, ⟨13, 4, 29833⟩, ⟨1, 1, 1⟩], [⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 33⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 9⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 372⟩, ⟨0, 1, 6⟩, ⟨1, 3, 231⟩, ⟨0, 1, 3⟩, ⟨1, 3, 450⟩, ⟨0, 1, 3⟩, ⟨1, 3, 2043⟩, ⟨0, 1, 9⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 90⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 4458⟩, ⟨0, 1, 3⟩, ⟨1, 3, 7971⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 573⟩, ⟨1, 3, 6⟩, ⟨0, 1, 384⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 1⟩]⟩ -- +1472 (step 18052, blks=68)
private def cfg_15 : MState := ⟨1, [⟨1, 1, 30919⟩, ⟨13, 4, 1⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 1, 1⟩, ⟨0, 1, 11⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 30⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 21⟩, ⟨0, 1, 18⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 72⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 2043⟩, ⟨0, 1, 9⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 90⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 4458⟩, ⟨0, 1, 3⟩, ⟨1, 3, 7971⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 573⟩, ⟨1, 3, 6⟩, ⟨0, 1, 384⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 132⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 654⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 1⟩]⟩ -- +1134 (step 19186, blks=75)
private def cfg_16 : MState := ⟨1, [⟨1, 1, 63⟩, ⟨13, 4, 1⟩, ⟨13, 4, 13⟩, ⟨1, 1, 4⟩, ⟨14, 4, 68⟩, ⟨1, 1, 32⟩, ⟨14, 4, 40⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 1412⟩, ⟨1, 1, 9⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 4⟩, ⟨1, 1, 24⟩, ⟨14, 4, 1784⟩, ⟨13, 4, 31485⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 1, 1⟩, ⟨0, 1, 17⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 15⟩, ⟨0, 1, 1716⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 999⟩, ⟨0, 1, 3⟩, ⟨1, 3, 7971⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 573⟩, ⟨1, 3, 6⟩, ⟨0, 1, 384⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 132⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 654⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 4143⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 1⟩]⟩ -- +1196 (step 20382, blks=85)
private def cfg_17 : MState := ⟨3, [⟨14, 4, 408⟩, ⟨1, 1, 36⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 24⟩, ⟨1, 1, 4⟩, ⟨14, 4, 76⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 16⟩, ⟨1, 1, 24⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 140⟩, ⟨1, 1, 4⟩, ⟨14, 4, 96⟩, ⟨13, 4, 36349⟩, ⟨1, 1, 1⟩], [⟨0, 1, 6⟩, ⟨1, 3, 18⟩, ⟨0, 1, 9⟩, ⟨1, 3, 27⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 465⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 174⟩, ⟨1, 3, 258⟩, ⟨0, 1, 3⟩, ⟨1, 3, 7518⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 573⟩, ⟨1, 3, 6⟩, ⟨0, 1, 384⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 132⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 654⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 4143⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 1⟩]⟩ -- +1112 (step 21494, blks=91)
private def cfg_18 : MState := ⟨3, [⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 38724⟩, ⟨1, 1, 1⟩], [⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 93⟩, ⟨0, 1, 3⟩, ⟨1, 3, 72⟩, ⟨0, 1, 6⟩, ⟨1, 3, 285⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6558⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 573⟩, ⟨1, 3, 6⟩, ⟨0, 1, 384⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 132⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 654⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 4143⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2418⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 1⟩]⟩ -- +1499 (step 22993, blks=77)
private def cfg_19 : MState := ⟨3, [⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 24⟩, ⟨13, 4, 1⟩, ⟨1, 1, 12⟩, ⟨14, 4, 44⟩, ⟨1, 1, 12⟩, ⟨14, 4, 32⟩, ⟨1, 1, 16⟩, ⟨14, 4, 4⟩, ⟨1, 1, 12⟩, ⟨14, 4, 39584⟩, ⟨1, 1, 1⟩], [⟨0, 1, 21⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 6045⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 4434⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 573⟩, ⟨1, 3, 6⟩, ⟨0, 1, 384⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 528⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 132⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 654⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 4143⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3384⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2418⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 1⟩]⟩ -- +1350 (step 24343, blks=83)
private def cfg_20 : MState := ⟨3, [⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 16⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 12⟩, ⟨14, 4, 72⟩, ⟨1, 1, 20⟩, ⟨14, 4, 51996⟩, ⟨1, 1, 1⟩], [⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 32⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 69⟩, ⟨0, 1, 135⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 654⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3624⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 768⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 123⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩ -- +1106 (step 25449, blks=109)
private def cfg_21 : MState := ⟨0, [⟨1, 1, 10⟩, ⟨0, 1, 1⟩, ⟨1, 1, 15⟩, ⟨13, 4, 1⟩, ⟨1, 1, 9⟩, ⟨14, 4, 12⟩, ⟨13, 4, 1⟩, ⟨1, 1, 16⟩, ⟨14, 4, 52840⟩, ⟨1, 1, 1⟩], [⟨0, 1, 3⟩, ⟨1, 3, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 426⟩, ⟨0, 1, 405⟩, ⟨1, 3, 3⟩, ⟨0, 1, 402⟩, ⟨1, 3, 3⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3624⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 768⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 123⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 1⟩]⟩ -- +1108 (step 26557, blks=102)
private def cfg_22 : MState := ⟨0, [⟨1, 1, 16⟩, ⟨0, 1, 1⟩, ⟨1, 1, 56240⟩], [⟨0, 1, 9⟩, ⟨1, 3, 87⟩, ⟨0, 1, 3⟩, ⟨1, 3, 351⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1038⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 303⟩, ⟨0, 1, 93⟩, ⟨1, 3, 69⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 768⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 123⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 1⟩]⟩ -- +1186 (step 27743, blks=129)
private def cfg_23 : MState := ⟨1, [⟨1, 1, 49⟩, ⟨14, 4, 8⟩, ⟨1, 1, 12⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨13, 4, 437⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 8⟩, ⟨14, 4, 152⟩, ⟨1, 1, 4⟩, ⟨14, 4, 56544⟩, ⟨1, 1, 1⟩], [⟨0, 1, 11⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 21⟩, ⟨1, 3, 75⟩, ⟨0, 1, 3⟩, ⟨1, 3, 45⟩, ⟨0, 1, 3⟩, ⟨1, 3, 87⟩, ⟨0, 1, 246⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 303⟩, ⟨0, 1, 93⟩, ⟨1, 3, 69⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 768⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 123⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩ -- +1101 (step 28844, blks=158)
private def cfg_24 : MState := ⟨3, [⟨7, 4, 164⟩, ⟨1, 1, 16⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 20⟩, ⟨14, 4, 36⟩, ⟨1, 1, 4⟩, ⟨14, 4, 32⟩, ⟨1, 1, 4⟩, ⟨14, 4, 72⟩, ⟨13, 4, 41⟩, ⟨13, 4, 33⟩, ⟨1, 1, 12⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 48⟩, ⟨13, 4, 117⟩, ⟨1, 1, 4⟩, ⟨14, 4, 57468⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 84⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 66⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 768⟩, ⟨1, 3, 3⟩, ⟨0, 1, 759⟩, ⟨1, 3, 123⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩ -- +1125 (step 29969, blks=149)
private def cfg_25 : MState := ⟨0, [⟨1, 1, 22⟩, ⟨0, 1, 1⟩, ⟨1, 1, 58911⟩, ⟨13, 4, 1⟩, ⟨1, 1, 1⟩], [⟨0, 1, 9⟩, ⟨1, 3, 72⟩, ⟨0, 1, 39⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 27⟩, ⟨0, 1, 3⟩, ⟨1, 3, 54⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 321⟩, ⟨1, 3, 24⟩, ⟨0, 1, 9⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 36⟩, ⟨0, 1, 48⟩, ⟨1, 3, 87⟩, ⟨0, 1, 3⟩, ⟨1, 3, 84⟩, ⟨0, 1, 3⟩, ⟨1, 3, 120⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1329 (step 31298, blks=155)
private def cfg_26 : MState := ⟨0, [⟨1, 1, 16⟩, ⟨0, 1, 1⟩, ⟨1, 1, 59824⟩], [⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 45⟩, ⟨0, 1, 3⟩, ⟨1, 3, 72⟩, ⟨0, 1, 18⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 12⟩, ⟨1, 3, 33⟩, ⟨0, 1, 9⟩, ⟨1, 3, 24⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 1575⟩, ⟨0, 1, 51⟩, ⟨1, 3, 6⟩, ⟨0, 1, 2103⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2154⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 216⟩, ⟨0, 1, 342⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1095⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 804⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 20520⟩, ⟨1, 3, 3⟩, ⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 1⟩]⟩ -- +1292 (step 32590, blks=155)
private def cfg_27 : MState := ⟨1, [⟨1, 1, 37⟩, ⟨14, 4, 8⟩, ⟨1, 1, 12⟩, ⟨14, 4, 68240⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 1, 1⟩, ⟨0, 1, 5⟩, ⟨1, 3, 12⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 45⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 51⟩, ⟨0, 1, 3⟩, ⟨1, 3, 102⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 93⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 36⟩, ⟨1, 3, 3⟩, ⟨0, 1, 159⟩, ⟨1, 3, 3⟩, ⟨0, 1, 36⟩, ⟨1, 3, 3⟩, ⟨0, 1, 42⟩, ⟨1, 3, 96⟩, ⟨0, 1, 3⟩, ⟨1, 3, 33⟩, ⟨0, 1, 3⟩, ⟨1, 3, 159⟩, ⟨0, 1, 306⟩, ⟨1, 3, 972⟩, ⟨0, 1, 1458⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 561⟩, ⟨0, 1, 3⟩, ⟨1, 3, 435⟩, ⟨0, 1, 216⟩, ⟨1, 3, 9⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 54⟩, ⟨0, 1, 3⟩, ⟨1, 3, 435⟩, ⟨0, 1, 195⟩, ⟨1, 3, 984⟩, ⟨0, 1, 342⟩, ⟨1, 3, 14322⟩, ⟨0, 1, 804⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 14157⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 1⟩]⟩ -- +1151 (step 33741, blks=195)
private def cfg_28 : MState := ⟨0, [⟨1, 1, 16⟩, ⟨0, 1, 1⟩, ⟨1, 1, 69284⟩], [⟨0, 1, 9⟩, ⟨1, 3, 12⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 18⟩, ⟨0, 1, 270⟩, ⟨1, 3, 6⟩, ⟨0, 1, 15⟩, ⟨1, 3, 18⟩, ⟨0, 1, 12⟩, ⟨1, 3, 957⟩, ⟨0, 1, 1458⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 561⟩, ⟨0, 1, 3⟩, ⟨1, 3, 435⟩, ⟨0, 1, 216⟩, ⟨1, 3, 9⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 54⟩, ⟨0, 1, 3⟩, ⟨1, 3, 435⟩, ⟨0, 1, 195⟩, ⟨1, 3, 984⟩, ⟨0, 1, 342⟩, ⟨1, 3, 14322⟩, ⟨0, 1, 804⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 14157⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 1⟩]⟩ -- +1211 (step 34952, blks=177)
private def cfg_29 : MState := ⟨3, [⟨7, 4, 8⟩, ⟨1, 1, 31⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 69908⟩, ⟨1, 1, 1⟩], [⟨1, 1, 1⟩, ⟨1, 3, 708⟩, ⟨0, 1, 1458⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 15⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 6⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 561⟩, ⟨0, 1, 3⟩, ⟨1, 3, 435⟩, ⟨0, 1, 216⟩, ⟨1, 3, 9⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 9⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 15⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 54⟩, ⟨0, 1, 3⟩, ⟨1, 3, 435⟩, ⟨0, 1, 195⟩, ⟨1, 3, 984⟩, ⟨0, 1, 342⟩, ⟨1, 3, 14322⟩, ⟨0, 1, 804⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 14157⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩ -- +1279 (step 36231, blks=186)
private def cfg_30 : MState := ⟨3, [⟨14, 4, 140⟩, ⟨1, 1, 1⟩, ⟨7, 4, 73835⟩, ⟨1, 1, 1⟩], [⟨0, 1, 11⟩, ⟨1, 3, 15⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 12⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 12⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 195⟩, ⟨0, 1, 3⟩, ⟨1, 3, 33⟩, ⟨0, 1, 180⟩, ⟨1, 3, 312⟩, ⟨0, 1, 3⟩, ⟨1, 3, 258⟩, ⟨0, 1, 342⟩, ⟨1, 3, 14322⟩, ⟨0, 1, 804⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 14157⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3846⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2274⟩, ⟨1, 3, 6⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩ -- +1244 (step 37475, blks=184)
private def cfg_31 : MState := ⟨1, [⟨1, 1, 74579⟩, ⟨13, 4, 1⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 18⟩, ⟨0, 1, 3⟩, ⟨1, 3, 78⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 6⟩, ⟨1, 3, 285⟩, ⟨0, 1, 3⟩, ⟨1, 3, 258⟩, ⟨0, 1, 342⟩, ⟨1, 3, 14322⟩, ⟨0, 1, 804⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 14157⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3846⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2274⟩, ⟨1, 3, 6⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 318⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 1⟩]⟩ -- +1143 (step 38618, blks=191)
private def cfg_32 : MState := ⟨3, [⟨14, 4, 13824⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 16⟩, ⟨14, 4, 8⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 12⟩, ⟨1, 1, 4⟩, ⟨14, 4, 40⟩, ⟨1, 1, 4⟩, ⟨14, 4, 44⟩, ⟨1, 1, 172⟩, ⟨14, 4, 180⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 344⟩, ⟨14, 4, 452⟩, ⟨1, 1, 4⟩, ⟨14, 4, 17124⟩, ⟨1, 1, 4⟩, ⟨14, 4, 57680⟩, ⟨1, 1, 1⟩], [⟨0, 1, 801⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 738⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2187⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 14157⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3846⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2274⟩, ⟨1, 3, 6⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 318⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 174⟩, ⟨1, 3, 6⟩, ⟨0, 1, 570⟩, ⟨1, 3, 1⟩]⟩ -- +1490 (step 40108, blks=202)
private def cfg_33 : MState := ⟨3, [⟨14, 4, 36⟩, ⟨1, 1, 24⟩, ⟨14, 4, 8⟩, ⟨1, 1, 8⟩, ⟨14, 4, 12⟩, ⟨13, 4, 5⟩, ⟨13, 4, 1⟩, ⟨1, 1, 12⟩, ⟨14, 4, 91952⟩, ⟨1, 1, 1⟩], [⟨1, 3, 60⟩, ⟨0, 1, 3⟩, ⟨1, 3, 126⟩, ⟨0, 1, 153⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 102⟩, ⟨0, 1, 69⟩, ⟨1, 3, 3⟩, ⟨0, 1, 5004⟩, ⟨1, 3, 6⟩, ⟨0, 1, 171⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 360⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1242⟩, ⟨1, 3, 6⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 33⟩, ⟨0, 1, 129⟩, ⟨1, 3, 135⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 258⟩, ⟨1, 3, 306⟩, ⟨0, 1, 33⟩, ⟨1, 3, 15⟩, ⟨0, 1, 69⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 10830⟩, ⟨1, 3, 3327⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3846⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2274⟩, ⟨1, 3, 6⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 318⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 174⟩, ⟨1, 3, 6⟩, ⟨0, 1, 570⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27807⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 342⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 570⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 1⟩]⟩ -- +1306 (step 41414, blks=211)
private def cfg_34 : MState := ⟨1, [⟨1, 1, 97919⟩, ⟨13, 4, 1⟩, ⟨1, 1, 1⟩], [⟨0, 1, 5⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 51⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 153⟩, ⟨0, 1, 48⟩, ⟨1, 3, 93⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 24⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 18⟩, ⟨1, 3, 705⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 33⟩, ⟨0, 1, 129⟩, ⟨1, 3, 135⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 258⟩, ⟨1, 3, 306⟩, ⟨0, 1, 33⟩, ⟨1, 3, 15⟩, ⟨0, 1, 69⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 942⟩, ⟨1, 3, 3⟩, ⟨0, 1, 444⟩, ⟨1, 3, 9441⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3324⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3846⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2274⟩, ⟨1, 3, 6⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 318⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 174⟩, ⟨1, 3, 6⟩, ⟨0, 1, 570⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27807⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 342⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 570⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 843⟩, ⟨1, 3, 3⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 8970⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 1⟩]⟩ -- +1143 (step 42557, blks=227)
private def cfg_end : MState := ⟨5, [⟨0, 1, 1⟩, ⟨1, 1, 5⟩, ⟨0, 1, 1⟩, ⟨1, 1, 20⟩, ⟨14, 4, 16⟩, ⟨13, 4, 29⟩, ⟨1, 1, 4⟩, ⟨14, 4, 36⟩, ⟨1, 1, 8⟩, ⟨14, 4, 84⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨13, 4, 13⟩, ⟨13, 4, 181⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 24⟩, ⟨1, 1, 4⟩, ⟨14, 4, 40⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨1, 1, 4⟩, ⟨14, 4, 4⟩, ⟨13, 4, 5⟩, ⟨1, 1, 4⟩, ⟨14, 4, 98016⟩, ⟨1, 1, 1⟩], [⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 150⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 489⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1392⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 15⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 24⟩, ⟨0, 1, 3⟩, ⟨1, 3, 27⟩, ⟨0, 1, 18⟩, ⟨1, 3, 705⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 12⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 9⟩, ⟨0, 1, 3⟩, ⟨1, 3, 30⟩, ⟨0, 1, 3⟩, ⟨1, 3, 33⟩, ⟨0, 1, 129⟩, ⟨1, 3, 135⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 258⟩, ⟨1, 3, 306⟩, ⟨0, 1, 33⟩, ⟨1, 3, 15⟩, ⟨0, 1, 69⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 276⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 486⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 129⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 237⟩, ⟨1, 3, 6⟩, ⟨0, 1, 942⟩, ⟨1, 3, 3⟩, ⟨0, 1, 444⟩, ⟨1, 3, 9441⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3324⟩, ⟨0, 1, 6⟩, ⟨1, 3, 3⟩, ⟨0, 1, 339⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 1410⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 633⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 3846⟩, ⟨1, 3, 3⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 2274⟩, ⟨1, 3, 6⟩, ⟨0, 1, 69⟩, ⟨1, 3, 6⟩, ⟨0, 1, 3⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 423⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 234⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 318⟩, ⟨1, 3, 3⟩, ⟨0, 1, 507⟩, ⟨1, 3, 3⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 48⟩, ⟨1, 3, 6⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 24⟩, ⟨1, 3, 3⟩, ⟨0, 1, 174⟩, ⟨1, 3, 6⟩, ⟨0, 1, 570⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27807⟩, ⟨1, 3, 3⟩, ⟨0, 1, 27⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 342⟩, ⟨1, 3, 6⟩, ⟨0, 1, 6⟩, ⟨1, 3, 6⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 570⟩, ⟨1, 3, 3⟩, ⟨0, 1, 297⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 108⟩, ⟨1, 3, 3⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 843⟩, ⟨1, 3, 3⟩, ⟨0, 1, 111⟩, ⟨1, 3, 6⟩, ⟨0, 1, 87⟩, ⟨1, 3, 3⟩, ⟨0, 1, 213⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 66⟩, ⟨1, 3, 3⟩, ⟨0, 1, 8970⟩, ⟨1, 3, 3⟩, ⟨0, 1, 45⟩, ⟨1, 3, 3⟩, ⟨0, 1, 192⟩, ⟨1, 3, 1⟩]⟩ -- +821 (step 43378, blks=231)

private lemma step_ckpt_0 : opt_mstate_beq (run_m_fast 1100 cfg_0) cfg_1 = true := by decide +kernel
private lemma step_ckpt_1 : opt_mstate_beq (run_m_fast 1102 cfg_1) cfg_2 = true := by decide +kernel
private lemma step_ckpt_2 : opt_mstate_beq (run_m_fast 1305 cfg_2) cfg_3 = true := by decide +kernel
private lemma step_ckpt_3 : opt_mstate_beq (run_m_fast 1360 cfg_3) cfg_4 = true := by decide +kernel
private lemma step_ckpt_4 : opt_mstate_beq (run_m_fast 1335 cfg_4) cfg_5 = true := by decide +kernel
private lemma step_ckpt_5 : opt_mstate_beq (run_m_fast 1165 cfg_5) cfg_6 = true := by decide +kernel
private lemma step_ckpt_6 : opt_mstate_beq (run_m_fast 1198 cfg_6) cfg_7 = true := by decide +kernel
private lemma step_ckpt_7 : opt_mstate_beq (run_m_fast 1439 cfg_7) cfg_8 = true := by decide +kernel
private lemma step_ckpt_8 : opt_mstate_beq (run_m_fast 1105 cfg_8) cfg_9 = true := by decide +kernel
private lemma step_ckpt_9 : opt_mstate_beq (run_m_fast 1323 cfg_9) cfg_10 = true := by decide +kernel
private lemma step_ckpt_10 : opt_mstate_beq (run_m_fast 1227 cfg_10) cfg_11 = true := by decide +kernel
private lemma step_ckpt_11 : opt_mstate_beq (run_m_fast 1472 cfg_11) cfg_12 = true := by decide +kernel
private lemma step_ckpt_12 : opt_mstate_beq (run_m_fast 1449 cfg_12) cfg_13 = true := by decide +kernel
private lemma step_ckpt_13 : opt_mstate_beq (run_m_fast 1472 cfg_13) cfg_14 = true := by decide +kernel
private lemma step_ckpt_14 : opt_mstate_beq (run_m_fast 1134 cfg_14) cfg_15 = true := by decide +kernel
private lemma step_ckpt_15 : opt_mstate_beq (run_m_fast 1196 cfg_15) cfg_16 = true := by decide +kernel
private lemma step_ckpt_16 : opt_mstate_beq (run_m_fast 1112 cfg_16) cfg_17 = true := by decide +kernel
private lemma step_ckpt_17 : opt_mstate_beq (run_m_fast 1499 cfg_17) cfg_18 = true := by decide +kernel
private lemma step_ckpt_18 : opt_mstate_beq (run_m_fast 1350 cfg_18) cfg_19 = true := by decide +kernel
private lemma step_ckpt_19 : opt_mstate_beq (run_m_fast 1106 cfg_19) cfg_20 = true := by decide +kernel
private lemma step_ckpt_20 : opt_mstate_beq (run_m_fast 1108 cfg_20) cfg_21 = true := by decide +kernel
private lemma step_ckpt_21 : opt_mstate_beq (run_m_fast 1186 cfg_21) cfg_22 = true := by decide +kernel
private lemma step_ckpt_22 : opt_mstate_beq (run_m_fast 1101 cfg_22) cfg_23 = true := by decide +kernel
private lemma step_ckpt_23 : opt_mstate_beq (run_m_fast 1125 cfg_23) cfg_24 = true := by decide +kernel
private lemma step_ckpt_24 : opt_mstate_beq (run_m_fast 1329 cfg_24) cfg_25 = true := by decide +kernel
private lemma step_ckpt_25 : opt_mstate_beq (run_m_fast 1292 cfg_25) cfg_26 = true := by decide +kernel
private lemma step_ckpt_26 : opt_mstate_beq (run_m_fast 1151 cfg_26) cfg_27 = true := by decide +kernel
private lemma step_ckpt_27 : opt_mstate_beq (run_m_fast 1211 cfg_27) cfg_28 = true := by decide +kernel
private lemma step_ckpt_28 : opt_mstate_beq (run_m_fast 1279 cfg_28) cfg_29 = true := by decide +kernel
private lemma step_ckpt_29 : opt_mstate_beq (run_m_fast 1244 cfg_29) cfg_30 = true := by decide +kernel
private lemma step_ckpt_30 : opt_mstate_beq (run_m_fast 1143 cfg_30) cfg_31 = true := by decide +kernel
private lemma step_ckpt_31 : opt_mstate_beq (run_m_fast 1490 cfg_31) cfg_32 = true := by decide +kernel
private lemma step_ckpt_32 : opt_mstate_beq (run_m_fast 1306 cfg_32) cfg_33 = true := by decide +kernel
private lemma step_ckpt_33 : opt_mstate_beq (run_m_fast 1143 cfg_33) cfg_34 = true := by decide +kernel
private lemma step_ckpt_end : opt_mstate_beq (run_m_fast 821 cfg_34) cfg_end = true := by decide +kernel

private lemma reach_34 : MReach cfg_34 cfg_end := mreach_base_fast step_ckpt_end
private lemma reach_33 : MReach cfg_33 cfg_end := mreach_step_fast step_ckpt_33 reach_34
private lemma reach_32 : MReach cfg_32 cfg_end := mreach_step_fast step_ckpt_32 reach_33
private lemma reach_31 : MReach cfg_31 cfg_end := mreach_step_fast step_ckpt_31 reach_32
private lemma reach_30 : MReach cfg_30 cfg_end := mreach_step_fast step_ckpt_30 reach_31
private lemma reach_29 : MReach cfg_29 cfg_end := mreach_step_fast step_ckpt_29 reach_30
private lemma reach_28 : MReach cfg_28 cfg_end := mreach_step_fast step_ckpt_28 reach_29
private lemma reach_27 : MReach cfg_27 cfg_end := mreach_step_fast step_ckpt_27 reach_28
private lemma reach_26 : MReach cfg_26 cfg_end := mreach_step_fast step_ckpt_26 reach_27
private lemma reach_25 : MReach cfg_25 cfg_end := mreach_step_fast step_ckpt_25 reach_26
private lemma reach_24 : MReach cfg_24 cfg_end := mreach_step_fast step_ckpt_24 reach_25
private lemma reach_23 : MReach cfg_23 cfg_end := mreach_step_fast step_ckpt_23 reach_24
private lemma reach_22 : MReach cfg_22 cfg_end := mreach_step_fast step_ckpt_22 reach_23
private lemma reach_21 : MReach cfg_21 cfg_end := mreach_step_fast step_ckpt_21 reach_22
private lemma reach_20 : MReach cfg_20 cfg_end := mreach_step_fast step_ckpt_20 reach_21
private lemma reach_19 : MReach cfg_19 cfg_end := mreach_step_fast step_ckpt_19 reach_20
private lemma reach_18 : MReach cfg_18 cfg_end := mreach_step_fast step_ckpt_18 reach_19
private lemma reach_17 : MReach cfg_17 cfg_end := mreach_step_fast step_ckpt_17 reach_18
private lemma reach_16 : MReach cfg_16 cfg_end := mreach_step_fast step_ckpt_16 reach_17
private lemma reach_15 : MReach cfg_15 cfg_end := mreach_step_fast step_ckpt_15 reach_16
private lemma reach_14 : MReach cfg_14 cfg_end := mreach_step_fast step_ckpt_14 reach_15
private lemma reach_13 : MReach cfg_13 cfg_end := mreach_step_fast step_ckpt_13 reach_14
private lemma reach_12 : MReach cfg_12 cfg_end := mreach_step_fast step_ckpt_12 reach_13
private lemma reach_11 : MReach cfg_11 cfg_end := mreach_step_fast step_ckpt_11 reach_12
private lemma reach_10 : MReach cfg_10 cfg_end := mreach_step_fast step_ckpt_10 reach_11
private lemma reach_9 : MReach cfg_9 cfg_end := mreach_step_fast step_ckpt_9 reach_10
private lemma reach_8 : MReach cfg_8 cfg_end := mreach_step_fast step_ckpt_8 reach_9
private lemma reach_7 : MReach cfg_7 cfg_end := mreach_step_fast step_ckpt_7 reach_8
private lemma reach_6 : MReach cfg_6 cfg_end := mreach_step_fast step_ckpt_6 reach_7
private lemma reach_5 : MReach cfg_5 cfg_end := mreach_step_fast step_ckpt_5 reach_6
private lemma reach_4 : MReach cfg_4 cfg_end := mreach_step_fast step_ckpt_4 reach_5
private lemma reach_3 : MReach cfg_3 cfg_end := mreach_step_fast step_ckpt_3 reach_4
private lemma reach_2 : MReach cfg_2 cfg_end := mreach_step_fast step_ckpt_2 reach_3
private lemma reach_1 : MReach cfg_1 cfg_end := mreach_step_fast step_ckpt_1 reach_2
private lemma reach_0 : MReach cfg_0 cfg_end := mreach_step_fast step_ckpt_0 reach_1


private lemma halt_cfg_end : is_halt_m cfg_end = true := by decide +kernel

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  rcases reach_0 with ⟨fuel, hfuel⟩
  rcases run_m_sound fuel cfg_0 cfg_end hfuel with ⟨n, hn⟩
  refine ⟨map_cfg_0155 (mstate_to_cfg cfg_end), ⟨n, ?_⟩, ?_⟩
  · have hinit : (init [] : Cfg (Fin 2) (Fin 6)) = map_cfg_0155 (mstate_to_cfg cfg_0) := rfl
    rw [hinit, multiStep_map_0155, hn]
    rfl
  · rw [step_map_0155, is_halt_m_sound cfg_end halt_cfg_end]
    rfl

-- END GOAL STATEMENT

end BusyBeaver.M_1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LDHHH
