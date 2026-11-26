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
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.Longitudinal


/-!
# Busy Beaver Machine `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => none
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 2, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Longitudinal

local notation "Γ" => Fin 2
local notation "Λ" => Fin 6

abbrev qA : Fin 6 := 0
abbrev qB : Fin 6 := 1
abbrev qC : Fin 6 := 2
abbrev qD : Fin 6 := 3
abbrev qE : Fin 6 := 4
abbrev qF : Fin 6 := 5

/-- Left-right mirror of `target_tm` (`1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC`). -/
abbrev mtm : Machine (Fin 2) (Fin 6) := flipTM target_tm

/-! ## Bounded Execution, Congruence & Binary Counter Helpers -/

def runSteps (M : Machine Γ Λ) :
    ℕ → BoundedConfig.BCfg Γ Λ → Option (BoundedConfig.BCfg Γ Λ)
  | 0, x => some x
  | n + 1, x => (BoundedConfig.step M x).bind (runSteps M n)

theorem runSteps_spec (M : Machine Γ Λ) (n : ℕ)
    (x x' : BoundedConfig.BCfg Γ Λ)
    (h : runSteps M n x = some x') (l₀ r₀ : ListBlank Γ) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢* (BoundedConfig.toCfg x' l₀ r₀) := by
  induction n generalizing x with
  | zero => cases h; exact stepStar_refl M _
  | succ n ih =>
    dsimp [runSteps] at h
    rcases hst : BoundedConfig.step M x with _ | y <;> rw [hst] at h
    · cases h
    · exact stepStar_trans ⟨1, BoundedConfig.step_spec M x hst l₀ r₀⟩ (ih y h)

theorem runSteps1_spec (M : Machine Γ Λ) (n : ℕ)
    (x x' : BoundedConfig.BCfg Γ Λ)
    (h : runSteps M (n + 1) x = some x') (l₀ r₀ : ListBlank Γ) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢⁺ (BoundedConfig.toCfg x' l₀ r₀) := by
  dsimp [runSteps] at h
  rcases hst : BoundedConfig.step M x with _ | y <;> rw [hst] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, BoundedConfig.step_spec M x hst l₀ r₀⟩
      (runSteps_spec M n y x' h l₀ r₀)

theorem segRLs_congr
    {ls₁ ls₁' ls₂ ls₂' : List (DH0 Γ Λ × DH0 Γ Λ)}
    {w₁ w₁' w₂ w₂' : List Γ}
    (h : SegRLs mtm ls₁ ls₂ w₁ w₂)
    (hls₁ : ls₁ = ls₁') (hls₂ : ls₂ = ls₂') (hw₁ : w₁ = w₁') (hw₂ : w₂ = w₂') :
    SegRLs mtm ls₁' ls₂' w₁' w₂' := by
  subst hls₁ hls₂ hw₁ hw₂; exact h

theorem sideRLs_congr
    {ls ls' : List (DH0 Γ Λ × DH0 Γ Λ)}
    {r₁ r₁' r₂ r₂' : ListBlank Γ}
    (h : SideRLs mtm ls r₁ r₂) (hls : ls = ls') (hr₁ : r₁ = r₁') (hr₂ : r₂ = r₂') :
    SideRLs mtm ls' r₁' r₂' := by
  subst hls hr₁ hr₂; exact h

theorem stepStar_congr {c₁ c₁' c₂ c₂' : Cfg Γ Λ}
    (h : c₁ [mtm]⊢* c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') :
    c₁' [mtm]⊢* c₂' := by
  subst hc₁ hc₂; exact h

theorem stepPlus_congr {c₁ c₁' c₂ c₂' : Cfg Γ Λ}
    (h : c₁ [mtm]⊢⁺ c₂) (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂') :
    c₁' [mtm]⊢⁺ c₂' := by
  subst hc₁ hc₂; exact h

theorem zeros_default : ∀ (k : ℕ), List.replicate k (0 : Γ) +> (default : ListBlank Γ) = default
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, append_cons, zeros_default k]
    change ListBlank.cons (default : ListBlank Γ).head (default : ListBlank Γ).tail = default
    exact ListBlank.cons_head_tail default

theorem zero_pow_default : ∀ (k : ℕ), ([0] : List Γ) ^ k +> (default : ListBlank Γ) = default
  | 0 => rfl
  | k + 1 => by
    rw [pow_succ_list, append_assoc, zero_pow_default k]
    exact zeros_default 1

theorem one_comm_11_pow : ∀ (n : ℕ), ([1] : List Γ) ++ ([1, 1] : List Γ) ^ n =
    ([1, 1] : List Γ) ^ n ++ [1]
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ_list, ← List.append_assoc,
      show ([1] ++ [1, 1] : List Γ) = [1, 1] ++ [1] from rfl,
      List.append_assoc, one_comm_11_pow n, List.append_assoc]

theorem one_comm_11_side (n : ℕ) (r : ListBlank Γ) :
    ([1] : List Γ) +> (([1, 1] : List Γ) ^ n +> r) =
      ([1, 1] : List Γ) ^ n +> (([1] : List Γ) +> r) := by
  rw [← append_assoc, one_comm_11_pow, append_assoc]

theorem pow2_pos (n : ℕ) : 0 < 2 ^ n := Nat.two_pow_pos n

/-- Complement-encoded left binary decrement counter (`BinaryCounter_v2.BinDec`). -/
def BinDec (d0 d1 : List Γ) : ℕ → ℕ → ListBlank Γ → ListBlank Γ
  | 0, _, l => l
  | len + 1, n, l =>
    (if n % 2 == 1 then d0 else d1) +> BinDec d0 d1 len (n / 2) l

theorem BinDec_O (d0 d1 : List Γ) (len : ℕ) (l : ListBlank Γ) :
    BinDec d0 d1 len 0 l = d1 ^ len +> l := by
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [BinDec, Nat.zero_mod, beq_iff_eq, zero_ne_one, ↓reduceIte, Nat.zero_div, ih,
      pow_succ_list, append_assoc]

theorem BinDec_full (d0 d1 : List Γ) (len : ℕ) (l : ListBlank Γ) :
    BinDec d0 d1 len (2 ^ len - 1) l = d0 ^ len +> l := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hp := pow2_pos len
    have hmod : ((2 ^ (len + 1) - 1) % 2 == 1) = true := by
      rw [beq_iff_eq, Nat.pow_succ]; omega
    have hdiv : (2 ^ (len + 1) - 1) / 2 = 2 ^ len - 1 := by
      rw [Nat.pow_succ]; omega
    simp only [BinDec, hmod, ↓reduceIte, hdiv, ih, pow_succ_list, append_assoc]

theorem BinDec_mulpow2sub1 (d0 d1 : List Γ) (L k z : ℕ) (l : ListBlank Γ) :
    d0 ^ z +> (d1 +> BinDec d0 d1 L k l) =
      BinDec d0 d1 (L + 1 + z) ((k * 2 + 1) * 2 ^ z - 1) l := by
  induction z with
  | zero =>
    have hm : ((k * 2 + 1) * 2 ^ 0 - 1) = k * 2 := by omega
    have hmod : ((k * 2) % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
    have hdiv : (k * 2) / 2 = k := by omega
    simp only [hm, BinDec, hmod, Bool.false_eq_true, ↓reduceIte, hdiv,
      pow_zero_list, append_nil]
  | succ z ih =>
    have hp : 0 < (k * 2 + 1) * 2 ^ z := Nat.mul_pos (by omega) (pow2_pos z)
    have hlen : L + 1 + (z + 1) = (L + 1 + z) + 1 := by omega
    have hm : (k * 2 + 1) * 2 ^ (z + 1) - 1 = ((k * 2 + 1) * 2 ^ z - 1) * 2 + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    have hmod : ((((k * 2 + 1) * 2 ^ z - 1) * 2 + 1) % 2 == 1) = true := by
      rw [beq_iff_eq]; omega
    have hdiv : (((k * 2 + 1) * 2 ^ z - 1) * 2 + 1) / 2 = (k * 2 + 1) * 2 ^ z - 1 := by omega
    rw [hlen, hm, BinDec, hmod, hdiv, ← ih, pow_succ_list, append_assoc]
    rfl

theorem BinDec_succ_split (d0 d1 : List Γ) (len n : ℕ) (l : ListBlank Γ)
    (h : 1 + n < 2 ^ len) :
    ∃ (m : ℕ) (l' : ListBlank Γ),
      BinDec d0 d1 len (1 + n) l = d1 ^ m +> (d0 +> l') ∧
      BinDec d0 d1 len n l = d0 ^ m +> (d1 +> l') := by
  induction len generalizing n with
  | zero => simp at h
  | succ len ih =>
    rw [Nat.pow_succ] at h
    rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
    · refine ⟨0, BinDec d0 d1 len q l, ?_, ?_⟩
      · have hmod : ((1 + 2 * q) % 2 == 1) = true := by rw [beq_iff_eq]; omega
        have hdiv : (1 + 2 * q) / 2 = q := by omega
        simp only [BinDec, hmod, ↓reduceIte, hdiv, pow_zero_list, append_nil]
      · have hmod : ((2 * q) % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
        have hdiv : (2 * q) / 2 = q := by omega
        simp only [BinDec, hmod, Bool.false_eq_true, ↓reduceIte, hdiv, pow_zero_list, append_nil]
    · obtain ⟨m, l', h1, h0⟩ := ih q (by omega)
      refine ⟨m + 1, l', ?_, ?_⟩
      · have hmod : ((1 + (2 * q + 1)) % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
        have hdiv : (1 + (2 * q + 1)) / 2 = 1 + q := by omega
        simp only [BinDec, hmod, Bool.false_eq_true, ↓reduceIte, hdiv, h1,
          pow_succ_list, append_assoc]
      · have hmod : ((2 * q + 1) % 2 == 1) = true := by rw [beq_iff_eq]; omega
        have hdiv : (2 * q + 1) / 2 = q := by omega
        simp only [BinDec, hmod, ↓reduceIte, hdiv, h0, pow_succ_list, append_assoc]

/-- Right binary increment counter (`BinaryCounter_v2.BinInc`). -/
def BinInc (d1 : List Γ) : ℕ → ListBlank Γ
  | 0 => default
  | k + 1 =>
    let m := k + 1
    (if m % 2 == 1 then d1 else List.replicate d1.length 0) +> BinInc d1 (m / 2)

theorem BinInc_O (d1 : List Γ) : BinInc d1 0 = default := by
  unfold BinInc; rfl

theorem BinInc_1 (d1 : List Γ) : BinInc d1 1 = d1 +> default := by
  rw [BinInc]; simp [BinInc_O]

theorem BinInc_mul2 (d1 : List Γ) (n : ℕ) :
    BinInc d1 (n * 2) = List.replicate d1.length 0 +> BinInc d1 n := by
  rcases n with _ | k
  · simp only [Nat.zero_mul, BinInc_O, zeros_default]
  · have hm : (k + 1) * 2 = (k * 2 + 1) + 1 := by omega
    have hmod : (((k * 2 + 1) + 1) % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
    have hdiv : ((k * 2 + 1) + 1) / 2 = k + 1 := by omega
    rw [hm, BinInc]
    simp only [hmod, Bool.false_eq_true, ↓reduceIte, hdiv]

theorem BinInc_mul2add1 (d1 : List Γ) (n : ℕ) :
    BinInc d1 (n * 2 + 1) = d1 +> BinInc d1 n := by
  have hmod : ((n * 2 + 1) % 2 == 1) = true := by rw [beq_iff_eq]; omega
  have hdiv : (n * 2 + 1) / 2 = n := by omega
  rw [BinInc]
  simp only [hmod, ↓reduceIte, hdiv]

theorem BinInc_mulpow2 (d1 : List Γ) (n u : ℕ) :
    BinInc d1 (n * 2 ^ u) = (List.replicate d1.length 0) ^ u +> BinInc d1 n := by
  induction u generalizing n with
  | zero => simp
  | succ u ih =>
    rw [show n * 2 ^ (u + 1) = (n * 2) * 2 ^ u by rw [Nat.pow_succ]; ring,
      ih (n * 2), BinInc_mul2, pow_succ_list', append_assoc]

theorem BinInc_succ_split (d1 : List Γ) : ∀ (n : ℕ),
    ∃ (m : ℕ) (r' : ListBlank Γ),
      BinInc d1 n = d1 ^ m +> (List.replicate d1.length 0 +> r') ∧
      BinInc d1 (1 + n) = (List.replicate d1.length 0) ^ m +> (d1 +> r')
  | n => by
    rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
    · refine ⟨0, BinInc d1 q, ?_, ?_⟩
      · rw [Nat.mul_comm 2 q, BinInc_mul2, pow_zero_list, append_nil]
      · rw [show 1 + 2 * q = q * 2 + 1 by omega, BinInc_mul2add1, pow_zero_list, append_nil]
    · have _hlt : q < 2 * q + 1 := by omega
      obtain ⟨m, r', h0, h1⟩ := BinInc_succ_split d1 q
      refine ⟨m + 1, r', ?_, ?_⟩
      · rw [show 2 * q + 1 = q * 2 + 1 by omega, BinInc_mul2add1, h0, pow_succ_list, append_assoc]
      · rw [show 1 + (2 * q + 1) = (1 + q) * 2 by omega, BinInc_mul2, h1,
          pow_succ_list, append_assoc]
termination_by n => n

/-! ## WallInvariant -/

namespace WallInvariant

def normal : List Bool → List Γ
  | [] => []
  | b :: bs => (if b then [1, 0, 0, 0, 0] else [0, 0, 0, 0, 0]) ++ normal bs

def shifted : List Bool → List Γ
  | [] => []
  | b :: bs => (if b then [0, 0, 0, 0, 1] else [0, 0, 0, 0, 0]) ++ shifted bs

def wall (w : List Γ) : Cfg Γ Λ :=
  (([0] : List Γ) +> (([1, 1] : List Γ) +> default)) {{qA}}> (w +> default)

def E (n : ℕ) (bs : List Bool) : Cfg Γ Λ :=
  wall (([1, 1] : List Γ) ^ n ++ shifted bs)

def Ed (n : ℕ) (bs : List Bool) : Cfg Γ Λ :=
  wall (([1, 1] : List Γ) ^ n ++ shifted bs ++ [0, 0, 0, 1, 0])

def O (n : ℕ) (bs : List Bool) : Cfg Γ Λ :=
  wall (([1, 1] : List Γ) ^ n ++ [1] ++ normal bs)

def Od (n : ℕ) (bs : List Bool) : Cfg Γ Λ :=
  wall (([1, 1] : List Γ) ^ n ++ [1] ++ normal bs ++ [0, 0, 0, 0, 1])

def marked (parity : ℕ) (bs : List Bool) : Prop :=
  ∃ pre post, bs = pre ++ true :: post ∧ pre.length % 2 = parity

def first_zero (bs : List Bool) : Prop :=
  ∃ rest, bs = false :: rest

inductive invariant : Cfg Γ Λ → Prop where
  | InvE {n : ℕ} {bs : List Bool} :
      bs.length + 2 ≤ n → marked 1 bs → invariant (E n bs)
  | InvEd {n : ℕ} {bs : List Bool} :
      bs.length + 3 ≤ n → invariant (Ed n bs)
  | InvO {n : ℕ} {bs : List Bool} :
      bs.length ≤ n → first_zero bs → true ∈ bs → invariant (O n bs)
  | InvOd {n : ℕ} {bs : List Bool} :
      bs.length + 1 ≤ n → first_zero bs → marked 0 bs → invariant (Od n bs)

end WallInvariant

/-! ## StrongInvariant -/

namespace StrongInvariant

def odd_first (bs : List Bool) : Prop :=
  ∃ u tail, bs = List.replicate (u * 2 + 1) false ++ true :: tail

def adjacent_first (bs : List Bool) : Prop :=
  ∃ u tail, 0 < u ∧ bs = List.replicate u false ++ true :: true :: tail

def close_even_first (bs : List Bool) : Prop :=
  ∃ a tail i, 0 < a ∧ bs = List.replicate (10 * a) false ++ true :: tail ∧
    bs.getD i false = true ∧ i % 2 = 1 ∧ i ≤ 14 * a + 3

def digit_guard (bs : List Bool) : Prop :=
  odd_first bs ∨ adjacent_first bs ∨ close_even_first bs

inductive strong : Cfg Γ Λ → Prop where
  | StrongE {n : ℕ} {bs : List Bool} :
      bs.length + 2 ≤ n → digit_guard bs → strong (WallInvariant.E n bs)
  | StrongEd {n : ℕ} {bs : List Bool} :
      (bs.length + 3 = n ∨ bs.length + 2 = n) →
      WallInvariant.marked 1 bs → strong (WallInvariant.Ed n bs)

theorem nth_true_split (bs : List Bool) (i : ℕ) (h : bs.getD i false = true) :
    ∃ pre post, bs = pre ++ true :: post ∧ pre.length = i := by
  induction bs generalizing i with
  | nil => simp [List.getD] at h
  | cons b bs ih =>
    rcases i with _ | i
    · dsimp [List.getD] at h
      subst h
      exact ⟨[], bs, rfl, rfl⟩
    · dsimp [List.getD] at h
      obtain ⟨pre, post, rfl, hlen⟩ := ih i h
      exact ⟨b :: pre, post, rfl, by simp [hlen]⟩

theorem nth_true_marked (bs : List Bool) (i : ℕ)
    (h : bs.getD i false = true) (hp : i % 2 = 1) :
    WallInvariant.marked 1 bs := by
  obtain ⟨pre, post, rfl, rfl⟩ := nth_true_split bs i h
  exact ⟨pre, post, rfl, hp⟩

theorem guard_marked (bs : List Bool) (h : digit_guard bs) :
    WallInvariant.marked 1 bs := by
  rcases h with ⟨u, tail, rfl⟩ | ⟨u, tail, _, rfl⟩ | ⟨a, tail, i, _, _, hbit, hodd, _⟩
  · exact ⟨List.replicate (u * 2 + 1) false, tail, rfl, by simp⟩
  · rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
    · exact ⟨List.replicate (2 * v) false ++ [true], tail, by simp, by simp⟩
    · exact ⟨List.replicate (2 * v + 1) false, true :: tail, rfl, by simp⟩
  · exact nth_true_marked bs i hbit hodd

theorem nth_append_true (bs cs : List Bool) (i : ℕ)
    (h : bs.getD i false = true) : (bs ++ cs).getD i false = true := by
  obtain ⟨pre, post, rfl, rfl⟩ := nth_true_split bs i h
  simp [List.getD]

theorem guard_append (bs cs : List Bool) (h : digit_guard bs) :
    digit_guard (bs ++ cs) := by
  rcases h with ⟨u, tail, rfl⟩ | ⟨u, tail, hu, rfl⟩ | ⟨a, tail, i, ha, heq, hbit, hodd, hbnd⟩
  · exact Or.inl ⟨u, tail ++ cs, by simp⟩
  · exact Or.inr (Or.inl ⟨u, tail ++ cs, hu, by simp⟩)
  · refine Or.inr (Or.inr ⟨a, tail ++ cs, i, ha, ?_, nth_append_true bs cs i hbit, hodd, hbnd⟩)
    rw [heq]; simp

theorem initial_guard : digit_guard [false, true, false, true] :=
  Or.inl ⟨0, [false, true], rfl⟩

end StrongInvariant

/-! ## LocalPasses -/

namespace LocalPasses

abbrev ld : List Γ := [1, 1]
abbrev d0 : List Γ := [0, 0, 0, 0, 0]
abbrev d1 : List Γ := [1, 0, 0, 0, 0]
abbrev d1' : List Γ := [0, 0, 0, 0, 1]

abbrev hR : DH0 Γ Λ := (qA, [0])
abbrev hRx : DH0 Γ Λ := (qC, [])
abbrev hL : DH0 Γ Λ := (qC, [0])
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [(hR, hL)]
abbrev hx : List (DH0 Γ Λ × DH0 Γ Λ) := [(hRx, hL)]
abbrev hR' : DH0 Γ Λ := (qA, [])
abbrev hL' : DH0 Γ Λ := (qB, [])
abbrev h' : List (DH0 Γ Λ × DH0 Γ Λ) := [(hR', hL')]
abbrev lh : ListBlank Γ := [1, 1] +> default

theorem am_helper {hs : List (DH0 Γ Λ × DH0 Γ Λ)} {w₁ w₂ : List Γ}
    (a a' k b b' : ℕ)
    (hb : SegRLs mtm (hs ^ b) (hs ^ b') w₁ w₂)
    (ha : SegRLs mtm (hs ^ a) (hs ^ a') w₂ w₂) :
    SegRLs mtm (hs ^ (k * a + b)) (hs ^ (k * a' + b')) w₁ w₂ :=
  SegRLs.addmul_v2 hb ha

theorem ld_Incs (k : ℕ) : SegRLs mtm (h ^ k) (h ^ (k * 2)) ld ld := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := h) (a := 1) (a' := 2) (x := k) (b := 0) (b' := 0)
    (.nil ld) (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem d0_Incs (k : ℕ) : SegRLs mtm (h' ^ (k * 2)) (h' ^ k) d0 d0 := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := h') (a := 2) (a' := 1) (x := k) (b := 0) (b' := 0)
    (.nil d0) (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem d01_Incs (k : ℕ) : SegRLs mtm (h' ^ (k * 2 + 1)) (h' ^ k) d0 d1 := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := h') (a := 2) (a' := 1) (x := k) (b := 1) (b' := 0)
    (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))
    (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem d10_Incs (k : ℕ) : SegRLs mtm (h' ^ (k * 2 + 1)) (h' ^ (k + 1)) d1 d0 := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := h') (a := 2) (a' := 1) (x := k) (b := 1) (b' := 1)
    (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))
    (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem d1_Incs (k : ℕ) : SegRLs mtm (h' ^ (k * 2)) (h' ^ k) d1 d1 := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := h') (a := 2) (a' := 1) (x := k) (b := 0) (b' := 0)
    (.nil d1) (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem m0_Incs (k : ℕ) : SegRLs mtm (h ^ k) (h' ^ k) [] [] := by
  refine SegRLs.wall_pow ?_ k
  exact BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem lds_Incs (k n : ℕ) : SegRLs mtm (h ^ k) (h ^ (k * 2 ^ n)) (ld ^ n) (ld ^ n) := by
  induction n with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one, pow_zero_list]
    exact SegRLs.empty mtm _
  | succ n ih =>
    rw [pow_succ_list', show k * 2 ^ (n + 1) = (k * 2 ^ n) * 2 by rw [Nat.pow_succ]; ring]
    exact ih.concat (ld_Incs (k * 2 ^ n))

theorem d0s_Incs (k n : ℕ) : SegRLs mtm (h' ^ (k * 2 ^ n)) (h' ^ k) (d0 ^ n) (d0 ^ n) := by
  induction n generalizing k with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one, pow_zero_list]
    exact SegRLs.empty mtm _
  | succ n ih =>
    rw [pow_succ_list, show k * 2 ^ (n + 1) = (k * 2 ^ n) * 2 by rw [Nat.pow_succ]; ring]
    exact (d0_Incs (k * 2 ^ n)).concat (ih k)

theorem d01s_Incs (k n : ℕ) :
    SegRLs mtm (h' ^ ((k + 1) * 2 ^ n - 1)) (h' ^ k) (d0 ^ n) (d1 ^ n) := by
  induction n generalizing k with
  | zero =>
    rw [show (k + 1) * 2 ^ 0 - 1 = k by omega, pow_zero_list]
    exact SegRLs.empty mtm _
  | succ n ih =>
    have hp : 0 < (k + 1) * 2 ^ n := Nat.mul_pos (by omega) (pow2_pos n)
    have heq : (k + 1) * 2 ^ (n + 1) - 1 = ((k + 1) * 2 ^ n - 1) * 2 + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [heq, pow_succ_list, pow_succ_list]
    exact (d01_Incs ((k + 1) * 2 ^ n - 1)).concat (ih k)

theorem BigStep {r r' : ListBlank Γ} (H : SideRLs mtm (h ^ 1) r r') :
    (toDHCfg (hR, .right) lh r) [mtm]⊢⁺ (toDHCfg (hR, .right) lh ([1] +> r')) := by
  rw [pow_one_list] at H
  have h1 := H.elim_single lh
  have h2 : (toDHCfg (hL, .left) lh r') [mtm]⊢* (toDHCfg (hR, .right) lh ([1] +> r')) := by
    have hs := runSteps_spec mtm 11 ⟨[0], [1, 1, 0], qC, .left⟩
      ⟨[0, 1, 1], [1], qA, .right⟩ (by decide) default r'
    have hd : ([1, 1, 0] : List Γ) +> (default : ListBlank Γ) = lh := by
      rw [show ([1, 1, 0] : List Γ) = [1, 1] ++ [0] from rfl, append_assoc,
        BoundedConfig.all0_spec (a := [0]) (by decide)]
    have hl : ([0, 1, 1] : List Γ) +> (default : ListBlank Γ) = [0] +> lh := rfl
    simpa only [BoundedConfig.toCfg, toDHCfg, hd, hl] using hs
  exact stepPlus_stepStar_trans h1 h2

end LocalPasses

/-! ## OddNormal -/

namespace OddNormal

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev b : List Γ := [1, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev d : List Γ := [0, 0, 0, 1, 0]
abbrev ld : List Γ := [1, 1]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]
abbrev y : List (DH0 Γ Λ × DH0 Γ Λ) := [((qD, []), (qB, []))]
abbrev hx : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qC, [0]))]
abbrev one : List Γ := [1]
abbrev z3 : List Γ := [0, 0, 0]

theorem c_zero_even (k : ℕ) : SegRLs mtm (x ^ (k * 2)) (x ^ k) a a := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := x) (a := 2) (a' := 1) (x := k) (b := 0) (b' := 0)
    (.nil a) (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem c_zero_odd (k : ℕ) : SegRLs mtm (x ^ (k * 2 + 1)) (x ^ k) a c := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := x) (a := 2) (a' := 1) (x := k) (b := 1) (b' := 0)
    (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))
    (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem d_zero_even (k : ℕ) : SegRLs mtm (y ^ (k * 2)) (y ^ k) a a := by
  simpa using SegRLs.addmul_v2 (M := mtm) (h := y) (a := 2) (a' := 1) (x := k) (b := 0) (b' := 0)
    (.nil a) (BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide))

theorem one_pair : SegRLs mtm (h ^ 2) x one one :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem one_pairs (k : ℕ) : SegRLs mtm (h ^ (k * 2)) (x ^ k) one one := by
  induction k with
  | zero => exact .nil one
  | succ k ih =>
    rw [show (k + 1) * 2 = 2 + k * 2 by omega, pow_add_list, pow_succ_list x]
    exact one_pair.trans ih

theorem c_zeros_allones (k n : ℕ) :
    SegRLs mtm (x ^ ((k + 1) * 2 ^ n - 1)) (x ^ k) (a ^ n) (c ^ n) := by
  induction n generalizing k with
  | zero =>
    rw [show (k + 1) * 2 ^ 0 - 1 = k by omega, pow_zero_list]
    exact SegRLs.empty mtm _
  | succ n ih =>
    have hp : 0 < (k + 1) * 2 ^ n := Nat.mul_pos (by omega) (pow2_pos n)
    have heq : (k + 1) * 2 ^ (n + 1) - 1 = ((k + 1) * 2 ^ n - 1) * 2 + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [heq, pow_succ_list, pow_succ_list]
    exact (c_zero_odd ((k + 1) * 2 ^ n - 1)).concat (ih k)

theorem prime_first (u : ℕ) :
    SegRLs mtm (h ^ ((2 ^ u - 1) * 2)) [] (one ++ a ^ u) (one ++ c ^ u) := by
  have hc := c_zeros_allones 0 u
  simp only [Nat.zero_add, Nat.one_mul, pow_zero_list] at hc
  exact (one_pairs (2 ^ u - 1)).concat hc

theorem one_expand (k : ℕ) :
    SegRLs mtm (h ^ (1 + k)) (hx ++ h ^ (1 + k * 2)) one ld := by
  have h1 : SegRLs mtm h (hx ++ h) one ld :=
    BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)
  have h2 := h1.trans (LocalPasses.ld_Incs k)
  refine segRLs_congr h2 ?_ ?_ rfl rfl
  · rw [Nat.add_comm 1 k, pow_succ_list]
  · rw [List.append_assoc, Nat.add_comm 1 (k * 2), pow_succ_list]

theorem first_conversion (u : ℕ) :
    SegRLs mtm hx [] (c ^ u ++ b) (one ^ (5 * u + 1) ++ z3) := by
  induction u with
  | zero => exact BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)
  | succ u ih =>
    have h1 : SegRLs mtm hx hx c (one ^ 5) :=
      BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)
    refine segRLs_congr (h1.concat ih) rfl rfl ?_ ?_
    · rw [pow_succ_list, List.append_assoc]
    · rw [show 5 * (u + 1) + 1 = 5 + (5 * u + 1) by omega]
      conv_rhs => rw [pow_add_list, List.append_assoc]

theorem odd_first_reduction (u k : ℕ) (r r' : ListBlank Γ)
    (H : SideRLs mtm (h ^ (1 + k * 2)) (one ^ (5 * u + 1) +> (z3 +> r)) r') :
    SideRLs mtm (h ^ ((2 ^ u - 1) * 2 + (1 + k)))
      (one +> (a ^ u +> (b +> r))) (ld +> r') := by
  rw [pow_add_list]
  have s1 : SideRLs mtm (h ^ ((2 ^ u - 1) * 2))
      (one +> (a ^ u +> (b +> r))) (one +> (c ^ u +> (b +> r))) := by
    have hs := (prime_first u).sideRLs_concat (.nil (b +> r))
    simpa only [append_assoc] using hs
  have s2_conv : SideRLs mtm hx (c ^ u +> (b +> r)) (one ^ (5 * u + 1) +> (z3 +> r)) := by
    have hs := (first_conversion u).sideRLs_concat (.nil r)
    simpa only [append_assoc] using hs
  have s2 := (one_expand k).sideRLs_concat (s2_conv.trans H)
  exact s1.trans s2

end OddNormal

/-! ## Elementary Shift Loops & CounterRules -/

section ShiftPrimitives

theorem shift_C_1_step (l r : ListBlank Γ) :
    (([1] +> l) <{{qC}} ([0] +> r)) [mtm]⊢* (l <{{qC}} ([0] +> ([1] +> r))) := by
  have h := runSteps_spec mtm 3 ⟨[0], [1], qC, .left⟩ ⟨[0, 1], [], qC, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_cons] using h

theorem shift_C_1_left (k : ℕ) (l r : ListBlank Γ) :
    (([1] ^ k +> l) <{{qC}} ([0] +> r)) [mtm]⊢* (l <{{qC}} ([0] +> ([1] ^ k +> r))) := by
  induction k generalizing r with
  | zero => exact stepStar_refl mtm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_1_step ([1] ^ k +> l) r) ?_
    refine stepStar_congr (ih ([1] +> r)) rfl ?_
    rw [← append_assoc ([1] ^ k) [1] r, ← pow_succ_list', pow_succ_list, append_assoc]

theorem shift_A_11_step (l r : ListBlank Γ) :
    (l {{qA}}> ([1, 1] +> r)) [mtm]⊢* (([0, 1] +> l) {{qA}}> r) := by
  have h := runSteps_spec mtm 2 ⟨[], [1, 1], qA, .right⟩ ⟨[0, 1], [], qA, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

theorem shift_A_11_right (k : ℕ) (l r : ListBlank Γ) :
    (l {{qA}}> ([1, 1] ^ k +> r)) [mtm]⊢* (([0, 1] ^ k +> l) {{qA}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl mtm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_A_11_step l ([1, 1] ^ k +> r)) ?_
    refine stepStar_congr (ih ([0, 1] +> l)) rfl ?_
    rw [← append_assoc, ← pow_succ_list']

theorem shift_A_rd1_step (l r : ListBlank Γ) :
    (l {{qA}}> ([1, 0, 0, 0, 0] +> r)) [mtm]⊢* ((([1] : List Γ) ^ 5 +> l) {{qA}}> r) := by
  have h := runSteps_spec mtm 5 ⟨[], [1, 0, 0, 0, 0], qA, .right⟩
    ⟨[1, 1, 1, 1, 1], [], qA, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil,
    show ([1, 1, 1, 1, 1] : List Γ) = ([1] : List Γ) ^ 5 from rfl] using h

theorem shift_A_rd1_right (k : ℕ) (l r : ListBlank Γ) :
    (l {{qA}}> ([1, 0, 0, 0, 0] ^ k +> r)) [mtm]⊢* ((([1] : List Γ) ^ (k * 5) +> l) {{qA}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl mtm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_A_rd1_step l ([1, 0, 0, 0, 0] ^ k +> r)) ?_
    refine stepStar_congr (ih (([1] : List Γ) ^ 5 +> l)) rfl ?_
    rw [← append_assoc, ← pow_add_list, show k * 5 + 5 = (k + 1) * 5 by omega]

theorem shift_B_1_step (l r : ListBlank Γ) :
    (([1] +> l) <{{qB}} r) [mtm]⊢* (l <{{qB}} ([0] +> r)) := by
  have h := runSteps_spec mtm 1 ⟨[], [1], qB, .left⟩ ⟨[0], [], qB, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

theorem shift_B_1_left (k : ℕ) (l r : ListBlank Γ) :
    (([1] ^ k +> l) <{{qB}} r) [mtm]⊢* (l <{{qB}} ([0] ^ k +> r)) := by
  induction k generalizing r with
  | zero => exact stepStar_refl mtm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_B_1_step ([1] ^ k +> l) r) ?_
    refine stepStar_congr (ih ([0] +> r)) rfl ?_
    rw [← append_assoc ([0] ^ k) [0] r, ← pow_succ_list']

theorem ones_even_pow (n : ℕ) : ([1] : List Γ) ^ (n * 2) = ([1, 1] : List Γ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show (n + 1) * 2 = 2 + n * 2 by omega, pow_add_list, ih]
    rfl

theorem zeros5_pow (n : ℕ) : ([0] : List Γ) ^ (n * 5) = ([0, 0, 0, 0, 0] : List Γ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show (n + 1) * 5 = 5 + n * 5 by omega, pow_add_list, ih]
    rfl

theorem B_01_to_C (l r : ListBlank Γ) :
    (([0, 1] +> l) <{{qB}} r) [mtm]⊢⁺ (l <{{qC}} ([0, 1] +> r)) := by
  have h := runSteps1_spec mtm 3 ⟨[], [0, 1], qB, .left⟩ ⟨[0, 1], [], qC, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

end ShiftPrimitives

namespace CounterRules

abbrev ld0 : List Γ := [0, 1]
abbrev ld1 : List Γ := [1, 1]
abbrev ldh : ListBlank Γ := [1] +> default
abbrev rd0 : List Γ := [0, 0, 0, 0, 0]
abbrev rd1 : List Γ := [1, 0, 0, 0, 0]

def LC (len n : ℕ) : ListBlank Γ := BinDec ld0 ld1 len n ldh
def RC (n : ℕ) : ListBlank Γ := BinInc rd1 n

abbrev rGate (l r : ListBlank Γ) : Cfg Γ Λ := ([0, 1] +> l) {{qA}}> r
abbrev lGate (l r : ListBlank Γ) : Cfg Γ Λ := l <{{qC}} ([0, 1] +> r)

theorem left_increment (l r : ListBlank Γ) (n : ℕ) :
    (lGate (ld1 ^ n +> (ld0 +> l)) r) [mtm]⊢⁺ (rGate (ld0 ^ n +> (ld1 +> l)) r) := by
  have h1 : (lGate (ld1 ^ n +> (ld0 +> l)) r) [mtm]⊢*
      ((ld0 +> l) <{{qC}} ([0, 1] +> (ld1 ^ n +> r))) := by
    have hs := shift_C_1_left (n * 2) (ld0 +> l) ([1] +> r)
    rw [ones_even_pow] at hs
    refine stepStar_congr hs rfl ?_
    rw [show ([0] +> (ld1 ^ n +> ([1] +> r))) = [0] +> (([1] +> (ld1 ^ n +> r))) by
      rw [one_comm_11_side]]
    rfl
  have h2 : ((ld0 +> l) <{{qC}} ([0, 1] +> (ld1 ^ n +> r))) [mtm]⊢⁺
      (([0, 1] +> (ld1 +> l)) {{qA}}> (ld1 ^ n +> r)) := by
    have hs := runSteps1_spec mtm 4 ⟨[0, 1], [0, 1], qC, .left⟩
      ⟨[0, 1, 1, 1], [], qA, .right⟩ (by decide) l (ld1 ^ n +> r)
    simpa only [BoundedConfig.toCfg, append_nil,
      show ([0, 1, 1, 1] : List Γ) +> l = [0, 1] +> (ld1 +> l) from rfl] using hs
  have h3 := shift_A_11_right n ([0, 1] +> (ld1 +> l)) r
  have h3_eq : (ld0 ^ n +> ([0, 1] +> (ld1 +> l))) = ([0, 1] +> (ld0 ^ n +> (ld1 +> l))) := by
    change (ld0 ^ n +> (ld0 +> (ld1 +> l))) = (ld0 +> (ld0 ^ n +> (ld1 +> l)))
    rw [← append_assoc, ← pow_succ_list', pow_succ_list, append_assoc]
  exact stepStar_stepPlus_trans h1
    (stepPlus_stepStar_trans h2 (stepStar_congr h3 rfl (by rw [h3_eq])))

theorem right_increment (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ n +> ([0] +> r))) [mtm]⊢⁺ (lGate l (rd0 ^ n +> ([1] +> r))) := by
  have h1 := shift_A_rd1_right n ([0, 1] +> l) ([0] +> r)
  have h2 : (([1] ^ (n * 5) +> ([0, 1] +> l)) {{qA}}> ([0] +> r)) [mtm]⊢⁺
      (([1] ^ (n * 5) +> ([0, 1] +> l)) <{{qB}} ([1] +> r)) := by
    have hs := runSteps1_spec mtm 0 ⟨[], [0], qA, .right⟩ ⟨[1], [], qB, .left⟩ (by decide)
      ([1] ^ (n * 5) +> ([0, 1] +> l)) r
    simpa only [BoundedConfig.toCfg, append_nil] using hs
  have h3 := shift_B_1_left (n * 5) ([0, 1] +> l) ([1] +> r)
  rw [zeros5_pow] at h3
  have h4 := B_01_to_C l (rd0 ^ n +> ([1] +> r))
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans h2 (stepStar_stepPlus_trans h3 h4))

theorem left_overflow (r : ListBlank Γ) (n : ℕ) :
    (lGate (ld1 ^ n +> ldh) r) [mtm]⊢⁺ (rGate (ld0 ^ n +> ldh) ([1] +> r)) := by
  have h1 : (lGate (ld1 ^ n +> ldh) r) [mtm]⊢*
      (default <{{qC}} ([0, 1, 1] +> (ld1 ^ n +> r))) := by
    have hs := shift_C_1_left (n * 2 + 1) default ([1] +> r)
    have hl : ([1] : List Γ) ^ (n * 2 + 1) +> (default : ListBlank Γ) = ld1 ^ n +> ldh := by
      rw [pow_succ_list', ones_even_pow, append_assoc]
    have hr : ([0] +> (([1] : List Γ) ^ (n * 2 + 1) +> ([1] +> r))) =
        [0, 1, 1] +> (ld1 ^ n +> r) := by
      rw [pow_succ_list ([1] : List Γ), ones_even_pow, append_assoc, ← one_comm_11_side]
      rfl
    exact stepStar_congr hs (by rw [hl]; rfl) (by rw [hr])
  have h2 : (default <{{qC}} ([0, 1, 1] +> (ld1 ^ n +> r))) [mtm]⊢⁺
      (([0, 1] +> ldh) {{qA}}> (ld1 ^ n +> ([1] +> r))) := by
    have hs' := runSteps1_spec mtm 4 ⟨[0, 1], [0], qC, .left⟩
      ⟨[0, 1, 1], [], qA, .right⟩ (by decide) default ([1] +> (ld1 ^ n +> r))
    have hd : ([0] : List Γ) +> (default : ListBlank Γ) = default := zeros_default 1
    have h_comm : [1] +> (ld1 ^ n +> r) = ld1 ^ n +> ([1] +> r) := one_comm_11_side n r
    have h_in : [0, 1] +> (ld1 ^ n +> ([1] +> r)) = [0, 1, 1] +> (ld1 ^ n +> r) := by
      rw [← h_comm]; rfl
    have h_out : ([0, 1, 1] : List Γ) +> (default : ListBlank Γ) = [0, 1] +> ldh := rfl
    simpa only [BoundedConfig.toCfg, append_nil, hd, h_comm, h_in, h_out] using hs'
  have h3 := shift_A_11_right n ([0, 1] +> ldh) ([1] +> r)
  have h3_eq : (ld0 ^ n +> ([0, 1] +> ldh)) = ([0, 1] +> (ld0 ^ n +> ldh)) := by
    change (ld0 ^ n +> (ld0 +> ldh)) = (ld0 +> (ld0 ^ n +> ldh))
    rw [← append_assoc, ← pow_succ_list', pow_succ_list, append_assoc]
  exact stepStar_stepPlus_trans h1
    (stepPlus_stepStar_trans h2 (stepStar_congr h3 rfl (by rw [h3_eq])))

theorem left_counter (len n : ℕ) (r : ListBlank Γ) (h : 1 + n < 2 ^ len) :
    (lGate (LC len (1 + n)) r) [mtm]⊢⁺ (rGate (LC len n) r) := by
  obtain ⟨m, l', h1, h0⟩ := BinDec_succ_split ld0 ld1 len n ldh h
  unfold LC
  rw [h1, h0]
  exact left_increment l' r m

theorem right_counter (n : ℕ) (l : ListBlank Γ) :
    (rGate l (RC n)) [mtm]⊢⁺ (lGate l (RC (1 + n))) := by
  obtain ⟨m, r', h0, h1⟩ := BinInc_succ_split rd1 n
  unfold RC
  rw [h0, h1]
  dsimp only [List.length]
  have h_in : rd1 ^ m +> (List.replicate 5 (0 : Γ) +> r') =
      rd1 ^ m +> ([0] +> ([0, 0, 0, 0] +> r')) := rfl
  have h_out : (List.replicate 5 (0 : Γ)) ^ m +> (rd1 +> r') =
      rd0 ^ m +> ([1] +> ([0, 0, 0, 0] +> r')) := rfl
  rw [h_in, h_out]
  exact right_increment l ([0, 0, 0, 0] +> r') m

theorem counter_round (len n m : ℕ) (h : 1 + n < 2 ^ len) :
    (rGate (LC len (1 + n)) (RC m)) [mtm]⊢⁺ (rGate (LC len n) (RC (1 + m))) :=
  stepPlus_trans (right_counter m (LC len (1 + n))) (left_counter len n (RC (1 + m)) h)

theorem counter_rounds (len n m k : ℕ) (h : n + k < 2 ^ len) :
    (rGate (LC len (n + k)) (RC m)) [mtm]⊢* (rGate (LC len n) (RC (m + k))) := by
  induction k generalizing n m with
  | zero => simp only [Nat.add_zero]; exact stepStar_refl mtm _
  | succ k ih =>
    rw [show n + (k + 1) = 1 + (n + k) by omega, show m + (k + 1) = (1 + m) + k by omega]
    exact stepStar_trans (stepPlus_to_stepStar (counter_round len (n + k) m (by omega)))
      (ih n (1 + m) (by omega))

end CounterRules

/-! ## CounterBatch -/

namespace CounterBatch

open CounterRules

abbrev p : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, []), (qB, []))]

theorem left_one (len k : ℕ) (hk : 1 + k < 2 ^ len) :
    SideLR mtm (qB, []) (qA, []) ([0, 1] +> LC len (1 + k)) ([0, 1] +> LC len k) := by
  intro r
  exact stepPlus_trans (B_01_to_C (LC len (1 + k)) r) (left_counter len k r hk)

theorem left_one_flip (len k : ℕ) (hk : 1 + k < 2 ^ len) :
    SideRL (flipTM mtm) (qB, []) (qA, []) ([0, 1] +> LC len (1 + k)) ([0, 1] +> LC len k) := by
  intro r
  exact toDHCfg_stepPlus_flip (left_one len k hk r)

theorem left_batch (len k amount : ℕ) (hk : k + amount < 2 ^ len) :
    SideRLs (flipTM mtm) ([((qB, []), (qA, []))] ^ amount)
      ([0, 1] +> LC len (k + amount)) ([0, 1] +> LC len k) := by
  induction amount generalizing k with
  | zero =>
    simp only [Nat.add_zero, pow_zero_list]
    exact .nil _
  | succ amount ih =>
    rw [show k + (amount + 1) = 1 + (k + amount) by omega, pow_succ_list]
    exact .cons (left_one_flip len (k + amount) (by omega)) (ih k (by omega))

theorem right_pass_batch (len k amount : ℕ) (r r' : ListBlank Γ)
    (hk : k + amount < 2 ^ len) (hr : SideRLs mtm (p ^ amount) r r') :
    (rGate (LC len (k + amount)) r) [mtm]⊢* (rGate (LC len k) r') :=
  SideRLs.concat_1 hr (left_batch len k amount hk)

end CounterBatch

/-! ## CounterFinish -/

namespace CounterFinish

open CounterRules

theorem return_wall (n : ℕ) (r : ListBlank Γ) :
    (lGate (LC n 0) r) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> ([1] +> ([1, 1] ^ n +> r))) := by
  unfold LC
  rw [BinDec_O]
  have h1 : (lGate (ld1 ^ n +> ldh) r) [mtm]⊢*
      (default <{{qC}} ([0, 1] +> ([1] +> (ld1 ^ n +> r)))) := by
    have hs := shift_C_1_left (n * 2 + 1) default ([1] +> r)
    have hl : ([1] : List Γ) ^ (n * 2 + 1) +> (default : ListBlank Γ) = ld1 ^ n +> ldh := by
      rw [pow_succ_list', ones_even_pow, append_assoc]
    have hr : ([0] +> (([1] : List Γ) ^ (n * 2 + 1) +> ([1] +> r))) =
        [0, 1] +> ([1] +> (ld1 ^ n +> r)) := by
      rw [pow_succ_list ([1] : List Γ), ones_even_pow, append_assoc, ← one_comm_11_side]
      rfl
    exact stepStar_congr hs (by rw [hl]; rfl) (by rw [hr])
  have h2 : (default <{{qC}} ([0, 1] +> ([1] +> (ld1 ^ n +> r)))) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> ([1] +> (ld1 ^ n +> r))) := by
    have hs := runSteps1_spec mtm 4 ⟨[0, 1], [0], qC, .left⟩
      ⟨[0, 1, 1], [], qA, .right⟩ (by decide) default ([1] +> (ld1 ^ n +> r))
    have hd : ([0] : List Γ) +> (default : ListBlank Γ) = default := zeros_default 1
    have hl : ([0, 1, 1] : List Γ) +> (default : ListBlank Γ) = [0] +> LocalPasses.lh := rfl
    simpa only [BoundedConfig.toCfg, append_nil, hd, hl] using hs
  exact stepStar_stepPlus_trans h1 h2

theorem counter_finish (n k r : ℕ) (hk : k < 2 ^ n) :
    (rGate (LC n k) (RC r)) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> ([1] +> ([1, 1] ^ n +> RC (r + k + 1)))) := by
  have h1 : (rGate (LC n k) (RC r)) [mtm]⊢* (rGate (LC n 0) (RC (r + k))) := by
    simpa only [Nat.zero_add] using counter_rounds n 0 r k (by omega)
  have h2 := right_counter (r + k) (LC n 0)
  rw [show 1 + (r + k) = r + k + 1 by omega] at h2
  exact stepStar_stepPlus_trans h1 (stepPlus_trans h2 (return_wall n (RC (r + k + 1))))

def digits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 == 1) :: digits n (v / 2)

theorem digits_length (n v : ℕ) : (digits n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [digits, ih]

theorem digits_even (n v : ℕ) : digits (n + 1) (v * 2) = false :: digits n v := by
  have hm : (v * 2) % 2 = 0 := by omega
  have hd : (v * 2) / 2 = v := by omega
  simp [digits, hm, hd]

theorem digits_odd (n v : ℕ) : digits (n + 1) (v * 2 + 1) = true :: digits n v := by
  have hm : (v * 2 + 1) % 2 = 1 := by omega
  have hd : (v * 2 + 1) / 2 = v := by omega
  simp [digits, hm, hd]

theorem digits_normal (n v : ℕ) (hv : v < 2 ^ n) :
    WallInvariant.normal (digits n v) +> default = RC v := by
  induction n generalizing v with
  | zero =>
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    simp [digits, WallInvariant.normal, RC, BinInc_O]
  | succ n ih =>
    rw [Nat.pow_succ] at hv
    rcases Nat.even_or_odd' v with ⟨q, rfl | rfl⟩
    · rw [Nat.mul_comm 2 q, digits_even, WallInvariant.normal]
      simp only [Bool.false_eq_true, ↓reduceIte, append_assoc, ih q (by omega)]
      unfold RC
      rw [BinInc_mul2]
      rfl
    · rw [show 2 * q + 1 = q * 2 + 1 by omega, digits_odd, WallInvariant.normal]
      simp only [↓reduceIte, append_assoc, ih q (by omega)]
      unfold RC
      rw [BinInc_mul2add1]

end CounterFinish

/-! ## BoundaryRules -/

namespace BoundaryRules

open CounterRules

private theorem gap0_turn (l r : ListBlank Γ) :
    (l {{qA}}> ([1, 1, 0, 0, 0, 0] +> r)) [mtm]⊢⁺ (([1] +> l) <{{qC}} ([0, 1, 0, 0, 0] +> r)) := by
  have hs := runSteps1_spec mtm 3 ⟨[], [1, 1, 0], qA, .right⟩
    ⟨[0, 1], [1], qC, .left⟩ (by decide) l ([0, 0, 0] +> r)
  have h_in : ([1, 1, 0] : List Γ) +> ([0, 0, 0] +> r) = [1, 1, 0, 0, 0, 0] +> r := rfl
  have h_out : ([0, 1] : List Γ) +> ([0, 0, 0] +> r) = [0, 1, 0, 0, 0] +> r := rfl
  simpa only [BoundedConfig.toCfg, append_nil, h_in, h_out] using hs

private theorem gap2_turn (l r : ListBlank Γ) :
    (l {{qA}}> ([1, 0, 0, 1, 0, 0, 0, 0] +> r)) [mtm]⊢⁺
      (([1, 1, 1] +> l) <{{qC}} ([0, 1, 0, 0, 0] +> r)) := by
  have hs := runSteps1_spec mtm 7 ⟨[], [1, 0, 0, 1, 0], qA, .right⟩
    ⟨[0, 1], [1, 1, 1], qC, .left⟩ (by decide) l ([0, 0, 0] +> r)
  have h_in : ([1, 0, 0, 1, 0] : List Γ) +> ([0, 0, 0] +> r) =
      [1, 0, 0, 1, 0, 0, 0, 0] +> r := rfl
  have h_out : ([0, 1] : List Γ) +> ([0, 0, 0] +> r) = [0, 1, 0, 0, 0] +> r := rfl
  simpa only [BoundedConfig.toCfg, append_nil, h_in, h_out] using hs

theorem gap0_even (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ (n * 2) +> ([1, 1, 0, 0, 0, 0] +> r))) [mtm]⊢⁺
      (rGate (ld0 ^ (n * 5) +> (ld1 +> l)) ([1, 0, 0, 0] +> r)) := by
  have h1 := shift_A_rd1_right (n * 2) ([0, 1] +> l) ([1, 1, 0, 0, 0, 0] +> r)
  have h2 := gap0_turn ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l)) r
  have h3 := shift_C_1_step ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l)) ([1, 0, 0, 0] +> r)
  have h3' : (([1] ^ ((n * 2) * 5) +> ([0, 1] +> l)) <{{qC}}
      ([0] +> ([1] +> ([1, 0, 0, 0] +> r)))) =
      lGate (ld1 ^ (n * 5) +> (ld0 +> l)) ([1, 0, 0, 0] +> r) := by
    rw [show (n * 2) * 5 = (n * 5) * 2 by omega, ones_even_pow]
    rfl
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans (stepPlus_stepStar_trans h2 (stepStar_congr h3 rfl h3'))
      (left_increment l ([1, 0, 0, 0] +> r) (n * 5)))

theorem gap0_odd (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ (n * 2 + 1) +> ([1, 1, 0, 0, 0, 0] +> r))) [mtm]⊢⁺
      (rGate (ld0 ^ (n * 5 + 3) +> (ld1 +> l)) ([0, 0, 0] +> r)) := by
  have h1 := shift_A_rd1_right (n * 2 + 1) ([0, 1] +> l) ([1, 1, 0, 0, 0, 0] +> r)
  have h2 := gap0_turn ([1] ^ ((n * 2 + 1) * 5) +> ([0, 1] +> l)) r
  have h2' : (([1] +> ([1] ^ ((n * 2 + 1) * 5) +> ([0, 1] +> l))) <{{qC}} ([0, 1, 0, 0, 0] +> r)) =
      lGate (ld1 ^ (n * 5 + 3) +> (ld0 +> l)) ([0, 0, 0] +> r) := by
    have hl : ([1] : List Γ) +> ([1] ^ ((n * 2 + 1) * 5) +> ([0, 1] +> l)) =
        ld1 ^ (n * 5 + 3) +> (ld0 +> l) := by
      rw [← append_assoc [1], ← pow_succ_list,
        show (n * 2 + 1) * 5 + 1 = (n * 5 + 3) * 2 by omega, ones_even_pow]
    rw [hl]
    rfl
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans (stepPlus_congr h2 rfl h2')
      (left_increment l ([0, 0, 0] +> r) (n * 5 + 3)))

theorem gap2_even (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ (n * 2) +> ([1, 0, 0, 1, 0, 0, 0, 0] +> r))) [mtm]⊢⁺
      (rGate (ld0 ^ (n * 5 + 1) +> (ld1 +> l)) ([1, 0, 0, 0] +> r)) := by
  have h1 := shift_A_rd1_right (n * 2) ([0, 1] +> l) ([1, 0, 0, 1, 0, 0, 0, 0] +> r)
  have h2 := gap2_turn ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l)) r
  have h3 := shift_C_1_step ([1, 1] +> ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l))) ([1, 0, 0, 0] +> r)
  have h3_in : (([1, 1, 1] +> ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l))) <{{qC}}
      ([0, 1, 0, 0, 0] +> r)) =
      (([1] +> ([1, 1] +> ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l)))) <{{qC}}
        ([0] +> ([1, 0, 0, 0] +> r))) := rfl
  have h3_out : (([1, 1] +> ([1] ^ ((n * 2) * 5) +> ([0, 1] +> l))) <{{qC}}
      ([0] +> ([1] +> ([1, 0, 0, 0] +> r)))) =
      lGate (ld1 ^ (n * 5 + 1) +> (ld0 +> l)) ([1, 0, 0, 0] +> r) := by
    rw [show (n * 2) * 5 = (n * 5) * 2 by omega, ones_even_pow,
      ← append_assoc [1, 1] (ld1 ^ (n * 5)), ← pow_succ_list]
    rfl
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans (stepPlus_stepStar_trans (stepPlus_congr h2 rfl h3_in)
        (stepStar_congr h3 rfl h3_out))
      (left_increment l ([1, 0, 0, 0] +> r) (n * 5 + 1)))

theorem gap2_odd (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ (n * 2 + 1) +> ([1, 0, 0, 1, 0, 0, 0, 0] +> r))) [mtm]⊢⁺
      (rGate (ld0 ^ (n * 5 + 4) +> (ld1 +> l)) ([0, 0, 0] +> r)) := by
  have h1 := shift_A_rd1_right (n * 2 + 1) ([0, 1] +> l) ([1, 0, 0, 1, 0, 0, 0, 0] +> r)
  have h2 := gap2_turn ([1] ^ ((n * 2 + 1) * 5) +> ([0, 1] +> l)) r
  have h2' : (([1, 1, 1] +> ([1] ^ ((n * 2 + 1) * 5) +> ([0, 1] +> l))) <{{qC}}
      ([0, 1, 0, 0, 0] +> r)) =
      lGate (ld1 ^ (n * 5 + 4) +> (ld0 +> l)) ([0, 0, 0] +> r) := by
    have hl : ([1, 1, 1] : List Γ) +> ([1] ^ ((n * 2 + 1) * 5) +> ([0, 1] +> l)) =
        ld1 ^ (n * 5 + 4) +> (ld0 +> l) := by
      rw [show ([1, 1, 1] : List Γ) = ([1] : List Γ) ^ 3 from rfl, ← append_assoc, ← pow_add_list,
        show 3 + (n * 2 + 1) * 5 = (n * 5 + 4) * 2 by omega, ones_even_pow]
    rw [hl]
    rfl
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans (stepPlus_congr h2 rfl h2')
      (left_increment l ([0, 0, 0] +> r) (n * 5 + 4)))

theorem gap3_forward (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ n +> ([1, 0, 0, 0, 1, 0, 0, 0, 0] +> r))) [mtm]⊢⁺
      ((([1] : List Γ) ^ (n * 5 + 9) +> ([0, 1] +> l)) {{qA}}> r) := by
  have h1 := shift_A_rd1_right n ([0, 1] +> l) ([1, 0, 0, 0, 1, 0, 0, 0, 0] +> r)
  have h2 : ((([1] : List Γ) ^ (n * 5) +> ([0, 1] +> l)) {{qA}}>
      ([1, 0, 0, 0, 1, 0, 0, 0, 0] +> r)) [mtm]⊢⁺
      ((([1] : List Γ) ^ (n * 5 + 9) +> ([0, 1] +> l)) {{qA}}> r) := by
    have hs := runSteps1_spec mtm 8 ⟨[], [1, 0, 0, 0, 1, 0, 0, 0, 0], qA, .right⟩
      ⟨([1] : List Γ) ^ 9, [], qA, .right⟩ (by decide) (([1] : List Γ) ^ (n * 5) +> ([0, 1] +> l)) r
    have hl : ([1] : List Γ) ^ 9 +> (([1] : List Γ) ^ (n * 5) +> ([0, 1] +> l)) =
        ([1] : List Γ) ^ (n * 5 + 9) +> ([0, 1] +> l) := by
      rw [← append_assoc, ← pow_add_list, Nat.add_comm 9 (n * 5)]
    simpa only [BoundedConfig.toCfg, append_nil, hl] using hs
  exact stepStar_stepPlus_trans h1 h2

theorem gap3_zero (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ n +> ([1, 0, 0, 0, 1, 0, 0, 0, 0, 0] +> r))) [mtm]⊢⁺
      (lGate l ([0] ^ (n * 5 + 9) +> ([1] +> r))) := by
  have h_split : ([1, 0, 0, 0, 1, 0, 0, 0, 0, 0] : List Γ) +> r =
      [1, 0, 0, 0, 1, 0, 0, 0, 0] +> ([0] +> r) := rfl
  rw [h_split]
  have h1 := gap3_forward l ([0] +> r) n
  have h2 : ((([1] : List Γ) ^ (n * 5 + 9) +> ([0, 1] +> l)) {{qA}}> ([0] +> r)) [mtm]⊢⁺
      ((([1] : List Γ) ^ (n * 5 + 9) +> ([0, 1] +> l)) <{{qB}} ([1] +> r)) := by
    have hs := runSteps1_spec mtm 0 ⟨[], [0], qA, .right⟩ ⟨[1], [], qB, .left⟩ (by decide)
      (([1] : List Γ) ^ (n * 5 + 9) +> ([0, 1] +> l)) r
    simpa only [BoundedConfig.toCfg, append_nil] using hs
  have h3 := shift_B_1_left (n * 5 + 9) ([0, 1] +> l) ([1] +> r)
  have h4 := B_01_to_C l ([0] ^ (n * 5 + 9) +> ([1] +> r))
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepStar_stepPlus_trans h3 h4))

theorem gap1_reaches_D1 (l r : ListBlank Γ) (n : ℕ) :
    (rGate l (rd1 ^ n +> ([1, 0, 1] +> r))) [mtm]⊢*
      ((([1] : List Γ) ^ (n * 5 + 2) +> ([0, 1] +> l)) {{qD}}> ([1] +> r)) := by
  have h1 := shift_A_rd1_right n ([0, 1] +> l) ([1, 0, 1] +> r)
  have h2 : ((([1] : List Γ) ^ (n * 5) +> ([0, 1] +> l)) {{qA}}> ([1, 0, 1] +> r)) [mtm]⊢*
      ((([1] : List Γ) ^ (n * 5 + 2) +> ([0, 1] +> l)) {{qD}}> ([1] +> r)) := by
    have hs := runSteps_spec mtm 2 ⟨[], [1, 0], qA, .right⟩ ⟨[1, 1], [], qD, .right⟩ (by decide)
      (([1] : List Γ) ^ (n * 5) +> ([0, 1] +> l)) ([1] +> r)
    have hl : ([1, 1] : List Γ) +> (([1] : List Γ) ^ (n * 5) +> ([0, 1] +> l)) =
        ([1] : List Γ) ^ (n * 5 + 2) +> ([0, 1] +> l) := by
      rw [show ([1, 1] : List Γ) = ([1] : List Γ) ^ 2 from rfl, ← append_assoc, ← pow_add_list,
        Nat.add_comm 2 (n * 5)]
    have h_in : ([1, 0] : List Γ) +> ([1] +> r) = [1, 0, 1] +> r := rfl
    simpa only [BoundedConfig.toCfg, append_nil, hl, h_in] using hs
  exact stepStar_trans h1 h2

abbrev hp : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]
abbrev cp : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]
abbrev xp : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qC, [0]))]
abbrev dz : List Γ := [0, 0, 0, 0, 0]
abbrev ds : List Γ := [0, 0, 0, 0, 1]
abbrev ones5 : List Γ := [1, 1, 1, 1, 1]

theorem conversion_digit : SegRLs mtm xp xp ds ones5 :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem conversion_stop : SegRLs mtm xp [] rd1 [1, 0, 0, 0] :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem conversion_digits (n : ℕ) : SegRLs mtm xp xp (ds ^ n) (ones5 ^ n) := by
  induction n with
  | zero => exact SegRLs.empty mtm _
  | succ n ih => exact conversion_digit.concat ih

theorem conversion_stopped (n : ℕ) :
    SegRLs mtm xp [] (ds ^ n ++ rd1) (ones5 ^ n ++ [1, 0, 0, 0]) :=
  (conversion_digits n).concat conversion_stop

theorem odd_prefix_x_one : SegRLs mtm hp (xp ++ hp) [1] [1, 1] :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem even_prefix_two : SegRLs mtm hp (hp ^ 2) [1, 1] [1, 1] :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem even_prefix_many (k : ℕ) : SegRLs mtm (hp ^ k) (hp ^ (k * 2)) [1, 1] [1, 1] :=
  LocalPasses.ld_Incs k

theorem odd_prefix_x (k : ℕ) : SegRLs mtm (hp ^ (k + 1)) (xp ++ hp ^ (k * 2 + 1)) [1] [1, 1] := by
  have h := odd_prefix_x_one.trans (even_prefix_many k)
  refine segRLs_congr h ?_ ?_ rfl rfl
  · rw [pow_succ_list]
  · rw [List.append_assoc, Nat.add_comm (k * 2) 1, Nat.add_comm 1 (k * 2), pow_succ_list]

theorem odd_prefix_c (k : ℕ) : SegRLs mtm (hp ^ (k * 2)) (cp ^ k) [1] [1] :=
  OddNormal.one_pairs k

theorem c_fill_zeros (k n : ℕ) :
    SegRLs mtm (cp ^ ((k + 1) * 2 ^ n - 1)) (cp ^ k) (dz ^ n) (ds ^ n) :=
  OddNormal.c_zeros_allones k n

theorem before_conversion (j : ℕ) :
    SegRLs mtm (hp ^ ((2 ^ j - 1) * 2)) [] ([1] ++ dz ^ j) ([1] ++ ds ^ j) :=
  OddNormal.prime_first j

theorem conversion_side (j : ℕ) (r : ListBlank Γ) :
    SideRLs mtm xp (ds ^ j +> (rd1 +> r)) (ones5 ^ j +> ([1, 0, 0, 0] +> r)) := by
  have hs := (conversion_stopped j).sideRLs_concat (.nil r)
  simpa only [append_assoc] using hs

theorem odd_conversion (j q : ℕ) (r r' : ListBlank Γ)
    (H : SideRLs mtm (hp ^ (q * 2 + 1)) (ones5 ^ j +> ([1, 0, 0, 0] +> r)) r') :
    SideRLs mtm (hp ^ ((2 ^ j - 1) * 2 + q + 1))
      ([1] +> (dz ^ j +> (rd1 +> r))) ([1, 1] +> r') := by
  rw [show (2 ^ j - 1) * 2 + q + 1 = (2 ^ j - 1) * 2 + (q + 1) by omega, pow_add_list]
  have s1 : SideRLs mtm (hp ^ ((2 ^ j - 1) * 2))
      ([1] +> (dz ^ j +> (rd1 +> r))) ([1] +> (ds ^ j +> (rd1 +> r))) := by
    have hs := (before_conversion j).sideRLs_concat (.nil (rd1 +> r))
    simpa only [append_assoc] using hs
  have s2 := (odd_prefix_x q).sideRLs_concat ((conversion_side j r).trans H)
  exact s1.trans s2

end BoundaryRules

/-! ## OddFuel -/

namespace OddFuel

open CounterRules CounterBatch

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev b : List Γ := [1, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev d : List Γ := [0, 0, 0, 1, 0]
abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev z3 : List Γ := [0, 0, 0]
abbrev r4 : List Γ := [1, 0, 0, 0]
abbrev g0 : List Γ := [1, 1, 0, 0, 0, 0]
abbrev g2 : List Γ := [1, 0, 0, 1, 0, 0, 0, 0]
abbrev t3 : List Γ := [1, 0, 0, 1, 0]

theorem scan_ones (n : ℕ) (r : ListBlank Γ) :
    ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> (ld ^ n +> r)) [mtm]⊢*
      (rGate (LC n (2 ^ n - 1)) r) := by
  unfold LC
  rw [BinDec_full]
  have hs := shift_A_11_right n ([0] +> LocalPasses.lh) r
  refine stepStar_congr hs rfl ?_
  have hl : (ld0 ^ n +> ([0, 1, 1] +> (default : ListBlank Γ))) =
      ([0, 1] +> (ld0 ^ n +> ldh)) := by
    have h_init : ([0, 1, 1] : List Γ) +> (default : ListBlank Γ) = ld0 +> ldh := rfl
    rw [h_init, ← append_assoc, ← pow_succ_list', pow_succ_list, append_assoc]
  exact congrArg (fun x => x {{qA}}> r) hl

def grown (k z : ℕ) : ℕ := (2 * k + 1) * 2 ^ z - 1

theorem grown_bound (L k z : ℕ) (hk : k < 2 ^ L) : grown k z + 1 < 2 ^ (L + 1 + z) := by
  unfold grown
  have hp := pow2_pos z
  have hpos : 1 ≤ (2 * k + 1) * 2 ^ z := by nlinarith
  have hlt : (2 * k + 1) * 2 ^ z < 2 ^ L * 2 * 2 ^ z := by nlinarith
  rw [show L + 1 + z = (L + 1) + z by omega, Nat.pow_add, Nat.pow_succ]
  omega

theorem grow_left (L k z : ℕ) (_hk : k < 2 ^ L) :
    ld0 ^ z +> (ld1 +> LC L k) = LC (L + 1 + z) (grown k z) := by
  unfold LC grown
  rw [Nat.mul_comm 2 k]
  exact BinDec_mulpow2sub1 ld0 ld1 L k z ldh

theorem p_one_pair : SegRLs mtm (p ^ 2) OddNormal.x one one :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem p_one_pairs (k : ℕ) : SegRLs mtm (p ^ (k * 2)) (OddNormal.x ^ k) one one := by
  induction k with
  | zero => exact .nil one
  | succ k ih =>
    rw [show (k + 1) * 2 = 2 + k * 2 by omega, pow_add_list, pow_succ_list OddNormal.x]
    exact p_one_pair.trans ih

theorem prime_one (u : ℕ) :
    SegRLs mtm (p ^ ((2 ^ u - 1) * 2)) [] (one ++ a ^ u) (one ++ c ^ u) := by
  have hc := OddNormal.c_zeros_allones 0 u
  simp only [Nat.zero_add, Nat.one_mul, pow_zero_list] at hc
  exact (p_one_pairs (2 ^ u - 1)).concat hc

private theorem one_c_pow_b : ∀ (u : ℕ), one ++ c ^ u ++ b = b ^ u ++ g0
  | 0 => rfl
  | u + 1 => by
    rw [pow_succ_list c, pow_succ_list b]
    have h_head : one ++ (c ++ c ^ u) ++ b = b ++ (one ++ c ^ u ++ b) := by
      simp only [List.append_assoc]; rfl
    rw [h_head, one_c_pow_b u, List.append_assoc]

theorem prime_gap0 (u : ℕ) (r : ListBlank Γ) :
    SideRLs mtm (p ^ ((2 ^ u - 1) * 2)) (one +> (a ^ u +> (b +> r))) (b ^ u +> (g0 +> r)) := by
  have hs := (prime_one u).sideRLs_concat (.nil (b +> r))
  refine sideRLs_congr hs rfl (by simp only [append_assoc]) ?_
  rw [← append_assoc, one_c_pow_b u, append_assoc]

theorem p_third_one : SegRLs mtm p [] d t3 :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem prime_gap2 (u : ℕ) (r : ListBlank Γ) :
    SideRLs mtm (p ^ (2 ^ (u + 1) - 1)) (a ^ u +> (d +> (z3 +> r))) (b ^ u +> (g2 +> r)) := by
  have h1 : SegRLs mtm (p ^ (2 ^ (u + 1) - 1)) p (a ^ u) (b ^ u) := by
    have hd := LocalPasses.d01s_Incs 1 u
    rw [Nat.pow_succ]
    simpa only [show (1 + 1) * 2 ^ u - 1 = 2 ^ u * 2 - 1 by omega, pow_one_list] using hd
  have h2 : SideRLs mtm p (d +> (z3 +> r)) (g2 +> r) := by
    have hs := p_third_one.sideRLs_concat (.nil (z3 +> r))
    have ht : (t3 ++ z3) +> r = g2 +> r := rfl
    simpa only [← append_assoc, ht] using hs
  exact h1.sideRLs_concat h2

theorem convert_gap0_even (L k v : ℕ) (r : ListBlank Γ) (hk : k < 2 ^ L) :
    (rGate (LC L k) (b ^ (v * 2) +> (g0 +> r))) [mtm]⊢⁺
      (rGate (LC (L + 1 + v * 5) (grown k (v * 5))) (r4 +> r)) := by
  rw [← grow_left L k (v * 5) hk]
  exact BoundaryRules.gap0_even (LC L k) r v

theorem convert_gap0_odd (L k v : ℕ) (r : ListBlank Γ) (hk : k < 2 ^ L) :
    (rGate (LC L k) (b ^ (v * 2 + 1) +> (g0 +> r))) [mtm]⊢⁺
      (rGate (LC (L + 1 + (v * 5 + 3)) (grown k (v * 5 + 3))) (z3 +> r)) := by
  rw [← grow_left L k (v * 5 + 3) hk]
  exact BoundaryRules.gap0_odd (LC L k) r v

theorem convert_gap2_even (L k v : ℕ) (r : ListBlank Γ) (hk : k < 2 ^ L) :
    (rGate (LC L k) (b ^ (v * 2) +> (g2 +> r))) [mtm]⊢⁺
      (rGate (LC (L + 1 + (v * 5 + 1)) (grown k (v * 5 + 1))) (r4 +> r)) := by
  rw [← grow_left L k (v * 5 + 1) hk]
  exact BoundaryRules.gap2_even (LC L k) r v

theorem convert_gap2_odd (L k v : ℕ) (r : ListBlank Γ) (hk : k < 2 ^ L) :
    (rGate (LC L k) (b ^ (v * 2 + 1) +> (g2 +> r))) [mtm]⊢⁺
      (rGate (LC (L + 1 + (v * 5 + 4)) (grown k (v * 5 + 4))) (z3 +> r)) := by
  rw [← grow_left L k (v * 5 + 4) hk]
  exact BoundaryRules.gap2_odd (LC L k) r v

theorem right_pass_finish (n k : ℕ) (r r' : ListBlank Γ)
    (hk : k < 2 ^ n) (hr : SideRLs mtm (p ^ (k + 1)) r r') :
    (rGate (LC n k) r) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> (one +> (ld ^ n +> r'))) := by
  rw [pow_succ_list'] at hr
  obtain ⟨mid, hfirst, hlast⟩ := hr.split
  have h1 : (rGate (LC n k) r) [mtm]⊢* (rGate (LC n 0) mid) := by
    simpa only [Nat.zero_add] using right_pass_batch n 0 k r mid (by omega) hfirst
  have h2 := hlast.elim_single ([0, 1] +> LC n 0)
  have h3 := B_01_to_C (LC n 0) r'
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans h2 (stepPlus_trans h3 (CounterFinish.return_wall n r')))

end OddFuel

/-! ## CDPasses -/

namespace CDPasses

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev d : List Γ := [0, 0, 0, 1, 0]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]
abbrev y : List (DH0 Γ Λ × DH0 Γ Λ) := [((qD, []), (qB, []))]

def bitval (b : Bool) : ℕ := if b then 1 else 0
def third_digit (b : Bool) : List Γ := if b then d else a
def fourth_digit (b : Bool) : List Γ := if b then c else a

def third : List Bool → List Γ
  | [] => []
  | b :: bs => third_digit b ++ third bs

def fourth : List Bool → List Γ
  | [] => []
  | b :: bs => fourth_digit b ++ fourth bs

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => bitval b + 2 * value bs

def any : List Bool → Bool
  | [] => false
  | b :: bs => b || any bs

def mass (pending : Bool) (n : ℕ) : List (DH0 Γ Λ × DH0 Γ Λ) :=
  if pending then y ++ x ^ (n - 1) else x ^ n

theorem c_zero_even (k : ℕ) : SegRLs mtm (x ^ (k * 2)) (x ^ k) a a :=
  OddNormal.c_zero_even k

theorem c_zero_odd (k : ℕ) : SegRLs mtm (x ^ (k * 2 + 1)) (x ^ k) a c :=
  OddNormal.c_zero_odd k

theorem c_phase_hit : SegRLs mtm x y d a :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem d_zero : SegRLs mtm y [] a d :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem d_one : SegRLs mtm y y d a :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem c_phase_even (k : ℕ) (hk : k ≠ 0) :
    SegRLs mtm (x ^ (k * 2)) (y ++ x ^ (k - 1)) d c := by
  have heq : k * 2 = 1 + ((k - 1) * 2 + 1) := by omega
  rw [heq, Nat.add_comm 1 _, pow_succ_list]
  exact c_phase_hit.trans (c_zero_odd (k - 1))

theorem c_phase_odd (k : ℕ) : SegRLs mtm (x ^ (k * 2 + 1)) (y ++ x ^ k) d a := by
  rw [Nat.add_comm (k * 2) 1, Nat.add_comm 1 (k * 2), pow_succ_list]
  exact c_phase_hit.trans (c_zero_even k)

theorem dc_zero_even (k : ℕ) (hk : k ≠ 0) :
    SegRLs mtm (y ++ x ^ (k * 2)) (y ++ x ^ (k - 1)) a c :=
  d_zero.trans (c_phase_even k hk)

theorem dc_zero_odd (k : ℕ) :
    SegRLs mtm (y ++ x ^ (k * 2 + 1)) (y ++ x ^ k) a a :=
  d_zero.trans (c_phase_odd k)

theorem dc_one_even (k : ℕ) :
    SegRLs mtm (y ++ x ^ (k * 2)) (y ++ x ^ k) d a :=
  d_one.trans (c_zero_even k)

theorem dc_one_odd (k : ℕ) :
    SegRLs mtm (y ++ x ^ (k * 2 + 1)) (y ++ x ^ k) d c :=
  d_one.trans (c_zero_odd k)

theorem mass_even (k : ℕ) (old bit : Bool) (hk : k ≠ 0) :
    SegRLs mtm (mass old (k * 2)) (mass (old || bit) k)
      (third_digit bit) (fourth_digit bit) := by
  cases old <;> cases bit <;> unfold mass third_digit fourth_digit <;>
    simp only [Bool.false_or, Bool.true_or, ↓reduceIte, Bool.false_eq_true]
  · exact c_zero_even k
  · exact c_phase_even k hk
  · rw [show k * 2 - 1 = (k - 1) * 2 + 1 by omega]; exact dc_zero_odd (k - 1)
  · rw [show k * 2 - 1 = (k - 1) * 2 + 1 by omega]; exact dc_one_odd (k - 1)

theorem mass_odd (k : ℕ) (old bit : Bool) (hk : k ≠ 0) :
    SegRLs mtm (mass old (1 + k * 2)) (mass (old || bit) (k + bitval bit))
      (third_digit bit) (fourth_digit (!bit)) := by
  cases old <;> cases bit <;> unfold mass third_digit fourth_digit bitval <;>
    simp only [Bool.false_or, Bool.true_or, Bool.not_false, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
  · rw [Nat.add_comm 1 (k * 2)]; exact c_zero_odd k
  · rw [Nat.add_comm 1 (k * 2), show k + 1 - 1 = k by omega]; exact c_phase_odd k
  · rw [show 1 + k * 2 - 1 = k * 2 by omega]; exact dc_zero_even k hk
  · rw [show 1 + k * 2 - 1 = k * 2 by omega, show k + 1 - 1 = k by omega]; exact dc_one_even k

theorem value_bound (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    cases b <;> simp [value, bitval, Nat.pow_succ] <;> omega

theorem mass_digits (bs : List Bool) (old : Bool) (n : ℕ) (hn : 2 ^ bs.length ≤ n) :
    ∃ out carry,
      out.length = bs.length ∧
      2 ^ bs.length * carry + value out = n + value bs ∧
      1 ≤ carry ∧
      SegRLs mtm (mass old n) (mass (old || any bs) carry) (third bs) (fourth out) := by
  induction bs generalizing old n with
  | nil =>
    refine ⟨[], n, rfl, ?_, by simp at hn; omega, ?_⟩
    · simp [value]
    · simp only [any, third, fourth, Bool.or_false]
      exact SegRLs.empty mtm _
  | cons bit bs ih =>
    have hp := pow2_pos bs.length
    simp only [List.length_cons, Nat.pow_succ] at hn
    rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
    · have hq : 2 ^ bs.length ≤ q := by omega
      obtain ⟨out, carry, hlen, hv, hcarry, hseg⟩ := ih (old || bit) q hq
      refine ⟨bit :: out, carry, by simp [hlen], ?_, hcarry, ?_⟩
      · simp only [value, List.length_cons, Nat.pow_succ]
        nlinarith
      · rw [show (old || any (bit :: bs)) = ((old || bit) || any bs) by
          simp [any, Bool.or_assoc], Nat.mul_comm 2 q]
        exact (mass_even q old bit (by omega)).concat hseg
    · have hq : 2 ^ bs.length ≤ q := by omega
      obtain ⟨out, carry, hlen, hv, hcarry, hseg⟩ :=
        ih (old || bit) (q + bitval bit) (by omega)
      refine ⟨(!bit) :: out, carry, by simp [hlen], ?_, hcarry, ?_⟩
      · cases bit <;> simp only [value, bitval, Bool.not_false, Bool.not_true,
          List.length_cons, Nat.pow_succ, ↓reduceIte, Bool.false_eq_true] at hv ⊢ <;> nlinarith
      · rw [show (old || any (bit :: bs)) = ((old || bit) || any bs) by
          simp [any, Bool.or_assoc], show 2 * q + 1 = 1 + q * 2 by omega]
        exact (mass_odd q old bit (by omega)).concat hseg

def terminal (pending : Bool) : List Γ := if pending then d else c

theorem flush_one (old : Bool) :
    SideRLs mtm (mass old 1) default (terminal old +> default) := by
  cases old
  · simpa [mass, terminal] using
      BoundedConfig.sideRLs_c_spec mtm (hs := x) (r := []) (r' := c) (T := 1000) (by decide)
  · simpa [mass, terminal] using
      BoundedConfig.sideRLs_c_spec mtm (hs := y) (r := []) (r' := d) (T := 1000) (by decide)

theorem mass_flush (budget : ℕ) (old : Bool) (n : ℕ) (hn : 0 < n ∧ n < 2 ^ budget) :
    ∃ out : List Bool,
      out.length < budget ∧
      value out + 2 ^ out.length = n ∧
      SideRLs mtm (mass old n) default (fourth out +> (terminal old +> default)) := by
  induction budget generalizing old n with
  | zero => simp at hn; omega
  | succ budget ih =>
    by_cases he1 : n = 1
    · subst he1
      exact ⟨[], by simp, by simp [value], flush_one old⟩
    · rw [Nat.pow_succ] at hn
      rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
      · obtain ⟨out, hlen, hv, hseg⟩ := ih old q ⟨by omega, by omega⟩
        refine ⟨false :: out, by simp; omega, ?_, ?_⟩
        · simp only [value, bitval, List.length_cons, Nat.pow_succ, Bool.false_eq_true, ↓reduceIte]
          nlinarith
        · have hm := mass_even q old false (by omega)
          simp only [Bool.or_false, third_digit, fourth_digit, Bool.false_eq_true, ↓reduceIte] at hm
          have hs := hm.sideRLs_concat hseg
          have ha : a +> (default : ListBlank Γ) = default := zeros_default 5
          rw [Nat.mul_comm 2 q]
          simpa only [fourth, fourth_digit, Bool.false_eq_true, ↓reduceIte,
            append_assoc, ha] using hs
      · obtain ⟨out, hlen, hv, hseg⟩ := ih old q ⟨by omega, by omega⟩
        refine ⟨true :: out, by simp; omega, ?_, ?_⟩
        · simp only [value, bitval, List.length_cons, Nat.pow_succ, ↓reduceIte]
          nlinarith
        · have hm := mass_odd q old false (by omega)
          simp only [Bool.or_false, bitval, Bool.not_false, Nat.add_zero,
            third_digit, fourth_digit, Bool.false_eq_true, ↓reduceIte] at hm
          have hs := hm.sideRLs_concat hseg
          have ha : a +> (default : ListBlank Γ) = default := zeros_default 5
          rw [show 2 * q + 1 = 1 + q * 2 by omega]
          simpa only [fourth, fourth_digit, ↓reduceIte, append_assoc, ha] using hs

theorem value_append (left right : List Bool) :
    value (left ++ right) = value left + 2 ^ left.length * value right := by
  induction left with
  | nil => simp [value]
  | cons b left ih =>
    simp only [List.cons_append, value, List.length_cons, Nat.pow_succ, ih]
    ring

theorem fourth_append (left right : List Bool) :
    fourth (left ++ right) = fourth left ++ fourth right := by
  induction left with
  | nil => rfl
  | cons b left ih => simp [fourth, ih, List.append_assoc]

theorem mass_full (bs : List Bool) (old : Bool) (n z : ℕ)
    (hn : 2 ^ bs.length ≤ n) (hbound : n + value bs < 2 ^ (bs.length + z)) :
    ∃ out : List Bool,
      out.length < bs.length + z ∧
      value out + 2 ^ out.length = n + value bs ∧
      SideRLs mtm (mass old n) (third bs +> default)
        (fourth out +> (terminal (old || any bs) +> default)) := by
  obtain ⟨low, carry, hlen, hv, hcarry, hseg⟩ := mass_digits bs old n hn
  have hp := pow2_pos bs.length
  rw [Nat.pow_add] at hbound
  have hc : 0 < carry ∧ carry < 2 ^ z := ⟨by omega, by nlinarith⟩
  obtain ⟨high, hhigh, hvalue, hflush⟩ := mass_flush z (old || any bs) carry hc
  refine ⟨low ++ high, by simp [hlen]; omega, ?_, ?_⟩
  · rw [List.length_append, value_append, hlen, Nat.pow_add]
    nlinarith
  · rw [fourth_append, append_assoc]
    exact hseg.sideRLs_concat hflush

end CDPasses

/-! ## OddImage -/

namespace OddImage

open CounterRules

theorem normal_app (bs cs : List Bool) :
    WallInvariant.normal (bs ++ cs) = WallInvariant.normal bs ++ WallInvariant.normal cs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [WallInvariant.normal, ih, List.append_assoc]

theorem normal_zeros (n : ℕ) :
    WallInvariant.normal (List.replicate n false) = ([0, 0, 0, 0, 0] : List Γ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, WallInvariant.normal, ih, pow_succ_list]
    rfl

theorem phase_three_word (bs : List Bool) :
    [0, 0, 0] ++ WallInvariant.normal bs = CDPasses.third bs ++ [0, 0, 0] := by
  induction bs with
  | nil => rfl
  | cons bit bs ih =>
    cases bit <;> simp only [WallInvariant.normal, CDPasses.third, CDPasses.third_digit,
      ↓reduceIte, Bool.false_eq_true]
    · change [0, 0, 0, 0, 0] ++ ([0, 0, 0] ++ WallInvariant.normal bs) =
        [0, 0, 0, 0, 0] ++ (CDPasses.third bs ++ [0, 0, 0])
      rw [ih]
    · change [0, 0, 0, 1, 0] ++ ([0, 0, 0] ++ WallInvariant.normal bs) =
        [0, 0, 0, 1, 0] ++ (CDPasses.third bs ++ [0, 0, 0])
      rw [ih]

theorem phase_three (bs : List Bool) :
    ([0, 0, 0] : List Γ) +> (WallInvariant.normal bs +> default) =
      CDPasses.third bs +> default := by
  rw [← append_assoc, phase_three_word, append_assoc,
    BoundedConfig.all0_spec (a := [0, 0, 0]) (by decide)]

theorem leading_one_C (t : ℕ) (bs out : List Bool) (term : List Γ)
    (H : SideRLs mtm (CDPasses.x ^ t) (CDPasses.third bs +> default)
      (CDPasses.fourth out +> (term +> default))) :
    SideRLs mtm (CounterBatch.p ^ (t * 2))
      ([1, 0, 0, 0] +> (WallInvariant.normal bs +> default))
      ([1] +> (CDPasses.fourth out +> (term +> default))) := by
  have h_in : ([1, 0, 0, 0] : List Γ) +> (WallInvariant.normal bs +> default) =
      [1] +> (CDPasses.third bs +> default) := by
    change [1] +> ([0, 0, 0] +> (WallInvariant.normal bs +> default)) = _
    rw [phase_three]
  rw [h_in]
  exact (OddFuel.p_one_pairs t).sideRLs_concat H

theorem fuel_C_image (L k t : ℕ) (bs : List Bool) (budget : ℕ)
    (hk : k < 2 ^ L) (ht : k + 1 = t * 2)
    (hmin : 2 ^ bs.length ≤ t) (hmax : t + CDPasses.value bs < 2 ^ (bs.length + budget)) :
    ∃ out,
      out.length < bs.length + budget ∧
      CDPasses.value out + 2 ^ out.length = t + CDPasses.value bs ∧
      (rGate (LC L k) ([1, 0, 0, 0] +> (WallInvariant.normal bs +> default))) [mtm]⊢⁺
        WallInvariant.wall
          (([1, 1] : List Γ) ^ (L + 1) ++ CDPasses.fourth out ++
            CDPasses.terminal (CDPasses.any bs)) := by
  obtain ⟨out, hlen, hval, hrun⟩ := CDPasses.mass_full bs false t budget hmin hmax
  simp only [CDPasses.mass, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hrun
  refine ⟨out, hlen, hval, ?_⟩
  have hr := leading_one_C t bs out (CDPasses.terminal (CDPasses.any bs)) hrun
  rw [← ht] at hr
  have hfin := OddFuel.right_pass_finish L k _ _ hk hr
  refine stepPlus_congr hfin rfl ?_
  unfold WallInvariant.wall LocalPasses.lh OddFuel.one OddFuel.ld
  have h_rhs : ([1] +> (([1, 1] : List Γ) ^ L +> ([1] +> (CDPasses.fourth out +>
      (CDPasses.terminal (CDPasses.any bs) +> (default : ListBlank Γ)))))) =
      (([1, 1] : List Γ) ^ (L + 1) ++ CDPasses.fourth out ++
        CDPasses.terminal (CDPasses.any bs)) +> default := by
    rw [one_comm_11_side L, pow_succ_list', List.append_assoc, append_assoc, append_assoc,
      append_assoc]
    rfl
  rw [h_rhs]

def first_fuel (n u : ℕ) : ℕ := 2 ^ n - 1 - (2 ^ u - 1) * 2

theorem first_fuel_bounds (n u : ℕ) (hn : u + 1 ≤ n) :
    first_fuel n u + (2 ^ u - 1) * 2 = 2 ^ n - 1 ∧ first_fuel n u < 2 ^ n := by
  unfold first_fuel
  have hpow : 2 ^ (u + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rw [Nat.pow_succ] at hpow
  have hp1 := pow2_pos u
  have hp2 := pow2_pos n
  omega

theorem initial_even_entry (n v : ℕ) (bs : List Bool) (hn : v * 2 + 1 ≤ n) :
    (WallInvariant.O n (List.replicate (v * 2) false ++ true :: bs)) [mtm]⊢⁺
      (rGate (LC (n + 1 + v * 5) (OddFuel.grown (first_fuel n (v * 2)) (v * 5)))
        ([1, 0, 0, 0] +> (WallInvariant.normal bs +> default))) := by
  obtain ⟨he, hb⟩ := first_fuel_bounds n (v * 2) hn
  unfold WallInvariant.O WallInvariant.wall
  rw [normal_app, normal_zeros, WallInvariant.normal]
  simp only [↓reduceIte, List.append_assoc, append_assoc]
  have h1 := OddFuel.scan_ones n
    ([1] +> (([0, 0, 0, 0, 0] : List Γ) ^ (v * 2) +>
      ([1, 0, 0, 0, 0] +> (WallInvariant.normal bs +> default))))
  rw [← he] at h1
  have hpn := pow2_pos n
  have h2 := CounterBatch.right_pass_batch n (first_fuel n (v * 2)) ((2 ^ (v * 2) - 1) * 2)
    _ _ (by omega) (OddFuel.prime_gap0 (v * 2) (WallInvariant.normal bs +> default))
  have h3 := OddFuel.convert_gap0_even n (first_fuel n (v * 2)) v
    (WallInvariant.normal bs +> default) hb
  exact stepStar_stepPlus_trans (stepStar_trans h1 h2) h3

def first_mass (n v : ℕ) : ℕ :=
  (2 * first_fuel n (v * 2) + 1) * 2 ^ (v * 5 - 1)

theorem first_mass_fuel (n v : ℕ) (hv : 0 < v) :
    OddFuel.grown (first_fuel n (v * 2)) (v * 5) + 1 = first_mass n v * 2 := by
  unfold OddFuel.grown first_mass
  have hp := pow2_pos (v * 5 - 1)
  have he : 2 ^ (v * 5) = 2 ^ (v * 5 - 1) * 2 := by
    conv_lhs => rw [show v * 5 = (v * 5 - 1) + 1 by omega, Nat.pow_succ]
  rw [he, ← Nat.mul_assoc]
  have hpos : 1 ≤ (2 * first_fuel n (v * 2) + 1) * 2 ^ (v * 5 - 1) * 2 := by nlinarith
  omega

theorem initial_even_image (n v : ℕ) (bs : List Bool) (budget : ℕ)
    (hv : 0 < v) (hn : v * 2 + 1 ≤ n)
    (hmin : 2 ^ bs.length ≤ first_mass n v)
    (hmax : first_mass n v + CDPasses.value bs < 2 ^ (bs.length + budget)) :
    ∃ out,
      out.length < bs.length + budget ∧
      CDPasses.value out + 2 ^ out.length = first_mass n v + CDPasses.value bs ∧
      (WallInvariant.O n (List.replicate (v * 2) false ++ true :: bs)) [mtm]⊢⁺
        WallInvariant.wall
          (([1, 1] : List Γ) ^ (n + v * 5 + 2) ++ CDPasses.fourth out ++
            CDPasses.terminal (CDPasses.any bs)) := by
  obtain ⟨_, hb⟩ := first_fuel_bounds n (v * 2) hn
  have hgrown : OddFuel.grown (first_fuel n (v * 2)) (v * 5) < 2 ^ (n + 1 + v * 5) := by
    have := OddFuel.grown_bound n (first_fuel n (v * 2)) (v * 5) hb; omega
  obtain ⟨out, hlen, hval, hrun⟩ := fuel_C_image (n + 1 + v * 5)
    (OddFuel.grown (first_fuel n (v * 2)) (v * 5)) (first_mass n v) bs budget
    hgrown (first_mass_fuel n v hv) hmin hmax
  refine ⟨out, hlen, hval, ?_⟩
  rw [show n + v * 5 + 2 = (n + 1 + v * 5) + 1 by omega]
  exact stepPlus_trans (initial_even_entry n v bs hn) hrun

end OddImage

/-! ## OddRecursion -/

namespace OddRecursion

open CounterRules

theorem initial_odd_entry (n v : ℕ) (bs : List Bool) (hn : v * 2 + 2 ≤ n) :
    (WallInvariant.O n (List.replicate (v * 2 + 1) false ++ true :: bs)) [mtm]⊢⁺
      (rGate (LC (n + 1 + (v * 5 + 3))
        (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)))
        ([0, 0, 0] +> (WallInvariant.normal bs +> default))) := by
  obtain ⟨he, hb⟩ := OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)
  unfold WallInvariant.O WallInvariant.wall
  rw [OddImage.normal_app, OddImage.normal_zeros, WallInvariant.normal]
  simp only [↓reduceIte, List.append_assoc, append_assoc]
  have h1 := OddFuel.scan_ones n
    ([1] +> (([0, 0, 0, 0, 0] : List Γ) ^ (v * 2 + 1) +>
      ([1, 0, 0, 0, 0] +> (WallInvariant.normal bs +> default))))
  rw [← he] at h1
  have hpn := pow2_pos n
  have h2 := CounterBatch.right_pass_batch n (OddImage.first_fuel n (v * 2 + 1))
    ((2 ^ (v * 2 + 1) - 1) * 2) _ _ (by omega)
    (OddFuel.prime_gap0 (v * 2 + 1) (WallInvariant.normal bs +> default))
  have h3 := OddFuel.convert_gap0_odd n (OddImage.first_fuel n (v * 2 + 1)) v
    (WallInvariant.normal bs +> default) hb
  exact stepStar_stepPlus_trans (stepStar_trans h1 h2) h3

theorem zero_rotate : ∀ (u : ℕ),
    ([0, 0, 0] : List Γ) ++ ([0, 0, 0, 0, 0] : List Γ) ^ u ++ [1, 0, 0, 0, 0] =
      ([0, 0, 0, 0, 0] : List Γ) ^ u ++ [0, 0, 0, 1, 0] ++ [0, 0, 0]
  | 0 => rfl
  | u + 1 => by
    rw [pow_succ_list]
    change [0, 0, 0, 0, 0] ++ ([0, 0, 0] ++ ([0, 0, 0, 0, 0] : List Γ) ^ u ++ [1, 0, 0, 0, 0]) =
      [0, 0, 0, 0, 0] ++ (([0, 0, 0, 0, 0] : List Γ) ^ u ++ [0, 0, 0, 1, 0] ++ [0, 0, 0])
    rw [zero_rotate u]

theorem zero_rotate_side (u : ℕ) (r : ListBlank Γ) :
    ([0, 0, 0] : List Γ) +> (([0, 0, 0, 0, 0] : List Γ) ^ u +> ([1, 0, 0, 0, 0] +> r)) =
      ([0, 0, 0, 0, 0] : List Γ) ^ u +> ([0, 0, 0, 1, 0] +> ([0, 0, 0] +> r)) := by
  simpa only [append_assoc] using congrArg (· +> r) (zero_rotate u)

theorem zero_prime (L k u : ℕ) (bs : List Bool) (r : ListBlank Γ)
    (hk : k + (2 ^ (u + 1) - 1) < 2 ^ L) :
    (rGate (LC L (k + (2 ^ (u + 1) - 1)))
      ([0, 0, 0] +> (WallInvariant.normal (List.replicate u false ++ true :: bs) +> r))) [mtm]⊢*
      (rGate (LC L k)
        (([1, 0, 0, 0, 0] : List Γ) ^ u +>
          ([1, 0, 0, 1, 0, 0, 0, 0] +> (WallInvariant.normal bs +> r)))) := by
  rw [OddImage.normal_app, OddImage.normal_zeros, WallInvariant.normal]
  simp only [↓reduceIte, append_assoc]
  rw [zero_rotate_side]
  exact CounterBatch.right_pass_batch L k (2 ^ (u + 1) - 1) _ _ hk
    (OddFuel.prime_gap2 u (WallInvariant.normal bs +> r))

theorem zero_even_step (L k v : ℕ) (bs : List Bool) (r : ListBlank Γ)
    (hk : k + (2 ^ (v * 2 + 1) - 1) < 2 ^ L) :
    (rGate (LC L (k + (2 ^ (v * 2 + 1) - 1)))
      ([0, 0, 0] +>
        (WallInvariant.normal (List.replicate (v * 2) false ++ true :: bs) +> r))) [mtm]⊢⁺
      (rGate (LC (L + 1 + (v * 5 + 1)) (OddFuel.grown k (v * 5 + 1)))
        ([1, 0, 0, 0] +> (WallInvariant.normal bs +> r))) :=
  stepStar_stepPlus_trans (zero_prime L k (v * 2) bs r hk)
    (OddFuel.convert_gap2_even L k v (WallInvariant.normal bs +> r) (by omega))

theorem zero_odd_step (L k v : ℕ) (bs : List Bool) (r : ListBlank Γ)
    (hk : k + (2 ^ (v * 2 + 2) - 1) < 2 ^ L) :
    (rGate (LC L (k + (2 ^ (v * 2 + 2) - 1)))
      ([0, 0, 0] +>
        (WallInvariant.normal (List.replicate (v * 2 + 1) false ++ true :: bs) +> r))) [mtm]⊢⁺
      (rGate (LC (L + 1 + (v * 5 + 4)) (OddFuel.grown k (v * 5 + 4)))
        ([0, 0, 0] +> (WallInvariant.normal bs +> r))) := by
  have hk' : k + (2 ^ ((v * 2 + 1) + 1) - 1) < 2 ^ L := hk
  exact stepStar_stepPlus_trans (zero_prime L k (v * 2 + 1) bs r hk')
    (OddFuel.convert_gap2_odd L k v (WallInvariant.normal bs +> r) (by omega))

theorem grown_odd (k z : ℕ) (hz : 0 < z) : OddFuel.grown k z % 2 = 1 := by
  rcases z with _ | z
  · omega
  · unfold OddFuel.grown
    have hp := pow2_pos z
    have hpos : 2 ≤ (2 * k + 1) * 2 ^ z * 2 := by nlinarith
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

theorem remaining_lower (k u m : ℕ) (hk : 2 ^ (u + 1 + m) - 1 ≤ k) :
    2 ^ (u + 1) - 1 ≤ k ∧ 2 ^ (u + 1) * (2 ^ m - 1) ≤ k - (2 ^ (u + 1) - 1) := by
  rw [Nat.pow_add] at hk
  have hp1 := pow2_pos (u + 1)
  have hp2 := pow2_pos m
  have h1 : 2 ^ (u + 1) * (2 ^ m - 1) + 2 ^ (u + 1) = 2 ^ (u + 1) * 2 ^ m := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hp2)]
  omega

theorem grown_lower (k u m z : ℕ) (hk : 2 ^ (u + 1) * (2 ^ m - 1) ≤ k) (hz : 0 < z) :
    2 ^ m - 1 ≤ OddFuel.grown k z := by
  unfold OddFuel.grown
  have hp1 := pow2_pos (u + 1)
  have hp2 := pow2_pos m
  have htwo : 2 ≤ 2 ^ z := by
    rcases z with _ | z
    · omega
    · have := pow2_pos z; rw [Nat.pow_succ]; omega
  have h1 : 2 ^ m - 1 ≤ k := by
    have : 1 * (2 ^ m - 1) ≤ 2 ^ (u + 1) * (2 ^ m - 1) := Nat.mul_le_mul_right _ hp1
    omega
  have h2 : 2 * k + 1 ≤ (2 * k + 1) * 2 ^ z := by nlinarith
  omega

end OddRecursion

/-! ## OddRoute -/

namespace OddRoute

open CounterRules

inductive route : ℕ → ℕ → List Bool → ℕ → ℕ → List Bool → Prop where
  | RouteEven {L k v : ℕ} {tail : List Bool} :
      route L (k + (2 ^ (v * 2 + 1) - 1)) (List.replicate (v * 2) false ++ true :: tail)
        (L + 1 + (v * 5 + 1)) (OddFuel.grown k (v * 5 + 1)) tail
  | RouteOdd {L k v : ℕ} {tail : List Bool} {L' k' : ℕ} {rest : List Bool} :
      route (L + 1 + (v * 5 + 4)) (OddFuel.grown k (v * 5 + 4)) tail L' k' rest →
      route L (k + (2 ^ (v * 2 + 2) - 1)) (List.replicate (v * 2 + 1) false ++ true :: tail)
        L' k' rest

theorem route_run (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool) (r : ListBlank Γ)
    (hr : route L k bs L' k' rest) (hk : k < 2 ^ L) :
    (rGate (LC L k) ([0, 0, 0] +> (WallInvariant.normal bs +> r))) [mtm]⊢⁺
      (rGate (LC L' k') ([1, 0, 0, 0] +> (WallInvariant.normal rest +> r))) := by
  induction hr with
  | @RouteEven L k v tail => exact OddRecursion.zero_even_step L k v tail r hk
  | @RouteOdd L k v tail L' k' rest _ ih =>
    have hb := OddFuel.grown_bound L k (v * 5 + 4) (by omega)
    exact stepPlus_trans (OddRecursion.zero_odd_step L k v tail r hk) (ih (by omega))

theorem route_bound (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hr : route L k bs L' k' rest) (hk : k < 2 ^ L) :
    k' + 1 < 2 ^ L' ∧ k' % 2 = 1 := by
  induction hr with
  | @RouteEven L k v tail =>
    exact ⟨OddFuel.grown_bound L k (v * 5 + 1) (by omega),
      OddRecursion.grown_odd k (v * 5 + 1) (by omega)⟩
  | @RouteOdd L k v tail L' k' rest _ ih =>
    have hb := OddFuel.grown_bound L k (v * 5 + 4) (by omega)
    exact ih (by omega)

theorem route_dimensions (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hr : route L k bs L' k' rest) :
    ∃ j, bs.length = 2 * j + 1 + rest.length ∧ L' = L + 5 * j + 2 := by
  induction hr with
  | @RouteEven L k v tail =>
    exact ⟨v, by simp; omega, by omega⟩
  | @RouteOdd L k v tail L' k' rest _ ih =>
    obtain ⟨j, hlen, hL⟩ := ih
    exact ⟨v + 1 + j, by simp; omega, by omega⟩

theorem first_true (bs : List Bool) (h : true ∈ bs) :
    ∃ u tail, bs = List.replicate u false ++ true :: tail := by
  induction bs with
  | nil => cases h
  | cons b bs ih =>
    cases b
    · simp only [List.mem_cons, Bool.true_eq_false, false_or] at h
      obtain ⟨u, tail, rfl⟩ := ih h
      exact ⟨u + 1, tail, by rw [List.replicate_succ]; rfl⟩
    · exact ⟨0, bs, rfl⟩

theorem marked_true (bs : List Bool) (h : WallInvariant.marked 0 bs) : true ∈ bs := by
  rcases h with ⟨pre, post, rfl, _⟩
  simp

theorem marked_drop_pair (b : Bool) (bs : List Bool)
    (h : WallInvariant.marked 0 (false :: b :: bs)) :
    WallInvariant.marked 0 bs := by
  rcases h with ⟨pre, post, he, hp⟩
  rcases pre with _ | ⟨a, _ | ⟨a', pre⟩⟩
  · simp at he
  · simp at hp
  · simp only [List.cons_append, List.cons.injEq] at he
    exact ⟨pre, post, he.2.2, by simp at hp; omega⟩

theorem marked_after_odd (v : ℕ) (bs : List Bool)
    (h : WallInvariant.marked 0 (List.replicate (v * 2 + 1) false ++ true :: bs)) :
    WallInvariant.marked 0 bs := by
  induction v with
  | zero => exact marked_drop_pair true bs h
  | succ v ih =>
    rw [show (v + 1) * 2 + 1 = (v * 2 + 1) + 1 + 1 by omega,
      List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append] at h
    exact ih (marked_drop_pair false _ h)

theorem grown_lower_double (k u m z : ℕ)
    (hk : 2 ^ (u + 1) * (2 ^ m - 1) ≤ k) (hz : 0 < z) :
    2 ^ (m + 1) - 1 ≤ OddFuel.grown k z := by
  unfold OddFuel.grown
  have hu : 2 ≤ 2 ^ (u + 1) := by have := pow2_pos u; rw [Nat.pow_succ]; omega
  have hm := pow2_pos m
  have htwo : 2 ≤ 2 ^ z := by
    rcases z with _ | z
    · omega
    · have := pow2_pos z; rw [Nat.pow_succ]; omega
  have h1 : 2 * (2 ^ m - 1) ≤ k := by nlinarith
  have h2 : 2 * (2 * k + 1) ≤ (2 * k + 1) * 2 ^ z := by nlinarith
  rw [Nat.pow_succ]
  omega

theorem marked_route_bounded (bound : ℕ) :
    ∀ bs L k, bs.length ≤ bound → WallInvariant.marked 0 bs → 2 ^ bs.length - 1 ≤ k →
      ∃ L' k' rest, route L k bs L' k' rest ∧ 2 ^ (rest.length + 1) - 1 ≤ k' := by
  induction bound with
  | zero =>
    intro bs _ _ hlen hmark _
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    cases marked_true [] hmark
  | succ bound ih =>
    intro bs L k hlen hmark hfuel
    obtain ⟨u, tail, rfl⟩ := first_true bs (marked_true bs hmark)
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen hfuel
    have hfuel' : 2 ^ (u + 1 + tail.length) - 1 ≤ k := by
      rwa [show u + 1 + tail.length = u + (tail.length + 1) by omega]
    obtain ⟨hprime, hremain⟩ := OddRecursion.remaining_lower k u tail.length hfuel'
    set rem := k - (2 ^ (u + 1) - 1)
    have hdecomp : k = rem + (2 ^ (u + 1) - 1) := by omega
    rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
    · refine ⟨L + 1 + (v * 5 + 1), OddFuel.grown rem (v * 5 + 1), tail, ?_, ?_⟩
      · rw [hdecomp, Nat.mul_comm 2 v]; exact .RouteEven
      · rw [Nat.mul_comm 2 v] at hremain
        exact grown_lower_double rem (v * 2) tail.length (v * 5 + 1) hremain (by omega)
    · rw [show 2 * v + 1 = v * 2 + 1 by omega] at hmark hlen hremain hdecomp ⊢
      have htail := marked_after_odd v tail hmark
      have hremain' :=
        OddRecursion.grown_lower rem (v * 2 + 1) tail.length (v * 5 + 4) hremain (by omega)
      obtain ⟨L', k', rest, hroute, hlower⟩ :=
        ih tail (L + 1 + (v * 5 + 4)) (OddFuel.grown rem (v * 5 + 4)) (by omega) htail hremain'
      exact ⟨L', k', rest, by rw [hdecomp]; exact .RouteOdd hroute, hlower⟩

theorem marked_route (L k : ℕ) (bs : List Bool)
    (hmark : WallInvariant.marked 0 bs) (hfuel : 2 ^ bs.length - 1 ≤ k) :
    ∃ L' k' rest, route L k bs L' k' rest ∧ 2 ^ (rest.length + 1) - 1 ≤ k' :=
  marked_route_bounded bs.length bs L k le_rfl hmark hfuel

theorem zero_marked_exit (L k : ℕ) (bs : List Bool) (r : ListBlank Γ)
    (hmark : WallInvariant.marked 0 bs) (hfuel : 2 ^ bs.length - 1 ≤ k) (hbound : k < 2 ^ L) :
    ∃ L' k' rest j,
      route L k bs L' k' rest ∧
      bs.length = 2 * j + 1 + rest.length ∧ L' = L + 5 * j + 2 ∧
      2 ^ (rest.length + 1) - 1 ≤ k' ∧ k' + 1 < 2 ^ L' ∧ k' % 2 = 1 ∧
      ((rGate (LC L k) ([0, 0, 0] +> (WallInvariant.normal bs +> r))) [mtm]⊢⁺
        (rGate (LC L' k') ([1, 0, 0, 0] +> (WallInvariant.normal rest +> r)))) := by
  obtain ⟨L', k', rest, hroute, hlower⟩ := marked_route L k bs hmark hfuel
  obtain ⟨j, hlen, hL⟩ := route_dimensions L k bs L' k' rest hroute
  obtain ⟨hb, ho⟩ := route_bound L k bs L' k' rest hroute hbound
  exact ⟨L', k', rest, j, hroute, hlen, hL, hlower, hb, ho,
    route_run L k bs L' k' rest r hroute hbound⟩

end OddRoute

/-! ## OddMarkedEntry -/

namespace OddMarkedEntry

open CounterRules

def odd_wall (n : ℕ) (bs : List Bool) (r : ListBlank Γ) : Cfg Γ Λ :=
  (([0] : List Γ) +> LocalPasses.lh) {{qA}}>
    (([1, 1] : List Γ) ^ n +> ([1] +> (WallInvariant.normal bs +> r)))

theorem even_entry (n v : ℕ) (bs : List Bool) (r : ListBlank Γ) (hn : v * 2 + 1 ≤ n) :
    (odd_wall n (List.replicate (v * 2) false ++ true :: bs) r) [mtm]⊢⁺
      (rGate (LC (n + 1 + v * 5) (OddFuel.grown (OddImage.first_fuel n (v * 2)) (v * 5)))
        ([1, 0, 0, 0] +> (WallInvariant.normal bs +> r))) := by
  obtain ⟨he, hb⟩ := OddImage.first_fuel_bounds n (v * 2) hn
  unfold odd_wall
  rw [OddImage.normal_app, OddImage.normal_zeros, WallInvariant.normal]
  simp only [↓reduceIte, append_assoc]
  have h1 := OddFuel.scan_ones n
    ([1] +> (([0, 0, 0, 0, 0] : List Γ) ^ (v * 2) +>
      ([1, 0, 0, 0, 0] +> (WallInvariant.normal bs +> r))))
  rw [← he] at h1
  have hpn := pow2_pos n
  have h2 := CounterBatch.right_pass_batch n (OddImage.first_fuel n (v * 2))
    ((2 ^ (v * 2) - 1) * 2) _ _ (by omega)
    (OddFuel.prime_gap0 (v * 2) (WallInvariant.normal bs +> r))
  have h3 := OddFuel.convert_gap0_even n (OddImage.first_fuel n (v * 2)) v
    (WallInvariant.normal bs +> r) hb
  exact stepStar_stepPlus_trans (stepStar_trans h1 h2) h3

theorem odd_entry (n v : ℕ) (bs : List Bool) (r : ListBlank Γ) (hn : v * 2 + 2 ≤ n) :
    (odd_wall n (List.replicate (v * 2 + 1) false ++ true :: bs) r) [mtm]⊢⁺
      (rGate (LC (n + 1 + (v * 5 + 3))
          (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)))
        ([0, 0, 0] +> (WallInvariant.normal bs +> r))) := by
  obtain ⟨he, hb⟩ := OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)
  unfold odd_wall
  rw [OddImage.normal_app, OddImage.normal_zeros, WallInvariant.normal]
  simp only [↓reduceIte, append_assoc]
  have h1 := OddFuel.scan_ones n
    ([1] +> (([0, 0, 0, 0, 0] : List Γ) ^ (v * 2 + 1) +>
      ([1, 0, 0, 0, 0] +> (WallInvariant.normal bs +> r))))
  rw [← he] at h1
  have hpn := pow2_pos n
  have h2 := CounterBatch.right_pass_batch n (OddImage.first_fuel n (v * 2 + 1))
    ((2 ^ (v * 2 + 1) - 1) * 2) _ _ (by omega)
    (OddFuel.prime_gap0 (v * 2 + 1) (WallInvariant.normal bs +> r))
  have h3 := OddFuel.convert_gap0_odd n (OddImage.first_fuel n (v * 2 + 1)) v
    (WallInvariant.normal bs +> r) hb
  exact stepStar_stepPlus_trans (stepStar_trans h1 h2) h3

theorem initial_margin (n u m z : ℕ) (hn : u + m + 2 ≤ n) (hz : 3 ≤ z) :
    2 ^ (m + 3) - 1 ≤ OddFuel.grown (OddImage.first_fuel n u) z := by
  obtain ⟨he, _⟩ := OddImage.first_fuel_bounds n u (by omega)
  have hcap : 2 ^ (u + m + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rw [Nat.pow_add 2 (u + m) 2, Nat.pow_add 2 u m] at hcap
  change 2 ^ u * 2 ^ m * 4 ≤ 2 ^ n at hcap
  have hpu := pow2_pos u
  have hpm := pow2_pos m
  have he' : OddImage.first_fuel n u + 2 ^ u * 2 = 2 ^ n + 1 := by omega
  have hpu1 : 2 ^ u ≤ 2 ^ u * 2 ^ m := by nlinarith
  have hk : 2 ^ m ≤ OddImage.first_fuel n u := by nlinarith
  have hzpow : 2 ^ 3 ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) hz
  change 8 ≤ 2 ^ z at hzpow
  unfold OddFuel.grown
  have hprod : 2 ^ m * 2 * 8 ≤ (2 * OddImage.first_fuel n u + 1) * 2 ^ z := by nlinarith
  rw [Nat.pow_add 2 m 3]
  change 2 ^ m * 8 - 1 ≤ _
  omega

theorem route_margin (extra L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hroute : OddRoute.route L k bs L' k' rest)
    (hfuel : 2 ^ (bs.length + extra) - 1 ≤ k) :
    2 ^ (rest.length + extra) - 1 ≤ k' := by
  induction hroute with
  | @RouteEven L k v tail =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hfuel
    have hfuel' : 2 ^ (v * 2 + 1 + (tail.length + extra)) - 1 ≤ k + (2 ^ (v * 2 + 1) - 1) := by
      rwa [show v * 2 + 1 + (tail.length + extra) = v * 2 + (tail.length + 1) + extra by omega]
    obtain ⟨_, hrem⟩ := OddRecursion.remaining_lower _ (v * 2) (tail.length + extra) hfuel'
    rw [Nat.add_sub_cancel] at hrem
    exact OddRecursion.grown_lower k (v * 2) (tail.length + extra) (v * 5 + 1) hrem (by omega)
  | @RouteOdd L k v tail L' k' rest _ ih =>
    apply ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at hfuel
    have hfuel' : 2 ^ ((v * 2 + 1) + 1 + (tail.length + extra)) - 1 ≤
        k + (2 ^ ((v * 2 + 1) + 1) - 1) := by
      rwa [show (v * 2 + 1) + 1 + (tail.length + extra) =
        v * 2 + 1 + (tail.length + 1) + extra by omega]
    obtain ⟨_, hrem⟩ := OddRecursion.remaining_lower _ (v * 2 + 1) (tail.length + extra) hfuel'
    rw [Nat.add_sub_cancel] at hrem
    exact OddRecursion.grown_lower k (v * 2 + 1) (tail.length + extra) (v * 5 + 4) hrem (by omega)

theorem marked_entry (n : ℕ) (bs : List Bool) (r : ListBlank Γ)
    (hzero : WallInvariant.first_zero bs) (hmark : WallInvariant.marked 0 bs)
    (hlen : bs.length + 1 ≤ n) :
    ∃ L k rest j,
      bs.length = 2 * j + 1 + rest.length ∧ L = n + 5 * j + 1 ∧
      k % 2 = 1 ∧ k + 1 < 2 ^ L ∧ 2 ^ (rest.length + 3) - 1 ≤ k ∧
      ((odd_wall n bs r) [mtm]⊢⁺
        (rGate (LC L k) ([1, 0, 0, 0] +> (WallInvariant.normal rest +> r)))) := by
  obtain ⟨u, tail, rfl⟩ := OddRoute.first_true bs (OddRoute.marked_true bs hmark)
  simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
  have hu : 0 < u := by
    rcases hzero with ⟨_, hz⟩
    rcases u with _ | u
    · simp at hz
    · omega
  rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
  · rw [Nat.mul_comm 2 v] at hlen hu ⊢
    refine ⟨n + 1 + v * 5, OddFuel.grown (OddImage.first_fuel n (v * 2)) (v * 5), tail, v,
      by simp; omega, by omega, OddRecursion.grown_odd _ _ (by omega),
      OddFuel.grown_bound _ _ _ (OddImage.first_fuel_bounds n (v * 2) (by omega)).2,
      initial_margin n (v * 2) tail.length (v * 5) (by omega) (by omega),
      even_entry n v tail r (by omega)⟩
  · rw [show 2 * v + 1 = v * 2 + 1 by omega] at hmark hlen ⊢
    have htail := OddRoute.marked_after_odd v tail hmark
    set L0 := n + 1 + (v * 5 + 3)
    set k0 := OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
    have hmargin : 2 ^ (tail.length + 3) - 1 ≤ k0 :=
      initial_margin n (v * 2 + 1) tail.length (v * 5 + 3) (by omega) (by omega)
    have hbasic : 2 ^ tail.length - 1 ≤ k0 := by
      have : 2 ^ tail.length ≤ 2 ^ (tail.length + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hcap : k0 + 1 < 2 ^ L0 :=
      OddFuel.grown_bound _ _ _ (OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)).2
    obtain ⟨L', k', rest, hroute, _⟩ := OddRoute.marked_route L0 k0 tail htail hbasic
    obtain ⟨j, hdim, hL⟩ := OddRoute.route_dimensions L0 k0 tail L' k' rest hroute
    obtain ⟨hbound, hodd⟩ := OddRoute.route_bound L0 k0 tail L' k' rest hroute (by omega)
    refine ⟨L', k', rest, v + 1 + j, by simp; omega, by omega, hodd, hbound,
      route_margin 3 L0 k0 tail L' k' rest hroute hmargin,
      stepPlus_trans (odd_entry n v tail r (by omega))
        (OddRoute.route_run L0 k0 tail L' k' rest r hroute (by omega))⟩

end OddMarkedEntry

/-! ## MarkedTrace -/

namespace MarkedTrace

open CounterRules

inductive wall_route : ℕ → List Bool → ℕ → ℕ → List Bool → Prop where
  | WallEven {n v : ℕ} {tail : List Bool} :
      wall_route n (List.replicate (v * 2) false ++ true :: tail)
        (n + 1 + v * 5) (OddFuel.grown (OddImage.first_fuel n (v * 2)) (v * 5)) tail
  | WallOdd {n v : ℕ} {tail : List Bool} {L k : ℕ} {rest : List Bool} :
      OddRoute.route (n + 1 + (v * 5 + 3))
        (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)) tail L k rest →
      wall_route n (List.replicate (v * 2 + 1) false ++ true :: tail) L k rest

theorem first_zero_prefix (u : ℕ) (tail : List Bool)
    (h : WallInvariant.first_zero (List.replicate u false ++ true :: tail)) : 0 < u := by
  rcases h with ⟨_, he⟩
  rcases u with _ | u
  · simp at he
  · omega

theorem initial_margin4 (n u m z : ℕ) (hn : u + m + 2 ≤ n) (hz : 3 ≤ z) :
    2 ^ (m + 4) - 1 ≤ OddFuel.grown (OddImage.first_fuel n u) z := by
  obtain ⟨he, _⟩ := OddImage.first_fuel_bounds n u (by omega)
  have hcap : 2 ^ (u + m + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rw [Nat.pow_add 2 (u + m) 2, Nat.pow_add 2 u m] at hcap
  change 2 ^ u * 2 ^ m * 4 ≤ 2 ^ n at hcap
  have hpu := pow2_pos u
  have hpm := pow2_pos m
  have he' : OddImage.first_fuel n u + 2 ^ u * 2 = 2 ^ n + 1 := by omega
  have hpu1 : 2 ^ u ≤ 2 ^ u * 2 ^ m := by nlinarith
  have hk : 2 ^ m ≤ OddImage.first_fuel n u := by nlinarith
  have hzpow : 2 ^ 3 ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) hz
  change 8 ≤ 2 ^ z at hzpow
  unfold OddFuel.grown
  have hprod : 2 ^ m * 16 ≤ (2 * OddImage.first_fuel n u + 1) * 2 ^ z := by nlinarith
  rw [Nat.pow_add 2 m 4]
  change 2 ^ m * 16 - 1 ≤ _
  omega

theorem route_dimensions (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : wall_route n bs L k rest) :
    ∃ j, bs.length = 2 * j + 1 + rest.length ∧ L = n + 5 * j + 1 := by
  cases hr with
  | @WallEven v _ => exact ⟨v, by simp; omega, by omega⟩
  | @WallOdd v tail L k rest h =>
    obtain ⟨j, hlen, hL⟩ := OddRoute.route_dimensions _ _ _ _ _ _ h
    exact ⟨v + 1 + j, by simp; omega, by omega⟩

theorem route_run (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool) (r : ListBlank Γ)
    (hr : wall_route n bs L k rest) (hlen : bs.length + 1 ≤ n) :
    (OddMarkedEntry.odd_wall n bs r) [mtm]⊢⁺
      (rGate (LC L k) ([1, 0, 0, 0] +> (WallInvariant.normal rest +> r))) := by
  cases hr with
  | @WallEven v _ =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    exact OddMarkedEntry.even_entry n v rest r (by omega)
  | @WallOdd v tail L k rest h =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    have hb := OddFuel.grown_bound n (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
      (OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)).2
    exact stepPlus_trans (OddMarkedEntry.odd_entry n v tail r (by omega))
      (OddRoute.route_run _ _ tail L k rest r h (by omega))

theorem route_bounds (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : wall_route n bs L k rest) (hzero : WallInvariant.first_zero bs)
    (hlen : bs.length + 1 ≤ n) :
    k + 1 < 2 ^ L ∧ k % 2 = 1 := by
  cases hr with
  | @WallEven v _ =>
    have hv := first_zero_prefix (v * 2) rest hzero
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    exact ⟨OddFuel.grown_bound _ _ _ (OddImage.first_fuel_bounds n (v * 2) (by omega)).2,
      OddRecursion.grown_odd _ _ (by omega)⟩
  | @WallOdd v tail L k rest h =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    have hb := OddFuel.grown_bound n (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
      (OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)).2
    exact OddRoute.route_bound _ _ tail L k rest h (by omega)

theorem route_margin4 (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : wall_route n bs L k rest) (hzero : WallInvariant.first_zero bs)
    (hlen : bs.length + 1 ≤ n) :
    2 ^ (rest.length + 4) - 1 ≤ k := by
  cases hr with
  | @WallEven v _ =>
    have hv := first_zero_prefix (v * 2) rest hzero
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    exact initial_margin4 n (v * 2) rest.length (v * 5) (by omega) (by omega)
  | @WallOdd v tail L k rest h =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    exact OddMarkedEntry.route_margin 4 _ _ tail L k rest h
      (initial_margin4 n (v * 2 + 1) tail.length (v * 5 + 3) (by omega) (by omega))

theorem marked_route_exists (n : ℕ) (bs : List Bool)
    (hzero : WallInvariant.first_zero bs) (hmark : WallInvariant.marked 0 bs)
    (hlen : bs.length + 1 ≤ n) :
    ∃ L k rest, wall_route n bs L k rest := by
  obtain ⟨u, tail, rfl⟩ := OddRoute.first_true bs (OddRoute.marked_true bs hmark)
  simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
  rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
  · rw [Nat.mul_comm 2 v]; exact ⟨_, _, tail, .WallEven⟩
  · rw [show 2 * v + 1 = v * 2 + 1 by omega] at hmark hlen ⊢
    have htail := OddRoute.marked_after_odd v tail hmark
    set L0 := n + 1 + (v * 5 + 3)
    set k0 := OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
    have hmargin : 2 ^ (tail.length + 4) - 1 ≤ k0 :=
      initial_margin4 n (v * 2 + 1) tail.length (v * 5 + 3) (by omega) (by omega)
    have hbasic : 2 ^ tail.length - 1 ≤ k0 := by
      have : 2 ^ tail.length ≤ 2 ^ (tail.length + 4) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨L, k, rest, hroute, _⟩ := OddRoute.marked_route L0 k0 tail htail hbasic
    exact ⟨L, k, rest, .WallOdd hroute⟩

theorem marked_entry_trace (n : ℕ) (bs : List Bool) (r : ListBlank Γ)
    (hzero : WallInvariant.first_zero bs) (hmark : WallInvariant.marked 0 bs)
    (hlen : bs.length + 1 ≤ n) :
    ∃ L k rest j,
      wall_route n bs L k rest ∧
      bs.length = 2 * j + 1 + rest.length ∧ L = n + 5 * j + 1 ∧
      k % 2 = 1 ∧ k + 1 < 2 ^ L ∧ 2 ^ (rest.length + 4) - 1 ≤ k ∧
      ((OddMarkedEntry.odd_wall n bs r) [mtm]⊢⁺
        (rGate (LC L k) ([1, 0, 0, 0] +> (WallInvariant.normal rest +> r)))) := by
  obtain ⟨L, k, rest, hroute⟩ := marked_route_exists n bs hzero hmark hlen
  obtain ⟨j, hdim, hL⟩ := route_dimensions n bs L k rest hroute
  obtain ⟨hbound, hodd⟩ := route_bounds n bs L k rest hroute hzero hlen
  exact ⟨L, k, rest, j, hroute, hdim, hL, hodd, hbound,
    route_margin4 n bs L k rest hroute hzero hlen, route_run n bs L k rest r hroute hlen⟩

end MarkedTrace

/-! ## OdDeficit -/

namespace OdDeficit

theorem grown_complete (k z : ℕ) : OddFuel.grown k z + 1 = (2 * k + 1) * 2 ^ z := by
  unfold OddFuel.grown
  have hp : 1 ≤ (2 * k + 1) * 2 ^ z := Nat.mul_pos (by omega) (pow2_pos z)
  omega

theorem step_deficit (L k D u z : ℕ) (h : k + (2 ^ (u + 1) - 1) + 1 + D = 2 ^ L) :
    OddFuel.grown k z + 1 + D * 2 ^ (z + 1) + (2 ^ (u + 2) - 1) * 2 ^ z = 2 ^ (L + 1 + z) := by
  rw [grown_complete]
  have hpu := pow2_pos u
  have hpz := pow2_pos z
  have h1 : 2 ^ (u + 1) = 2 ^ u * 2 := Nat.pow_succ _ _
  have h2 : 2 ^ (u + 2) = 2 ^ u * 4 := Nat.pow_add 2 u 2
  have h3 : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
  have h4 : 2 ^ (L + 1 + z) = 2 ^ L * 2 * 2 ^ z := by
    rw [show L + 1 + z = (L + 1) + z by omega, Nat.pow_add, Nat.pow_succ]
  rw [h1] at h
  have hk_eq : k + 2 ^ u * 2 + D = 2 ^ L := by omega
  rw [h2, h3, h4]
  have hsub : (2 ^ u * 4 - 1) * 2 ^ z + 2 ^ z = 2 ^ u * 4 * 2 ^ z := by
    have : 1 ≤ 2 ^ u * 4 := by omega
    rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (by nlinarith)]
  nlinarith

theorem correction_bound (u z : ℕ) :
    0 < (2 ^ (u + 2) - 1) * 2 ^ z ∧ (2 ^ (u + 2) - 1) * 2 ^ z < 2 ^ (u + 2 + z) := by
  have hpu := pow2_pos u
  have hpz := pow2_pos z
  have h1 : 4 ≤ 2 ^ (u + 2) := by rw [Nat.pow_add 2 u 2]; change 4 ≤ 2 ^ u * 4; omega
  rw [Nat.pow_add 2 (u + 2) z]
  have hsub : 2 ^ (u + 2) - 1 < 2 ^ (u + 2) := by omega
  exact ⟨Nat.mul_pos (by omega) hpz, Nat.mul_lt_mul_of_pos_right hsub hpz⟩

theorem route_deficit (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hr : OddRoute.route L k bs L' k' rest) :
    ∀ D, k + 1 + D = 2 ^ L →
      ∃ j c,
        bs.length = 2 * j + 1 + rest.length ∧ L' = L + 5 * j + 2 ∧
        (0 < c ∧ c < 2 ^ (7 * j + 3)) ∧
        k' + 1 + D * 2 ^ (5 * j + 2) + c = 2 ^ L' := by
  induction hr with
  | @RouteEven L k v tail =>
    intro D hD
    refine ⟨v, (2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5 + 1), by simp; omega, by omega, ?_, ?_⟩
    · have hc := correction_bound (v * 2) (v * 5 + 1)
      rwa [show v * 2 + 2 + (v * 5 + 1) = 7 * v + 3 by omega] at hc
    · rw [show 5 * v + 2 = (v * 5 + 1) + 1 by omega]
      exact step_deficit L k D (v * 2) (v * 5 + 1) (by omega)
  | @RouteOdd L k v tail L' k' rest _ ih =>
    intro D hD
    set c0 := (2 ^ (v * 2 + 3) - 1) * 2 ^ (v * 5 + 4)
    set D0 := D * 2 ^ (v * 5 + 5) + c0
    have hD0 : OddFuel.grown k (v * 5 + 4) + 1 + D0 = 2 ^ (L + 1 + (v * 5 + 4)) := by
      unfold D0 c0
      have hs := step_deficit L k D (v * 2 + 1) (v * 5 + 4) (by omega)
      rw [show (v * 5 + 4) + 1 = v * 5 + 5 by omega,
        show (v * 2 + 1) + 2 = v * 2 + 3 by omega] at hs
      linarith
    obtain ⟨j, c, hlen, hL, hc, hE⟩ := ih D0 hD0
    refine ⟨v + 1 + j, c0 * 2 ^ (5 * j + 2) + c, by simp; omega, by omega, ?_, ?_⟩
    · have hc0 : 0 < c0 ∧ c0 < 2 ^ (7 * v + 7) := by
        have hcb := correction_bound (v * 2 + 1) (v * 5 + 4)
        simpa only [show (v * 2 + 1) + 2 + (v * 5 + 4) = 7 * v + 7 by omega,
          show (v * 2 + 1) + 2 = v * 2 + 3 by omega] using hcb
      have hprod : c0 * 2 ^ (5 * j + 2) < 2 ^ (7 * v + 5 * j + 9) := by
        rw [show 7 * v + 5 * j + 9 = (7 * v + 7) + (5 * j + 2) by omega,
          Nat.pow_add 2 (7 * v + 7) (5 * j + 2)]
        exact Nat.mul_lt_mul_of_pos_right hc0.2 (pow2_pos (5 * j + 2))
      have hp1 : 2 ^ (7 * v + 5 * j + 9) ≤ 2 ^ (7 * (v + 1 + j) + 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hp2 : 2 ^ (7 * j + 3) ≤ 2 ^ (7 * (v + 1 + j) + 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [show 7 * (v + 1 + j) + 3 = (7 * (v + 1 + j) + 2) + 1 by omega,
        Nat.pow_succ 2 (7 * (v + 1 + j) + 2)]
      exact ⟨Nat.add_pos_right _ hc.1, by linarith [hc.2, hprod, hp1, hp2]⟩
    · have hP : 2 ^ (5 * (v + 1 + j) + 2) = 2 ^ (v * 5 + 5) * 2 ^ (5 * j + 2) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hP]
      unfold D0 at hE
      linarith

theorem initial_deficit (n u z : ℕ) (hn : u + 1 ≤ n) :
    OddFuel.grown (OddImage.first_fuel n u) z + 1 +
      (2 ^ (u + 2) - 3) * 2 ^ z = 2 ^ (n + 1 + z) := by
  obtain ⟨hE, _⟩ := OddImage.first_fuel_bounds n u hn
  rw [grown_complete]
  have hpu := pow2_pos u
  have hpz := pow2_pos z
  have hpn := pow2_pos n
  have hE' : OddImage.first_fuel n u + 2 ^ u * 2 = 2 ^ n + 1 := by omega
  have h1 : 2 ^ (u + 2) = 2 ^ u * 4 := Nat.pow_add 2 u 2
  have h2 : 2 ^ (n + 1 + z) = 2 ^ n * 2 * 2 ^ z := by
    rw [show n + 1 + z = (n + 1) + z by omega, Nat.pow_add, Nat.pow_succ]
  rw [h1, h2]
  have hsub : (2 ^ u * 4 - 3) * 2 ^ z + 3 * 2 ^ z = 2 ^ u * 4 * 2 ^ z := by
    rw [Nat.sub_mul, Nat.sub_add_cancel (by nlinarith)]
  nlinarith

theorem initial_even_deficit (n v : ℕ) (tail : List Bool)
    (h : (List.replicate (v * 2) false ++ true :: tail).length + 1 ≤ n) :
    OddFuel.grown (OddImage.first_fuel n (v * 2)) (v * 5) + 1 +
      (2 ^ (v * 2 + 2) - 3) * 2 ^ (v * 5) = 2 ^ (n + 1 + v * 5) := by
  simp only [List.length_append, List.length_replicate, List.length_cons] at h
  exact initial_deficit n (v * 2) (v * 5) (by omega)

theorem initial_odd_route_deficit (n v : ℕ) (tail : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : OddRoute.route (n + 1 + (v * 5 + 3))
      (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)) tail L k rest)
    (hn : (List.replicate (v * 2 + 1) false ++ true :: tail).length + 1 ≤ n) :
    ∃ j c,
      tail.length = 2 * j + 1 + rest.length ∧ L = n + 5 * (v + 1 + j) + 1 ∧
      (0 < c ∧ c < 2 ^ (7 * j + 3)) ∧
      k + 1 + (2 ^ (v * 2 + 3) - 3) * 2 ^ (5 * (v + 1 + j)) + c = 2 ^ L := by
  simp only [List.length_append, List.length_replicate, List.length_cons] at hn
  have hD := initial_deficit n (v * 2 + 1) (v * 5 + 3) (by omega)
  obtain ⟨j, c, hlen, hL, hc, hE⟩ :=
    route_deficit _ _ tail L k rest hr ((2 ^ (v * 2 + 1 + 2) - 3) * 2 ^ (v * 5 + 3)) hD
  refine ⟨j, c, hlen, by omega, hc, ?_⟩
  have hP : 2 ^ (5 * (v + 1 + j)) = 2 ^ (v * 5 + 3) * 2 ^ (5 * j + 2) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hP, show v * 2 + 3 = v * 2 + 1 + 2 by omega]
  linarith

end OdDeficit

/-! ## RouteMarkerBound -/

namespace RouteMarkerBound

theorem prefix_true_index (u : ℕ) (tail : List Bool) (i : ℕ)
    (h : (List.replicate u false ++ true :: tail).getD i false = true) : u ≤ i := by
  by_contra hgt
  have hi : i < (List.replicate u false).length := by simp; omega
  simp [List.getD, List.getElem?_append_left hi,
    show i < u by omega] at h

theorem prefix_tail_nth (u : ℕ) (tail : List Bool) (i : ℕ)
    (hi : u < i)
    (h : (List.replicate u false ++ true :: tail).getD i false = true) :
    tail.getD (i - u - 1) false = true := by
  have hle : (List.replicate u false).length ≤ i := by simp; omega
  simp only [List.getD, List.getElem?_append_right hle, List.length_replicate] at h
  rw [show i - u = (i - u - 1) + 1 by omega] at h
  simpa [List.getD] using h

theorem route_known_even (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hroute : OddRoute.route L k bs L' k' rest) :
    ∀ i, bs.getD i false = true → i % 2 = 0 → bs.length ≤ i + 1 + rest.length := by
  induction hroute with
  | @RouteEven L k v tail =>
    intro i hnth _
    have := prefix_true_index (v * 2) tail i hnth
    simp; omega
  | @RouteOdd L k v tail L' k' rest _ ih =>
    intro i hnth hpar
    have hlow := prefix_true_index (v * 2 + 1) tail i hnth
    have hstrict : v * 2 + 1 < i := by omega
    have htail := prefix_tail_nth (v * 2 + 1) tail i hstrict hnth
    have hbound := ih (i - (v * 2 + 1) - 1) htail (by omega)
    simp; omega

theorem route_known_even_bound (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool) (j i : ℕ)
    (hr : OddRoute.route L k bs L' k' rest)
    (hlen : bs.length = 2 * j + 1 + rest.length)
    (hnth : bs.getD i false = true) (hpar : i % 2 = 0) :
    2 * j ≤ i := by
  have := route_known_even L k bs L' k' rest hr i hnth hpar
  omega

end RouteMarkerBound

/-! ## GuardedRoute -/

namespace GuardedRoute

def good_deficit (j delta : ℕ) : Prop :=
  (1 ≤ j ∧ delta = (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j)) ∨
  (∃ u c, 2 ≤ j ∧ u + 1 ≤ 2 * j ∧ c < 2 ^ (5 * j - 5) ∧
    delta = (2 ^ (u + 2) - 3) * 2 ^ (5 * j) + c)

def source_data (n : ℕ) (bs : List Bool) : Prop :=
  ∃ L k rest j delta,
    MarkedTrace.wall_route n bs L k rest ∧
    bs.length = 2 * j + 1 + rest.length ∧ L = n + 5 * j + 1 ∧
    k + 1 + delta = 2 ^ L ∧ good_deficit j delta

theorem package (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool) (j delta : ℕ)
    (hr : MarkedTrace.wall_route n bs L k rest) (hL : L = n + 5 * j + 1)
    (hD : k + 1 + delta = 2 ^ L) (hG : good_deficit j delta) :
    source_data n bs := by
  obtain ⟨j0, hlen, hL0⟩ := MarkedTrace.route_dimensions n bs L k rest hr
  have hj : j0 = j := by omega
  subst hj
  exact ⟨L, k, rest, j0, delta, hr, hlen, hL, hD, hG⟩

theorem direct_data (n j : ℕ) (tail : List Bool)
    (hj : 1 ≤ j) (hlen : (List.replicate (j * 2) false ++ true :: tail).length + 1 ≤ n) :
    source_data n (List.replicate (j * 2) false ++ true :: tail) := by
  refine package n _ (n + 1 + j * 5)
    (OddFuel.grown (OddImage.first_fuel n (j * 2)) (j * 5)) tail j
    ((2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j)) .WallEven (by omega) ?_ (Or.inl ⟨hj, rfl⟩)
  rw [Nat.mul_comm 2 j, Nat.mul_comm 5 j]
  exact OdDeficit.initial_even_deficit n j tail hlen

theorem routed_data (n v : ℕ) (tail : List Bool) (L k : ℕ) (rest : List Bool) (r : ℕ)
    (hr : OddRoute.route (n + 1 + (v * 5 + 3))
      (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)) tail L k rest)
    (hn : (List.replicate (v * 2 + 1) false ++ true :: tail).length + 1 ≤ n)
    (hlen : tail.length = 2 * r + 1 + rest.length)
    (hj : 2 ≤ v + 1 + r) (hsmall : 7 * r + 3 ≤ 5 * (v + 1 + r) - 5) :
    source_data n (List.replicate (v * 2 + 1) false ++ true :: tail) := by
  obtain ⟨r0, c, hlen0, hL, hc, hE⟩ := OdDeficit.initial_odd_route_deficit n v tail L k rest hr hn
  have hr_eq : r0 = r := by omega
  subst hr_eq
  refine package n _ L k rest (v + 1 + r0)
    ((2 ^ (v * 2 + 3) - 3) * 2 ^ (5 * (v + 1 + r0)) + c) (.WallOdd hr) hL (by linarith) ?_
  refine Or.inr ⟨v * 2 + 1, c, hj, by omega, ?_, rfl⟩
  exact lt_of_lt_of_le hc.2 (Nat.pow_le_pow_right (by decide) hsmall)

theorem adjacent_data (n v : ℕ) (tail : List Bool)
    (hv : 1 ≤ v) (hn : (List.replicate (v * 2 + 1) false ++ true :: true :: tail).length + 1 ≤ n) :
    source_data n (List.replicate (v * 2 + 1) false ++ true :: true :: tail) := by
  set L0 := n + 1 + (v * 5 + 3)
  set k0 := OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
  have hk : 1 ≤ k0 := by
    unfold k0 OddFuel.grown
    have hz : 2 ^ 3 ≤ 2 ^ (v * 5 + 3) := Nat.pow_le_pow_right (by decide) (by omega)
    change 8 ≤ 2 ^ (v * 5 + 3) at hz
    have h8 : 8 ≤ (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 3) := by nlinarith
    omega
  have hr : OddRoute.route L0 k0 (true :: tail) (L0 + 1 + 1) (OddFuel.grown (k0 - 1) 1) tail := by
    have hk_eq : k0 = (k0 - 1) + (2 ^ (0 * 2 + 1) - 1) := by simp; omega
    rw [hk_eq]
    exact OddRoute.route.RouteEven (v := 0)
  exact routed_data n v (true :: tail) (L0 + 1 + 1) (OddFuel.grown (k0 - 1) 1) tail 0
    hr hn (by simp; omega) (by omega) (by omega)

theorem odd_index_even_tail (a i : ℕ) (hi : 10 * a < i) (hp : i % 2 = 1) :
    (i - 10 * a - 1) % 2 = 0 := by omega

theorem close_data (n a : ℕ) (tail : List Bool) (i : ℕ)
    (ha : 0 < a) (hn : (List.replicate (10 * a + 1) false ++ true :: tail).length + 1 ≤ n)
    (hbit : (List.replicate (10 * a) false ++ true :: tail).getD i false = true)
    (hp : i % 2 = 1) (hbound : i ≤ 14 * a + 3) :
    source_data n (List.replicate (10 * a + 1) false ++ true :: tail) := by
  have hlo := RouteMarkerBound.prefix_true_index (10 * a) tail i hbit
  have hi : 10 * a < i := by omega
  have htail := RouteMarkerBound.prefix_tail_nth (10 * a) tail i hi hbit
  have heven := odd_index_even_tail a i hi hp
  have hmark : WallInvariant.marked 0 tail := by
    obtain ⟨pre, post, rfl, hlen⟩ := StrongInvariant.nth_true_split tail (i - 10 * a - 1) htail
    exact ⟨pre, post, rfl, by rw [hlen]; exact heven⟩
  set L0 := n + 1 + ((5 * a) * 5 + 3)
  set k0 := OddFuel.grown (OddImage.first_fuel n ((5 * a) * 2 + 1)) ((5 * a) * 5 + 3)
  have hn' : (5 * a) * 2 + 1 + tail.length + 2 ≤ n := by simp at hn; omega
  have hmargin : 2 ^ (tail.length + 4) - 1 ≤ k0 :=
    MarkedTrace.initial_margin4 n ((5 * a) * 2 + 1) tail.length ((5 * a) * 5 + 3) hn' (by omega)
  have hbasic : 2 ^ tail.length - 1 ≤ k0 := by
    have : 2 ^ tail.length ≤ 2 ^ (tail.length + 4) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨L, k, rest, hr, _⟩ := OddRoute.marked_route L0 k0 tail hmark hbasic
  obtain ⟨r, hlen, _⟩ := OddRoute.route_dimensions L0 k0 tail L k rest hr
  have hrbound := RouteMarkerBound.route_known_even_bound L0 k0 tail L k rest r
    (i - 10 * a - 1) hr hlen htail heven
  rw [show 10 * a + 1 = (5 * a) * 2 + 1 by omega] at hn ⊢
  exact routed_data n (5 * a) tail L k rest r hr hn hlen (by omega) (by omega)

theorem prepend_repeat (u : ℕ) (tail : List Bool) :
    false :: (List.replicate u false ++ tail) = List.replicate (u + 1) false ++ tail := by
  rw [List.replicate_succ, List.cons_append]

theorem guard_source (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 ≤ n) (hG : StrongInvariant.digit_guard bs) :
    source_data n (false :: bs) := by
  rcases hG with ⟨u, tail, rfl⟩ | ⟨u, tail, hu, rfl⟩ | ⟨a, tail, i, ha, rfl, hbit, hp, hib⟩
  · rw [prepend_repeat, show u * 2 + 1 + 1 = (u + 1) * 2 by omega]
    exact direct_data n (u + 1) tail (by omega) (by simp at hn ⊢; omega)
  · rw [prepend_repeat]
    rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
    · rw [Nat.mul_comm 2 v] at hn hu ⊢
      exact adjacent_data n v tail (by omega) (by simp at hn ⊢; omega)
    · rw [show 2 * v + 1 + 1 = (v + 1) * 2 by omega]
      exact direct_data n (v + 1) (true :: tail) (by omega) (by simp at hn ⊢; omega)
  · rw [prepend_repeat]
    exact close_data n a tail i ha (by simp at hn ⊢; omega) hbit hp hib

end GuardedRoute

/-! ## CounterBits -/

namespace CounterBits

open CounterRules CounterFinish WallInvariant

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * value bs

theorem value_eq_cd (bs : List Bool) : value bs = CDPasses.value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [value, CDPasses.value, CDPasses.bitval, ih]

theorem digits_value (n v : ℕ) (hv : v < 2 ^ n) : value (digits n v) = v := by
  induction n generalizing v with
  | zero => simp only [Nat.pow_zero, Nat.lt_one_iff] at hv; subst hv; rfl
  | succ n ih =>
    rw [Nat.pow_succ] at hv
    rcases Nat.even_or_odd' v with ⟨q, rfl | rfl⟩
    · rw [Nat.mul_comm 2 q, digits_even, value, ih q (by omega)]; simp; omega
    · rw [show 2 * q + 1 = q * 2 + 1 by omega, digits_odd, value, ih q (by omega)]; simp; omega

theorem value_nonzero (bs : List Bool) (h : value bs ≠ 0) : true ∈ bs := by
  induction bs with
  | nil => simp [value] at h
  | cons b bs ih =>
    cases b
    · simp [value] at h; exact List.mem_cons_of_mem false (ih (by omega))
    · exact List.mem_cons_self

theorem digits_split (n i v : ℕ) (hi : i ≤ n) :
    CounterFinish.digits n v =
      CounterFinish.digits i v ++ CounterFinish.digits (n - i) (v / 2 ^ i) := by
  induction i generalizing n v with
  | zero => simp [CounterFinish.digits]
  | succ i ih =>
    rcases n with _ | n
    · omega
    · simp only [CounterFinish.digits, List.cons_append, Nat.succ_sub_succ_eq_sub]
      rw [ih n (v / 2) (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem digits_marked (n v i q : ℕ) (hin : i < n) (hq : v / 2 ^ i = q * 2 + 1) :
    marked (i % 2) (digits n v) := by
  rw [digits_split n i v (by omega), hq, show n - i = (n - i - 1) + 1 by omega, digits_odd]
  exact ⟨digits i v, digits (n - i - 1) q, rfl, by rw [digits_length]⟩

theorem marked_shift_odd (n q i : ℕ) (hin : i < n) (hi : i % 2 = 1) :
    marked 1 (digits n ((q * 2 + 1) * 2 ^ i)) := by
  have hm := digits_marked n ((q * 2 + 1) * 2 ^ i) i q hin (Nat.mul_div_cancel _ (pow2_pos i))
  rwa [hi] at hm

theorem marked_remainder (n v i q r : ℕ) (hi : i < n) (hr : r < 2 ^ i)
    (hv : v = (q * 2 + 1) * 2 ^ i + r) :
    marked (i % 2) (digits n v) := by
  refine digits_marked n v i q hi ?_
  have hp := pow2_pos i
  rw [hv, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem shifted_normal_word (bs : List Bool) :
    [0, 0, 0, 0] ++ normal bs = shifted bs ++ [0, 0, 0, 0] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [normal, shifted, ↓reduceIte, Bool.false_eq_true]
    · change [0, 0, 0, 0, 0] ++ ([0, 0, 0, 0] ++ normal bs) =
        [0, 0, 0, 0, 0] ++ (shifted bs ++ [0, 0, 0, 0])
      rw [ih]
    · change [0, 0, 0, 0, 1] ++ ([0, 0, 0, 0] ++ normal bs) =
        [0, 0, 0, 0, 1] ++ (shifted bs ++ [0, 0, 0, 0])
      rw [ih]

theorem shifted_normal (bs : List Bool) :
    ([0, 0, 0, 0] : List Γ) +> (normal bs +> default) = shifted bs +> default := by
  rw [← append_assoc, shifted_normal_word, append_assoc,
    BoundedConfig.all0_spec (a := [0, 0, 0, 0]) (by decide)]

theorem numeric_even (n v : ℕ) (hv : 0 < v) (hbound : v * 2 < 2 ^ n) :
    invariant ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> ([1] +> ([1, 1] ^ n +> RC (v * 2)))) := by
  rw [← digits_normal n (v * 2) hbound, one_comm_11_side]
  have heq : ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      (([1, 1] : List Γ) ^ n +> ([1] +> (normal (digits n (v * 2)) +> default)))) =
      O n (digits n (v * 2)) := by
    unfold O wall LocalPasses.lh
    simp only [append_assoc]
  rw [heq]
  refine .InvO (by rw [digits_length]) ?_ ?_
  · rcases n with _ | n
    · simp at hbound; omega
    · rw [digits_even]; exact ⟨digits n v, rfl⟩
  · apply value_nonzero
    rw [digits_value n (v * 2) hbound]
    omega

theorem numeric_odd (n v : ℕ) (hv : v < 2 ^ n) (hmark : marked 1 (digits n v)) :
    invariant ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      ([1] +> ([1, 1] ^ (n + 1) +> RC (v * 2 + 1)))) := by
  have hrc : RC (v * 2 + 1) = [1, 0, 0, 0, 0] +> RC v := BinInc_mul2add1 rd1 v
  rw [hrc, ← digits_normal n v hv, one_comm_11_side]
  have heq : (([1, 1] : List Γ) ^ (n + 1) +>
      ([1] +> ([1, 0, 0, 0, 0] +> (normal (digits n v) +> default)))) =
      ([1, 1] : List Γ) ^ (n + 2) +> (shifted (digits n v) +> default) := by
    have h1 : ([1] : List Γ) +> ([1, 0, 0, 0, 0] +> (normal (digits n v) +> default)) =
        [1, 1] +> ([0, 0, 0, 0] +> (normal (digits n v) +> default)) := rfl
    rw [h1, shifted_normal, ← append_assoc ([1, 1] ^ (n + 1)) [1, 1], ← pow_succ_list']
  rw [heq]
  have hE : ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      (([1, 1] : List Γ) ^ (n + 2) +> (shifted (digits n v) +> default))) =
      WallInvariant.E (n + 2) (digits n v) := by
    unfold WallInvariant.E wall LocalPasses.lh
    simp only [append_assoc]
  rw [hE]
  exact .InvE (by rw [digits_length]) hmark

theorem numeric_even_value (n t : ℕ) (ht : 0 < t) (hb : t < 2 ^ n) (he : t % 2 = 0) :
    invariant ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> ([1] +> ([1, 1] ^ n +> RC t))) := by
  have ht2 : (t / 2) * 2 = t := by omega
  rw [← ht2]
  exact numeric_even n (t / 2) (by omega) (by omega)

theorem counter_finish_even (n k r : ℕ)
    (hk : k < 2 ^ n) (hpos : 0 < r + k + 1) (hb : r + k + 1 < 2 ^ n)
    (he : (r + k + 1) % 2 = 0) :
    ∃ cfg, ((rGate (LC n k) (RC r)) [mtm]⊢⁺ cfg) ∧ invariant cfg :=
  ⟨_, counter_finish n k r hk, numeric_even_value n (r + k + 1) hpos hb he⟩

end CounterBits

/-! ## MarkerArithmetic -/

namespace MarkerArithmetic

open CounterBits CounterFinish WallInvariant

theorem value_bound (bs : List Bool) : value bs < 2 ^ bs.length := by
  rw [value_eq_cd]
  exact CDPasses.value_bound bs

theorem digits_value_inverse (bs : List Bool) :
    CounterFinish.digits bs.length (value bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [List.length_cons, value, ↓reduceIte, Bool.false_eq_true]
    · rw [Nat.zero_add, Nat.mul_comm 2 (value bs), digits_even, ih]
    · rw [show 1 + 2 * value bs = value bs * 2 + 1 by omega, digits_odd, ih]

theorem marked_value_remainder (bs : List Bool) (i q low : ℕ)
    (hi : i < bs.length) (hlow : low < 2 ^ i)
    (heq : value bs = (q * 2 + 1) * 2 ^ i + low) :
    marked (i % 2) bs := by
  rw [← digits_value_inverse bs]
  exact marked_remainder bs.length (value bs) i q low hi hlow heq

theorem marked_residue (bs : List Bool) (i r : ℕ)
    (hi : i < bs.length) (hr : r < 2 ^ i)
    (he : value bs % 2 ^ (i + 1) = 2 ^ i + r) :
    marked (i % 2) bs := by
  have hdiv := Nat.div_add_mod (value bs) (2 ^ (i + 1))
  set Q := value bs / 2 ^ (i + 1)
  refine marked_value_remainder bs i Q r hi hr ?_
  rw [he, show 2 ^ (i + 1) * Q = 2 ^ i * 2 * Q by rw [Nat.pow_succ]] at hdiv
  linarith

theorem power_multiple (low high : ℕ) (h : low ≤ high) :
    2 ^ high = 2 ^ (high - low) * 2 ^ low := by
  rw [← Nat.pow_add, Nat.sub_add_cancel h]

theorem carry_width (bs : List Bool) (j big v : ℕ)
    (hbig : 0 < big) (heq : value bs + 2 ^ bs.length = big * 2 ^ j + v) :
    j ≤ bs.length := by
  by_contra hgt
  have hlt : bs.length + 1 ≤ j := by omega
  have hp : 2 ^ (bs.length + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hlt
  have hv := value_bound bs
  rw [Nat.pow_succ] at hp
  have hprod : 1 * 2 ^ j ≤ big * 2 ^ j := Nat.mul_le_mul_right _ hbig
  omega

theorem low_marker_preserved (bs : List Bool) (v i q r j big : ℕ)
    (hbig : 0 < big) (hij : i < j) (hr : r < 2 ^ i)
    (hv : v = (q * 2 + 1) * 2 ^ i + r)
    (heq : value bs + 2 ^ bs.length = big * 2 ^ j + v) :
    marked (i % 2) bs := by
  have hlen := carry_width bs j big v hbig heq
  refine marked_residue bs i r (by omega) hr ?_
  have heq' := heq
  rw [power_multiple (i + 1) bs.length (by omega),
    power_multiple (i + 1) j (by omega)] at heq'
  have hmod : (value bs + 2 ^ (bs.length - (i + 1)) * 2 ^ (i + 1)) % 2 ^ (i + 1) =
      (big * (2 ^ (j - (i + 1)) * 2 ^ (i + 1)) + v) % 2 ^ (i + 1) :=
    congrArg (fun x => x % 2 ^ (i + 1)) heq'
  have hrhs_eq : big * (2 ^ (j - (i + 1)) * 2 ^ (i + 1)) + v =
      v + (big * 2 ^ (j - (i + 1))) * 2 ^ (i + 1) := by ring
  have hv_eq : (q * 2 + 1) * 2 ^ i + r = (2 ^ i + r) + q * 2 ^ (i + 1) := by
    rw [Nat.pow_succ]; ring
  have hsmall : 2 ^ i + r < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
  rw [Nat.add_mul_mod_self_right, hrhs_eq, Nat.add_mul_mod_self_right, hv, hv_eq,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsmall] at hmod
  exact hmod

end MarkerArithmetic

/-! ## RouteDeficit -/

namespace RouteDeficit

theorem step_deficit (L k deficit u z : ℕ)
    (hleft : k + (2 ^ (u + 1) - 1) + deficit + 1 = 2 ^ L) :
    ∃ correction,
      OddFuel.grown k z + deficit * 2 ^ (z + 1) + correction + 1 = 2 ^ (L + z + 1) ∧
      correction < 2 ^ (z + u + 2) := by
  refine ⟨(2 ^ (u + 2) - 1) * 2 ^ z, ?_, ?_⟩
  · have hs := OdDeficit.step_deficit L k deficit u z (by omega)
    rw [show L + z + 1 = L + 1 + z by omega]
    linarith
  · have hc := (OdDeficit.correction_bound u z).2
    rwa [show z + u + 2 = u + 2 + z by omega]

theorem route_deficit (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hroute : OddRoute.route L k bs L' k' rest) :
    ∀ deficit, k + deficit + 1 = 2 ^ L →
      ∃ j correction,
        bs.length = 2 * j + 1 + rest.length ∧ L' = L + 5 * j + 2 ∧
        k' + deficit * 2 ^ (5 * j + 2) + correction + 1 = 2 ^ L' ∧
        correction < 2 ^ (7 * j + 3) := by
  intro deficit hleft
  obtain ⟨j, c, hlen, hL, hc, hE⟩ :=
    OdDeficit.route_deficit L k bs L' k' rest hroute deficit (by omega)
  exact ⟨j, c, hlen, hL, by linarith, hc.2⟩

theorem route_suffix (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hroute : OddRoute.route L k bs L' k' rest) :
    ∃ pre, bs = pre ++ rest := by
  induction hroute with
  | @RouteEven L k v tail =>
    exact ⟨List.replicate (v * 2) false ++ [true], by simp⟩
  | @RouteOdd L k v tail L' k' rest _ ih =>
    obtain ⟨pre, rfl⟩ := ih
    exact ⟨List.replicate (v * 2 + 1) false ++ true :: pre, by simp⟩

end RouteDeficit

/-! ## MarkedDeficit -/

namespace MarkedDeficit

def initial_deficit (u z : ℕ) : ℕ := (2 ^ (u + 2) - 3) * 2 ^ z

theorem initial_balance (n u z : ℕ) (hn : u + 1 ≤ n) :
    OddFuel.grown (OddImage.first_fuel n u) z + initial_deficit u z + 1 = 2 ^ (n + 1 + z) := by
  have hd := OdDeficit.initial_deficit n u z hn
  unfold initial_deficit
  linarith

theorem initial_bound (u z : ℕ) : initial_deficit u z < 2 ^ (u + 2 + z) := by
  unfold initial_deficit
  rw [Nat.pow_add 2 (u + 2) z]
  have hpz := pow2_pos z
  have hpu := pow2_pos u
  have hu : 3 < 2 ^ (u + 2) := by rw [Nat.pow_add 2 u 2]; change 3 < 2 ^ u * 4; omega
  exact Nat.mul_lt_mul_of_pos_right (by omega) hpz

theorem wall_deficit (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool)
    (hroute : MarkedTrace.wall_route n bs L k rest) (hlen : bs.length + 1 ≤ n) :
    ∃ j deficit,
      bs.length = 2 * j + 1 + rest.length ∧ L = n + 5 * j + 1 ∧
      k + deficit + 1 = 2 ^ L ∧ deficit < 2 ^ (7 * j + 2) := by
  cases hroute with
  | @WallEven v tail =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    refine ⟨v, initial_deficit (v * 2) (v * 5), by simp; omega, by omega,
      initial_balance n (v * 2) (v * 5) (by omega), ?_⟩
    rw [show 7 * v + 2 = v * 2 + 2 + v * 5 by omega]
    exact initial_bound (v * 2) (v * 5)
  | @WallOdd v tail L k rest h =>
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    set d0 := initial_deficit (v * 2 + 1) (v * 5 + 3)
    have hbal : OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3) + d0 + 1 =
        2 ^ (n + 1 + (v * 5 + 3)) := initial_balance n (v * 2 + 1) (v * 5 + 3) (by omega)
    obtain ⟨j, corr, hdim, hL, hend, hcorr⟩ :=
      RouteDeficit.route_deficit _ _ tail L k rest h d0 hbal
    refine ⟨v + 1 + j, d0 * 2 ^ (5 * j + 2) + corr, by simp; omega, by omega, by linarith, ?_⟩
    have hd0 : d0 < 2 ^ (7 * v + 6) := by
      unfold d0
      rw [show 7 * v + 6 = (v * 2 + 1) + 2 + (v * 5 + 3) by omega]
      exact initial_bound (v * 2 + 1) (v * 5 + 3)
    have hprod : d0 * 2 ^ (5 * j + 2) < 2 ^ (7 * v + 5 * j + 8) := by
      rw [show 7 * v + 5 * j + 8 = (7 * v + 6) + (5 * j + 2) by omega,
        Nat.pow_add 2 (7 * v + 6) (5 * j + 2)]
      exact Nat.mul_lt_mul_of_pos_right hd0 (pow2_pos (5 * j + 2))
    have hone : 2 ^ (7 * v + 5 * j + 8) ≤ 2 ^ (7 * (v + 1 + j) + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have htwo : 2 ^ (7 * j + 3) ≤ 2 ^ (7 * (v + 1 + j) + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [show 7 * (v + 1 + j) + 2 = (7 * (v + 1 + j) + 1) + 1 by omega,
      Nat.pow_succ 2 (7 * (v + 1 + j) + 1)]
    linarith

theorem wall_deficit_at (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool) (j : ℕ)
    (hroute : MarkedTrace.wall_route n bs L k rest) (hlen : bs.length + 1 ≤ n)
    (hdim : bs.length = 2 * j + 1 + rest.length) :
    ∃ deficit, k + deficit + 1 = 2 ^ L ∧ deficit < 2 ^ (7 * j + 2) := by
  obtain ⟨j0, d, hdim0, _, hbal, hb⟩ := wall_deficit n bs L k rest hroute hlen
  have hj : j0 = j := by omega
  subst hj
  exact ⟨d, hbal, hb⟩

theorem tight_coefficient_bound (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool)
    (j T q : ℕ)
    (hroute : MarkedTrace.wall_route n (false :: bs) L k rest) (hn : bs.length + 2 = n)
    (hdim : bs.length = 2 * j + rest.length)
    (hT : T ≤ 2 ^ rest.length) (hbudget : k + 1 = 2 * (T + q)) :
    ∃ deficit,
      k + deficit + 1 = 2 ^ L ∧ deficit < 2 ^ (7 * j + 2) ∧
      q * 4 + 3 + 2 * deficit + 4 * T = 2 ^ (L + 1) + 3 ∧ 2 ^ L ≤ q * 4 + 3 := by
  obtain ⟨j0, d, hdim0, hL, hbal, hd⟩ := wall_deficit n (false :: bs) L k rest hroute
    (by simp; omega)
  simp only [List.length_cons] at hdim0
  have hj : j0 = j := by omega
  subst hj
  have hL' : L = 7 * j0 + rest.length + 3 := by omega
  have hcap : 2 ^ L = 2 ^ (7 * j0 + 2) * 2 ^ rest.length * 2 := by
    rw [hL', show 7 * j0 + rest.length + 3 = (7 * j0 + 2) + rest.length + 1 by omega,
      Nat.pow_add, Nat.pow_add, Nat.pow_one]
  have hx : 4 ≤ 2 ^ (7 * j0 + 2) := by
    rw [Nat.pow_add 2 (7 * j0) 2]; have := pow2_pos (7 * j0); change 4 ≤ 2 ^ (7 * j0) * 4; omega
  have hy := pow2_pos rest.length
  refine ⟨d, hbal, hd, ?_, ?_⟩
  · rw [Nat.pow_succ]
    linarith
  · rw [hcap] at hbal ⊢
    nlinarith

end MarkedDeficit

/-! ## GapMarker -/

namespace GapMarker

open CounterBits MarkerArithmetic WallInvariant

private theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private theorem pow2_strict_mono {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by decide) h

theorem marked_residue_auto (bs : List Bool) (i r : ℕ)
    (hr : r < 2 ^ i) (he : value bs % 2 ^ (i + 1) = 2 ^ i + r) :
    marked (i % 2) bs := by
  refine marked_residue bs i r ?_ hr he
  by_contra hge
  have hp : 2 ^ bs.length ≤ 2 ^ i := pow2_mono (by omega)
  have hv := value_bound bs
  have hsmall : value bs < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
  rw [Nat.mod_eq_of_lt hsmall] at he
  omega

theorem complement_residue (v d c : ℕ)
    (hc : 0 < c) (hcd : c < d) (hsum : (v + c) % d = 0) :
    v % d = d - c := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt hcd] at hsum
  have hv : v % d < d := Nat.mod_lt v (by omega)
  have hdiv := Nat.div_add_mod (v % d + c) d
  rw [hsum, Nat.add_zero] at hdiv
  rcases hq : (v % d + c) / d with _ | _ | q
  · rw [hq, Nat.mul_zero] at hdiv; omega
  · rw [hq, Nat.mul_one] at hdiv; omega
  · rw [hq] at hdiv
    have : d * 2 ≤ d * (q + 1 + 1) := Nat.mul_le_mul_left d (by omega)
    omega

theorem subtraction_marker_at (bs : List Bool) (A J D c i : ℕ)
    (hJA : J ≤ A) (hi : i < J) (hlo : J - 2 ≤ i) (hpar : i % 2 = 1)
    (hc : 0 < c) (hsmall : c < 2 ^ (J - 2))
    (heq : value bs + c + D * 2 ^ J = 2 ^ A) :
    marked 1 bs := by
  have hci : c < 2 ^ i := lt_of_lt_of_le hsmall (pow2_mono hlo)
  have hcd : c < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
  have hsum : (value bs + c) % 2 ^ (i + 1) = 0 := by
    have heq' := heq
    rw [power_multiple (i + 1) A (by omega), power_multiple (i + 1) J (by omega)] at heq'
    have hmul : value bs + c + D * (2 ^ (J - (i + 1)) * 2 ^ (i + 1)) =
        (value bs + c) + (D * 2 ^ (J - (i + 1))) * 2 ^ (i + 1) := by ring
    have hrhs : 2 ^ (A - (i + 1)) * 2 ^ (i + 1) =
        0 + 2 ^ (A - (i + 1)) * 2 ^ (i + 1) := by omega
    rw [hmul, hrhs] at heq'
    have hmod := congrArg (fun n => n % 2 ^ (i + 1)) heq'
    rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.zero_mod] at hmod
    exact hmod
  have hmod := complement_residue (value bs) (2 ^ (i + 1)) c hc hcd hsum
  have hmark := marked_residue_auto bs i (2 ^ i - c) (by omega) (by
    rw [hmod, Nat.pow_succ]; omega)
  rwa [hpar] at hmark

theorem small_subtraction_marker (bs : List Bool) (A B J c : ℕ)
    (hJ : 3 ≤ J) (hB : 3 ≤ B) (hc : 0 < c) (hsmall : c < 2 ^ (J - 2))
    (heq : value bs + c + (2 ^ B - 3) * 2 ^ J = 2 ^ A) :
    marked 1 bs := by
  have hpowB : 8 ≤ 2 ^ B := by change 2 ^ 3 ≤ 2 ^ B; exact pow2_mono hB
  have hJA : J ≤ A := by
    by_contra hgt
    have hlt : 2 ^ A < 2 ^ J := pow2_strict_mono (by omega)
    have hpos : 1 * 2 ^ J ≤ (2 ^ B - 3) * 2 ^ J := Nat.mul_le_mul_right _ (by omega)
    omega
  rcases Nat.even_or_odd' J with ⟨a, rfl | rfl⟩
  · exact subtraction_marker_at bs A (2 * a) (2 ^ B - 3) c (2 * a - 1)
      hJA (by omega) (by omega) (by omega) hc hsmall heq
  · exact subtraction_marker_at bs A (2 * a + 1) (2 ^ B - 3) c (2 * a + 1 - 2)
      hJA (by omega) (by omega) (by omega) hc hsmall heq

end GapMarker

/-! ## MultiGapMarker -/

namespace MultiGapMarker

open CounterBits MarkerArithmetic GapMarker WallInvariant

private theorem pow2_strict_mono {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by decide) h

theorem positive_subtraction_marker (bs : List Bool) (A J D c : ℕ)
    (hJ : 3 ≤ J) (hD : 0 < D) (hc : 0 < c) (hsmall : c < 2 ^ (J - 2))
    (heq : value bs + c + D * 2 ^ J = 2 ^ A) :
    marked 1 bs := by
  have hJA : J ≤ A := by
    by_contra hgt
    have hlt : 2 ^ A < 2 ^ J := pow2_strict_mono (by omega)
    have hpos : 1 * 2 ^ J ≤ D * 2 ^ J := Nat.mul_le_mul_right _ hD
    omega
  rcases Nat.even_or_odd' J with ⟨a, rfl | rfl⟩
  · exact subtraction_marker_at bs A (2 * a) D c (2 * a - 1)
      hJA (by omega) (by omega) (by omega) hc hsmall heq
  · exact subtraction_marker_at bs A (2 * a + 1) D c (2 * a + 1 - 2)
      hJA (by omega) (by omega) (by omega) hc hsmall heq

theorem two_gap_marker (bs : List Bool) (A J K D E c : ℕ)
    (hD : 0 < D) (hE : 0 < E) (hmin : 3 ≤ min J K)
    (hc : 0 < c) (hsmall : c < 2 ^ (min J K - 2))
    (heq : value bs + c + D * 2 ^ J + E * 2 ^ K = 2 ^ A) :
    marked 1 bs := by
  set m := min J K
  have hmJ : m ≤ J := by omega
  have hmK : m ≤ K := by omega
  have hpJ := pow2_pos (J - m)
  have hpK := pow2_pos (K - m)
  have hd_pos : 0 < D * 2 ^ (J - m) + E * 2 ^ (K - m) := by
    have : 1 * 1 ≤ D * 2 ^ (J - m) := Nat.mul_le_mul hD hpJ
    have : 1 * 1 ≤ E * 2 ^ (K - m) := Nat.mul_le_mul hE hpK
    omega
  refine positive_subtraction_marker bs A m (D * 2 ^ (J - m) + E * 2 ^ (K - m)) c
    hmin hd_pos hc hsmall ?_
  have heq' := heq
  rw [power_multiple m J hmJ, power_multiple m K hmK] at heq'
  rw [← heq']
  ring

end MultiGapMarker

/-! ## MagnitudeMarker -/

namespace MagnitudeMarker

open CounterBits CounterFinish MarkerArithmetic WallInvariant

theorem value_app (bs cs : List Bool) :
    value (bs ++ cs) = value bs + 2 ^ bs.length * value cs := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    simp only [List.cons_append, value, List.length_cons, Nat.pow_succ, ih]
    ring

theorem same_value_marker (bs cs : List Bool)
    (he : value bs = value cs) (hm : marked 1 bs) :
    marked 1 cs := by
  obtain ⟨pre, post, rfl, hpar⟩ := hm
  have hp := value_bound pre
  have hval : value cs = (value post * 2 + 1) * 2 ^ pre.length + value pre := by
    rw [value_app, value] at he
    simp only [↓reduceIte] at he
    rw [← he]
    ring
  have hindex : pre.length < cs.length := by
    by_contra hge
    have hcs := value_bound cs
    have hpow : 2 ^ cs.length ≤ 2 ^ pre.length := Nat.pow_le_pow_right (by decide) (by omega)
    have hge1 : 1 * 2 ^ pre.length ≤ (value post * 2 + 1) * 2 ^ pre.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hm' := marked_value_remainder cs pre.length (value post) (value pre) hindex hp hval
  rwa [hpar] at hm'

theorem add_two_marker (b c : Bool) (bs : List Bool) (hm : marked 1 bs) :
    marked 1 (b :: c :: bs) := by
  obtain ⟨pre, post, rfl, hp⟩ := hm
  refine ⟨b :: c :: pre, post, rfl, ?_⟩
  simp only [List.length_cons]
  omega

theorem marker_or_bound (bs : List Bool) :
    marked 1 bs ∨ 3 * value bs < 2 ^ (bs.length + 1) := by
  suffices h : (marked 1 bs ∨ 3 * value bs < 2 ^ (bs.length + 1)) ∧
      (∀ b, marked 1 (b :: bs) ∨ 3 * value (b :: bs) < 2 ^ ((b :: bs).length + 1)) from h.1
  induction bs with
  | nil =>
    refine ⟨Or.inr (by simp [value]), fun b => ?_⟩
    cases b <;> exact Or.inr (by simp [value])
  | cons c bs ih =>
    refine ⟨ih.2 c, fun b => ?_⟩
    cases c
    · rcases ih.1 with hm | hb
      · exact Or.inl (add_two_marker b false bs hm)
      · right
        simp only [value, List.length_cons, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        rw [Nat.pow_succ, Nat.pow_succ]
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    · exact Or.inl ⟨[b], bs, rfl, rfl⟩

theorem magnitude_marker (bs : List Bool) (A : ℕ)
    (hv : value bs < 2 ^ A) (hlarge : 2 ^ (A + 1) < 3 * value bs) :
    marked 1 bs := by
  have hval := digits_value A (value bs) hv
  rcases marker_or_bound (digits A (value bs)) with hm | hb
  · exact same_value_marker (digits A (value bs)) bs hval hm
  · rw [digits_length, hval] at hb
    omega

end MagnitudeMarker

/-! ## OdEvenMarker -/

namespace OdEvenMarker

private theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem power_positive (n : ℕ) : 0 < 2 ^ n := pow2_pos n

theorem minus_three_positive (u : ℕ) : 0 < 2 ^ (u + 2) - 3 := by
  have := pow2_pos u
  rw [Nat.pow_succ, Nat.pow_succ]
  omega

theorem scaled_minus_three (u J : ℕ) : (2 ^ (u + 2) - 3) * 2 ^ J < 2 ^ (u + 2 + J) := by
  rw [Nat.pow_add 2 (u + 2) J]
  refine Nat.mul_lt_mul_of_pos_right ?_ (pow2_pos J)
  have := pow2_pos u
  rw [Nat.pow_succ, Nat.pow_succ]
  omega

theorem terminal_small (m T : ℕ) (h : T ≤ 6 * 2 ^ m) : 2 * T - 1 < 2 ^ (m + 4) := by
  have := pow2_pos m
  rw [show m + 4 = m + 1 + 1 + 1 + 1 by omega,
    Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
  omega

theorem sum_small (J x y : ℕ) (hJ : 3 ≤ J)
    (hx : x < 2 ^ (J - 3)) (hy : y < 2 ^ (J - 3)) :
    x + y < 2 ^ (J - 2) := by
  rw [show J - 2 = (J - 3) + 1 by omega, Nat.pow_succ]
  omega

theorem three_small (J x y z : ℕ) (hJ : 4 ≤ J)
    (hx : x < 2 ^ (J - 4)) (hy : y < 2 ^ (J - 4)) (hz : z < 2 ^ (J - 4)) :
    x + y + z < 2 ^ (J - 2) := by
  rw [show J - 2 = (J - 4) + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ]
  omega

theorem magnitude_from_parts (bs : List Bool) (A x y z t : ℕ)
    (hA : 6 ≤ A) (hx : x < 2 ^ (A - 2)) (hy : y < 2 ^ (A - 6))
    (hz : z < 2 ^ (A - 6)) (ht : t < 2 ^ (A - 6))
    (hpos : 0 < x + y + z + t)
    (hE : CounterBits.value bs + x + y + z + t = 2 ^ A) :
    WallInvariant.marked 1 bs := by
  have hp := pow2_pos (A - 6)
  have hP : 2 ^ A = 64 * 2 ^ (A - 6) := by
    conv_lhs => rw [show A = (A - 6) + 6 by omega, Nat.pow_add]
    ring
  have hPx : 2 ^ (A - 2) = 16 * 2 ^ (A - 6) := by
    conv_lhs => rw [show A - 2 = (A - 6) + 4 by omega, Nat.pow_add]
    ring
  refine MagnitudeMarker.magnitude_marker bs A (by omega) ?_
  rw [Nat.pow_succ, hP]
  rw [hP] at hE
  rw [hPx] at hx
  omega

private theorem reachable_even_core (bs : List Bool) (a j m C T D E : ℕ)
    (hj : 2 ≤ j) (hm : m ≤ 4 * a) (hT : 0 < T)
    (hC : C < 2 ^ (5 * j - 5))
    (hD : 0 < D) (hEpos : 0 < E)
    (hF : D * 2 ^ (5 * j) < 2 ^ (7 * j + 1))
    (hQ : E * 2 ^ (25 * a + 9) < 2 ^ (35 * a + 15))
    (hTs : 2 * T - 1 < 2 ^ (m + 4))
    (hE : CounterBits.value bs + (C + 2 * T - 1) +
      D * 2 ^ (5 * j) + E * 2 ^ (25 * a + 9) = 2 ^ (m + 7 * j + 3)) :
    WallInvariant.marked 1 bs := by
  by_cases hsmall : 7 * j ≤ 25 * a + 4
  · have hF' : D * 2 ^ (5 * j) < 2 ^ (25 * a + 9 - 4) :=
      lt_of_lt_of_le hF (pow2_mono (by clear hC hF hQ hTs hE; omega))
    have hC' : C < 2 ^ (25 * a + 9 - 4) :=
      lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE; omega))
    have hT' : 2 * T - 1 < 2 ^ (25 * a + 9 - 4) :=
      lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE; omega))
    have hpos_cf : 0 < (C + 2 * T - 1) + D * 2 ^ (5 * j) := by
      generalize D * 2 ^ (5 * j) = F; clear hC hF hQ hTs hE hF' hC' hT'; omega
    have heq_cf : CounterBits.value bs + ((C + 2 * T - 1) + D * 2 ^ (5 * j)) +
        E * 2 ^ (25 * a + 9) = 2 ^ (m + 7 * j + 3) := by
      rw [← Nat.add_assoc (CounterBits.value bs)]; exact hE
    refine MultiGapMarker.positive_subtraction_marker bs (m + 7 * j + 3) (25 * a + 9)
      E ((C + 2 * T - 1) + D * 2 ^ (5 * j))
      (by clear hC hF hQ hTs hE hF' hC' hT' heq_cf; omega) hEpos hpos_cf ?_ heq_cf
    have hsplit : (C + 2 * T - 1) + D * 2 ^ (5 * j) =
        C + (2 * T - 1) + D * 2 ^ (5 * j) := by
      generalize D * 2 ^ (5 * j) = F; clear hC hF hQ hTs hE hF' hC' hT' hpos_cf heq_cf; omega
    rw [hsplit]
    exact three_small (25 * a + 9) C (2 * T - 1) _
      (by clear hC hF hQ hTs hE hF' hC' hT' hpos_cf heq_cf hsplit; omega) hC' hT' hF'
  · by_cases hmiddle : j ≤ 5 * a + 2
    · have hCJ : C < 2 ^ (5 * j - 3) :=
        lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE; omega))
      have hTJ : 2 * T - 1 < 2 ^ (5 * j - 3) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE; omega))
      have hcJ : C + 2 * T - 1 < 2 ^ (5 * j - 2) := by
        rw [show C + 2 * T - 1 = C + (2 * T - 1) by clear hC hF hQ hTs hE hCJ hTJ; omega]
        exact sum_small (5 * j) C (2 * T - 1)
          (by clear hC hF hQ hTs hE hCJ hTJ; omega) hCJ hTJ
      have hCK : C < 2 ^ (25 * a + 9 - 3) :=
        lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE hCJ hTJ hcJ; omega))
      have hTK : 2 * T - 1 < 2 ^ (25 * a + 9 - 3) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK; omega))
      have hcK : C + 2 * T - 1 < 2 ^ (25 * a + 9 - 2) := by
        rw [show C + 2 * T - 1 = C + (2 * T - 1) by
          clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK; omega]
        exact sum_small (25 * a + 9) C (2 * T - 1)
          (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK; omega) hCK hTK
      refine MultiGapMarker.two_gap_marker bs (m + 7 * j + 3) (5 * j) (25 * a + 9)
        D E (C + 2 * T - 1) hD hEpos
        (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega)
        (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega) ?_ hE
      by_cases hJK : 5 * j ≤ 25 * a + 9
      · rw [show min (5 * j) (25 * a + 9) = 5 * j by
          clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega]
        exact hcJ
      · rw [show min (5 * j) (25 * a + 9) = 25 * a + 9 by
          clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega]
        exact hcK
    · have hFA : D * 2 ^ (5 * j) < 2 ^ (m + 7 * j + 3 - 2) :=
        lt_of_lt_of_le hF (pow2_mono (by clear hC hF hQ hTs hE; omega))
      have hCA : C < 2 ^ (m + 7 * j + 3 - 6) :=
        lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE hFA; omega))
      have hTA : 2 * T - 1 < 2 ^ (m + 7 * j + 3 - 6) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE hFA hCA; omega))
      have hQA : E * 2 ^ (25 * a + 9) < 2 ^ (m + 7 * j + 3 - 6) :=
        lt_of_lt_of_le hQ (pow2_mono (by clear hC hF hQ hTs hE hFA hCA hTA; omega))
      refine magnitude_from_parts bs (m + 7 * j + 3)
        (D * 2 ^ (5 * j)) C (2 * T - 1) (E * 2 ^ (25 * a + 9))
        (by clear hC hF hQ hTs hE hFA hCA hTA hQA; omega)
        hFA hCA hTA hQA ?_ ?_
      · generalize D * 2 ^ (5 * j) = F
        generalize E * 2 ^ (25 * a + 9) = Q
        clear hC hF hQ hTs hE hFA hCA hTA hQA; omega
      · generalize D * 2 ^ (5 * j) = F at hE ⊢
        generalize E * 2 ^ (25 * a + 9) = Q at hE ⊢
        generalize 2 ^ (m + 7 * j + 3) = R at hE ⊢
        clear hC hF hQ hTs hFA hCA hTA hQA; omega

theorem reachable_even_marker (bs : List Bool) (a j m u C T : ℕ)
    (hj : 2 ≤ j) (hu : u + 1 ≤ 2 * j) (hm : m ≤ 4 * a)
    (hT : 0 < T) (hTb : T ≤ 6 * 2 ^ m) (hC : C < 2 ^ (5 * j - 5))
    (hE : CounterBits.value bs + (C + 2 * T - 1) +
      (2 ^ (u + 2) - 3) * 2 ^ (5 * j) + (2 ^ (10 * a + 6) - 3) * 2 ^ (25 * a + 9) =
      2 ^ (m + 7 * j + 3)) :
    WallInvariant.marked 1 bs := by
  refine reachable_even_core bs a j m C T (2 ^ (u + 2) - 3) (2 ^ (10 * a + 6) - 3)
    hj hm hT hC (minus_three_positive u) ?_ ?_ ?_ (terminal_small m T hTb) hE
  · rw [show 10 * a + 6 = (10 * a + 4) + 2 by clear hTb hC hE; omega]
    exact minus_three_positive (10 * a + 4)
  · exact lt_of_lt_of_le (scaled_minus_three u (5 * j))
      (pow2_mono (by clear hTb hC hE; omega))
  · have h := scaled_minus_three (10 * a + 4) (25 * a + 9)
    have e1 : 10 * a + 4 + 2 = 10 * a + 6 := by clear hTb hC hE h; omega
    have e2 : 10 * a + 6 + (25 * a + 9) = 35 * a + 15 := by clear hTb hC hE h e1; omega
    rw [e1, e2] at h
    exact h

end OdEvenMarker

/-! ## OdOddMarker -/

namespace OdOddMarker

open OdEvenMarker

private theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem terminal_small_odd (m T : ℕ) (hm : 1 ≤ m) (hT : T ≤ 6 * 2 ^ m) :
    T + 3 < 2 ^ (m + 3) := by
  have : 2 ≤ 2 ^ m := by change 2 ^ 1 ≤ 2 ^ m; exact pow2_mono hm
  rw [show m + 3 = m + 1 + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
  omega

private theorem reachable_odd_core (bs : List Bool) (a j m C T D E : ℕ)
    (hj : 2 ≤ j) (hm : 1 ≤ m ∧ m ≤ 4 * a + 2) (hT : 0 < T)
    (hC : C < 2 ^ (5 * j - 6))
    (hD : 0 < D) (hEpos : 0 < E)
    (hF : D * 2 ^ (5 * j - 1) < 2 ^ (7 * j))
    (hQ : E * 2 ^ (25 * a + 24) < 2 ^ (35 * a + 35))
    (hTs : T + 3 < 2 ^ (m + 3))
    (hE : CounterBits.value bs + (C + T + 3) +
      D * 2 ^ (5 * j - 1) + E * 2 ^ (25 * a + 24) = 2 ^ (m + 7 * j + 2)) :
    WallInvariant.marked 1 bs := by
  by_cases hsmall : 7 * j ≤ 25 * a + 20
  · have hF' : D * 2 ^ (5 * j - 1) < 2 ^ (25 * a + 24 - 4) :=
      lt_of_lt_of_le hF (pow2_mono (by clear hC hF hQ hTs hE; omega))
    have hC' : C < 2 ^ (25 * a + 24 - 4) :=
      lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE; omega))
    have hT' : T + 3 < 2 ^ (25 * a + 24 - 4) :=
      lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE; omega))
    have hpos_cf : 0 < (C + T + 3) + D * 2 ^ (5 * j - 1) := by
      generalize D * 2 ^ (5 * j - 1) = F; clear hC hF hQ hTs hE hF' hC' hT'; omega
    have heq_cf : CounterBits.value bs + ((C + T + 3) + D * 2 ^ (5 * j - 1)) +
        E * 2 ^ (25 * a + 24) = 2 ^ (m + 7 * j + 2) := by
      rw [← Nat.add_assoc (CounterBits.value bs)]; exact hE
    refine MultiGapMarker.positive_subtraction_marker bs (m + 7 * j + 2) (25 * a + 24)
      E ((C + T + 3) + D * 2 ^ (5 * j - 1))
      (by clear hC hF hQ hTs hE hF' hC' hT' heq_cf; omega) hEpos hpos_cf ?_ heq_cf
    have hsplit : (C + T + 3) + D * 2 ^ (5 * j - 1) =
        C + (T + 3) + D * 2 ^ (5 * j - 1) := by
      generalize D * 2 ^ (5 * j - 1) = F; clear hC hF hQ hTs hE hF' hC' hT' hpos_cf heq_cf; omega
    rw [hsplit]
    exact three_small (25 * a + 24) C (T + 3) _
      (by clear hC hF hQ hTs hE hF' hC' hT' hpos_cf heq_cf hsplit; omega) hC' hT' hF'
  · by_cases hmiddle : j ≤ 5 * a + 5
    · have hCJ : C < 2 ^ (5 * j - 1 - 3) :=
        lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE; omega))
      have hTJ : T + 3 < 2 ^ (5 * j - 1 - 3) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE; omega))
      have hcJ : C + T + 3 < 2 ^ (5 * j - 1 - 2) := by
        rw [show C + T + 3 = C + (T + 3) by clear hC hF hQ hTs hE hCJ hTJ; omega]
        exact sum_small (5 * j - 1) C (T + 3)
          (by clear hC hF hQ hTs hE hCJ hTJ; omega) hCJ hTJ
      have hCK : C < 2 ^ (25 * a + 24 - 3) :=
        lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE hCJ hTJ hcJ; omega))
      have hTK : T + 3 < 2 ^ (25 * a + 24 - 3) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK; omega))
      have hcK : C + T + 3 < 2 ^ (25 * a + 24 - 2) := by
        rw [show C + T + 3 = C + (T + 3) by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK; omega]
        exact sum_small (25 * a + 24) C (T + 3)
          (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK; omega) hCK hTK
      refine MultiGapMarker.two_gap_marker bs (m + 7 * j + 2) (5 * j - 1) (25 * a + 24)
        D E (C + T + 3) hD hEpos
        (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega)
        (by clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega) ?_ hE
      by_cases hJK : 5 * j - 1 ≤ 25 * a + 24
      · rw [show min (5 * j - 1) (25 * a + 24) = 5 * j - 1 by
          clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega]
        exact hcJ
      · rw [show min (5 * j - 1) (25 * a + 24) = 25 * a + 24 by
          clear hC hF hQ hTs hE hCJ hTJ hcJ hCK hTK hcK; omega]
        exact hcK
    · have hFA : D * 2 ^ (5 * j - 1) < 2 ^ (m + 7 * j + 2 - 2) :=
        lt_of_lt_of_le hF (pow2_mono (by clear hC hF hQ hTs hE; omega))
      have hCA : C < 2 ^ (m + 7 * j + 2 - 6) :=
        lt_of_lt_of_le hC (pow2_mono (by clear hC hF hQ hTs hE hFA; omega))
      have hTA : T + 3 < 2 ^ (m + 7 * j + 2 - 6) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hC hF hQ hTs hE hFA hCA; omega))
      have hQA : E * 2 ^ (25 * a + 24) < 2 ^ (m + 7 * j + 2 - 6) :=
        lt_of_lt_of_le hQ (pow2_mono (by clear hC hF hQ hTs hE hFA hCA hTA; omega))
      refine magnitude_from_parts bs (m + 7 * j + 2)
        (D * 2 ^ (5 * j - 1)) C (T + 3) (E * 2 ^ (25 * a + 24))
        (by clear hC hF hQ hTs hE hFA hCA hTA hQA; omega)
        hFA hCA hTA hQA ?_ ?_
      · generalize D * 2 ^ (5 * j - 1) = F
        generalize E * 2 ^ (25 * a + 24) = Q
        clear hC hF hQ hTs hE hFA hCA hTA hQA; omega
      · generalize D * 2 ^ (5 * j - 1) = F at hE ⊢
        generalize E * 2 ^ (25 * a + 24) = Q at hE ⊢
        generalize 2 ^ (m + 7 * j + 2) = R at hE ⊢
        clear hC hF hQ hTs hFA hCA hTA hQA; omega

theorem reachable_odd_marker (bs : List Bool) (a j m u C T : ℕ)
    (hj : 2 ≤ j) (hu : u + 1 ≤ 2 * j) (hm : 1 ≤ m ∧ m ≤ 4 * a + 2)
    (hT : 0 < T) (hTb : T ≤ 6 * 2 ^ m) (hC : C < 2 ^ (5 * j - 6))
    (hE : CounterBits.value bs + (C + T + 3) +
      (2 ^ (u + 2) - 3) * 2 ^ (5 * j - 1) + (2 ^ (10 * a + 11) - 3) * 2 ^ (25 * a + 24) =
      2 ^ (m + 7 * j + 2)) :
    WallInvariant.marked 1 bs := by
  refine reachable_odd_core bs a j m C T (2 ^ (u + 2) - 3) (2 ^ (10 * a + 11) - 3)
    hj hm hT hC (minus_three_positive u) ?_ ?_ ?_ (terminal_small_odd m T hm.1 hTb) hE
  · rw [show 10 * a + 11 = (10 * a + 9) + 2 by clear hTb hC hE; omega]
    exact minus_three_positive (10 * a + 9)
  · exact lt_of_lt_of_le (scaled_minus_three u (5 * j - 1))
      (pow2_mono (by clear hTb hC hE; omega))
  · have h := scaled_minus_three (10 * a + 9) (25 * a + 24)
    have e1 : 10 * a + 9 + 2 = 10 * a + 11 := by clear hTb hC hE h; omega
    have e2 : 10 * a + 11 + (25 * a + 24) = 35 * a + 35 := by clear hTb hC hE h e1; omega
    rw [e1, e2] at h
    exact h

end OdOddMarker

/-! ## OdDirectMarker -/

namespace OdDirectMarker

open OdEvenMarker OdOddMarker

private theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem direct_even_marker (bs : List Bool) (a j m T : ℕ)
    (hj : 1 ≤ j) (hm : m ≤ 4 * a) (hT : 0 < T) (hTb : T ≤ 6 * 2 ^ m)
    (hE : CounterBits.value bs + (2 * T - 1) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j) +
      (2 ^ (10 * a + 6) - 3) * 2 ^ (25 * a + 9) = 2 ^ (m + 7 * j + 3)) :
    WallInvariant.marked 1 bs := by
  have hD : 0 < 2 ^ (2 * j + 2) - 3 := minus_three_positive (2 * j)
  have hEp : 0 < 2 ^ (10 * a + 6) - 3 := by
    rw [show 10 * a + 6 = (10 * a + 4) + 2 by clear hTb hE; omega]
    exact minus_three_positive (10 * a + 4)
  have hTs : 2 * T - 1 < 2 ^ (m + 4) := terminal_small m T hTb
  by_cases hsmall : m + 6 ≤ 5 * j
  · refine MultiGapMarker.two_gap_marker bs (m + 7 * j + 3) (5 * j) (25 * a + 9)
      (2 ^ (2 * j + 2) - 3) (2 ^ (10 * a + 6) - 3) (2 * T - 1)
      hD hEp (by clear hTb hE hD hEp hTs; omega)
      (by clear hTb hE hD hEp hTs; omega) ?_ hE
    exact lt_of_lt_of_le hTs (pow2_mono (by clear hTb hE hD hEp hTs; omega))
  · rcases a with _ | a
    · have hm0 : m = 0 := by clear hTb hE hD hEp hTs; omega
      have hj1 : j = 1 := by clear hTb hE hD hEp hTs; omega
      subst hm0 hj1
      exfalso
      have hbad : (2 ^ (10 * 0 + 6) - 3) * 2 ^ (25 * 0 + 9) > 2 ^ (0 + 7 * 1 + 3) := by decide
      generalize (2 ^ (2 * 1 + 2) - 3) * 2 ^ (5 * 1) = X at hE
      generalize (2 ^ (10 * 0 + 6) - 3) * 2 ^ (25 * 0 + 9) = Y at hE hbad
      generalize 2 ^ (0 + 7 * 1 + 3) = Z at hE hbad
      clear hTb hD hEp hTs
      omega
    · have hF : (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j) < 2 ^ (7 * j + 2) := by
        have h := scaled_minus_three (2 * j) (5 * j)
        have e1 : 2 * j + 2 + 5 * j = 7 * j + 2 := by clear hTb hE hD hEp hTs h; omega
        rw [e1] at h
        exact h
      have hFK : (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j) < 2 ^ (25 * (a + 1) + 9 - 3) :=
        lt_of_lt_of_le hF (pow2_mono (by clear hTb hE hD hEp hTs hF; omega))
      have hTK : 2 * T - 1 < 2 ^ (25 * (a + 1) + 9 - 3) :=
        lt_of_lt_of_le hTs (pow2_mono (by clear hTb hE hD hEp hTs hF hFK; omega))
      have hpos : 0 < (2 * T - 1) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j) := by
        generalize (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j) = F
        clear hTb hE hD hEp hTs hF hFK hTK; omega
      have heq : CounterBits.value bs + ((2 * T - 1) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j)) +
          (2 ^ (10 * (a + 1) + 6) - 3) * 2 ^ (25 * (a + 1) + 9) = 2 ^ (m + 7 * j + 3) := by
        rw [← Nat.add_assoc (CounterBits.value bs)]; exact hE
      refine MultiGapMarker.positive_subtraction_marker bs (m + 7 * j + 3) (25 * (a + 1) + 9)
        (2 ^ (10 * (a + 1) + 6) - 3) ((2 * T - 1) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j))
        (by clear hTb hE hD hEp hTs hF hFK hTK hpos heq; omega) hEp hpos ?_ heq
      exact sum_small (25 * (a + 1) + 9) (2 * T - 1) _
        (by clear hTb hE hD hEp hTs hF hFK hTK hpos heq; omega) hTK hFK

theorem direct_odd_marker (bs : List Bool) (a j m T : ℕ)
    (hj : 1 ≤ j) (hm : 1 ≤ m ∧ m ≤ 4 * a + 2) (hT : 0 < T) (hTb : T ≤ 6 * 2 ^ m)
    (hE : CounterBits.value bs + (T + 3) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1) +
      (2 ^ (10 * a + 11) - 3) * 2 ^ (25 * a + 24) = 2 ^ (m + 7 * j + 2)) :
    WallInvariant.marked 1 bs := by
  have hD : 0 < 2 ^ (2 * j + 2) - 3 := minus_three_positive (2 * j)
  have hEp : 0 < 2 ^ (10 * a + 11) - 3 := by
    rw [show 10 * a + 11 = (10 * a + 9) + 2 by clear hTb hE; omega]
    exact minus_three_positive (10 * a + 9)
  have hTs : T + 3 < 2 ^ (m + 3) := terminal_small_odd m T hm.1 hTb
  by_cases hsmall : m + 6 ≤ 5 * j
  · refine MultiGapMarker.two_gap_marker bs (m + 7 * j + 2) (5 * j - 1) (25 * a + 24)
      (2 ^ (2 * j + 2) - 3) (2 ^ (10 * a + 11) - 3) (T + 3)
      hD hEp (by clear hTb hE hD hEp hTs; omega)
      (by clear hTb hE hD hEp hTs; omega) ?_ hE
    exact lt_of_lt_of_le hTs (pow2_mono (by clear hTb hE hD hEp hTs; omega))
  · have hF : (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1) < 2 ^ (7 * j + 1) :=
      lt_of_lt_of_le (scaled_minus_three (2 * j) (5 * j - 1))
        (pow2_mono (by clear hTb hE hD hEp hTs; omega))
    have hFK : (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1) < 2 ^ (25 * a + 24 - 3) :=
      lt_of_lt_of_le hF (pow2_mono (by clear hTb hE hD hEp hTs hF; omega))
    have hTK : T + 3 < 2 ^ (25 * a + 24 - 3) :=
      lt_of_lt_of_le hTs (pow2_mono (by clear hTb hE hD hEp hTs hF hFK; omega))
    have hpos : 0 < (T + 3) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1) := by
      generalize (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1) = F
      clear hTb hE hD hEp hTs hF hFK hTK; omega
    have heq : CounterBits.value bs + ((T + 3) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1)) +
        (2 ^ (10 * a + 11) - 3) * 2 ^ (25 * a + 24) = 2 ^ (m + 7 * j + 2) := by
      rw [← Nat.add_assoc (CounterBits.value bs)]; exact hE
    refine MultiGapMarker.positive_subtraction_marker bs (m + 7 * j + 2) (25 * a + 24)
      (2 ^ (10 * a + 11) - 3) ((T + 3) + (2 ^ (2 * j + 2) - 3) * 2 ^ (5 * j - 1))
      (by clear hTb hE hD hEp hTs hF hFK hTK hpos heq; omega) hEp hpos ?_ heq
    exact sum_small (25 * a + 24) (T + 3) _
      (by clear hTb hE hD hEp hTs hF hFK hTK hpos heq; omega) hTK hFK

end OdDirectMarker

/-! ## SignedGapMarker -/

namespace SignedGapMarker

open CounterBits MarkerArithmetic WallInvariant GapMarker

private theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem high_residue (v A C M low : ℕ)
    (hA : M ≤ A) (hC : M ≤ C) (heq : v + 2 ^ C = 2 ^ A + low) :
    v % 2 ^ M = low % 2 ^ M := by
  have heq' := heq
  rw [power_multiple M C hC, power_multiple M A hA] at heq'
  have hrhs : 2 ^ (A - M) * 2 ^ M + low = low + 2 ^ (A - M) * 2 ^ M := by omega
  rw [hrhs] at heq'
  have hmod := congrArg (fun n => n % 2 ^ M) heq'
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at hmod
  exact hmod

theorem positive_three_marker (bs : List Bool) (A B J delta : ℕ)
    (hB : 3 ≤ B) (hA : J + 2 ≤ A) (hd : delta < 2 ^ J)
    (heq : value bs + (2 ^ B - 3) * 2 ^ J = 2 ^ A + delta) :
    marked 1 bs := by
  have hpowB : 8 ≤ 2 ^ B := by change 2 ^ 3 ≤ 2 ^ B; exact pow2_mono hB
  have hsum : value bs + 2 ^ (B + J) = 2 ^ A + (3 * 2 ^ J + delta) := by
    rw [Nat.pow_add]
    have hdist : (2 ^ B - 3) * 2 ^ J + 3 * 2 ^ J = 2 ^ B * 2 ^ J := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    omega
  rcases Nat.even_or_odd' J with ⟨a, rfl | rfl⟩
  · have hmod := high_residue (value bs) A (B + 2 * a) (2 * a + 2)
      (3 * 2 ^ (2 * a) + delta) (by clear heq hsum hd; omega) (by clear heq hsum hd; omega) hsum
    have hmark := marked_residue_auto bs (2 * a + 1) (2 ^ (2 * a) + delta)
      (by rw [Nat.pow_succ]; clear heq hsum hmod; omega) (by
        rw [show 2 * a + 1 + 1 = 2 * a + 2 by clear heq hsum hmod hd; omega, hmod, Nat.mod_eq_of_lt]
        · rw [Nat.pow_succ]; clear heq hsum hmod; omega
        · rw [show 2 * a + 2 = (2 * a) + 1 + 1 by clear heq hsum hmod hd; omega,
            Nat.pow_succ, Nat.pow_succ]
          clear heq hsum hmod; omega)
    have hpar : (2 * a + 1) % 2 = 1 := by clear heq hsum hmod hmark hd; omega
    rwa [hpar] at hmark
  · have hmod := high_residue (value bs) A (B + (2 * a + 1)) ((2 * a + 1) + 1)
      (3 * 2 ^ (2 * a + 1) + delta) (by clear heq hsum hd; omega) (by clear heq hsum hd; omega) hsum
    have hmark := marked_residue_auto bs (2 * a + 1) delta hd (by
      rw [hmod]
      have hsplit : 3 * 2 ^ (2 * a + 1) + delta =
          (2 ^ (2 * a + 1) + delta) + 1 * 2 ^ ((2 * a + 1) + 1) := by
        rw [Nat.pow_succ]; clear heq hsum hmod; omega
      rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
      rw [Nat.pow_succ]; clear heq hsum hmod hsplit; omega)
    have hpar : (2 * a + 1) % 2 = 1 := by clear heq hsum hmod hmark hd; omega
    rwa [hpar] at hmark

theorem signed_small_marker (bs : List Bool) (A B J c small : ℕ)
    (hJ : 3 ≤ J) (hB : 3 ≤ B) (hA : J + 2 ≤ A)
    (hc : 0 < c) (hcsmall : c < 2 ^ (J - 2)) (hsmall : small < 2 ^ (J - 2))
    (heq : value bs + c + (2 ^ B - 3) * 2 ^ J = 2 ^ A + small) :
    marked 1 bs := by
  by_cases hneg : small < c
  · exact small_subtraction_marker bs A B J (c - small) hJ hB
      (by clear hcsmall hsmall heq; omega)
      (by clear heq; omega)
      (by generalize (2 ^ B - 3) * 2 ^ J = X at heq ⊢; generalize 2 ^ A = Y at heq ⊢;
          clear hcsmall hsmall; omega)
  · refine positive_three_marker bs A B J (small - c) hB hA ?_ ?_
    · have hp : 2 ^ (J - 2) ≤ 2 ^ J := pow2_mono (by clear hcsmall hsmall heq; omega)
      clear heq; omega
    · generalize (2 ^ B - 3) * 2 ^ J = X at heq ⊢
      generalize 2 ^ A = Y at heq ⊢
      clear hcsmall hsmall; omega

end SignedGapMarker

/-! ## DeficitResidues -/

namespace DeficitResidues

inductive pre_deficit : ℕ → Prop where
  | PreInitial (v : ℕ) : pre_deficit ((2 ^ (2 * v + 3) - 3) * 2 ^ (5 * v + 3))
  | PreOdd (d v : ℕ) : pre_deficit d →
      pre_deficit ((2 * d + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4))

def residues : List ℕ := [0, 40, 112, 1392, 3696, 7424, 7680]

theorem power_mod_zero (coefficient z : ℕ) (hz : 13 ≤ z) :
    (coefficient * 2 ^ z) % 8192 = 0 := by
  have hp : 2 ^ z = 2 ^ (z - 13) * 8192 := by
    change 2 ^ z = 2 ^ (z - 13) * 2 ^ 13
    rw [← Nat.pow_add, Nat.sub_add_cancel hz]
  rw [hp, show coefficient * (2 ^ (z - 13) * 8192) =
    0 + (coefficient * 2 ^ (z - 13)) * 8192 by ring,
    Nat.add_mul_mod_self_right]

theorem step_mod (d v : ℕ) :
    ((2 * d + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4)) % 8192 =
      ((2 * (d % 8192) + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4)) % 8192 := by
  have hd := Nat.div_add_mod d 8192
  have hp := pow2_pos (2 * v + 3)
  have hsplit : (2 * d + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4) =
      (2 * (d % 8192) + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4) +
        (2 * (d / 8192) * 2 ^ (5 * v + 4)) * 8192 := by
    have h1 : 2 * d + 2 ^ (2 * v + 3) - 1 =
        (2 * (d % 8192) + 2 ^ (2 * v + 3) - 1) + 2 * (d / 8192) * 8192 := by omega
    rw [h1, Nat.add_mul]
    congr 1
    ring
  rw [hsplit, Nat.add_mul_mod_self_right]

theorem initial_residue (v : ℕ) :
    ((2 ^ (2 * v + 3) - 3) * 2 ^ (5 * v + 3)) % 8192 ∈ residues := by
  rcases v with _ | _ | v
  · decide
  · decide
  · rw [power_mod_zero _ _ (by omega)]
    decide

theorem finite_step :
    residues.all (fun r =>
      [0, 1].all (fun v =>
        residues.any (fun x =>
          (((2 * r + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4)) % 8192) == x))) = true := by
  decide

theorem residue_step (d v : ℕ) (hd : d % 8192 ∈ residues) :
    ((2 * d + 2 ^ (2 * v + 3) - 1) * 2 ^ (5 * v + 4)) % 8192 ∈ residues := by
  by_cases hv : 2 ≤ v
  · rw [power_mod_zero _ _ (by omega)]
    decide
  · rw [step_mod]
    have hcheck := finite_step
    rw [List.all_eq_true] at hcheck
    have hr := hcheck (d % 8192) hd
    rw [List.all_eq_true] at hr
    have hvin : v ∈ [0, 1] := by
      rcases v with _ | _ | v <;> simp at hv ⊢
    have hv' := hr v hvin
    rw [List.any_eq_true] at hv'
    obtain ⟨x, hx, heq⟩ := hv'
    rw [beq_iff_eq] at heq
    rwa [heq]

theorem deficit_residue (d : ℕ) (hd : pre_deficit d) : d % 8192 ∈ residues := by
  induction hd with
  | PreInitial v => exact initial_residue v
  | PreOdd d v _ ih => exact residue_step d v ih

def window_test (r h p c i : ℕ) : Bool :=
  Nat.ble h i && (Nat.ble i (3 * h + 6) &&
    ((i % 2 == p) && (((r + c) / 2 ^ i) % 2 == 0)))

theorem finite_windows :
    residues.all (fun r =>
      (List.range 4).all (fun h =>
        (List.range 2).all (fun p =>
          (List.range (2 ^ h)).all (fun c =>
            (List.range 13).any (window_test r h p c))))) = true := by
  decide

theorem residue_window (r h p c : ℕ)
    (hr : r ∈ residues) (hh : h ≤ 3) (hp : p < 2) (hc : c < 2 ^ h) :
    ∃ i, h ≤ i ∧ i < 13 ∧ i ≤ 3 * h + 6 ∧ i % 2 = p ∧
      ((r + c) / 2 ^ i) % 2 = 0 := by
  have hcheck := finite_windows
  rw [List.all_eq_true] at hcheck
  have h1 := hcheck r hr
  rw [List.all_eq_true] at h1
  have h2 := h1 h (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at h2
  have h3 := h2 p (List.mem_range.mpr hp)
  rw [List.all_eq_true] at h3
  have h4 := h3 c (List.mem_range.mpr hc)
  rw [List.any_eq_true] at h4
  obtain ⟨i, hi, htest⟩ := h4
  rw [List.mem_range] at hi
  unfold window_test at htest
  simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at htest
  exact ⟨i, htest.1, hi, htest.2.1, htest.2.2.1, htest.2.2.2⟩

theorem bit_residue (d c i : ℕ) (hi : i < 13) :
    ((d + c) / 2 ^ i) % 2 = (((d % 8192) + c) / 2 ^ i) % 2 := by
  have hp : 8192 = (2 ^ (12 - i) * 2) * 2 ^ i := by
    change 2 ^ 13 = (2 ^ (12 - i) * 2 ^ 1) * 2 ^ i
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hd := Nat.div_add_mod d 8192
  have he : d + c = (d % 8192 + c) + ((d / 8192) * 2 ^ (12 - i) * 2) * 2 ^ i := by
    have hd' : d = ((2 ^ (12 - i) * 2) * 2 ^ i) * (d / 8192) + d % 8192 := by
      rw [← hp]; omega
    conv_lhs => rw [hd']
    ring
  rw [he, Nat.add_mul_div_right _ _ (pow2_pos i), Nat.add_mul_mod_self_right]

theorem small_window (d h p c : ℕ)
    (hd : pre_deficit d) (hh : h ≤ 3) (hp : p < 2) (hc : c < 2 ^ h) :
    ∃ i, h ≤ i ∧ i ≤ 3 * h + 6 ∧ i % 2 = p ∧
      ((d + c) / 2 ^ i) % 2 = 0 := by
  obtain ⟨i, hlo, hi, hhi, hpar, hbit⟩ :=
    residue_window (d % 8192) h p c (deficit_residue d hd) hh hp hc
  refine ⟨i, hlo, hhi, hpar, ?_⟩
  rw [bit_residue d c i hi]
  exact hbit

end DeficitResidues

/-! ## BinaryZero -/

namespace BinaryZero

theorem parity_index (n p : ℕ) (hp : p < 2) :
    ∃ i, n ≤ i ∧ i ≤ n + 1 ∧ i % 2 = p := by
  by_cases h : n % 2 = p
  · exact ⟨n, by omega, by omega, h⟩
  · exact ⟨n + 1, by omega, by omega, by omega⟩

theorem parity_lift (s i p : ℕ) (hp : p < 2) (hi : i % 2 = (p + s) % 2) :
    (s + i) % 2 = p := by
  omega

theorem zero_below_shift (d z c h i : ℕ)
    (hc : c < 2 ^ h) (hhi : h ≤ i) (hiz : i < z) :
    ((d * 2 ^ z + c) / 2 ^ i) % 2 = 0 := by
  have hp : 2 ^ h ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hhi
  have hpow : 2 ^ z = 2 ^ (z - i) * 2 ^ i := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hrew : d * 2 ^ z + c = c + (d * 2 ^ (z - i)) * 2 ^ i := by
    rw [hpow]; ring
  rw [hrew, Nat.add_mul_div_right _ _ (pow2_pos i), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [show z - i = (z - i - 1) + 1 by omega, Nat.pow_succ,
    show d * (2 ^ (z - i - 1) * 2) = 0 + (d * 2 ^ (z - i - 1)) * 2 by ring,
    Nat.add_mul_mod_self_right]

theorem step_div (d a z c : ℕ) :
    ((2 * d + 2 ^ (a + 1) - 1) * 2 ^ z + c) / 2 ^ (z + 1) =
      d + (2 ^ a - 1) + (2 ^ z + c) / 2 ^ (z + 1) := by
  have hpa := pow2_pos a
  have hsplit : (2 * d + 2 ^ (a + 1) - 1) * 2 ^ z + c =
      (2 ^ z + c) + (d + (2 ^ a - 1)) * 2 ^ (z + 1) := by
    have hcoeff : 2 * d + 2 ^ (a + 1) - 1 = 1 + 2 * (d + (2 ^ a - 1)) := by
      rw [Nat.pow_succ]; omega
    rw [hcoeff, Nat.pow_succ]
    generalize 2 ^ a - 1 = A
    ring
  rw [hsplit, Nat.add_mul_div_right _ _ (pow2_pos (z + 1))]
  omega

theorem step_bit (d a z c i : ℕ) :
    (((2 * d + 2 ^ (a + 1) - 1) * 2 ^ z + c) / 2 ^ ((z + 1) + i)) % 2 =
      ((d + (2 ^ a - 1) + (2 ^ z + c) / 2 ^ (z + 1)) / 2 ^ i) % 2 := by
  rw [Nat.pow_add 2 (z + 1) i, ← Nat.div_div_eq_div_mul, step_div]

theorem low_carry (z c h : ℕ) (hc : c < 2 ^ h) (hh : h ≤ z) :
    (2 ^ z + c) / 2 ^ (z + 1) = 0 := by
  apply Nat.div_eq_of_lt
  have hp : 2 ^ h ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) hh
  rw [Nat.pow_succ]
  omega

theorem high_carry (z c h : ℕ) (hc : c < 2 ^ h) (hh : z + 1 ≤ h) :
    (2 ^ z + c) / 2 ^ (z + 1) ≤ 2 ^ (h - z - 1) := by
  have he : 2 ^ h = 2 ^ (z + 1) * 2 ^ (h - z - 1) := by
    rw [← Nat.pow_add, show (z + 1) + (h - z - 1) = h by omega]
  rw [he] at hc
  by_contra hgt
  have hge : 2 ^ (h - z - 1) + 1 ≤ (2 ^ z + c) / 2 ^ (z + 1) := by omega
  have hprod : 2 ^ (z + 1) * (2 ^ (h - z - 1) + 1) ≤
      2 ^ (z + 1) * ((2 ^ z + c) / 2 ^ (z + 1)) :=
    Nat.mul_le_mul_left _ hge
  have hdiv := Nat.div_add_mod (2 ^ z + c) (2 ^ (z + 1))
  rw [Nat.mul_add, Nat.mul_one] at hprod
  have hz : 2 ^ z < 2 ^ (z + 1) := by have := pow2_pos z; rw [Nat.pow_succ]; omega
  omega

def window (d : ℕ) : Prop :=
  ∀ h p c, p < 2 → c < 2 ^ h →
    ∃ i, h ≤ i ∧ i ≤ 3 * h + 6 ∧ i % 2 = p ∧ ((d + c) / 2 ^ i) % 2 = 0

theorem lift_low (d a z h bound p c : ℕ)
    (hd : window d) (hp : p < 2) (hc : c < 2 ^ h) (hh : h ≤ z)
    (hb : z + 1 + 3 * a + 6 ≤ bound) :
    ∃ i, h ≤ i ∧ i ≤ bound ∧ i % 2 = p ∧
      (((2 * d + 2 ^ (a + 1) - 1) * 2 ^ z + c) / 2 ^ i) % 2 = 0 := by
  have hpa := pow2_pos a
  obtain ⟨i, hi, hupper, hpar, hzero⟩ :=
    hd a ((p + (z + 1)) % 2) (2 ^ a - 1) (by omega) (by omega)
  refine ⟨(z + 1) + i, by omega, by omega, parity_lift (z + 1) i p hp hpar, ?_⟩
  rw [step_bit, low_carry z c h hc hh, Nat.add_zero]
  exact hzero

theorem lift_high (d a z h bound p c : ℕ)
    (hd : window d) (hp : p < 2) (hc : c < 2 ^ h) (hh : z + 1 ≤ h)
    (ha : z + 1 + 3 * (a + 1) + 6 ≤ bound)
    (hb : z + 1 + 3 * (h - z) + 6 ≤ bound) :
    ∃ i, h ≤ i ∧ i ≤ bound ∧ i % 2 = p ∧
      (((2 * d + 2 ^ (a + 1) - 1) * 2 ^ z + c) / 2 ^ i) % 2 = 0 := by
  set j := max (a + 1) (h - z)
  set r := (2 ^ z + c) / 2 ^ (z + 1)
  have hcarry : r ≤ 2 ^ (h - z - 1) := high_carry z c h hc hh
  have hpowA : 2 * 2 ^ a ≤ 2 ^ j := by
    have : 2 * 2 ^ a = 2 ^ (a + 1) := by rw [Nat.pow_succ]; omega
    rw [this]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpowB : 2 * 2 ^ (h - z - 1) ≤ 2 ^ j := by
    have : 2 * 2 ^ (h - z - 1) = 2 ^ (h - z) := by
      conv_rhs => rw [show h - z = (h - z - 1) + 1 by omega, Nat.pow_succ]
      omega
    rw [this]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpa := pow2_pos a
  have hsmall : 2 ^ a - 1 + r < 2 ^ j := by omega
  obtain ⟨i, hi, hupper, hpar, hzero⟩ :=
    hd j ((p + (z + 1)) % 2) (2 ^ a - 1 + r) (by omega) hsmall
  refine ⟨(z + 1) + i, by omega, by omega, parity_lift (z + 1) i p hp hpar, ?_⟩
  rw [step_bit, show d + (2 ^ a - 1) + r = d + (2 ^ a - 1 + r) by omega]
  exact hzero

end BinaryZero

/-! ## DeficitWindow -/

namespace DeficitWindow

theorem internal_window (d : ℕ) (hd : DeficitResidues.pre_deficit d) :
    BinaryZero.window d := by
  induction hd with
  | PreInitial v =>
    intro h p c hp hc
    by_cases hsmall : h ≤ 3
    · exact DeficitResidues.small_window _ h p c (.PreInitial v) hsmall hp hc
    · by_cases hz : h + 2 ≤ 5 * v + 3
      · obtain ⟨i, hi, htop, hpar⟩ := BinaryZero.parity_index h p hp
        exact ⟨i, hi, by omega, hpar, BinaryZero.zero_below_shift _ _ _ h i hc hi (by omega)⟩
      · have hd_lt : (2 ^ (2 * v + 3) - 3) * 2 ^ (5 * v + 3) < 2 ^ (7 * v + 6) := by
          have h0 := OdEvenMarker.scaled_minus_three (2 * v + 1) (5 * v + 3)
          have e1 : (2 * v + 1) + 2 = 2 * v + 3 := by clear hc h0; omega
          have e2 : 2 * v + 3 + (5 * v + 3) = 7 * v + 6 := by clear hc h0 e1; omega
          rw [e1, e2] at h0
          exact h0
        set j := max h (7 * v + 6)
        have hpowH : 2 ^ h ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
        have hpowV : 2 ^ (7 * v + 6) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
        have hsum : (2 ^ (2 * v + 3) - 3) * 2 ^ (5 * v + 3) + c < 2 ^ (j + 1) := by
          rw [Nat.pow_succ 2 j]; omega
        obtain ⟨i, hi, htop, hpar⟩ := BinaryZero.parity_index (j + 1) p hp
        refine ⟨i, by omega, by omega, hpar, ?_⟩
        have hpowI : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
        rw [Nat.div_eq_of_lt (by omega)]
  | PreOdd d v hd ih =>
    intro h p c hp hc
    by_cases hsmall : h ≤ 3
    · exact DeficitResidues.small_window _ h p c (.PreOdd d v hd) hsmall hp hc
    · by_cases hz : h + 2 ≤ 5 * v + 4
      · obtain ⟨i, hi, htop, hpar⟩ := BinaryZero.parity_index h p hp
        exact ⟨i, hi, by omega, hpar, BinaryZero.zero_below_shift _ _ _ h i hc hi (by omega)⟩
      · rw [show 2 * v + 3 = (2 * v + 2) + 1 by omega]
        by_cases hh : h ≤ 5 * v + 4
        · exact BinaryZero.lift_low d (2 * v + 2) (5 * v + 4) h (3 * h + 6) p c
            ih hp hc hh (by omega)
        · exact BinaryZero.lift_high d (2 * v + 2) (5 * v + 4) h (3 * h + 6) p c
            ih hp hc (by omega) (by omega) (by omega)

theorem final_window (d v h p c : ℕ)
    (hd : DeficitResidues.pre_deficit d) (hh : 2 ≤ h) (hp : p < 2) (hc : c < 2 ^ h) :
    ∃ i, h ≤ i ∧ i ≤ 3 * h + 8 ∧ i % 2 = p ∧
      (((2 * d + 2 ^ (2 * v + 2) - 1) * 2 ^ (5 * v + 1) + c) / 2 ^ i) % 2 = 0 := by
  have hw := internal_window d hd
  by_cases hz : h + 2 ≤ 5 * v + 1
  · obtain ⟨i, hi, htop, hpar⟩ := BinaryZero.parity_index h p hp
    exact ⟨i, hi, by omega, hpar, BinaryZero.zero_below_shift _ _ _ h i hc hi (by omega)⟩
  · rw [show 2 * v + 2 = (2 * v + 1) + 1 by omega]
    by_cases hlow : h ≤ 5 * v + 1
    · exact BinaryZero.lift_low d (2 * v + 1) (5 * v + 1) h (3 * h + 8) p c
        hw hp hc hlow (by omega)
    · exact BinaryZero.lift_high d (2 * v + 1) (5 * v + 1) h (3 * h + 8) p c
        hw hp hc (by omega) (by omega) (by omega)

theorem half_window (d v h p c : ℕ)
    (hd : DeficitResidues.pre_deficit d) (hh : 2 ≤ h) (hp : p < 2) (hc : c < 2 ^ h) :
    ∃ i, h ≤ i ∧ i ≤ 3 * h + 9 ∧ i % 2 = p ∧
      (((2 * d + 2 ^ (2 * v + 2) - 1) * 2 ^ (5 * v) + c) / 2 ^ i) % 2 = 0 := by
  have hw := internal_window d hd
  by_cases hz : h + 2 ≤ 5 * v
  · obtain ⟨i, hi, htop, hpar⟩ := BinaryZero.parity_index h p hp
    exact ⟨i, hi, by omega, hpar, BinaryZero.zero_below_shift _ _ _ h i hc hi (by omega)⟩
  · rw [show 2 * v + 2 = (2 * v + 1) + 1 by omega]
    by_cases hlow : h ≤ 5 * v
    · exact BinaryZero.lift_low d (2 * v + 1) (5 * v) h (3 * h + 9) p c
        hw hp hc hlow (by omega)
    · exact BinaryZero.lift_high d (2 * v + 1) (5 * v) h (3 * h + 9) p c
        hw hp hc (by omega) (by omega) (by omega)

end DeficitWindow

/-! ## ZeroComplement -/

namespace ZeroComplement

theorem zero_bit_residue (S i : ℕ) (hS : 0 < S) (hz : ((S - 1) / 2 ^ i) % 2 = 0) :
    ∃ r, r < 2 ^ i ∧ S % 2 ^ (i + 1) = r + 1 := by
  have hp := pow2_pos i
  have hdiv := Nat.div_add_mod (S - 1) (2 ^ i)
  have hquot := Nat.div_add_mod ((S - 1) / 2 ^ i) 2
  rw [hz, Nat.add_zero] at hquot
  have hr : (S - 1) % 2 ^ i < 2 ^ i := Nat.mod_lt (S - 1) hp
  set r := (S - 1) % 2 ^ i
  set q := ((S - 1) / 2 ^ i) / 2
  refine ⟨r, hr, ?_⟩
  have hE : S = (r + 1) + q * 2 ^ (i + 1) := by
    have h1 : S - 1 = 2 ^ i * (2 * q) + r := by rw [hquot]; exact hdiv.symm
    have h2 : 2 ^ i * (2 * q) = q * 2 ^ (i + 1) := by rw [Nat.pow_succ]; ring
    omega
  rw [hE, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega)]

theorem zero_complement_mod (bs : List Bool) (S i : ℕ)
    (hS : 0 < S) (hi : i % 2 = 1) (hz : ((S - 1) / 2 ^ i) % 2 = 0)
    (hsum : (CounterBits.value bs + S) % 2 ^ (i + 1) = 0) :
    WallInvariant.marked 1 bs := by
  obtain ⟨r, hr, hres⟩ := zero_bit_residue S i hS hz
  have hp := pow2_pos i
  have hcd : r + 1 < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
  have hsum' : (CounterBits.value bs + (r + 1)) % 2 ^ (i + 1) = 0 := by
    rw [Nat.add_mod, hres] at hsum
    rw [Nat.add_mod, Nat.mod_eq_of_lt hcd]
    exact hsum
  have hvalue := GapMarker.complement_residue (CounterBits.value bs) (2 ^ (i + 1)) (r + 1)
    (by omega) hcd hsum'
  have hmark := GapMarker.marked_residue_auto bs i (2 ^ i - (r + 1))
    (by omega) (by rw [hvalue, Nat.pow_succ]; omega)
  rwa [hi] at hmark

theorem zero_complement_multiple (bs : List Bool) (A J D S i : ℕ)
    (hS : 0 < S) (hiA : i < A) (hiJ : i < J) (hi : i % 2 = 1)
    (hz : ((S - 1) / 2 ^ i) % 2 = 0)
    (hE : CounterBits.value bs + S + D * 2 ^ J = 2 ^ A) :
    WallInvariant.marked 1 bs := by
  refine zero_complement_mod bs S i hS hi hz ?_
  have heq := hE
  rw [MarkerArithmetic.power_multiple (i + 1) A (by omega),
    MarkerArithmetic.power_multiple (i + 1) J (by omega)] at heq
  have hmul : CounterBits.value bs + S + D * (2 ^ (J - (i + 1)) * 2 ^ (i + 1)) =
      (CounterBits.value bs + S) + (D * 2 ^ (J - (i + 1))) * 2 ^ (i + 1) := by ring
  have hrhs : 2 ^ (A - (i + 1)) * 2 ^ (i + 1) =
      0 + 2 ^ (A - (i + 1)) * 2 ^ (i + 1) := by omega
  rw [hmul, hrhs] at heq
  have hmod := congrArg (fun x => x % 2 ^ (i + 1)) heq
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.zero_mod] at hmod
  exact hmod

theorem zero_complement (bs : List Bool) (L S i : ℕ)
    (hS : 0 < S) (hiL : i < L) (hi : i % 2 = 1)
    (hz : ((S - 1) / 2 ^ i) % 2 = 0)
    (hE : CounterBits.value bs + S = 2 ^ L) :
    WallInvariant.marked 1 bs :=
  zero_complement_multiple bs L L 0 S i hS hiL hiL hi hz (by omega)

theorem zero_complement_digits (L v S i : ℕ)
    (hS : 0 < S) (hE : v + S = 2 ^ L) (hiL : i < L) (hi : i % 2 = 1)
    (hz : ((S - 1) / 2 ^ i) % 2 = 0) :
    WallInvariant.marked 1 (CounterFinish.digits L v) := by
  refine zero_complement (CounterFinish.digits L v) L S i hS hiL hi hz ?_
  rw [CounterBits.digits_value L v (by omega)]
  exact hE

end ZeroComplement

/-! ## ExceptionalPasses -/

namespace ExceptionalPasses

abbrev da : List Γ := [0, 0, 0, 0, 0]
abbrev db : List Γ := [1, 0, 0, 0, 0]
abbrev dc : List Γ := [0, 0, 0, 0, 1]
abbrev dd : List Γ := [1, 0, 0, 0, 1]
abbrev p : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, []), (qB, []))]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]

theorem shifted_two : SegRLs mtm (p ^ 2) x dc da :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem shifted_even (k : ℕ) : SegRLs mtm (p ^ (2 * k + 2)) (x ++ p ^ k) dc da := by
  rw [show 2 * k + 2 = 2 + k * 2 by omega, pow_add_list]
  exact shifted_two.trans (LocalPasses.d0_Incs k)

theorem shifted_odd (k : ℕ) : SegRLs mtm (p ^ (2 * k + 3)) (x ++ p ^ k) dc db := by
  rw [show 2 * k + 3 = 2 + (k * 2 + 1) by omega, pow_add_list]
  exact shifted_two.trans (LocalPasses.d01_Incs k)

theorem exception_zero : SegRLs mtm x [] da dc :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem exception_one : SegRLs mtm (x ++ p) [] da dd :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem exception_even (k : ℕ) : SegRLs mtm (x ++ p ^ (2 * k + 2)) (x ++ p ^ k) da da :=
  exception_zero.trans (shifted_even k)

theorem exception_odd (k : ℕ) : SegRLs mtm (x ++ p ^ (2 * k + 3)) (x ++ p ^ k) da db :=
  exception_zero.trans (shifted_odd k)

theorem exception_shifted : SegRLs mtm x x dc da :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem exception_shifted_even (k : ℕ) : SegRLs mtm (x ++ p ^ (k * 2)) (x ++ p ^ k) dc da :=
  exception_shifted.trans (LocalPasses.d0_Incs k)

theorem exception_shifted_odd (k : ℕ) : SegRLs mtm (x ++ p ^ (k * 2 + 1)) (x ++ p ^ k) dc db :=
  exception_shifted.trans (LocalPasses.d01_Incs k)

theorem exception_zeros (k n : ℕ) :
    SegRLs mtm (x ++ p ^ ((k + 2) * 2 ^ n - 2)) (x ++ p ^ k) (da ^ n) (da ^ n) := by
  induction n generalizing k with
  | zero =>
    rw [show (k + 2) * 2 ^ 0 - 2 = k by omega, pow_zero_list]
    exact SegRLs.empty mtm _
  | succ n ih =>
    have hp := pow2_pos n
    have hge : 2 ≤ (k + 2) * 2 ^ n := by nlinarith
    have heq : (k + 2) * 2 ^ (n + 1) - 2 = 2 * ((k + 2) * 2 ^ n - 2) + 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [heq, pow_succ_list]
    exact (exception_even ((k + 2) * 2 ^ n - 2)).concat (ih k)

theorem exception_shifteds (k n : ℕ) :
    SegRLs mtm (x ++ p ^ (k * 2 ^ n)) (x ++ p ^ k) (dc ^ n) (da ^ n) := by
  induction n generalizing k with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one, pow_zero_list]
    exact SegRLs.empty mtm _
  | succ n ih =>
    rw [show k * 2 ^ (n + 1) = (k * 2 ^ n) * 2 by rw [Nat.pow_succ]; ring,
      pow_succ_list, pow_succ_list]
    exact (exception_shifted_even (k * 2 ^ n)).concat (ih k)

end ExceptionalPasses

/-! ## PhaseE -/

namespace PhaseE

open ExceptionalPasses

abbrev shifted : List Bool → List Γ := WallInvariant.shifted
abbrev normal : List Bool → List Γ := WallInvariant.normal

def lag (b : Bool) : List Bool → List Bool
  | [] => []
  | c :: t => b :: lag c t

def finalbit (b : Bool) : List Bool → Bool
  | [] => b
  | c :: t => finalbit c t

def xp (n : ℕ) (b : Bool) : List (DH0 Γ Λ × DH0 Γ Λ) :=
  x ++ p ^ (2 ^ n - 2 + if b then 1 else 0)

theorem lds_Incs' (k n : ℕ) :
    SegRLs mtm (LocalPasses.h ^ k) (p ^ (k * 2 ^ n))
      (LocalPasses.ld ^ n) (LocalPasses.ld ^ n) := by
  have h := (LocalPasses.lds_Incs k n).concat (LocalPasses.m0_Incs (k * 2 ^ n))
  simpa only [List.append_nil] using h

theorem da_pow_default : ∀ (n : ℕ), da ^ n +> (default : ListBlank Γ) = default
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ_list, append_assoc, da_pow_default n]
    exact zeros_default 5

theorem normal_app (a b : List Bool) : normal (a ++ b) = normal a ++ normal b :=
  OddImage.normal_app a b

theorem lag_final (b : Bool) (bs : List Bool) : lag b bs ++ [finalbit b bs] = b :: bs := by
  induction bs generalizing b with
  | nil => rfl
  | cons c t ih => simp only [lag, finalbit, List.cons_append, ih]

theorem digit_shift (n : ℕ) (previous bit : Bool) (hn : n ≠ 0) :
    SegRLs mtm (xp (n + 1) previous) (xp n bit)
      (if bit then dc else da) (if previous then db else da) := by
  have hpow : 2 ≤ 2 ^ n := by
    rcases n with _ | m
    · contradiction
    · have := pow2_pos m; rw [Nat.pow_succ]; omega
  unfold xp
  rw [Nat.pow_succ]
  cases previous <;> cases bit <;> simp only [↓reduceIte, Bool.false_eq_true]
  · refine segRLs_congr (exception_even (2 ^ n - 2)) ?_ rfl rfl rfl
    congr 2; omega
  · refine segRLs_congr (exception_shifted_even (2 ^ n - 1)) ?_ ?_ rfl rfl
    · congr 2; omega
    · congr 2; omega
  · refine segRLs_congr (exception_odd (2 ^ n - 2)) ?_ rfl rfl rfl
    congr 2; omega
  · refine segRLs_congr (exception_shifted_odd (2 ^ n - 1)) ?_ ?_ rfl rfl
    · congr 2; omega
    · congr 2; omega

theorem digits_shift (n : ℕ) (previous : Bool) (bs : List Bool) (hn : n ≠ 0) :
    SegRLs mtm (xp (bs.length + n) previous) (xp n (finalbit previous bs))
      (shifted bs) (normal (lag previous bs)) := by
  induction bs generalizing previous with
  | nil =>
    dsimp only [List.length_nil, finalbit, shifted, WallInvariant.shifted,
      lag, normal, WallInvariant.normal]
    rw [Nat.zero_add]
    exact SegRLs.empty mtm _
  | cons b bs ih =>
    dsimp only [List.length_cons, shifted, WallInvariant.shifted, lag, normal,
      WallInvariant.normal, finalbit]
    rw [show bs.length + 1 + n = (bs.length + n) + 1 by omega]
    exact (digit_shift (bs.length + n) previous b (by omega)).concat (ih b)

theorem exception_blank : SideRLs mtm x default (dc +> default) := by
  simpa using BoundedConfig.sideRLs_c_spec mtm (hs := x) (r := []) (r' := dc)
    (T := 1000) (by decide)

theorem flush_zeros (n : ℕ) :
    SideRLs mtm (xp (n + 1) false) default (da ^ n +> (dc +> default)) := by
  unfold xp
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  have hp := pow2_pos n
  have heq : 2 ^ (n + 1) - 2 = (0 + 2) * 2 ^ n - 2 := by rw [Nat.pow_succ]; omega
  rw [heq]
  have hs := (exception_zeros 0 n).sideRLs_concat exception_blank
  simpa only [pow_zero_list, List.append_nil, da_pow_default n] using hs

theorem flush (n : ℕ) (b : Bool) :
    SideRLs mtm (xp (n + 2) b) default ((if b then db else da) +> (da ^ n +> (dc +> default))) := by
  rw [show n + 2 = (n + 1) + 1 by omega]
  have hs := (digit_shift (n + 1) b false (by omega)).sideRLs_concat (flush_zeros n)
  have hd : da +> (default : ListBlank Γ) = default := zeros_default 5
  simpa only [Bool.false_eq_true, ↓reduceIte, hd] using hs

theorem normal_lag (b : Bool) (bs : List Bool) :
    normal (lag b bs) ++ (if finalbit b bs then db else da) =
      (if b then db else da) ++ normal bs := by
  have hr : (if finalbit b bs then db else da) = normal [finalbit b bs] := by
    simp [WallInvariant.normal]
  rw [hr, ← normal_app, lag_final]
  rfl

theorem digits_flush (n : ℕ) (previous : Bool) (bs : List Bool) :
    SideRLs mtm (xp (bs.length + n + 2) previous) (shifted bs +> default)
      ((if previous then db else da) +> (normal bs +> (da ^ n +> (dc +> default)))) := by
  rw [show bs.length + n + 2 = bs.length + (n + 2) by omega]
  have hs := (digits_shift (n + 2) previous bs (by omega)).sideRLs_concat
    (flush n (finalbit previous bs))
  refine sideRLs_congr hs rfl rfl ?_
  rw [← append_assoc (normal (lag previous bs)), normal_lag, append_assoc]

theorem shifted_suffix (u : ℕ) (bs : List Bool) (n : ℕ) :
    SideRLs mtm (p ^ (2 ^ (u + bs.length + n + 3)))
      (da ^ u +> (dc +> (shifted bs +> default)))
      (da ^ (u + 1) +> (db +> (normal bs +> (da ^ n +> (dc +> default))))) := by
  have h1 : SegRLs mtm (p ^ (2 ^ (u + bs.length + n + 3))) (p ^ (2 ^ (bs.length + n + 3)))
      (da ^ u) (da ^ u) := by
    refine segRLs_congr (LocalPasses.d0s_Incs (2 ^ (bs.length + n + 3)) u) ?_ rfl rfl rfl
    change p ^ (2 ^ (bs.length + n + 3) * 2 ^ u) = p ^ (2 ^ (u + bs.length + n + 3))
    rw [← Nat.pow_add, show bs.length + n + 3 + u = u + bs.length + n + 3 by omega]
  have hpow : 2 ≤ 2 ^ (bs.length + n + 2) := by
    have hp := pow2_pos (bs.length + n + 1)
    have hstep : 2 ^ (bs.length + n + 2) = 2 ^ (bs.length + n + 1) * 2 := by
      rw [show bs.length + n + 2 = (bs.length + n + 1) + 1 by omega, Nat.pow_succ]
    omega
  have h2 : SegRLs mtm (p ^ (2 ^ (bs.length + n + 3))) (xp (bs.length + n + 2) true) dc da := by
    unfold xp
    simp only [↓reduceIte]
    refine segRLs_congr (shifted_even (2 ^ (bs.length + n + 2) - 1)) ?_ ?_ rfl rfl
    · congr 1
      have heq : 2 ^ (bs.length + n + 3) = 2 ^ (bs.length + n + 2) * 2 :=
        Nat.pow_succ 2 (bs.length + n + 2)
      rw [heq]
      omega
    · congr 2; omega
  have hs := h1.sideRLs_concat (h2.sideRLs_concat (digits_flush n true bs))
  simp only [↓reduceIte] at hs
  refine sideRLs_congr hs rfl rfl ?_
  rw [pow_succ_list', append_assoc]

theorem even_wall (u : ℕ) (bs : List Bool) (n : ℕ) :
    let k := u + bs.length + n + 3
    ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      (([1, 1] : List Γ) ^ k +> (da ^ u +> (dc +> (shifted bs +> default))))) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        ([1] +> (([1, 1] : List Γ) ^ k +>
          (da ^ (u + 1) +> (db +> (normal bs +> (da ^ n +> (dc +> default)))))))) := by
  intro k
  refine LocalPasses.BigStep ?_
  have h1 := lds_Incs' 1 k
  rw [Nat.one_mul] at h1
  exact h1.sideRLs_concat (shifted_suffix u bs n)

theorem shifted_app (a b : List Bool) :
    WallInvariant.shifted (a ++ b) = WallInvariant.shifted a ++ WallInvariant.shifted b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [WallInvariant.shifted, ih, List.append_assoc]

theorem shifted_zeros (n : ℕ) : WallInvariant.shifted (List.replicate n false) = da ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, WallInvariant.shifted, Bool.false_eq_true, ↓reduceIte,
      ih, pow_succ_list]

theorem normal_zeros (n : ℕ) : WallInvariant.normal (List.replicate n false) = da ^ n :=
  OddImage.normal_zeros n

theorem first_true (bs : List Bool) (h : true ∈ bs) :
    ∃ u t, bs = List.replicate u false ++ true :: t := by
  induction bs with
  | nil => simp at h
  | cons a bs ih =>
    cases a
    · simp only [List.mem_cons, Bool.true_eq_false, false_or] at h
      obtain ⟨u, t, rfl⟩ := ih h
      exact ⟨u + 1, t, by simp [List.replicate_succ]⟩
    · exact ⟨0, bs, rfl⟩

def output_bits (n : ℕ) (bs : List Bool) : List Bool :=
  false :: (bs ++ List.replicate (n - bs.length - 2) false)

theorem phase_E (n : ℕ) (bs : List Bool) (hlen : bs.length + 2 ≤ n) (hin : true ∈ bs) :
    (WallInvariant.E n bs) [mtm]⊢⁺ (WallInvariant.Od n (output_bits n bs)) := by
  obtain ⟨u, t, rfl⟩ := first_true bs hin
  set padding := n - (List.replicate u false ++ true :: t).length - 2
  have hk : n = u + t.length + padding + 3 := by
    simp only [padding, List.length_append, List.length_replicate, List.length_cons] at hlen ⊢
    omega
  have hrun := even_wall u t padding
  dsimp only at hrun
  rw [← hk] at hrun
  refine stepPlus_congr hrun ?_ ?_
  · unfold WallInvariant.E WallInvariant.wall LocalPasses.lh
    rw [shifted_app, shifted_zeros]
    dsimp only [WallInvariant.shifted, shifted]
    simp only [↓reduceIte, append_assoc]
  · unfold WallInvariant.Od WallInvariant.wall LocalPasses.lh
    dsimp only [output_bits, normal]
    have hout : WallInvariant.normal (false :: ((List.replicate u false ++ true :: t)
        ++ List.replicate padding false)) =
        da ^ (u + 1) ++ db ++ WallInvariant.normal t ++ da ^ padding := by
      simp only [WallInvariant.normal, Bool.false_eq_true, ↓reduceIte, List.append_assoc,
        OddImage.normal_app, OddImage.normal_zeros]
      rw [pow_succ_list da u]
      simp only [List.append_assoc]
    change ((([0] : List Γ) +> ([1, 1] +> default)) {{qA}}>
        ([1] +> (([1, 1] : List Γ) ^ n +> (da ^ (u + 1) +> (db +>
          (WallInvariant.normal t +> (da ^ padding +> (dc +> default)))))))) =
      (([0] : List Γ) +> ([1, 1] +> default)) {{qA}}>
        ((([1, 1] : List Γ) ^ n ++ [1] ++
          WallInvariant.normal (false :: ((List.replicate u false ++ true :: t) ++
            List.replicate padding false)) ++ [0, 0, 0, 0, 1]) +> default)
    rw [hout, one_comm_11_side]
    simp only [List.append_assoc, append_assoc]

theorem output_length (n : ℕ) (bs : List Bool) (h : bs.length + 2 ≤ n) :
    (output_bits n bs).length + 1 = n := by
  unfold output_bits
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

theorem output_first_zero (n : ℕ) (bs : List Bool) :
    WallInvariant.first_zero (output_bits n bs) :=
  ⟨bs ++ List.replicate (n - bs.length - 2) false, rfl⟩

theorem output_marked (n : ℕ) (bs : List Bool) (h : WallInvariant.marked 1 bs) :
    WallInvariant.marked 0 (output_bits n bs) := by
  rcases h with ⟨pre, post, rfl, hp⟩
  refine ⟨false :: pre, post ++ List.replicate (n - (pre ++ true :: post).length - 2) false,
    ?_, ?_⟩
  · unfold output_bits; simp [List.append_assoc]
  · simp only [List.length_cons]; omega

theorem phase_E_invariant (n : ℕ) (bs : List Bool)
    (hlen : bs.length + 2 ≤ n) (hmark : WallInvariant.marked 1 bs) :
    ∃ c, ((WallInvariant.E n bs) [mtm]⊢⁺ c) ∧ WallInvariant.invariant c := by
  refine ⟨WallInvariant.Od n (output_bits n bs), phase_E n bs hlen ?_, ?_⟩
  · rcases hmark with ⟨pre, post, rfl, _⟩
    simp
  · exact .InvOd (by have := output_length n bs hlen; omega)
      (output_first_zero n bs) (output_marked n bs hmark)

end PhaseE

/-! ## PhaseEd -/

namespace PhaseEd

open ExceptionalPasses PhaseE

abbrev dd : List Γ := [0, 0, 0, 1, 0]
abbrev dd1 : List Γ := [1, 0, 0, 1, 0]

def fuel : List Bool → ℕ
  | [] => 3
  | b :: t => 2 * fuel t + if b then 1 else 3

abbrev value : List Bool → ℕ := CounterBits.value

theorem defect_carry :
    SideRLs mtm (x ++ p ^ 3) (dd +> default) (db +> (dd1 +> default)) := by
  have hs := BoundedConfig.sideRLs_c_spec mtm (hs := x ++ p ^ 3)
    (r := dd) (r' := db ++ dd1) (T := 1000) (by decide)
  simpa only [append_assoc] using hs

theorem carried_prefix (bs : List Bool) :
    SegRLs mtm (x ++ p ^ fuel bs) (x ++ p ^ 3) (shifted bs) (db ^ bs.length) := by
  induction bs with
  | nil =>
    dsimp only [fuel, shifted, WallInvariant.shifted, List.length_nil]
    rw [pow_zero_list]
    exact SegRLs.empty mtm _
  | cons b bs ih =>
    dsimp only [fuel, shifted, WallInvariant.shifted, List.length_cons]
    rw [pow_succ_list db]
    refine SegRLs.concat ?_ ih
    cases b
    · exact exception_odd (fuel bs)
    · change SegRLs mtm (x ++ p ^ (2 * fuel bs + 1)) (x ++ p ^ fuel bs) dc db
      rw [show 2 * fuel bs + 1 = fuel bs * 2 + 1 by omega]
      exact exception_shifted_odd (fuel bs)

theorem ordinary_prefix (bs : List Bool) (h : true ∈ bs) :
    SegRLs mtm (p ^ (fuel bs + 2)) (x ++ p ^ 3) (shifted bs) (db ^ bs.length) := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
    cases b <;> dsimp only [fuel, shifted, WallInvariant.shifted, List.length_cons] <;>
      rw [pow_succ_list db]
    · simp only [List.mem_cons, Bool.true_eq_false, false_or] at h
      rw [show (2 * fuel bs + if false = true then 1 else 3) + 2 =
        (fuel bs + 2) * 2 + 1 by simp; omega]
      exact (LocalPasses.d01_Incs (fuel bs + 2)).concat (ih h)
    · rw [show (2 * fuel bs + if true = true then 1 else 3) + 2 =
        2 * fuel bs + 3 by simp]
      exact (shifted_odd (fuel bs)).concat (carried_prefix bs)

theorem nonzero_preconversion (bs : List Bool) (h : true ∈ bs) :
    SideRLs mtm (p ^ (fuel bs + 2)) (shifted bs +> (dd +> default))
      (db ^ (bs.length + 1) +> (dd1 +> default)) := by
  rw [pow_succ_list' db bs.length, append_assoc]
  exact (ordinary_prefix bs h).sideRLs_concat defect_carry

theorem fuel_value (bs : List Bool) : fuel bs + 2 * value bs + 3 = 6 * 2 ^ bs.length := by
  unfold value
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [fuel, CounterBits.value, List.length_cons, Nat.pow_succ,
      ↓reduceIte, Bool.false_eq_true] <;> omega

theorem value_bound (bs : List Bool) : value bs < 2 ^ bs.length :=
  MarkerArithmetic.value_bound bs

theorem fuel_bound (bs : List Bool) : fuel bs + 3 ≤ 6 * 2 ^ bs.length := by
  have := fuel_value bs; omega

theorem fuel_positive (bs : List Bool) : 3 ≤ fuel bs := by
  induction bs with
  | nil => simp [fuel]
  | cons b bs ih =>
    cases b <;> simp only [fuel, ↓reduceIte, Bool.false_eq_true] <;> omega

theorem fuel_fits (n : ℕ) (bs : List Bool) (hn : bs.length + 3 ≤ n) :
    fuel bs + 3 < 2 ^ n := by
  have hb := fuel_bound bs
  have hp : 2 ^ (bs.length + 3) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hp0 := pow2_pos bs.length
  rw [Nat.pow_add] at hp
  change 2 ^ bs.length * 8 ≤ 2 ^ n at hp
  omega

theorem even_wall_counter (n : ℕ) (r : ListBlank Γ) :
    ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> (([1, 1] : List Γ) ^ n +> r)) [mtm]⊢*
      (CounterRules.rGate (CounterRules.LC n (2 ^ n - 1)) r) :=
  OddFuel.scan_ones n r

theorem shifted_rank_bound (len k s : ℕ) (hk : k < 2 ^ len) :
    (k * 2 + 1) * 2 ^ s - 1 < 2 ^ (len + 1 + s) := by
  have hs := pow2_pos s
  rw [show len + 1 + s = (len + 1) + s by omega, Nat.pow_add, Nat.pow_succ]
  have hlt : (k * 2 + 1) * 2 ^ s ≤ 2 ^ len * 2 * 2 ^ s := by nlinarith
  have hpos : 1 ≤ (k * 2 + 1) * 2 ^ s := by nlinarith
  omega

theorem gap2_even_counter (len k a : ℕ) (_hk : k < 2 ^ len) :
    (CounterRules.rGate (CounterRules.LC len k) (db ^ (a * 2) +> (dd1 +> default))) [mtm]⊢⁺
      (CounterRules.rGate
        (CounterRules.LC (len + 1 + (a * 5 + 1)) ((k * 2 + 1) * 2 ^ (a * 5 + 1) - 1))
        (CounterRules.RC 1)) := by
  have hstep := BoundaryRules.gap2_even (CounterRules.LC len k) default a
  refine stepPlus_congr hstep ?_ ?_
  · congr 1
    have hd : ([1, 0, 0, 1, 0, 0, 0, 0] : List Γ) +> (default : ListBlank Γ) = dd1 +> default := by
      rw [show ([1, 0, 0, 1, 0, 0, 0, 0] : List Γ) = dd1 ++ [0, 0, 0] from rfl,
        append_assoc, BoundedConfig.all0_spec (a := [0, 0, 0]) (by decide)]
    rw [hd]
  · congr 1
    · unfold CounterRules.LC
      exact BinDec_mulpow2sub1 CounterRules.ld0 CounterRules.ld1 len k (a * 5 + 1) CounterRules.ldh
    · unfold CounterRules.RC
      rw [BinInc_1, show CounterRules.rd1 = [1, 0, 0, 0] ++ [0] from rfl,
        append_assoc, BoundedConfig.all0_spec (a := [0]) (by decide)]

theorem gap2_odd_counter (len k a : ℕ) (_hk : k < 2 ^ len) :
    (CounterRules.rGate (CounterRules.LC len k) (db ^ (a * 2 + 1) +> (dd1 +> default))) [mtm]⊢⁺
      (CounterRules.rGate
        (CounterRules.LC (len + 1 + (a * 5 + 4)) ((k * 2 + 1) * 2 ^ (a * 5 + 4) - 1))
        (CounterRules.RC 0)) := by
  have hstep := BoundaryRules.gap2_odd (CounterRules.LC len k) default a
  refine stepPlus_congr hstep ?_ ?_
  · congr 1
    have hd : ([1, 0, 0, 1, 0, 0, 0, 0] : List Γ) +> (default : ListBlank Γ) = dd1 +> default := by
      rw [show ([1, 0, 0, 1, 0, 0, 0, 0] : List Γ) = dd1 ++ [0, 0, 0] from rfl,
        append_assoc, BoundedConfig.all0_spec (a := [0, 0, 0]) (by decide)]
    rw [hd]
  · congr 1
    · unfold CounterRules.LC
      exact BinDec_mulpow2sub1 CounterRules.ld0 CounterRules.ld1 len k (a * 5 + 4) CounterRules.ldh
    · unfold CounterRules.RC
      rw [BinInc_O, BoundedConfig.all0_spec (a := [0, 0, 0]) (by decide)]

theorem gap2_even_wall (len k a : ℕ) (hk : k < 2 ^ len) :
    (CounterRules.rGate (CounterRules.LC len k) (db ^ (a * 2) +> (dd1 +> default))) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        ([1] +> (([1, 1] : List Γ) ^ (len + 1 + (a * 5 + 1)) +>
          CounterRules.RC ((k * 2 + 1) * 2 ^ (a * 5 + 1) + 1)))) := by
  have h1 := gap2_even_counter len k a hk
  have h2 := CounterFinish.counter_finish (len + 1 + (a * 5 + 1))
    ((k * 2 + 1) * 2 ^ (a * 5 + 1) - 1) 1 (shifted_rank_bound len k (a * 5 + 1) hk)
  have hp := pow2_pos (a * 5 + 1)
  have heq : 1 + ((k * 2 + 1) * 2 ^ (a * 5 + 1) - 1) + 1 =
      (k * 2 + 1) * 2 ^ (a * 5 + 1) + 1 := by
    have : 1 ≤ (k * 2 + 1) * 2 ^ (a * 5 + 1) := by nlinarith
    omega
  rw [heq] at h2
  exact stepPlus_trans h1 h2

theorem gap2_odd_wall (len k a : ℕ) (hk : k < 2 ^ len) :
    (CounterRules.rGate (CounterRules.LC len k) (db ^ (a * 2 + 1) +> (dd1 +> default))) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        ([1] +> (([1, 1] : List Γ) ^ (len + 1 + (a * 5 + 4)) +>
          CounterRules.RC ((k * 2 + 1) * 2 ^ (a * 5 + 4))))) := by
  have h1 := gap2_odd_counter len k a hk
  have h2 := CounterFinish.counter_finish (len + 1 + (a * 5 + 4))
    ((k * 2 + 1) * 2 ^ (a * 5 + 4) - 1) 0 (shifted_rank_bound len k (a * 5 + 4) hk)
  have hp := pow2_pos (a * 5 + 4)
  have heq : 0 + ((k * 2 + 1) * 2 ^ (a * 5 + 4) - 1) + 1 = (k * 2 + 1) * 2 ^ (a * 5 + 4) := by
    have : 1 ≤ (k * 2 + 1) * 2 ^ (a * 5 + 4) := by nlinarith
    omega
  rw [heq] at h2
  exact stepPlus_trans h1 h2

theorem nonzero_counter_entry (n : ℕ) (bs : List Bool)
    (hlen : bs.length + 3 ≤ n) (hin : true ∈ bs) :
    (WallInvariant.Ed n bs) [mtm]⊢*
      (CounterRules.rGate (CounterRules.LC n (2 ^ n - fuel bs - 3))
        (db ^ (bs.length + 1) +> (dd1 +> default))) := by
  have hfits := fuel_fits n bs hlen
  unfold WallInvariant.Ed WallInvariant.wall
  simp only [List.append_assoc, append_assoc]
  have h1 := even_wall_counter n (shifted bs +> (dd +> default))
  have heq : 2 ^ n - 1 = (2 ^ n - fuel bs - 3) + (fuel bs + 2) := by omega
  rw [heq] at h1
  have h2 := CounterBatch.right_pass_batch n (2 ^ n - fuel bs - 3) (fuel bs + 2)
    _ _ (by omega) (nonzero_preconversion bs hin)
  exact stepStar_trans h1 h2

theorem shifted_value_bound (len k s : ℕ) (hk : k < 2 ^ len) :
    (k * 2 + 1) * 2 ^ s < 2 ^ (len + 1 + s) := by
  have hs := pow2_pos s
  rw [show len + 1 + s = (len + 1) + s by omega, Nat.pow_add, Nat.pow_succ]
  nlinarith

theorem remaining_bound (n : ℕ) (bs : List Bool) (hn : bs.length + 3 ≤ n) :
    2 ^ n - fuel bs - 3 < 2 ^ n := by
  have := fuel_fits n bs hn; omega

theorem remaining_decomposition (n : ℕ) (bs : List Bool) (hn : bs.length + 3 ≤ n) :
    ∃ q, 2 ^ n - fuel bs - 3 = (q * 2 + 1) * 2 ^ (bs.length + 1) + 2 * value bs := by
  have hfuel := fuel_value bs
  have hfits := fuel_fits n bs hn
  set d := n - bs.length - 2
  have hd : 0 < d := by omega
  have he : n = bs.length + 2 + d := by omega
  have hp : 2 ≤ 2 ^ d := by
    rcases d with _ | m
    · omega
    · have := pow2_pos m; rw [Nat.pow_succ]; omega
  refine ⟨2 ^ d - 2, ?_⟩
  have hpow_n : 2 ^ n = 2 ^ bs.length * 4 * 2 ^ d := by
    rw [he, Nat.pow_add, Nat.pow_add]
  have hpow_b1 : 2 ^ (bs.length + 1) = 2 ^ bs.length * 2 := Nat.pow_succ 2 bs.length
  set M := (2 ^ d - 2) * 2 + 1
  have hM : M + 3 = 2 ^ d * 2 := by omega
  have hmul : M * (2 ^ bs.length * 2) + 6 * 2 ^ bs.length = 2 ^ bs.length * 4 * 2 ^ d := by
    calc M * (2 ^ bs.length * 2) + 6 * 2 ^ bs.length
      _ = (M + 3) * (2 ^ bs.length * 2) := by ring
      _ = (2 ^ d * 2) * (2 ^ bs.length * 2) := by rw [hM]
      _ = 2 ^ bs.length * 4 * 2 ^ d := by ring
  rw [hpow_n, hpow_b1]
  omega

theorem remaining_lower_bound (n : ℕ) (bs : List Bool) (hn : bs.length + 3 ≤ n) :
    0 < 2 ^ n - fuel bs - 3 := by
  obtain ⟨q, hq⟩ := remaining_decomposition n bs hn
  have hp := pow2_pos (bs.length + 1)
  have : 1 ≤ (q * 2 + 1) * 2 ^ (bs.length + 1) := by nlinarith
  omega

end PhaseEd

/-! ## EdEvenOrbit -/

namespace EdEvenOrbit

theorem fourth_eq_shifted (bs : List Bool) :
    CDPasses.fourth bs = WallInvariant.shifted bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> dsimp only [CDPasses.fourth, CDPasses.fourth_digit, WallInvariant.shifted] <;>
      rw [ih]

theorem first_mass_bounds (n v width k : ℕ)
    (hv : 0 < v) (hn : v * 2 + 2 ≤ n) (hw : width ≤ n) (hk : k < 2 ^ width) :
    2 ^ width ≤ OddImage.first_mass n v ∧
    OddImage.first_mass n v + k < 2 ^ (n + v * 5 + 1) := by
  obtain ⟨he, hf⟩ := OddImage.first_fuel_bounds n (v * 2) (by omega)
  have hscale : 2 ^ (v * 2) * 4 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    rw [Nat.pow_add] at h
    exact h
  have hpos := pow2_pos (v * 2)
  have hbase : 2 ^ n ≤ 2 * OddImage.first_fuel n (v * 2) + 1 := by omega
  have hpow := pow2_pos (v * 5 - 1)
  have hwidth : 2 ^ width ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hw
  refine ⟨by unfold OddImage.first_mass; nlinarith, ?_⟩
  have hb := PhaseEd.shifted_value_bound n (OddImage.first_fuel n (v * 2)) (v * 5 - 1) hf
  rw [show n + 1 + (v * 5 - 1) = n + v * 5 by omega,
    Nat.mul_comm (OddImage.first_fuel n (v * 2)) 2] at hb
  have hsmall : 2 ^ n ≤ 2 ^ (n + v * 5) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_succ]
  unfold OddImage.first_mass
  omega

theorem any_true (bs : List Bool) (h : true ∈ bs) : CDPasses.any bs = true := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
    cases b
    · simp only [List.mem_cons, Bool.true_eq_false, false_or] at h
      simp [CDPasses.any, ih h]
    · rfl

theorem normal_shift_odd (width k u : ℕ) (hk : k < 2 ^ width) :
    WallInvariant.normal (List.replicate u false ++ true :: CounterFinish.digits width k) +>
      default = CounterRules.RC ((k * 2 + 1) * 2 ^ u) := by
  rw [OddImage.normal_app, OddImage.normal_zeros, WallInvariant.normal]
  simp only [↓reduceIte, append_assoc, CounterFinish.digits_normal width k hk]
  unfold CounterRules.RC
  rw [BinInc_mulpow2, BinInc_mul2add1]
  rfl

theorem even_image_marker (n v width k i q r : ℕ)
    (hv : 0 < v) (hn : v * 2 + 2 ≤ n) (hw : width ≤ n) (hk : k < 2 ^ width)
    (hi : i < v * 5 - 1) (hodd : i % 2 = 1) (hr : r < 2 ^ i)
    (hdecomp : k = (q * 2 + 1) * 2 ^ i + r) :
    ∃ out,
      out.length + 2 ≤ n + v * 5 + 2 ∧
      WallInvariant.marked 1 out ∧
      ((WallInvariant.O n
        (List.replicate (v * 2) false ++ true :: CounterFinish.digits width k)) [mtm]⊢⁺
        (WallInvariant.Ed (n + v * 5 + 2) out)) := by
  obtain ⟨hmin, hmax⟩ := first_mass_bounds n v width k hv hn hw hk
  have hlength : width + (n + v * 5 + 1 - width) = n + v * 5 + 1 := by omega
  have hvalue : CDPasses.value (CounterFinish.digits width k) = k := by
    rw [← CounterBits.value_eq_cd]
    exact CounterBits.digits_value width k hk
  have hmin' : 2 ^ (CounterFinish.digits width k).length ≤ OddImage.first_mass n v := by
    rw [CounterFinish.digits_length]; exact hmin
  have hmax' : OddImage.first_mass n v + CDPasses.value (CounterFinish.digits width k) <
      2 ^ ((CounterFinish.digits width k).length + (n + v * 5 + 1 - width)) := by
    rw [CounterFinish.digits_length, hvalue, hlength]; exact hmax
  obtain ⟨out, hlen, hval, hrun⟩ := OddImage.initial_even_image n v (CounterFinish.digits width k)
    (n + v * 5 + 1 - width) hv (by omega) hmin' hmax'
  rw [CounterFinish.digits_length, hlength] at hlen
  rw [hvalue] at hval
  have hnonzero : k ≠ 0 := by
    have hp := pow2_pos i
    have : 1 ≤ (q * 2 + 1) * 2 ^ i := by nlinarith
    omega
  have hany : CDPasses.any (CounterFinish.digits width k) = true := by
    apply any_true
    apply CounterBits.value_nonzero
    rw [CounterBits.digits_value width k hk]
    exact hnonzero
  rw [hany, fourth_eq_shifted] at hrun
  refine ⟨out, by omega, ?_, hrun⟩
  rw [← hodd]
  refine MarkerArithmetic.low_marker_preserved out k i q r (v * 5 - 1)
    (2 * OddImage.first_fuel n (v * 2) + 1) (by omega) hi hr hdecomp ?_
  rw [CounterBits.value_eq_cd]
  exact hval

theorem Ed_even_valuation_image (n : ℕ) (bs : List Bool) (b : ℕ)
    (hlength : bs.length = 4 * b) (hn : bs.length + 3 ≤ n) (hin : true ∈ bs) :
    ∃ out,
      out.length + 2 ≤ n + 35 * b + 17 ∧
      WallInvariant.marked 1 out ∧
      ((WallInvariant.Ed n bs) [mtm]⊢⁺ (WallInvariant.Ed (n + 35 * b + 17) out)) := by
  set k := 2 ^ n - PhaseEd.fuel bs - 3
  have hk : k < 2 ^ n := PhaseEd.remaining_bound n bs hn
  obtain ⟨q, hdecomp⟩ := PhaseEd.remaining_decomposition n bs hn
  rw [hlength] at hdecomp
  have hsmall := PhaseEd.value_bound bs
  rw [hlength] at hsmall
  have hr : 2 * PhaseEd.value bs < 2 ^ (4 * b + 1) := by
    rw [Nat.pow_succ]; omega
  obtain ⟨out, hlen, hmark, hrun⟩ := even_image_marker (n + 10 * b + 5) (5 * b + 2) n k
    (4 * b + 1) q (2 * PhaseEd.value bs) (by omega) (by omega) (by omega) hk (by omega)
    (by omega) hr hdecomp
  have hdim : n + 10 * b + 5 + (5 * b + 2) * 5 + 2 = n + 35 * b + 17 := by omega
  rw [hdim] at hlen hrun
  refine ⟨out, hlen, hmark, stepPlus_trans ?_ hrun⟩
  have hentry := PhaseEd.nonzero_counter_entry n bs hn hin
  rw [show bs.length + 1 = (b * 2) * 2 + 1 by omega] at hentry
  have hwall := PhaseEd.gap2_odd_wall n k (b * 2) hk
  have hstart := stepStar_stepPlus_trans hentry hwall
  refine stepPlus_congr hstart rfl ?_
  rw [show n + 1 + (b * 2 * 5 + 4) = n + 10 * b + 5 by omega,
    show b * 2 * 5 + 4 = (5 * b + 2) * 2 by omega]
  unfold WallInvariant.O WallInvariant.wall LocalPasses.lh
  simp only [List.append_assoc, append_assoc]
  rw [normal_shift_odd n k ((5 * b + 2) * 2) hk, one_comm_11_side]

end EdEvenOrbit

/-! ## EdOddOrbit -/

namespace EdOddOrbit

theorem first_fuel_half (n u : ℕ) (hn : u + 2 ≤ n) :
    2 ^ n ≤ 2 * OddImage.first_fuel n u + 1 := by
  obtain ⟨he, _⟩ := OddImage.first_fuel_bounds n u (by omega)
  have hscale : 2 ^ u * 4 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    rw [Nat.pow_add] at h
    exact h
  have hp := pow2_pos u
  omega

theorem grown_first_lower (n u width z : ℕ) (hn : u + 2 ≤ n) (hw : width ≤ n) :
    2 ^ width - 1 ≤ OddFuel.grown (OddImage.first_fuel n u) z := by
  have h1 := first_fuel_half n u hn
  have h2 : 2 ^ width ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hw
  have hz := pow2_pos z
  unfold OddFuel.grown
  have h3 : 2 ^ width ≤ (2 * OddImage.first_fuel n u + 1) * 2 ^ z := by nlinarith
  omega

theorem deficit_after_prime (L k deficit u z : ℕ)
    (hleft : k + deficit + 1 = 2 ^ L) (hprime : 2 ^ (u + 1) - 1 ≤ k) :
    OddFuel.grown (k - (2 ^ (u + 1) - 1)) z +
      (2 * deficit + 2 ^ (u + 2) - 1) * 2 ^ z + 1 = 2 ^ (L + 1 + z) := by
  have hp := pow2_pos (u + 1)
  have hz := pow2_pos z
  have hu : 2 ^ (u + 2) = 2 ^ (u + 1) * 2 := Nat.pow_succ 2 (u + 1)
  have hL : 2 ^ (L + 1 + z) = 2 ^ L * 2 * 2 ^ z := by
    rw [show L + 1 + z = (L + 1) + z by omega, Nat.pow_add, Nat.pow_succ]
  set k' := k - (2 ^ (u + 1) - 1)
  have hk_eq : k' + 2 ^ (u + 1) = k + 1 := by omega
  set B := 2 * deficit + 2 ^ (u + 2) - 1
  have hsum : (2 * k' + 1) + B = 2 ^ L * 2 := by omega
  unfold OddFuel.grown
  have hgpos : 1 ≤ (2 * k' + 1) * 2 ^ z := by nlinarith
  have hprod : (2 * k' + 1) * 2 ^ z + B * 2 ^ z = 2 ^ L * 2 * 2 ^ z := by
    rw [← Nat.add_mul, hsum]
  rw [hL]
  omega

def source_rank (n : ℕ) (bs : List Bool) : ℕ := 2 ^ n - PhaseEd.fuel bs - 3
def initial_width (n b : ℕ) : ℕ := n + 35 * b + 34
def initial_rank (n b : ℕ) : ℕ :=
  OddFuel.grown (OddImage.first_fuel (n + 10 * b + 10) (10 * b + 9)) (25 * b + 23)

theorem Ed_odd_valuation_entry (n : ℕ) (bs : List Bool) (b : ℕ)
    (hlength : bs.length = 4 * b + 2) (hn : bs.length + 3 ≤ n) (hin : true ∈ bs) :
    (WallInvariant.Ed n bs) [mtm]⊢⁺
      (CounterRules.rGate (CounterRules.LC (initial_width n b) (initial_rank n b))
        ([0, 0, 0] +> (WallInvariant.normal (CounterFinish.digits n (source_rank n bs)) +>
          default))) := by
  set k := source_rank n bs
  have hk : k < 2 ^ n := PhaseEd.remaining_bound n bs hn
  have hodd := OddRecursion.initial_odd_entry (n + 10 * b + 10) (5 * b + 4)
    (CounterFinish.digits n k) (by omega)
  have hodd' : (WallInvariant.O (n + 10 * b + 10)
      (List.replicate ((5 * b + 4) * 2 + 1) false ++ true :: CounterFinish.digits n k)) [mtm]⊢⁺
      (CounterRules.rGate (CounterRules.LC (initial_width n b) (initial_rank n b))
        ([0, 0, 0] +> (WallInvariant.normal (CounterFinish.digits n k) +> default))) := by
    refine stepPlus_congr hodd rfl ?_
    unfold initial_width initial_rank
    rw [show (5 * b + 4) * 2 + 1 = 10 * b + 9 by omega,
      show (5 * b + 4) * 5 + 3 = 25 * b + 23 by omega,
      show n + 10 * b + 10 + 1 + (25 * b + 23) = n + 35 * b + 34 by omega]
  refine stepPlus_trans ?_ hodd'
  have hentry := PhaseEd.nonzero_counter_entry n bs hn hin
  change (WallInvariant.Ed n bs) [mtm]⊢*
    (CounterRules.rGate (CounterRules.LC n k)
      (ExceptionalPasses.db ^ (bs.length + 1) +> (PhaseEd.dd1 +> default))) at hentry
  rw [show bs.length + 1 = (b * 2 + 1) * 2 + 1 by omega] at hentry
  have hwall := PhaseEd.gap2_odd_wall n k (b * 2 + 1) hk
  have hstart := stepStar_stepPlus_trans hentry hwall
  refine stepPlus_congr hstart rfl ?_
  rw [show n + 1 + ((b * 2 + 1) * 5 + 4) = n + 10 * b + 10 by omega,
    show (b * 2 + 1) * 5 + 4 = (5 * b + 4) * 2 + 1 by omega]
  unfold WallInvariant.O WallInvariant.wall LocalPasses.lh
  simp only [List.append_assoc, append_assoc]
  rw [EdEvenOrbit.normal_shift_odd n k ((5 * b + 4) * 2 + 1) hk, one_comm_11_side]

theorem Ed_odd_entry_fuel (n : ℕ) (bs : List Bool) (b : ℕ)
    (hlength : bs.length = 4 * b + 2) (hn : bs.length + 3 ≤ n) :
    2 ^ (CounterFinish.digits n (source_rank n bs)).length - 1 ≤ initial_rank n b ∧
    initial_rank n b < 2 ^ initial_width n b ∧
    initial_rank n b % 2 = 1 := by
  rw [CounterFinish.digits_length]
  unfold initial_rank initial_width
  refine ⟨grown_first_lower (n + 10 * b + 10) (10 * b + 9) n (25 * b + 23) (by omega) (by omega),
    ?_, OddRecursion.grown_odd _ _ (by omega)⟩
  obtain ⟨_, hf⟩ := OddImage.first_fuel_bounds (n + 10 * b + 10) (10 * b + 9) (by omega)
  have hbound := OddFuel.grown_bound (n + 10 * b + 10)
    (OddImage.first_fuel (n + 10 * b + 10) (10 * b + 9)) (25 * b + 23) hf
  rw [show n + 10 * b + 10 + 1 + (25 * b + 23) = n + 35 * b + 34 by omega] at hbound
  omega

theorem source_even_marker (n : ℕ) (bs : List Bool)
    (hn : bs.length + 5 ≤ n) (hpar : bs.length % 2 = 0) :
    WallInvariant.marked 0 (CounterFinish.digits n (source_rank n bs)) := by
  set m := bs.length
  set d := n - m - 5
  have he : n = m + 5 + d := by omega
  have hfuel : PhaseEd.fuel bs + 2 * PhaseEd.value bs + 3 = 6 * 2 ^ m := PhaseEd.fuel_value bs
  have hval : PhaseEd.value bs < 2 ^ m := PhaseEd.value_bound bs
  have hfits := PhaseEd.fuel_fits n bs (by omega)
  have hp := pow2_pos m
  have hd := pow2_pos d
  have hbig : 2 ^ n = 2 ^ m * 32 * 2 ^ d := by
    rw [he, Nat.pow_add, Nat.pow_add]
  have hbit : 2 ^ (m + 4) = 2 ^ m * 16 := by
    rw [Nat.pow_add]
  have hmark := CounterBits.marked_remainder n (source_rank n bs) (m + 4)
    (2 ^ d - 1) (10 * 2 ^ m + 2 * PhaseEd.value bs) (by omega)
    (by rw [hbit]; omega)
  rw [show (m + 4) % 2 = 0 by omega] at hmark
  apply hmark
  unfold source_rank
  set Q := (2 ^ d - 1) * 2 + 1
  have hQ : Q + 1 = 2 ^ d * 2 := by omega
  have hmul : Q * (2 ^ m * 16) + 16 * 2 ^ m = 2 ^ m * 32 * 2 ^ d := by
    calc Q * (2 ^ m * 16) + 16 * 2 ^ m
      _ = (Q + 1) * (2 ^ m * 16) := by ring
      _ = (2 ^ d * 2) * (2 ^ m * 16) := by rw [hQ]
      _ = 2 ^ m * 32 * 2 ^ d := by ring
  rw [hbig, hbit]
  omega

end EdOddOrbit

/-! ## TightEd -/

namespace TightEd

open ExceptionalPasses (da db dc p x shifted_even)
open PhaseE PhaseEd

theorem terminal_tight (b : Bool) :
    SideRLs mtm (xp 2 b) (dd +> default) ((if b then db else da) +> (dd1 +> default)) := by
  cases b
  · have hs := BoundedConfig.sideRLs_c_spec mtm (hs := xp 2 false)
      (r := dd) (r' := da ++ dd1) (T := 1000) (by decide)
    simpa only [Bool.false_eq_true, ↓reduceIte, append_assoc] using hs
  · change SideRLs mtm (x ++ p ^ 3) (dd +> default) (db +> (dd1 +> default))
    exact defect_carry

theorem digits_terminal (previous : Bool) (bs : List Bool) :
    SideRLs mtm (xp (bs.length + 2) previous) (shifted bs +> (dd +> default))
      ((if previous then db else da) +> (normal bs +> (dd1 +> default))) := by
  have hs := (digits_shift 2 previous bs (by omega)).sideRLs_concat
    (terminal_tight (finalbit previous bs))
  refine sideRLs_congr hs rfl rfl ?_
  rw [← append_assoc (normal (lag previous bs)), normal_lag, append_assoc]

theorem shifted_terminal (u : ℕ) (bs : List Bool) :
    SideRLs mtm (p ^ (2 ^ (u + bs.length + 3)))
      (da ^ u +> (dc +> (shifted bs +> (dd +> default))))
      (da ^ (u + 1) +> (db +> (normal bs +> (dd1 +> default)))) := by
  have h1 : SegRLs mtm (p ^ (2 ^ (u + bs.length + 3))) (p ^ (2 ^ (bs.length + 3)))
      (da ^ u) (da ^ u) := by
    refine segRLs_congr (LocalPasses.d0s_Incs (2 ^ (bs.length + 3)) u) ?_ rfl rfl rfl
    change p ^ (2 ^ (bs.length + 3) * 2 ^ u) = p ^ (2 ^ (u + bs.length + 3))
    rw [← Nat.pow_add, show bs.length + 3 + u = u + bs.length + 3 by omega]
  have hpow : 2 ≤ 2 ^ (bs.length + 2) := by
    have hp := pow2_pos (bs.length + 1)
    have hstep : 2 ^ (bs.length + 2) = 2 ^ (bs.length + 1) * 2 := by
      rw [show bs.length + 2 = (bs.length + 1) + 1 by omega, Nat.pow_succ]
    omega
  have h2 : SegRLs mtm (p ^ (2 ^ (bs.length + 3))) (xp (bs.length + 2) true) dc da := by
    unfold xp
    simp only [↓reduceIte]
    refine segRLs_congr (shifted_even (2 ^ (bs.length + 2) - 1)) ?_ ?_ rfl rfl
    · congr 1
      have heq : 2 ^ (bs.length + 3) = 2 ^ (bs.length + 2) * 2 :=
        Nat.pow_succ 2 (bs.length + 2)
      rw [heq]
      omega
    · congr 2; omega
  have hs := h1.sideRLs_concat (h2.sideRLs_concat (digits_terminal true bs))
  simp only [↓reduceIte] at hs
  refine sideRLs_congr hs rfl rfl ?_
  rw [pow_succ_list', append_assoc]

theorem even_tight_wall (u : ℕ) (bs : List Bool) :
    let k := u + bs.length + 3
    ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      (([1, 1] : List Γ) ^ k +> (da ^ u +> (dc +> (shifted bs +> (dd +> default)))))) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        ([1] +> (([1, 1] : List Γ) ^ k +>
          (da ^ (u + 1) +> (db +> (normal bs +> (dd1 +> default))))))) := by
  intro k
  refine LocalPasses.BigStep ?_
  have h1 := lds_Incs' 1 k
  rw [Nat.one_mul] at h1
  exact h1.sideRLs_concat (shifted_terminal u bs)

def after (n : ℕ) (bs : List Bool) : Cfg Γ Λ :=
  WallInvariant.wall (([1, 1] : List Γ) ^ n ++ [1] ++ WallInvariant.normal (false :: bs) ++ dd1)

theorem tight_Ed_step (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 = n) (hin : true ∈ bs) :
    (WallInvariant.Ed n bs) [mtm]⊢⁺ (after n bs) := by
  obtain ⟨u, t, rfl⟩ := first_true bs hin
  simp only [List.length_append, List.length_replicate, List.length_cons] at hn
  have hk : n = u + t.length + 3 := by omega
  have hrun := even_tight_wall u t
  dsimp only at hrun
  rw [← hk] at hrun
  refine stepPlus_congr hrun ?_ ?_
  · unfold WallInvariant.Ed WallInvariant.wall LocalPasses.lh
    rw [shifted_app, shifted_zeros]
    dsimp only [WallInvariant.shifted, shifted]
    simp only [↓reduceIte, append_assoc]
  · unfold after WallInvariant.wall LocalPasses.lh
    have hout : WallInvariant.normal (false :: (List.replicate u false ++ true :: t)) =
        da ^ (u + 1) ++ db ++ WallInvariant.normal t := by
      simp only [WallInvariant.normal, Bool.false_eq_true, ↓reduceIte, List.append_assoc,
        OddImage.normal_app, OddImage.normal_zeros]
      rw [pow_succ_list da u]
      simp only [List.append_assoc]
    dsimp only [normal]
    rw [hout, one_comm_11_side]
    simp only [List.append_assoc, append_assoc]

end TightEd

/-! ## ZeroDefect -/

namespace ZeroDefect

theorem shifted_zeros (u : ℕ) :
    WallInvariant.shifted (List.replicate u false) = ExceptionalPasses.da ^ u :=
  PhaseE.shifted_zeros u

theorem zero_terminal :
    SideRLs mtm CounterBatch.p (PhaseEd.dd +> default) (PhaseEd.dd1 +> default) := by
  simpa using BoundedConfig.sideRLs_c_spec mtm (hs := CounterBatch.p)
    (r := PhaseEd.dd) (r' := PhaseEd.dd1) (T := 1000) (by decide)

theorem zero_preconversion (u : ℕ) :
    SideRLs mtm (CounterBatch.p ^ (2 ^ (u + 1) - 1))
      (ExceptionalPasses.da ^ u +> (PhaseEd.dd +> default))
      (ExceptionalPasses.db ^ u +> (PhaseEd.dd1 +> default)) := by
  have h1 : SegRLs mtm (CounterBatch.p ^ (2 ^ (u + 1) - 1)) CounterBatch.p
      (ExceptionalPasses.da ^ u) (ExceptionalPasses.db ^ u) := by
    have hd := LocalPasses.d01s_Incs 1 u
    rw [Nat.pow_succ]
    simpa only [show (1 + 1) * 2 ^ u - 1 = 2 ^ u * 2 - 1 by omega, pow_one_list] using hd
  exact h1.sideRLs_concat zero_terminal

theorem zero_remaining_bound (n u : ℕ) (hn : u + 3 ≤ n) :
    0 < 2 ^ n - 2 ^ (u + 1) ∧ 2 ^ n - 2 ^ (u + 1) < 2 ^ n := by
  have hlt : 2 ^ (u + 1) < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
  have hp := pow2_pos (u + 1)
  omega

theorem zero_remaining_decomposition (n u : ℕ) (hn : u + 3 ≤ n) :
    ∃ q, 2 ^ n - 2 ^ (u + 1) = (q * 2 + 1) * 2 ^ (u + 2) + 2 ^ (u + 1) := by
  set d := n - u - 3
  have he : n = u + 3 + d := by omega
  have hd := pow2_pos d
  refine ⟨2 ^ d - 1, ?_⟩
  have hpow_n : 2 ^ n = 2 ^ u * 8 * 2 ^ d := by
    rw [he, Nat.pow_add, Nat.pow_add]
  have hpow_u2 : 2 ^ (u + 2) = 2 ^ u * 4 := by rw [Nat.pow_add]
  have hpow_u1 : 2 ^ (u + 1) = 2 ^ u * 2 := Nat.pow_succ 2 u
  set Q := (2 ^ d - 1) * 2 + 1
  have hQ : Q + 1 = 2 ^ d * 2 := by omega
  have hmul : Q * (2 ^ u * 4) + 2 ^ u * 4 = 2 ^ u * 8 * 2 ^ d := by
    calc Q * (2 ^ u * 4) + 2 ^ u * 4
      _ = (Q + 1) * (2 ^ u * 4) := by ring
      _ = (2 ^ d * 2) * (2 ^ u * 4) := by rw [hQ]
      _ = 2 ^ u * 8 * 2 ^ d := by ring
  rw [hpow_n, hpow_u2, hpow_u1]
  omega

theorem zero_even_marker (n a : ℕ) (hn : a * 2 + 3 ≤ n) :
    WallInvariant.marked 1
      (CounterFinish.digits (n + a * 5 + 1)
        (((2 ^ n - 2 ^ (a * 2 + 1)) * 2 + 1) * 2 ^ (a * 5))) := by
  rcases Nat.even_or_odd' a with ⟨b, rfl | rfl⟩
  · obtain ⟨q, hq⟩ := zero_remaining_decomposition n ((2 * b) * 2) hn
    have hmark := CounterBits.marked_remainder (n + (2 * b) * 5 + 1)
      (((2 ^ n - 2 ^ ((2 * b) * 2 + 1)) * 2 + 1) * 2 ^ ((2 * b) * 5))
      (14 * b + 3) q ((2 ^ ((2 * b) * 2 + 2) + 1) * 2 ^ ((2 * b) * 5))
      (by omega)
    rw [show (14 * b + 3) % 2 = 1 by omega] at hmark
    apply hmark
    · have hp1 := pow2_pos ((2 * b) * 2)
      have hp2 := pow2_pos ((2 * b) * 5)
      have hpow_i : 2 ^ (14 * b + 3) = (2 ^ ((2 * b) * 2) * 8) * 2 ^ ((2 * b) * 5) := by
        rw [show 14 * b + 3 = ((2 * b) * 2 + 3) + (2 * b) * 5 by omega,
          Nat.pow_add, Nat.pow_add]
      have hpow_r : 2 ^ ((2 * b) * 2 + 2) = 2 ^ ((2 * b) * 2) * 4 := by
        rw [Nat.pow_add]
      rw [hpow_i, hpow_r]
      nlinarith
    · rw [hq]
      have hpow_i : 2 ^ (14 * b + 3) = 2 ^ ((2 * b) * 2 + 2) * 2 * 2 ^ ((2 * b) * 5) := by
        rw [show 14 * b + 3 = ((2 * b) * 2 + 2 + 1) + (2 * b) * 5 by omega,
          Nat.pow_add, Nat.pow_succ]
      have hpow_r : 2 ^ ((2 * b) * 2 + 2) = 2 ^ ((2 * b) * 2 + 1) * 2 :=
        Nat.pow_succ 2 ((2 * b) * 2 + 1)
      rw [hpow_i, hpow_r]
      ring
  · exact CounterBits.marked_shift_odd (n + (2 * b + 1) * 5 + 1)
      (2 ^ n - 2 ^ ((2 * b + 1) * 2 + 1)) ((2 * b + 1) * 5) (by omega) (by omega)

theorem zero_counter_entry (n u : ℕ) (hn : u + 3 ≤ n) :
    (WallInvariant.Ed n (List.replicate u false)) [mtm]⊢*
      (CounterRules.rGate (CounterRules.LC n (2 ^ n - 2 ^ (u + 1)))
        (ExceptionalPasses.db ^ u +> (PhaseEd.dd1 +> default))) := by
  unfold WallInvariant.Ed WallInvariant.wall
  rw [shifted_zeros]
  simp only [List.append_assoc, append_assoc]
  have h1 := PhaseEd.even_wall_counter n (ExceptionalPasses.da ^ u +> (PhaseEd.dd +> default))
  obtain ⟨hpos, hb⟩ := zero_remaining_bound n u hn
  have hp := pow2_pos (u + 1)
  have heq : 2 ^ n - 1 = (2 ^ n - 2 ^ (u + 1)) + (2 ^ (u + 1) - 1) := by omega
  rw [heq] at h1
  have h2 := CounterBatch.right_pass_batch n (2 ^ n - 2 ^ (u + 1)) (2 ^ (u + 1) - 1)
    _ _ (by omega) (zero_preconversion u)
  exact stepStar_trans h1 h2

theorem zero_defect_invariant (n u : ℕ) (hn : u + 3 ≤ n) :
    ∃ c, ((WallInvariant.Ed n (List.replicate u false)) [mtm]⊢⁺ c) ∧ WallInvariant.invariant c := by
  obtain ⟨hpos, hb⟩ := zero_remaining_bound n u hn
  rcases Nat.even_or_odd' u with ⟨a, rfl | rfl⟩
  · rw [Nat.mul_comm 2 a] at hn hpos hb ⊢
    refine ⟨_, stepStar_stepPlus_trans (zero_counter_entry n (a * 2) hn)
      (PhaseEd.gap2_even_wall n (2 ^ n - 2 ^ (a * 2 + 1)) a hb), ?_⟩
    rw [show n + 1 + (a * 5 + 1) = (n + a * 5 + 1) + 1 by omega,
      show ((2 ^ n - 2 ^ (a * 2 + 1)) * 2 + 1) * 2 ^ (a * 5 + 1) + 1 =
        (((2 ^ n - 2 ^ (a * 2 + 1)) * 2 + 1) * 2 ^ (a * 5)) * 2 + 1 by
        rw [Nat.pow_succ]; ring]
    refine CounterBits.numeric_odd (n + a * 5 + 1)
      (((2 ^ n - 2 ^ (a * 2 + 1)) * 2 + 1) * 2 ^ (a * 5)) ?_ (zero_even_marker n a hn)
    have hsv := PhaseEd.shifted_value_bound n (2 ^ n - 2 ^ (a * 2 + 1)) (a * 5) hb
    rwa [show n + 1 + a * 5 = n + a * 5 + 1 by omega] at hsv
  · rw [Nat.mul_comm 2 a] at hn hpos hb ⊢
    refine ⟨_, stepStar_stepPlus_trans (zero_counter_entry n (a * 2 + 1) hn)
      (PhaseEd.gap2_odd_wall n (2 ^ n - 2 ^ (a * 2 + 1 + 1)) a hb), ?_⟩
    have heq : ((2 ^ n - 2 ^ (a * 2 + 1 + 1)) * 2 + 1) * 2 ^ (a * 5 + 4) =
        (((2 ^ n - 2 ^ (a * 2 + 1 + 1)) * 2 + 1) * 2 ^ (a * 5 + 3)) * 2 := by
      rw [show a * 5 + 4 = (a * 5 + 3) + 1 by omega, Nat.pow_succ]; ring
    rw [heq]
    refine CounterBits.numeric_even (n + 1 + (a * 5 + 4))
      (((2 ^ n - 2 ^ (a * 2 + 1 + 1)) * 2 + 1) * 2 ^ (a * 5 + 3)) ?_ ?_
    · have hp := pow2_pos (a * 5 + 3)
      nlinarith
    · rw [← heq]
      exact PhaseEd.shifted_value_bound n (2 ^ n - 2 ^ (a * 2 + 1 + 1)) (a * 5 + 4) hb

end ZeroDefect

/-! ## ZeroEdOrbit -/

namespace ZeroEdOrbit

def rank (n m : ℕ) : ℕ := 2 ^ n - 2 ^ (m + 1)

theorem digits_ones (n : ℕ) :
    CounterFinish.digits n (2 ^ n - 1) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := pow2_pos n
    rw [show 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 by rw [Nat.pow_succ]; omega,
      CounterFinish.digits_odd, ih, List.replicate_succ]

theorem digits_power_shift (n v u : ℕ) :
    CounterFinish.digits (n + u) (v * 2 ^ u) =
      List.replicate u false ++ CounterFinish.digits n v := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [show n + (u + 1) = (n + u) + 1 by omega,
      show v * 2 ^ (u + 1) = (v * 2 ^ u) * 2 by rw [Nat.pow_succ]; ring,
      CounterFinish.digits_even, ih, List.replicate_succ, List.cons_append]

theorem rank_digits (n m : ℕ) (hn : m + 1 ≤ n) :
    CounterFinish.digits n (rank n m) =
      List.replicate (m + 1) false ++ List.replicate (n - m - 1) true := by
  have he : n = (n - m - 1) + (m + 1) := by omega
  have hrank : rank n m = (2 ^ (n - m - 1) - 1) * 2 ^ (m + 1) := by
    unfold rank
    have hp := pow2_pos (n - m - 1)
    have hpow : 2 ^ n = 2 ^ (n - m - 1) * 2 ^ (m + 1) := by
      conv_lhs => rw [he, Nat.pow_add]
    rw [hpow, Nat.sub_mul, Nat.one_mul]
  rw [hrank]
  conv_lhs => arg 1; rw [he]
  rw [digits_power_shift, digits_ones]

theorem zero_odd_exit (n a : ℕ) (hn : a * 2 + 4 ≤ n) :
    (WallInvariant.Ed n (List.replicate (a * 2 + 1) false)) [mtm]⊢⁺
      (WallInvariant.O (n + a * 5 + 5)
        (List.replicate (a * 5 + 4) false ++
          true :: CounterFinish.digits n (rank n (a * 2 + 1)))) := by
  obtain ⟨_, hb⟩ := ZeroDefect.zero_remaining_bound n (a * 2 + 1) (by omega)
  change rank n (a * 2 + 1) < 2 ^ n at hb
  have hentry := ZeroDefect.zero_counter_entry n (a * 2 + 1) (by omega)
  change (WallInvariant.Ed n (List.replicate (a * 2 + 1) false)) [mtm]⊢*
    (CounterRules.rGate (CounterRules.LC n (rank n (a * 2 + 1)))
      (ExceptionalPasses.db ^ (a * 2 + 1) +> (PhaseEd.dd1 +> default))) at hentry
  have hwall := PhaseEd.gap2_odd_wall n (rank n (a * 2 + 1)) a hb
  have hstart := stepStar_stepPlus_trans hentry hwall
  refine stepPlus_congr hstart rfl ?_
  rw [show n + 1 + (a * 5 + 4) = n + a * 5 + 5 by omega]
  unfold WallInvariant.O WallInvariant.wall LocalPasses.lh
  simp only [List.append_assoc, append_assoc]
  rw [EdEvenOrbit.normal_shift_odd n (rank n (a * 2 + 1)) (a * 5 + 4) hb, one_comm_11_side]

theorem zero_even_valuation (n b : ℕ) (hn : 4 * b + 4 ≤ n) :
    ∃ out,
      out.length + 2 ≤ n + 35 * b + 17 ∧
      WallInvariant.marked 1 out ∧
      ((WallInvariant.Ed n (List.replicate (4 * b + 1) false)) [mtm]⊢⁺
        (WallInvariant.Ed (n + 35 * b + 17) out)) := by
  obtain ⟨_, hk⟩ := ZeroDefect.zero_remaining_bound n (4 * b + 1) (by omega)
  change rank n (4 * b + 1) < 2 ^ n at hk
  obtain ⟨q, he⟩ := ZeroDefect.zero_remaining_decomposition n (4 * b + 1) (by omega)
  change rank n (4 * b + 1) = (q * 2 + 1) * 2 ^ (4 * b + 1 + 2) + 2 ^ (4 * b + 1 + 1) at he
  have hsmall : 2 ^ (4 * b + 1 + 1) < 2 ^ (4 * b + 1 + 2) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨out, hlen, hmark, hrun⟩ := EdEvenOrbit.even_image_marker (n + 10 * b + 5) (5 * b + 2) n
    (rank n (4 * b + 1)) (4 * b + 1 + 2) q (2 ^ (4 * b + 1 + 1))
    (by omega) (by omega) (by omega) hk (by omega) (by omega) hsmall he
  have hdim : n + 10 * b + 5 + (5 * b + 2) * 5 + 2 = n + 35 * b + 17 := by omega
  rw [hdim] at hlen hrun
  refine ⟨out, hlen, hmark, stepPlus_trans ?_ hrun⟩
  have hexit := zero_odd_exit n (b * 2) (by omega)
  refine stepPlus_congr hexit ?_ ?_
  · rw [show b * 2 * 2 + 1 = 4 * b + 1 by omega]
  · rw [show n + b * 2 * 5 + 5 = n + 10 * b + 5 by omega,
      show b * 2 * 5 + 4 = (5 * b + 2) * 2 by omega,
      show b * 2 * 2 + 1 = 4 * b + 1 by omega]

theorem zero_odd_valuation_entry (n b : ℕ) (hn : 4 * b + 6 ≤ n) :
    (WallInvariant.Ed n (List.replicate (4 * b + 3) false)) [mtm]⊢⁺
      (CounterRules.rGate
        (CounterRules.LC (EdOddOrbit.initial_width n b) (EdOddOrbit.initial_rank n b))
        ([0, 0, 0] +> (WallInvariant.normal (CounterFinish.digits n (rank n (4 * b + 3))) +>
          default))) := by
  have hexit := zero_odd_exit n (b * 2 + 1) (by omega)
  have hexit' : (WallInvariant.Ed n (List.replicate (4 * b + 3) false)) [mtm]⊢⁺
      (WallInvariant.O (n + 10 * b + 10)
        (List.replicate ((5 * b + 4) * 2 + 1) false ++
          true :: CounterFinish.digits n (rank n (4 * b + 3)))) := by
    refine stepPlus_congr hexit ?_ ?_
    · rw [show (b * 2 + 1) * 2 + 1 = 4 * b + 3 by omega]
    · rw [show n + (b * 2 + 1) * 5 + 5 = n + 10 * b + 10 by omega,
        show (b * 2 + 1) * 5 + 4 = (5 * b + 4) * 2 + 1 by omega,
        show (b * 2 + 1) * 2 + 1 = 4 * b + 3 by omega]
  have hentry := OddRecursion.initial_odd_entry (n + 10 * b + 10) (5 * b + 4)
    (CounterFinish.digits n (rank n (4 * b + 3))) (by omega)
  refine stepPlus_trans hexit' (stepPlus_congr hentry rfl ?_)
  unfold EdOddOrbit.initial_width EdOddOrbit.initial_rank
  rw [show (5 * b + 4) * 2 + 1 = 10 * b + 9 by omega,
    show (5 * b + 4) * 5 + 3 = 25 * b + 23 by omega,
    show n + 10 * b + 10 + 1 + (25 * b + 23) = n + 35 * b + 34 by omega]

end ZeroEdOrbit

/-! ## StrongDigits -/

namespace StrongDigits

private theorem getD_append_eq (a b : List Bool) (i : ℕ) (h : a.length = i) :
    (a ++ true :: b).getD i false = true := by
  subst h
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.getD, List.length_cons]
    exact ih

theorem shifted_digits (n q u : ℕ) :
    CounterFinish.digits (n + u + 1) ((q * 2 + 1) * 2 ^ u) =
      List.replicate u false ++ true :: CounterFinish.digits n q := by
  rw [show n + u + 1 = (n + 1) + u by omega,
    ZeroEdOrbit.digits_power_shift, CounterFinish.digits_odd]

theorem odd_shift_guard (n q u : ℕ) (h : u % 2 = 1) :
    StrongInvariant.digit_guard (CounterFinish.digits (n + u + 1) ((q * 2 + 1) * 2 ^ u)) := by
  rw [shifted_digits]
  rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
  · omega
  · exact Or.inl ⟨v, CounterFinish.digits n q, by rw [Nat.mul_comm 2 v]⟩

theorem adjacent_shift_guard (n q u : ℕ) (hu : 0 < u) :
    StrongInvariant.digit_guard (CounterFinish.digits (n + u + 2) ((q * 4 + 3) * 2 ^ u)) := by
  rw [show q * 4 + 3 = (q * 2 + 1) * 2 + 1 by omega,
    show n + u + 2 = (n + 1) + u + 1 by omega,
    shifted_digits, CounterFinish.digits_odd]
  exact Or.inr (Or.inl ⟨u, CounterFinish.digits n q, hu, rfl⟩)

theorem digits_true_at (width v i q : ℕ) (hi : i < width) (hq : v / 2 ^ i = q * 2 + 1) :
    (CounterFinish.digits width v).getD i false = true := by
  rw [CounterBits.digits_split width i v (by omega), hq,
    show width - i = (width - i - 1) + 1 by omega, CounterFinish.digits_odd]
  exact getD_append_eq (CounterFinish.digits i v) (CounterFinish.digits (width - i - 1) q) i
    (CounterFinish.digits_length i v)

theorem digits_bit_remainder (width v i q r : ℕ)
    (hi : i < width) (hr : r < 2 ^ i) (hv : v = (q * 2 + 1) * 2 ^ i + r) :
    (CounterFinish.digits width v).getD i false = true := by
  refine digits_true_at width v i q hi ?_
  have hp := pow2_pos i
  rw [hv, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem close_shift_guard (n q a i : ℕ) (ha : 0 < a)
    (hi : (CounterFinish.digits (n + 10 * a + 1) ((q * 2 + 1) * 2 ^ (10 * a))).getD i false = true)
    (hp : i % 2 = 1) (hb : i ≤ 14 * a + 3) :
    StrongInvariant.digit_guard
      (CounterFinish.digits (n + 10 * a + 1) ((q * 2 + 1) * 2 ^ (10 * a))) :=
  Or.inr (Or.inr ⟨a, CounterFinish.digits n q, i, ha, shifted_digits n q (10 * a), hi, hp, hb⟩)

theorem odd_counter_wall (n v : ℕ) (hv : v < 2 ^ n) :
    ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      ([1] +> (([1, 1] : List Γ) ^ (n + 1) +> CounterRules.RC (v * 2 + 1)))) =
      WallInvariant.E (n + 2) (CounterFinish.digits n v) := by
  have hrc : CounterRules.RC (v * 2 + 1) = [1, 0, 0, 0, 0] +> CounterRules.RC v :=
    BinInc_mul2add1 CounterRules.rd1 v
  rw [hrc, ← CounterFinish.digits_normal n v hv, one_comm_11_side]
  have heq : (([1, 1] : List Γ) ^ (n + 1) +>
      ([1] +> ([1, 0, 0, 0, 0] +> (WallInvariant.normal (CounterFinish.digits n v) +> default)))) =
      ([1, 1] : List Γ) ^ (n + 2) +>
        (WallInvariant.shifted (CounterFinish.digits n v) +> default) := by
    have h1 : ([1] : List Γ) +> ([1, 0, 0, 0, 0] +>
        (WallInvariant.normal (CounterFinish.digits n v) +> default)) =
        [1, 1] +> ([0, 0, 0, 0] +>
          (WallInvariant.normal (CounterFinish.digits n v) +> default)) := rfl
    rw [h1, CounterBits.shifted_normal, ← append_assoc ([1, 1] ^ (n + 1)) [1, 1], ← pow_succ_list']
  rw [heq]
  unfold WallInvariant.E WallInvariant.wall LocalPasses.lh
  simp only [append_assoc]

end StrongDigits

/-! ## StrongEdDirect -/

namespace StrongEdDirect

theorem direct_guard (n : ℕ) (bs : List Bool) (a : ℕ)
    (hlen : bs.length + 1 = a * 2) (hn : bs.length + 3 ≤ n) :
    StrongInvariant.digit_guard
      (CounterFinish.digits (n + a * 5 + 1)
        (((2 ^ n - PhaseEd.fuel bs - 3) * 2 + 1) * 2 ^ (a * 5))) := by
  set k := 2 ^ n - PhaseEd.fuel bs - 3
  rcases Nat.even_or_odd' a with ⟨b, rfl | rfl⟩
  · rw [show (2 * b) * 5 = 10 * b by omega]
    refine StrongDigits.close_shift_guard n k b (14 * b + 1) (by omega) ?_ (by omega) (by omega)
    obtain ⟨q, hk_eq⟩ := PhaseEd.remaining_decomposition n bs hn
    have h4b : bs.length + 1 = 4 * b := by omega
    rw [h4b] at hk_eq
    refine StrongDigits.digits_bit_remainder (n + 10 * b + 1)
      ((k * 2 + 1) * 2 ^ (10 * b)) (14 * b + 1) q ((PhaseEd.value bs * 4 + 1) * 2 ^ (10 * b))
      (by omega) ?_ ?_
    · have hv := PhaseEd.value_bound bs
      have hp10 := pow2_pos (10 * b)
      have hpow4 : 2 ^ (4 * b) = 2 ^ bs.length * 2 := by
        rw [← h4b, Nat.pow_succ]
      have hpow14 : 2 ^ (14 * b + 1) = (2 ^ bs.length * 4) * 2 ^ (10 * b) := by
        rw [show 14 * b + 1 = (4 * b + 1) + 10 * b by omega, Nat.pow_add, Nat.pow_succ, hpow4]
        ring
      rw [hpow14]
      nlinarith
    · have hpow14 : 2 ^ (14 * b + 1) = 2 ^ (4 * b) * 2 * 2 ^ (10 * b) := by
        rw [show 14 * b + 1 = (4 * b + 1) + 10 * b by omega, Nat.pow_add, Nat.pow_succ]
      have hk_eq' : k = (q * 2 + 1) * 2 ^ (4 * b) + 2 * PhaseEd.value bs := hk_eq
      rw [hk_eq', hpow14]
      ring
  · exact StrongDigits.odd_shift_guard n k ((2 * b + 1) * 5) (by omega)

theorem Ed_direct_strong (n : ℕ) (bs : List Bool) (a : ℕ)
    (hlen : bs.length + 1 = a * 2) (hn : bs.length + 3 ≤ n) (hmark : WallInvariant.marked 1 bs) :
    ∃ c, ((WallInvariant.Ed n bs) [mtm]⊢⁺ c) ∧ StrongInvariant.strong c := by
  have hin : true ∈ bs := by
    rcases hmark with ⟨pre, post, rfl, _⟩
    simp
  set k := 2 ^ n - PhaseEd.fuel bs - 3
  have hk : k < 2 ^ n := PhaseEd.remaining_bound n bs hn
  have hentry := PhaseEd.nonzero_counter_entry n bs hn hin
  change (WallInvariant.Ed n bs) [mtm]⊢*
    (CounterRules.rGate (CounterRules.LC n k)
      (ExceptionalPasses.db ^ (bs.length + 1) +> (PhaseEd.dd1 +> default))) at hentry
  rw [hlen] at hentry
  have hwall := PhaseEd.gap2_even_wall n k a hk
  set v := (k * 2 + 1) * 2 ^ (a * 5)
  have hv : v < 2 ^ (n + a * 5 + 1) := by
    unfold v
    rw [show n + a * 5 + 1 = n + 1 + a * 5 by omega]
    exact PhaseEd.shifted_value_bound n k (a * 5) hk
  have heq : (k * 2 + 1) * 2 ^ (a * 5 + 1) + 1 = v * 2 + 1 := by
    unfold v; rw [Nat.pow_succ]; ring
  rw [heq, show n + 1 + (a * 5 + 1) = (n + a * 5 + 1) + 1 by omega,
    StrongDigits.odd_counter_wall (n + a * 5 + 1) v hv] at hwall
  refine ⟨WallInvariant.E (n + a * 5 + 1 + 2) (CounterFinish.digits (n + a * 5 + 1) v),
    stepStar_stepPlus_trans hentry hwall, ?_⟩
  refine .StrongE (by rw [CounterFinish.digits_length]) ?_
  exact direct_guard n bs a hlen hn

end StrongEdDirect

/-! ## CounterH -/

namespace CounterH

open CounterRules CounterFinish WallInvariant

abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]

theorem left_one (len k : ℕ) (hk : 1 + k < 2 ^ len) :
    SideLR mtm (qC, [0]) (qA, [0]) ([1] +> LC len (1 + k)) ([1] +> LC len k) := by
  intro r
  exact stepStar_stepPlus_trans (shift_C_1_step (LC len (1 + k)) r) (left_counter len k r hk)

theorem left_one_flip (len k : ℕ) (hk : 1 + k < 2 ^ len) :
    SideRL (flipTM mtm) (qC, [0]) (qA, [0]) ([1] +> LC len (1 + k)) ([1] +> LC len k) := by
  intro r
  exact toDHCfg_stepPlus_flip (left_one len k hk r)

theorem left_batch (len k amount : ℕ) (hk : k + amount < 2 ^ len) :
    SideRLs (flipTM mtm) ([((qC, [0]), (qA, [0]))] ^ amount)
      ([1] +> LC len (k + amount)) ([1] +> LC len k) := by
  induction amount generalizing k with
  | zero =>
    simp only [Nat.add_zero, pow_zero_list]
    exact .nil _
  | succ amount ih =>
    rw [show k + (amount + 1) = 1 + (k + amount) by omega, pow_succ_list]
    exact .cons (left_one_flip len (k + amount) (by omega)) (ih k (by omega))

theorem right_h_batch (len k amount : ℕ) (r r' : ListBlank Γ)
    (hk : k + amount < 2 ^ len) (hr : SideRLs mtm (h ^ amount) r r') :
    (rGate (LC len (k + amount)) r) [mtm]⊢* (rGate (LC len k) r') :=
  SideRLs.concat_1 hr (left_batch len k amount hk)

theorem right_h_finish (n k : ℕ) (r r' : ListBlank Γ)
    (hk : k < 2 ^ n) (hr : SideRLs mtm (h ^ (k + 1)) r r') :
    (rGate (LC n k) r) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}> ([1] +> ([1, 1] ^ n +> r'))) := by
  rw [pow_succ_list'] at hr
  obtain ⟨mid, hfirst, hlast⟩ := hr.split
  have h1 : (rGate (LC n k) r) [mtm]⊢* (rGate (LC n 0) mid) := by
    simpa only [Nat.zero_add] using right_h_batch n 0 k r mid (by omega) hfirst
  have h2 := hlast.elim_single ([1] +> LC n 0)
  have h3 := shift_C_1_step (LC n 0) r'
  exact stepStar_stepPlus_trans h1
    (stepPlus_trans h2 (stepStar_stepPlus_trans h3 (CounterFinish.return_wall n r')))

end CounterH

/-! ## BlankPasses -/

namespace BlankPasses

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev b : List Γ := [1, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev p : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, []), (qB, []))]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]

def shifted_counter (n : ℕ) : ListBlank Γ := BinInc c n

private theorem shift_C_c_step (l r : ListBlank Γ) :
    (l {{qC}}> (c +> r)) [mtm]⊢* ((([1] : List Γ) ^ 5 +> l) {{qC}}> r) := by
  have hs := runSteps_spec mtm 5 ⟨[], [0, 0, 0, 0, 1], qC, .right⟩
    ⟨[1, 1, 1, 1, 1], [], qC, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil,
    show ([1, 1, 1, 1, 1] : List Γ) = ([1] : List Γ) ^ 5 from rfl] using hs

private theorem shift_C_c_right (k : ℕ) (l r : ListBlank Γ) :
    (l {{qC}}> (c ^ k +> r)) [mtm]⊢* ((([1] : List Γ) ^ (k * 5) +> l) {{qC}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl mtm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (shift_C_c_step l (c ^ k +> r)) ?_
    refine stepStar_congr (ih (([1] : List Γ) ^ 5 +> l)) rfl ?_
    rw [← append_assoc, ← pow_add_list, show k * 5 + 5 = (k + 1) * 5 by omega]

theorem ordinary_increment (l r : ListBlank Γ) (n : ℕ) :
    (l {{qA}}> (b ^ n +> (a +> r))) [mtm]⊢⁺ (l <{{qB}} (a ^ n +> (b +> r))) := by
  have h1 := shift_A_rd1_right n l (a +> r)
  have h2 : ((([1] : List Γ) ^ (n * 5) +> l) {{qA}}> (a +> r)) [mtm]⊢⁺
      ((([1] : List Γ) ^ (n * 5) +> l) <{{qB}} (b +> r)) := by
    have hs := runSteps1_spec mtm 0 ⟨[], [0, 0, 0, 0, 0], qA, .right⟩
      ⟨[1, 0, 0, 0, 0], [], qB, .left⟩ (by decide) (([1] : List Γ) ^ (n * 5) +> l) r
    simpa only [BoundedConfig.toCfg, append_nil] using hs
  have h3 := shift_B_1_left (n * 5) l (b +> r)
  rw [zeros5_pow] at h3
  exact stepStar_stepPlus_trans h1 (stepPlus_stepStar_trans h2 h3)

theorem shifted_increment (l r : ListBlank Γ) (n : ℕ) :
    (l {{qC}}> (c ^ n +> (a +> r))) [mtm]⊢⁺ (l <{{qB}} (a ^ n +> (c +> r))) := by
  have h1 := shift_C_c_right n l (a +> r)
  have h2 : ((([1] : List Γ) ^ (n * 5) +> l) {{qC}}> (a +> r)) [mtm]⊢⁺
      ((([1] : List Γ) ^ (n * 5 + 4) +> l) <{{qB}} ([1] +> r)) := by
    have hs := runSteps1_spec mtm 4 ⟨[], [0, 0, 0, 0, 0], qC, .right⟩
      ⟨[1], [1, 1, 1, 1], qB, .left⟩ (by decide) (([1] : List Γ) ^ (n * 5) +> l) r
    have hl : ([1, 1, 1, 1] : List Γ) +> (([1] : List Γ) ^ (n * 5) +> l) =
        ([1] : List Γ) ^ (n * 5 + 4) +> l := by
      rw [show ([1, 1, 1, 1] : List Γ) = ([1] : List Γ) ^ 4 from rfl, ← append_assoc,
        ← pow_add_list, Nat.add_comm 4 (n * 5)]
    simpa only [BoundedConfig.toCfg, append_nil, hl] using hs
  have h3 := shift_B_1_left (n * 5 + 4) l ([1] +> r)
  have hr : ([0] : List Γ) ^ (n * 5 + 4) +> ([1] +> r) = a ^ n +> (c +> r) := by
    rw [pow_add_list, zeros5_pow, append_assoc]
    rfl
  rw [hr] at h3
  exact stepStar_stepPlus_trans h1 (stepPlus_stepStar_trans h2 h3)

theorem ordinary_step (n : ℕ) :
    SideRLs mtm p (CounterRules.RC n) (CounterRules.RC (1 + n)) := by
  obtain ⟨m, r', h0, h1⟩ := BinInc_succ_split b n
  unfold CounterRules.RC
  rw [h0, h1]
  exact .single (fun l => ordinary_increment l r' m)

theorem shifted_step (n : ℕ) :
    SideRLs mtm x (shifted_counter n) (shifted_counter (1 + n)) := by
  obtain ⟨m, r', h0, h1⟩ := BinInc_succ_split c n
  unfold shifted_counter
  rw [h0, h1]
  exact .single (fun l => shifted_increment l r' m)

theorem ordinary_blank (n : ℕ) :
    SideRLs mtm (p ^ n) default (CounterRules.RC n) := by
  induction n with
  | zero =>
    rw [CounterRules.RC, BinInc_O]
    exact .nil default
  | succ n ih =>
    rw [pow_succ_list', show n + 1 = 1 + n by omega]
    exact ih.trans (ordinary_step n)

theorem shifted_blank (n : ℕ) :
    SideRLs mtm (x ^ n) default (shifted_counter n) := by
  induction n with
  | zero =>
    rw [shifted_counter, BinInc_O]
    exact .nil default
  | succ n ih =>
    rw [pow_succ_list', show n + 1 = 1 + n by omega]
    exact ih.trans (shifted_step n)

theorem digits_shifted (n v : ℕ) (hv : v < 2 ^ n) :
    WallInvariant.shifted (CounterFinish.digits n v) +> default = shifted_counter v := by
  induction n generalizing v with
  | zero =>
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    simp [CounterFinish.digits, WallInvariant.shifted, shifted_counter, BinInc_O]
  | succ n ih =>
    rw [Nat.pow_succ] at hv
    rcases Nat.even_or_odd' v with ⟨q, rfl | rfl⟩
    · rw [Nat.mul_comm 2 q, CounterFinish.digits_even, WallInvariant.shifted]
      simp only [Bool.false_eq_true, ↓reduceIte, append_assoc, ih q (by omega)]
      unfold shifted_counter
      rw [BinInc_mul2]
      rfl
    · rw [show 2 * q + 1 = q * 2 + 1 by omega, CounterFinish.digits_odd, WallInvariant.shifted]
      simp only [↓reduceIte, append_assoc, ih q (by omega)]
      unfold shifted_counter
      rw [BinInc_mul2add1]

theorem shifted_counter_rotate (n v : ℕ) (hv : v < 2 ^ n) :
    shifted_counter v = [0, 0, 0, 0] +> CounterRules.RC v := by
  rw [← digits_shifted n v hv, ← CounterFinish.digits_normal n v hv, CounterBits.shifted_normal]

theorem even_ones (k n : ℕ) :
    SideRLs mtm (h ^ k) (([1, 1] : List Γ) ^ n +> default)
      (([1, 1] : List Γ) ^ n +> CounterRules.RC (k * 2 ^ n)) :=
  (LocalPasses.lds_Incs k n).sideRLs_concat
    ((LocalPasses.m0_Incs (k * 2 ^ n)).sideRLs_concat (ordinary_blank (k * 2 ^ n)))

end BlankPasses

/-! ## EndpointClasses -/

namespace EndpointClasses

abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev z : List Γ := [0]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]

theorem coefficient_bound (L T q : ℕ) (hT : 0 < T) (hB : 2 * (T + q) ≤ 2 ^ L) :
    q * 4 + 3 < 2 ^ (L + 1) := by
  rw [Nat.pow_succ]; omega

theorem budget_positive (L T q : ℕ) (hT : 0 < T) (hB : 2 * (T + q) ≤ 2 ^ L) :
    0 < L := by
  rcases L with _ | L
  · simp at hB; omega
  · omega

theorem adjacent_marked (n q s : ℕ) (hn : s + 1 < n) :
    WallInvariant.marked 1 (CounterFinish.digits n ((q * 4 + 3) * 2 ^ s)) := by
  by_cases hs : s % 2 = 1
  · rw [show q * 4 + 3 = (q * 2 + 1) * 2 + 1 by omega]
    exact CounterBits.marked_shift_odd n (q * 2 + 1) s (by omega) hs
  · have hs1 : (s + 1) % 2 = 1 := by omega
    rw [← hs1]
    refine CounterBits.marked_remainder n ((q * 4 + 3) * 2 ^ s) (s + 1) q (2 ^ s) hn ?_ ?_
    · have hp := pow2_pos s
      rw [Nat.pow_succ]; omega
    · rw [Nat.pow_succ]; ring

theorem numeric_bound (L T q s : ℕ) (hT : 0 < T) (hB : 2 * (T + q) ≤ 2 ^ L) :
    (q * 4 + 3) * 2 ^ s < 2 ^ (L + s + 1) := by
  have hc := coefficient_bound L T q hT hB
  have hp := pow2_pos s
  rw [show L + s + 1 = (L + 1) + s by omega, Nat.pow_add]
  nlinarith

theorem shifted_numeric (n v : ℕ) (hv : v < 2 ^ n)
    (hm : WallInvariant.marked 1 (CounterFinish.digits n v)) :
    WallInvariant.invariant
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        (ld ^ (n + 2) +> BlankPasses.shifted_counter v)) := by
  rw [← BlankPasses.digits_shifted n v hv, ← append_assoc]
  exact WallInvariant.invariant.InvE (by rw [CounterFinish.digits_length]) hm

theorem shifted_endpoint (L T q s : ℕ) (hT : 0 < T) (hB : 2 * (T + q) ≤ 2 ^ L) :
    WallInvariant.invariant
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        (ld ^ (L + s + 3) +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ s))) := by
  rw [show L + s + 3 = (L + s + 1) + 2 by omega]
  exact shifted_numeric (L + s + 1) ((q * 4 + 3) * 2 ^ s)
    (numeric_bound L T q s hT hB)
    (adjacent_marked (L + s + 1) q s (by have := budget_positive L T q hT hB; omega))

theorem ordinary_endpoint (L T q s : ℕ) (hT : 0 < T) (hs : 0 < s) (hB : 2 * (T + q) ≤ 2 ^ L) :
    WallInvariant.invariant
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        (one +> (ld ^ (L + s + 1) +> CounterRules.RC ((q * 4 + 3) * 2 ^ s)))) := by
  refine CounterBits.numeric_even_value (L + s + 1) ((q * 4 + 3) * 2 ^ s) ?_ ?_ ?_
  · exact Nat.mul_pos (by omega) (pow2_pos s)
  · exact numeric_bound L T q s hT hB
  · rcases s with _ | s'
    · omega
    · rw [Nat.pow_succ, ← Nat.mul_assoc]; omega

theorem even_word (L s : ℕ) :
    one ++ ld ^ L ++ ld ++ ld ^ (s + 1) ++ one = ld ^ (L + s + 3) := by
  change ([1] : List Γ) ^ 1 ++ ld ^ L ++ ([1] : List Γ) ^ 2 ++ ld ^ (s + 1) ++ ([1] : List Γ) ^ 1 =
    ld ^ (L + s + 3)
  rw [← ones_even_pow L, ← ones_even_pow (s + 1), ← ones_even_pow (L + s + 3)]
  simp only [← pow_add_list]
  congr 1
  omega

theorem odd_word (L s : ℕ) :
    one ++ ld ^ L ++ ld ++ ld ^ s = one ++ ld ^ (L + s + 1) := by
  rw [List.append_assoc one, List.append_assoc one]
  congr 1
  change ld ^ L ++ ld ^ 1 ++ ld ^ s = ld ^ (L + s + 1)
  simp only [← pow_add_list]
  congr 1
  omega

theorem counter_shifted (L k T q s : ℕ) (r : ListBlank Γ)
    (hk : k < 2 ^ L) (hE : k + 1 = 2 * (T + q)) (hT : 0 < T)
    (hr : SideRLs mtm (h ^ (k + 1)) r
      (ld +> (ld ^ (s + 1) +> (one +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ s))))) :
    ∃ out, ((CounterRules.rGate (CounterRules.LC L k) r) [mtm]⊢⁺ out) ∧
      WallInvariant.invariant out := by
  refine ⟨(([0] : List Γ) +> LocalPasses.lh) {{qA}}>
    (ld ^ (L + s + 3) +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ s)), ?_,
    shifted_endpoint L T q s hT (by omega)⟩
  have hfin := CounterH.right_h_finish L k r _ hk hr
  simp only [← append_assoc] at hfin
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, even_word] at hfin
  exact hfin

theorem counter_ordinary (L k T q s : ℕ) (r : ListBlank Γ)
    (hk : k < 2 ^ L) (hE : k + 1 = 2 * (T + q)) (hT : 0 < T) (hs : 0 < s)
    (hr : SideRLs mtm (h ^ (k + 1)) r
      (ld +> (ld ^ s +> CounterRules.RC ((q * 4 + 3) * 2 ^ s)))) :
    ∃ out, ((CounterRules.rGate (CounterRules.LC L k) r) [mtm]⊢⁺ out) ∧
      WallInvariant.invariant out := by
  refine ⟨(([0] : List Γ) +> LocalPasses.lh) {{qA}}>
    (one +> (ld ^ (L + s + 1) +> CounterRules.RC ((q * 4 + 3) * 2 ^ s))), ?_,
    ordinary_endpoint L T q s hT hs (by omega)⟩
  have hfin := CounterH.right_h_finish L k r _ hk hr
  simp only [← append_assoc] at hfin
  rw [← List.append_assoc, ← List.append_assoc, odd_word, append_assoc] at hfin
  exact hfin

end EndpointClasses

/-! ## OddDefectTail -/

namespace OddDefectTail

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]
abbrev y : List (DH0 Γ Λ × DH0 Γ Λ) := [((qD, []), (qB, []))]
abbrev hx : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qC, [0]))]
abbrev terminal_word : List Γ := [0, 0, 0, 0, 0, 0, 0, 1]
abbrev q2 : List Γ := [0, 0, 1]
abbrev ones5 : List Γ := [1, 1, 1, 1, 1]
abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev three : List Γ := [1, 1, 1]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]

theorem value_zero (bs : List Bool) (hv : CDPasses.value bs = 0) :
    bs = List.replicate bs.length false := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [CDPasses.value, CDPasses.bitval, List.length_cons,
      List.replicate_succ, ↓reduceIte, Bool.false_eq_true] at hv ⊢
    · congr 1
      exact ih (by omega)
    · omega

theorem value_full (bs : List Bool) (hv : CDPasses.value bs = 2 ^ bs.length - 1) :
    bs = List.replicate bs.length true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hp := pow2_pos bs.length
    have hvb := CDPasses.value_bound bs
    cases b <;> simp only [CDPasses.value, CDPasses.bitval, List.length_cons, Nat.pow_succ,
      List.replicate_succ, ↓reduceIte, Bool.false_eq_true] at hv ⊢
    · omega
    · congr 1
      exact ih (by omega)

theorem value_positive_any (bs : List Bool) (hv : 0 < CDPasses.value bs) :
    CDPasses.any bs = true := by
  induction bs with
  | nil => simp [CDPasses.value] at hv
  | cons b bs ih =>
    cases b
    · simp only [CDPasses.value, CDPasses.bitval, CDPasses.any, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add, Bool.false_or] at hv ⊢
      exact ih (by omega)
    · rfl

theorem third_zeros (n : ℕ) : CDPasses.third (List.replicate n false) = a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, CDPasses.third, ih, pow_succ_list]
    rfl

theorem fourth_ones (n : ℕ) : CDPasses.fourth (List.replicate n true) = c ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, CDPasses.fourth, ih, pow_succ_list]
    rfl

theorem tail_five :
    SideRLs mtm (CDPasses.mass true 5) (terminal_word +> default)
      (c ^ 2 +> (q2 +> default)) := by
  have hs := BoundedConfig.sideRLs_c_spec mtm (hs := CDPasses.mass true 5)
    (r := terminal_word) (r' := c ^ 2 ++ q2) (T := 1000) (by decide)
  rwa [append_assoc (c ^ 2) q2] at hs

theorem prime_positive (bs : List Bool) (hvpos : 0 < CDPasses.value bs) :
    SideRLs mtm (x ^ (6 * 2 ^ bs.length - CDPasses.value bs - 1))
      (CDPasses.third bs +> (terminal_word +> default))
      (c ^ (bs.length + 2) +> (q2 +> default)) := by
  have hvbound := CDPasses.value_bound bs
  have hp := pow2_pos bs.length
  have hn : 2 ^ bs.length ≤ 6 * 2 ^ bs.length - CDPasses.value bs - 1 := by omega
  obtain ⟨low, carry, hlen, hval, hcarry, hseg⟩ :=
    CDPasses.mass_digits bs false (6 * 2 ^ bs.length - CDPasses.value bs - 1) hn
  have hlowbound := CDPasses.value_bound low
  rw [hlen] at hlowbound
  have hval' : 2 ^ bs.length * carry + CDPasses.value low + 1 = 6 * 2 ^ bs.length := by omega
  have hfive : carry = 5 := by nlinarith
  subst hfive
  have hfull : CDPasses.value low = 2 ^ low.length - 1 := by rw [hlen]; omega
  have hlow_eq := value_full low hfull
  rw [hlow_eq, hlen, fourth_ones] at hseg
  rw [show CDPasses.mass false (6 * 2 ^ bs.length - CDPasses.value bs - 1) =
    x ^ (6 * 2 ^ bs.length - CDPasses.value bs - 1) from rfl,
    Bool.false_or, value_positive_any bs hvpos] at hseg
  rw [pow_add_list, append_assoc]
  exact hseg.sideRLs_concat tail_five

theorem prime_zero (bs : List Bool) (hv : CDPasses.value bs = 0) :
    SideRLs mtm (x ^ (2 ^ (bs.length + 1) - 1))
      (CDPasses.third bs +> (terminal_word +> default))
      (c ^ (bs.length + 1) +> (q2 +> default)) := by
  have heq := value_zero bs hv
  have ht : CDPasses.third bs = a ^ bs.length := by
    conv_lhs => rw [heq]
    rw [third_zeros]
  rw [ht]
  have h_in : a ^ bs.length +> (terminal_word +> (default : ListBlank Γ)) =
      a ^ (bs.length + 1) +> (q2 +> default) := by
    rw [pow_succ_list', append_assoc]
    rfl
  rw [h_in]
  have hc := BoundaryRules.c_fill_zeros 0 (bs.length + 1)
  simp only [Nat.zero_add, Nat.one_mul, pow_zero_list] at hc
  exact hc.sideRLs_concat (.nil (q2 +> default))

theorem final_x :
    SideRLs mtm hx (q2 +> default) (three +> default) :=
  BoundedConfig.sideRLs_c_spec mtm (hs := hx) (r := q2) (r' := three) (T := 1000) (by decide)

theorem convert_tail (g : ℕ) :
    SideRLs mtm hx (c ^ g +> (q2 +> default)) (ones5 ^ g +> (three +> default)) :=
  (BoundaryRules.conversion_digits g).sideRLs_concat final_x

theorem positive_exit (bs : List Bool) (hpos : 0 < CDPasses.value bs) :
    SideRLs mtm (x ^ (6 * 2 ^ bs.length - CDPasses.value bs - 1) ++ hx)
      (CDPasses.third bs +> (terminal_word +> default))
      (ones5 ^ (bs.length + 2) +> (three +> default)) :=
  (prime_positive bs hpos).trans (convert_tail (bs.length + 2))

theorem zero_exit (bs : List Bool) (hz : CDPasses.value bs = 0) :
    SideRLs mtm (x ^ (2 ^ (bs.length + 1) - 1) ++ hx)
      (CDPasses.third bs +> (terminal_word +> default))
      (ones5 ^ (bs.length + 1) +> (three +> default)) :=
  (prime_zero bs hz).trans (convert_tail (bs.length + 1))

def demand (bs : List Bool) : ℕ :=
  if CDPasses.value bs == 0 then 2 ^ (bs.length + 1)
  else 6 * 2 ^ bs.length - CDPasses.value bs

def converted_digits (bs : List Bool) : ℕ :=
  if CDPasses.value bs == 0 then bs.length + 1 else bs.length + 2

theorem prime (bs : List Bool) :
    SideRLs mtm (x ^ (demand bs - 1))
      (CDPasses.third bs +> (terminal_word +> default))
      (c ^ converted_digits bs +> (q2 +> default)) := by
  unfold demand converted_digits
  by_cases hz : CDPasses.value bs = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte]
    exact prime_zero bs hz
  · have hne : (CDPasses.value bs == 0) = false := beq_eq_false_iff_ne.mpr hz
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact prime_positive bs (by omega)

theorem odd_terminal_reduction (bs : List Bool) (q : ℕ) (r' : ListBlank Γ)
    (H : SideRLs mtm (h ^ (1 + q * 2))
      (ones5 ^ converted_digits bs +> (three +> default)) r') :
    SideRLs mtm (h ^ ((demand bs - 1) * 2 + (1 + q)))
      (one +> (CDPasses.third bs +> (terminal_word +> default))) (ld +> r') := by
  rw [pow_add_list]
  exact ((OddNormal.one_pairs (demand bs - 1)).sideRLs_concat (prime bs)).trans
    ((OddNormal.one_expand q).sideRLs_concat ((convert_tail (converted_digits bs)).trans H))

end OddDefectTail

/-! ## OddDefectFinish -/

namespace OddDefectFinish

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev b : List Γ := [1, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev z3 : List Γ := [0, 0, 0]
abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev three : List Γ := [1, 1, 1]
abbrev ones5 : List Γ := [1, 1, 1, 1, 1]
abbrev terminal_word : List Γ := [0, 0, 0, 0, 0, 0, 0, 1]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]

theorem demand_positive (bs : List Bool) : 0 < OddDefectTail.demand bs := by
  unfold OddDefectTail.demand
  have hv := CDPasses.value_bound bs
  have hp := pow2_pos bs.length
  by_cases hz : CDPasses.value bs == 0 <;> simp only [hz, ↓reduceIte, Bool.false_eq_true]
  · exact pow2_pos (bs.length + 1)
  · omega

theorem ones_even (w : ℕ) :
    ones5 ^ (w * 2) ++ three = ld ^ (w * 5 + 1) ++ one := by
  change (([1] : List Γ) ^ 5) ^ (w * 2) ++ ([1] : List Γ) ^ 3 =
    (([1] : List Γ) ^ 2) ^ (w * 5 + 1) ++ ([1] : List Γ) ^ 1
  simp only [← pow_mul_list, ← pow_add_list]
  congr 1
  omega

theorem ones_odd (w : ℕ) :
    ones5 ^ (w * 2 + 1) ++ three = ld ^ (w * 5 + 4) := by
  change (([1] : List Γ) ^ 5) ^ (w * 2 + 1) ++ ([1] : List Γ) ^ 3 =
    (([1] : List Γ) ^ 2) ^ (w * 5 + 4)
  simp only [← pow_mul_list, ← pow_add_list]
  congr 1
  omega

theorem odd_ones (k n : ℕ) :
    SideRLs mtm (h ^ k) (ld ^ (n + 1) +> (one +> default))
      (ld ^ (n + 1) +> (one +> BlankPasses.shifted_counter (k * 2 ^ n))) := by
  refine (LocalPasses.lds_Incs k (n + 1)).sideRLs_concat ?_
  rw [show k * 2 ^ (n + 1) = (k * 2 ^ n) * 2 by rw [Nat.pow_succ]; ring]
  exact (OddNormal.one_pairs (k * 2 ^ n)).sideRLs_concat (BlankPasses.shifted_blank (k * 2 ^ n))

theorem finish_even (bs : List Bool) (w q : ℕ)
    (hg : OddDefectTail.converted_digits bs = w * 2) :
    SideRLs mtm (h ^ (2 * (OddDefectTail.demand bs + q)))
      (one +> (CDPasses.third bs +> (terminal_word +> default)))
      (ld +> (ld ^ (w * 5 + 1) +>
        (one +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ (w * 5))))) := by
  have hd := demand_positive bs
  rw [show 2 * (OddDefectTail.demand bs + q) =
    (OddDefectTail.demand bs - 1) * 2 + (1 + (1 + q * 2)) by omega]
  refine OddDefectTail.odd_terminal_reduction bs (1 + q * 2) _ ?_
  rw [show 1 + (1 + q * 2) * 2 = q * 4 + 3 by omega, hg, ← append_assoc, ones_even, append_assoc]
  exact odd_ones (q * 4 + 3) (w * 5)

theorem finish_odd (bs : List Bool) (w q : ℕ)
    (hg : OddDefectTail.converted_digits bs = w * 2 + 1) :
    SideRLs mtm (h ^ (2 * (OddDefectTail.demand bs + q)))
      (one +> (CDPasses.third bs +> (terminal_word +> default)))
      (ld +> (ld ^ (w * 5 + 4) +> CounterRules.RC ((q * 4 + 3) * 2 ^ (w * 5 + 4)))) := by
  have hd := demand_positive bs
  rw [show 2 * (OddDefectTail.demand bs + q) =
    (OddDefectTail.demand bs - 1) * 2 + (1 + (1 + q * 2)) by omega]
  refine OddDefectTail.odd_terminal_reduction bs (1 + q * 2) _ ?_
  rw [show 1 + (1 + q * 2) * 2 = q * 4 + 3 by omega, hg, ← append_assoc, ones_odd]
  exact BlankPasses.even_ones (q * 4 + 3) (w * 5 + 4)

theorem third_normal (bs : List Bool) :
    z3 ++ WallInvariant.normal bs = CDPasses.third bs ++ z3 :=
  OddImage.phase_three_word bs

theorem third_normal_side (bs : List Bool) :
    z3 +> (WallInvariant.normal bs +> (c +> default)) =
      CDPasses.third bs +> (terminal_word +> default) := by
  rw [← append_assoc, third_normal, append_assoc]
  rfl

theorem prefix_even (u : ℕ) : one ^ (5 * (u * 2) + 1) = ld ^ (u * 5) ++ one := by
  change ([1] : List Γ) ^ (5 * (u * 2) + 1) = (([1] : List Γ) ^ 2) ^ (u * 5) ++ ([1] : List Γ) ^ 1
  simp only [← pow_mul_list, ← pow_add_list]
  congr 1
  omega

theorem first_even_reduction (u k : ℕ) (bs : List Bool) (r' : ListBlank Γ)
    (H : SideRLs mtm (h ^ ((1 + k * 2) * 2 ^ (u * 5)))
      (one +> (CDPasses.third bs +> (terminal_word +> default))) r') :
    SideRLs mtm (h ^ ((2 ^ (u * 2) - 1) * 2 + (1 + k)))
      (one +> (a ^ (u * 2) +> (b +> (WallInvariant.normal bs +> (c +> default)))))
      (ld +> (ld ^ (u * 5) +> r')) := by
  refine OddNormal.odd_first_reduction (u * 2) k (WallInvariant.normal bs +> (c +> default))
    (ld ^ (u * 5) +> r') ?_
  rw [prefix_even, append_assoc, third_normal_side]
  exact (LocalPasses.lds_Incs (1 + k * 2) (u * 5)).sideRLs_concat H

end OddDefectFinish

/-! ## TightTail -/

namespace TightTail

abbrev tail : List Γ := [0, 0, 0, 1, 0, 0, 1, 0]
abbrev ones : List Γ := [1, 1, 1, 1, 1, 1, 1]
abbrev xp : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qC, [0]))]
abbrev yp : List (DH0 Γ Λ × DH0 Γ Λ) := [((qD, []), (qC, [0]))]

theorem terminal_C : SegRLs mtm xp [] tail ones :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem terminal_D : SegRLs mtm yp [] tail ones :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

end TightTail

/-! ## TightPrimer -/

namespace TightPrimer

abbrev a : List Γ := [0, 0, 0, 0, 0]
abbrev c : List Γ := [0, 0, 0, 0, 1]
abbrev d : List Γ := [0, 0, 0, 1, 0]
abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev ones5 : List Γ := [1, 1, 1, 1, 1]
abbrev ones7 : List Γ := [1, 1, 1, 1, 1, 1, 1]
abbrev tail : List Γ := [0, 0, 0, 1, 0, 0, 1, 0]
abbrev x : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qB, []))]
abbrev y : List (DH0 Γ Λ × DH0 Γ Λ) := [((qD, []), (qB, []))]
abbrev hx : List (DH0 Γ Λ × DH0 Γ Λ) := [((qC, []), (qC, [0]))]
abbrev hy : List (DH0 Γ Λ × DH0 Γ Λ) := [((qD, []), (qC, [0]))]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]

def special (old : Bool) : List (DH0 Γ Λ × DH0 Γ Λ) := if old then hy else hx

def departure (old : Bool) : ℕ → List (DH0 Γ Λ × DH0 Γ Λ)
  | 0 => special old
  | k + 1 => (if old then y else x) ++ x ^ k ++ hx

theorem departure_positive (old : Bool) (n : ℕ) (hn : n ≠ 0) :
    departure old n = CDPasses.mass old n ++ hx := by
  rcases n with _ | k
  · contradiction
  · cases old <;> rfl

theorem departure_false (n : ℕ) : departure false n = x ^ n ++ hx := by
  rcases n with _ | k <;> rfl

theorem conversion_digit : SegRLs mtm hx hx c ones5 :=
  BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)

theorem digit_exit (k : ℕ) (old bit : Bool) :
    SegRLs mtm (departure old ((k + 1) * 2 - CDPasses.bitval bit - 1))
      (departure (old || bit) k) (CDPasses.third_digit bit) ones5 := by
  rcases k with _ | k
  · cases old <;> cases bit <;> exact BoundedConfig.segRLs_c_spec mtm (T := 1000) (by decide)
  · rw [departure_positive old _ (by cases bit <;> simp [CDPasses.bitval] <;> omega),
      departure_positive (old || bit) (k + 1) (by omega)]
    cases bit
    · have hm := CDPasses.mass_odd (k + 1) old false (by omega)
      simp only [CDPasses.bitval, CDPasses.fourth_digit, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero] at hm ⊢
      rw [show (k + 1 + 1) * 2 - 0 - 1 = 1 + (k + 1) * 2 by omega]
      exact hm.trans conversion_digit
    · have hm := CDPasses.mass_even (k + 1) old true (by omega)
      simp only [CDPasses.bitval, CDPasses.fourth_digit, ↓reduceIte] at hm ⊢
      rw [show (k + 1 + 1) * 2 - 1 - 1 = (k + 1) * 2 by omega]
      exact hm.trans conversion_digit

theorem digits_exit (bs : List Bool) (old : Bool) :
    SegRLs mtm (departure old (2 ^ bs.length - CDPasses.value bs - 1))
      (special (old || CDPasses.any bs)) (CDPasses.third bs) (ones5 ^ bs.length) := by
  induction bs generalizing old with
  | nil =>
    simp only [CDPasses.third, CDPasses.value, CDPasses.any, List.length_nil, Nat.pow_zero,
      pow_zero_list, Bool.or_false, departure]
    exact SegRLs.empty mtm _
  | cons bit bs ih =>
    have hv := CDPasses.value_bound bs
    simp only [CDPasses.third, CDPasses.value, CDPasses.any, List.length_cons, Nat.pow_succ,
      pow_succ_list]
    have heq : 2 ^ bs.length * 2 - (CDPasses.bitval bit + 2 * CDPasses.value bs) - 1 =
        ((2 ^ bs.length - CDPasses.value bs - 1) + 1) * 2 - CDPasses.bitval bit - 1 := by
      cases bit <;> simp [CDPasses.bitval] <;> omega
    rw [heq, ← Bool.or_assoc]
    exact (digit_exit (2 ^ bs.length - CDPasses.value bs - 1) old bit).concat (ih (old || bit))

theorem terminal (old : Bool) : SegRLs mtm (special old) [] tail ones7 := by
  cases old
  · exact TightTail.terminal_C
  · exact TightTail.terminal_D

theorem exit_side (bs : List Bool) (old : Bool) :
    SideRLs mtm (departure old (2 ^ bs.length - CDPasses.value bs - 1))
      (CDPasses.third bs +> (tail +> default)) (ones5 ^ bs.length +> (ones7 +> default)) :=
  (digits_exit bs old).sideRLs_concat
    ((terminal (old || CDPasses.any bs)).sideRLs_concat (.nil (default : ListBlank Γ)))

theorem exit_C (bs : List Bool) :
    SideRLs mtm (x ^ (2 ^ bs.length - CDPasses.value bs - 1) ++ hx)
      (CDPasses.third bs +> (tail +> default)) (ones5 ^ bs.length +> (ones7 +> default)) := by
  rw [← departure_false]
  exact exit_side bs false

def demand (bs : List Bool) : ℕ := 2 ^ bs.length - CDPasses.value bs

theorem one_sequence (k q : ℕ) :
    SegRLs mtm (h ^ (k * 2 + (1 + q))) (x ^ k ++ hx ++ h ^ (1 + q * 2)) one ld := by
  rw [pow_add_list, List.append_assoc]
  exact (OddNormal.one_pairs k).trans (OddNormal.one_expand q)

theorem odd_reduction (bs : List Bool) (q : ℕ) (r' : ListBlank Γ)
    (H : SideRLs mtm (h ^ (1 + q * 2)) (ones5 ^ bs.length +> (ones7 +> default)) r') :
    SideRLs mtm (h ^ ((demand bs - 1) * 2 + (1 + q)))
      (one +> (CDPasses.third bs +> (tail +> default))) (ld +> r') :=
  (one_sequence (demand bs - 1) q).sideRLs_concat ((exit_C bs).trans H)

end TightPrimer

/-! ## TightFinish -/

namespace TightFinish

abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev ones5 : List Γ := [1, 1, 1, 1, 1]
abbrev ones7 : List Γ := [1, 1, 1, 1, 1, 1, 1]
abbrev tail : List Γ := [0, 0, 0, 1, 0, 0, 1, 0]
abbrev h : List (DH0 Γ Λ × DH0 Γ Λ) := [((qA, [0]), (qC, [0]))]

theorem demand_positive (bs : List Bool) : 0 < TightPrimer.demand bs := by
  unfold TightPrimer.demand
  have := CDPasses.value_bound bs
  omega

theorem ones_even (w : ℕ) :
    ones5 ^ (w * 2) ++ ones7 = ld ^ (w * 5 + 3) ++ one := by
  change (([1] : List Γ) ^ 5) ^ (w * 2) ++ ([1] : List Γ) ^ 7 =
    (([1] : List Γ) ^ 2) ^ (w * 5 + 3) ++ ([1] : List Γ) ^ 1
  simp only [← pow_mul_list, ← pow_add_list]
  congr 1
  omega

theorem ones_odd (w : ℕ) :
    ones5 ^ (w * 2 + 1) ++ ones7 = ld ^ (w * 5 + 6) := by
  change (([1] : List Γ) ^ 5) ^ (w * 2 + 1) ++ ([1] : List Γ) ^ 7 =
    (([1] : List Γ) ^ 2) ^ (w * 5 + 6)
  simp only [← pow_mul_list, ← pow_add_list]
  congr 1
  omega

theorem finish_even (bs : List Bool) (w q : ℕ) (hg : bs.length = w * 2) :
    SideRLs mtm (h ^ (2 * (TightPrimer.demand bs + q)))
      (one +> (CDPasses.third bs +> (tail +> default)))
      (ld +> (ld ^ (w * 5 + 3) +>
        (one +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ (w * 5 + 2))))) := by
  have hd := demand_positive bs
  rw [show 2 * (TightPrimer.demand bs + q) =
    (TightPrimer.demand bs - 1) * 2 + (1 + (1 + q * 2)) by omega]
  refine TightPrimer.odd_reduction bs (1 + q * 2) _ ?_
  rw [show 1 + (1 + q * 2) * 2 = q * 4 + 3 by omega, hg, ← append_assoc, ones_even, append_assoc,
    show w * 5 + 3 = (w * 5 + 2) + 1 by omega]
  exact OddDefectFinish.odd_ones (q * 4 + 3) (w * 5 + 2)

theorem finish_odd (bs : List Bool) (w q : ℕ) (hg : bs.length = w * 2 + 1) :
    SideRLs mtm (h ^ (2 * (TightPrimer.demand bs + q)))
      (one +> (CDPasses.third bs +> (tail +> default)))
      (ld +> (ld ^ (w * 5 + 6) +> CounterRules.RC ((q * 4 + 3) * 2 ^ (w * 5 + 6)))) := by
  have hd := demand_positive bs
  rw [show 2 * (TightPrimer.demand bs + q) =
    (TightPrimer.demand bs - 1) * 2 + (1 + (1 + q * 2)) by omega]
  refine TightPrimer.odd_reduction bs (1 + q * 2) _ ?_
  rw [show 1 + (1 + q * 2) * 2 = q * 4 + 3 by omega, hg, ← append_assoc, ones_odd]
  exact BlankPasses.even_ones (q * 4 + 3) (w * 5 + 6)

end TightFinish

/-! ## TerminalClosure -/

namespace TerminalClosure

abbrev one : List Γ := [1]
abbrev ld : List Γ := [1, 1]
abbrev z : List Γ := [0]
abbrev defect : List Γ := [0, 0, 0, 0, 0, 0, 0, 1]
abbrev tight : List Γ := [0, 0, 0, 1, 0, 0, 1, 0]

theorem split_budget (k T : ℕ) (ho : k % 2 = 1) (hb : 2 * T ≤ k + 1) :
    ∃ q, k + 1 = 2 * (T + q) :=
  ⟨(k + 1) / 2 - T, by omega⟩

theorem defect_counter (L k : ℕ) (bs : List Bool)
    (hk : k < 2 ^ L) (ho : k % 2 = 1) (hb : 2 * OddDefectTail.demand bs ≤ k + 1) :
    ∃ out,
      ((CounterRules.rGate (CounterRules.LC L k)
        (one +> (CDPasses.third bs +> (defect +> default)))) [mtm]⊢⁺ out) ∧
      WallInvariant.invariant out := by
  obtain ⟨q, hE⟩ := split_budget k (OddDefectTail.demand bs) ho hb
  rcases Nat.even_or_odd' (OddDefectTail.converted_digits bs) with ⟨w, hg | hg⟩
  · refine EndpointClasses.counter_shifted L k (OddDefectTail.demand bs) q (w * 5) _
      hk hE (OddDefectFinish.demand_positive bs) ?_
    rw [hE]
    exact OddDefectFinish.finish_even bs w q (by omega)
  · refine EndpointClasses.counter_ordinary L k (OddDefectTail.demand bs) q (w * 5 + 4) _
      hk hE (OddDefectFinish.demand_positive bs) (by omega) ?_
    rw [hE]
    exact OddDefectFinish.finish_odd bs w q (by omega)

theorem tight_counter (L k : ℕ) (bs : List Bool)
    (hk : k < 2 ^ L) (ho : k % 2 = 1) (hb : 2 * TightPrimer.demand bs ≤ k + 1) :
    ∃ out,
      ((CounterRules.rGate (CounterRules.LC L k)
        (one +> (CDPasses.third bs +> (tight +> default)))) [mtm]⊢⁺ out) ∧
      WallInvariant.invariant out := by
  obtain ⟨q, hE⟩ := split_budget k (TightPrimer.demand bs) ho hb
  rcases Nat.even_or_odd' bs.length with ⟨w, hg | hg⟩
  · refine EndpointClasses.counter_shifted L k (TightPrimer.demand bs) q (w * 5 + 2) _
      hk hE (TightFinish.demand_positive bs) ?_
    rw [show w * 5 + 2 + 1 = w * 5 + 3 by omega, hE]
    exact TightFinish.finish_even bs w q (by omega)
  · refine EndpointClasses.counter_ordinary L k (TightPrimer.demand bs) q (w * 5 + 6) _
      hk hE (TightFinish.demand_positive bs) (by omega) ?_
    rw [hE]
    exact TightFinish.finish_odd bs w q (by omega)

def even_wall (L s q : ℕ) : Cfg Γ Λ :=
  (([0] : List Γ) +> LocalPasses.lh) {{qA}}>
    (ld ^ (L + s + 3) +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ s))

def odd_wall (L s q : ℕ) : Cfg Γ Λ :=
  (([0] : List Γ) +> LocalPasses.lh) {{qA}}>
    (one +> (ld ^ (L + s + 1) +> CounterRules.RC ((q * 4 + 3) * 2 ^ s)))

theorem counter_shifted_exact (L k q s : ℕ) (r : ListBlank Γ)
    (hk : k < 2 ^ L)
    (hr : SideRLs mtm ([((qA, [0]), (qC, [0]))] ^ (k + 1)) r
      (ld +> (ld ^ (s + 1) +> (one +> BlankPasses.shifted_counter ((q * 4 + 3) * 2 ^ s))))) :
    (CounterRules.rGate (CounterRules.LC L k) r) [mtm]⊢⁺ even_wall L s q := by
  unfold even_wall
  have hfin := CounterH.right_h_finish L k r _ hk hr
  simp only [← append_assoc] at hfin
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
    EndpointClasses.even_word] at hfin
  exact hfin

theorem counter_ordinary_exact (L k q s : ℕ) (r : ListBlank Γ)
    (hk : k < 2 ^ L)
    (hr : SideRLs mtm ([((qA, [0]), (qC, [0]))] ^ (k + 1)) r
      (ld +> (ld ^ s +> CounterRules.RC ((q * 4 + 3) * 2 ^ s)))) :
    (CounterRules.rGate (CounterRules.LC L k) r) [mtm]⊢⁺ odd_wall L s q := by
  unfold odd_wall
  have hfin := CounterH.right_h_finish L k r _ hk hr
  simp only [← append_assoc] at hfin
  rw [← List.append_assoc, ← List.append_assoc, EndpointClasses.odd_word, append_assoc] at hfin
  exact hfin

theorem defect_counter_cases (L k : ℕ) (bs : List Bool)
    (hk : k < 2 ^ L) (ho : k % 2 = 1) (hb : 2 * OddDefectTail.demand bs ≤ k + 1) :
    ∃ q,
      k + 1 = 2 * (OddDefectTail.demand bs + q) ∧ q * 4 + 3 < 2 ^ (L + 1) ∧
      ((∃ w, OddDefectTail.converted_digits bs = w * 2 ∧
        ((CounterRules.rGate (CounterRules.LC L k)
          (one +> (CDPasses.third bs +> (defect +> default)))) [mtm]⊢⁺ even_wall L (w * 5) q) ∧
        WallInvariant.invariant (even_wall L (w * 5) q)) ∨
       (∃ w, OddDefectTail.converted_digits bs = w * 2 + 1 ∧
        ((CounterRules.rGate (CounterRules.LC L k)
          (one +> (CDPasses.third bs +> (defect +> default)))) [mtm]⊢⁺
            odd_wall L (w * 5 + 4) q))) := by
  obtain ⟨q, hE⟩ := split_budget k (OddDefectTail.demand bs) ho hb
  have hT := OddDefectFinish.demand_positive bs
  have hB : 2 * (OddDefectTail.demand bs + q) ≤ 2 ^ L := by omega
  refine ⟨q, hE, EndpointClasses.coefficient_bound L (OddDefectTail.demand bs) q hT hB, ?_⟩
  rcases Nat.even_or_odd' (OddDefectTail.converted_digits bs) with ⟨w, hg | hg⟩
  · refine Or.inl ⟨w, by omega, ?_, ?_⟩
    · refine counter_shifted_exact L k q (w * 5) _ hk ?_
      rw [hE]
      exact OddDefectFinish.finish_even bs w q (by omega)
    · unfold even_wall
      exact EndpointClasses.shifted_endpoint L (OddDefectTail.demand bs) q (w * 5) hT hB
  · refine Or.inr ⟨w, by omega, ?_⟩
    refine counter_ordinary_exact L k q (w * 5 + 4) _ hk ?_
    rw [hE]
    exact OddDefectFinish.finish_odd bs w q (by omega)

theorem tight_counter_cases (L k : ℕ) (bs : List Bool)
    (hk : k < 2 ^ L) (ho : k % 2 = 1) (hb : 2 * TightPrimer.demand bs ≤ k + 1) :
    ∃ q,
      k + 1 = 2 * (TightPrimer.demand bs + q) ∧ q * 4 + 3 < 2 ^ (L + 1) ∧
      ((∃ w, bs.length = w * 2 ∧
        ((CounterRules.rGate (CounterRules.LC L k)
          (one +> (CDPasses.third bs +> (tight +> default)))) [mtm]⊢⁺
            even_wall L (w * 5 + 2) q) ∧
        WallInvariant.invariant (even_wall L (w * 5 + 2) q)) ∨
       (∃ w, bs.length = w * 2 + 1 ∧
        ((CounterRules.rGate (CounterRules.LC L k)
          (one +> (CDPasses.third bs +> (tight +> default)))) [mtm]⊢⁺
            odd_wall L (w * 5 + 6) q))) := by
  obtain ⟨q, hE⟩ := split_budget k (TightPrimer.demand bs) ho hb
  have hT := TightFinish.demand_positive bs
  have hB : 2 * (TightPrimer.demand bs + q) ≤ 2 ^ L := by omega
  refine ⟨q, hE, EndpointClasses.coefficient_bound L (TightPrimer.demand bs) q hT hB, ?_⟩
  rcases Nat.even_or_odd' bs.length with ⟨w, hg | hg⟩
  · refine Or.inl ⟨w, by omega, ?_, ?_⟩
    · refine counter_shifted_exact L k q (w * 5 + 2) _ hk ?_
      rw [show w * 5 + 2 + 1 = w * 5 + 3 by omega, hE]
      exact TightFinish.finish_even bs w q (by omega)
    · unfold even_wall
      exact EndpointClasses.shifted_endpoint L (TightPrimer.demand bs) q (w * 5 + 2) hT hB
  · refine Or.inr ⟨w, by omega, ?_⟩
    refine counter_ordinary_exact L k q (w * 5 + 6) _ hk ?_
    rw [hE]
    exact TightFinish.finish_odd bs w q (by omega)

end TerminalClosure

/-! ## OddAdjacent -/

namespace OddAdjacent

open CounterRules

def odd_rank (n v : ℕ) : ℕ :=
  OddFuel.grown (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3) - 1) 1

def odd_mass (n v : ℕ) : ℕ :=
  (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 4) - 3

theorem odd_rank_bound (n v : ℕ) (hn : v * 2 + 2 ≤ n) :
    odd_rank n v + 1 < 2 ^ (n + v * 5 + 6) := by
  have hfirst := OddFuel.grown_bound n (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
    (OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)).2
  unfold odd_rank
  rw [show n + v * 5 + 6 = (n + 1 + (v * 5 + 3)) + 1 + 1 by omega]
  exact OddFuel.grown_bound _ _ 1 (by omega)

theorem odd_mass_rank (n v : ℕ) : odd_rank n v + 1 = odd_mass n v * 2 := by
  unfold odd_rank odd_mass OddFuel.grown
  have hz : 2 ^ 3 ≤ 2 ^ (v * 5 + 3) := Nat.pow_le_pow_right (by decide) (by omega)
  change 8 ≤ 2 ^ (v * 5 + 3) at hz
  rw [show v * 5 + 4 = (v * 5 + 3) + 1 by omega, Nat.pow_succ 2 (v * 5 + 3),
    ← Nat.mul_assoc]
  have h8 : 8 ≤ (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 3) := by
    have hm := Nat.mul_le_mul (show 1 ≤ 2 * OddImage.first_fuel n (v * 2 + 1) + 1 by omega) hz
    omega
  generalize (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 3) = X at h8 ⊢
  omega

theorem odd_entry (n v : ℕ) (bs : List Bool) (hn : v * 2 + 2 ≤ n) :
    (WallInvariant.O n (List.replicate (v * 2 + 1) false ++ true :: true :: bs)) [mtm]⊢⁺
      (rGate (LC (n + v * 5 + 6) (odd_rank n v))
        ([1, 0, 0, 0] +> (WallInvariant.normal bs +> default))) := by
  set L0 := n + 1 + (v * 5 + 3)
  set k0 := OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
  have hk0 : k0 + 1 < 2 ^ L0 :=
    OddFuel.grown_bound n (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)
      (OddImage.first_fuel_bounds n (v * 2 + 1) (by omega)).2
  have hpos : 1 ≤ k0 := by
    unfold k0 OddFuel.grown
    have hz : 2 ^ 3 ≤ 2 ^ (v * 5 + 3) := Nat.pow_le_pow_right (by decide) (by omega)
    change 8 ≤ 2 ^ (v * 5 + 3) at hz
    have h8 : 8 ≤ (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 3) := by
      nlinarith [hz]
    omega
  have hbefore : (k0 - 1) + (2 ^ (0 * 2 + 1) - 1) < 2 ^ L0 := by simp; omega
  have hsecond := OddRecursion.zero_even_step L0 (k0 - 1) 0 bs default hbefore
  simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_one,
    List.replicate_zero, List.nil_append] at hsecond
  rw [show k0 - 1 + 1 = k0 by omega] at hsecond
  have hfirst := OddRecursion.initial_odd_entry n v (true :: bs) hn
  unfold odd_rank
  rw [show n + v * 5 + 6 = L0 + 1 + 1 by omega]
  exact stepPlus_trans hfirst hsecond

theorem odd_mass_bounds (n v width q : ℕ)
    (hn : v * 2 + 3 ≤ n) (hw : width ≤ n) (hq : q < 2 ^ width) :
    2 ^ width ≤ odd_mass n v ∧ odd_mass n v + q < 2 ^ (n + v * 5 + 6) := by
  have hfirst := EdOddOrbit.first_fuel_half n (v * 2 + 1) (by omega)
  have hwidth : 2 ^ width ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hw
  have hz : 2 ^ 4 ≤ 2 ^ (v * 5 + 4) := Nat.pow_le_pow_right (by decide) (by omega)
  change 16 ≤ 2 ^ (v * 5 + 4) at hz
  have hpos := pow2_pos n
  have h16 : 16 * 2 ^ n ≤ (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 4) := by
    nlinarith
  refine ⟨by unfold odd_mass; omega, ?_⟩
  have hb := odd_rank_bound n v (by omega)
  rw [odd_mass_rank] at hb
  unfold odd_mass at hb ⊢
  omega

theorem odd_image (n v : ℕ) (bs : List Bool) (budget : ℕ)
    (hn : v * 2 + 2 ≤ n)
    (hmin : 2 ^ bs.length ≤ odd_mass n v)
    (hmax : odd_mass n v + CDPasses.value bs < 2 ^ (bs.length + budget)) :
    ∃ out,
      out.length < bs.length + budget ∧
      CDPasses.value out + 2 ^ out.length = odd_mass n v + CDPasses.value bs ∧
      ((WallInvariant.O n (List.replicate (v * 2 + 1) false ++ true :: true :: bs)) [mtm]⊢⁺
        (WallInvariant.wall (([1, 1] : List Γ) ^ (n + v * 5 + 7) ++ CDPasses.fourth out ++
          CDPasses.terminal (CDPasses.any bs)))) := by
  have hb := odd_rank_bound n v hn
  obtain ⟨out, hlen, hval, hrun⟩ := OddImage.fuel_C_image (n + v * 5 + 6) (odd_rank n v)
    (odd_mass n v) bs budget (by omega) (odd_mass_rank n v) hmin hmax
  refine ⟨out, hlen, hval, ?_⟩
  rw [show n + v * 5 + 7 = (n + v * 5 + 6) + 1 by omega]
  exact stepPlus_trans (odd_entry n v bs hn) hrun

end OddAdjacent

/-! ## TerminalSuccessor -/

namespace TerminalSuccessor

open CounterRules CounterFinish

theorem coefficient_parts (L q : ℕ) (h : q * 4 + 3 < 2 ^ (L + 1)) :
    0 < L ∧ q < 2 ^ L ∧ q * 2 + 1 < 2 ^ L := by
  rcases L with _ | L
  · simp at h
  · rw [Nat.pow_succ] at h
    exact ⟨by omega, by omega, by omega⟩

theorem first_coefficient (n u : ℕ) (hn : u + 2 ≤ n) :
    2 ^ n + 3 ≤ 2 * OddImage.first_fuel n u + 1 := by
  obtain ⟨he, _⟩ := OddImage.first_fuel_bounds n u (by omega)
  have hcap : 2 ^ (u + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rw [Nat.pow_add 2 u 2] at hcap
  change 2 ^ u * 4 ≤ 2 ^ n at hcap
  have hpu := pow2_pos u
  omega

theorem first_mass_lower (n v : ℕ) (hv : 0 < v) (hn : v * 2 + 2 ≤ n) :
    2 ^ (n + v * 5 - 1) ≤ OddImage.first_mass n v := by
  have hc := first_coefficient n (v * 2) hn
  unfold OddImage.first_mass
  rw [show n + v * 5 - 1 = n + (v * 5 - 1) by omega, Nat.pow_add 2 n (v * 5 - 1)]
  exact Nat.mul_le_mul_right _ (by omega)

theorem odd_mass_lower (n v : ℕ) (hn : v * 2 + 3 ≤ n) :
    2 ^ (n + v * 5 + 4) ≤ OddAdjacent.odd_mass n v := by
  have hc := first_coefficient n (v * 2 + 1) (by omega)
  unfold OddAdjacent.odd_mass
  rw [show n + v * 5 + 4 = n + (v * 5 + 4) by omega, Nat.pow_add 2 n (v * 5 + 4)]
  have hp := pow2_pos (v * 5 + 4)
  have hprod : 2 ^ n * 2 ^ (v * 5 + 4) + 3 * 2 ^ (v * 5 + 4) ≤
      (2 * OddImage.first_fuel n (v * 2 + 1) + 1) * 2 ^ (v * 5 + 4) := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ hc
  have h3 : 3 ≤ 3 * 2 ^ (v * 5 + 4) := by omega
  omega

theorem mass_length (out : List Bool) (base mass : ℕ)
    (he : CDPasses.value out + 2 ^ out.length = mass)
    (hlo : 2 ^ base ≤ mass) (hhi : mass < 2 ^ (base + 2)) :
    out.length = base ∨ out.length = base + 1 := by
  have hv := CDPasses.value_bound out
  have hlower : base ≤ out.length := by
    by_contra hlt
    have hp : 2 ^ (out.length + 1) ≤ 2 ^ base := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    omega
  have hupper : out.length < base + 2 := by
    by_contra hge
    have hp : 2 ^ (base + 2) ≤ 2 ^ out.length := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega

theorem ordinary_source (L s q : ℕ) (h : q * 4 + 3 < 2 ^ (L + 1)) :
    TerminalClosure.odd_wall L s q =
      WallInvariant.O (L + s + 1) (List.replicate s false ++ true :: digits L (q * 2 + 1)) := by
  obtain ⟨_, _, htail⟩ := coefficient_parts L q h
  unfold TerminalClosure.odd_wall TerminalClosure.one TerminalClosure.ld
    WallInvariant.O WallInvariant.wall LocalPasses.lh
  simp only [append_assoc]
  rw [EdEvenOrbit.normal_shift_odd L (q * 2 + 1) s htail,
    show (q * 2 + 1) * 2 + 1 = q * 4 + 3 by omega,
    one_comm_11_side]

theorem ordinary_source_adjacent (L s q : ℕ) (h : q * 4 + 3 < 2 ^ (L + 1)) :
    TerminalClosure.odd_wall L s q =
      WallInvariant.O (L + s + 1) (List.replicate s false ++ true :: true :: digits L q) := by
  obtain ⟨_, _, htail⟩ := coefficient_parts L q h
  have htail' : q * 2 + 1 < 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
  have henc := EdEvenOrbit.normal_shift_odd (L + 1) (q * 2 + 1) s htail'
  rw [digits_odd, show (q * 2 + 1) * 2 + 1 = q * 4 + 3 by omega] at henc
  unfold TerminalClosure.odd_wall TerminalClosure.one TerminalClosure.ld
    WallInvariant.O WallInvariant.wall LocalPasses.lh
  simp only [append_assoc]
  rw [henc, one_comm_11_side]

theorem ordinary_even_image (L v q : ℕ) (hv : 0 < v) (hcoef : q * 4 + 3 < 2 ^ (L + 1)) :
    ∃ out,
      (out.length + 3 = L + v * 7 + 3 ∨ out.length + 2 = L + v * 7 + 3) ∧
      2 ^ (L + v * 7) ≤ OddImage.first_mass (L + v * 2 + 1) v + (q * 2 + 1) ∧
      OddImage.first_mass (L + v * 2 + 1) v + (q * 2 + 1) < 2 ^ (L + v * 7 + 2) ∧
      CDPasses.value out + 2 ^ out.length = OddImage.first_mass (L + v * 2 + 1) v + (q * 2 + 1) ∧
      ((TerminalClosure.odd_wall L (v * 2) q) [mtm]⊢⁺ (WallInvariant.Ed (L + v * 7 + 3) out)) := by
  obtain ⟨_, _, htail⟩ := coefficient_parts L q hcoef
  set n := L + v * 2 + 1
  obtain ⟨hmin, hmax⟩ := EdEvenOrbit.first_mass_bounds n v L (q * 2 + 1) hv
    (by omega) (by omega) htail
  have hlen : L + (n + v * 5 + 1 - L) = n + v * 5 + 1 := by omega
  have hval : CDPasses.value (digits L (q * 2 + 1)) = q * 2 + 1 := by
    rw [← CounterBits.value_eq_cd]
    exact CounterBits.digits_value L (q * 2 + 1) htail
  obtain ⟨out, _, hmass, hrun⟩ := OddImage.initial_even_image n v (digits L (q * 2 + 1))
    (n + v * 5 + 1 - L) hv (by omega)
    (by rw [digits_length]; exact hmin)
    (by rw [digits_length, hval, hlen]; exact hmax)
  rw [hval] at hmass
  have hany : CDPasses.any (digits L (q * 2 + 1)) = true := by
    apply EdEvenOrbit.any_true
    apply CounterBits.value_nonzero
    rw [CounterBits.digits_value L (q * 2 + 1) htail]
    omega
  rw [hany, EdEvenOrbit.fourth_eq_shifted] at hrun
  have hlow : 2 ^ (L + v * 7) ≤ OddImage.first_mass n v + (q * 2 + 1) := by
    have hfl := first_mass_lower n v hv (by omega)
    rw [show n + v * 5 - 1 = L + v * 7 by omega] at hfl
    omega
  have hmax' : OddImage.first_mass n v + (q * 2 + 1) < 2 ^ (L + v * 7 + 2) := by
    rwa [show L + v * 7 + 2 = n + v * 5 + 1 by omega]
  have hd := mass_length out (L + v * 7) _ hmass hlow hmax'
  refine ⟨out, by omega, hlow, hmax', hmass, ?_⟩
  rw [ordinary_source L (v * 2) q hcoef, show L + v * 7 + 3 = n + v * 5 + 2 by omega]
  exact hrun

theorem ordinary_odd_image (L v q : ℕ) (hqpos : 0 < q) (hcoef : q * 4 + 3 < 2 ^ (L + 1)) :
    ∃ out,
      (out.length + 3 = L + v * 7 + 9 ∨ out.length + 2 = L + v * 7 + 9) ∧
      2 ^ (L + v * 7 + 6) ≤ OddAdjacent.odd_mass (L + v * 2 + 2) v + q ∧
      OddAdjacent.odd_mass (L + v * 2 + 2) v + q < 2 ^ (L + v * 7 + 8) ∧
      CDPasses.value out + 2 ^ out.length = OddAdjacent.odd_mass (L + v * 2 + 2) v + q ∧
      ((TerminalClosure.odd_wall L (v * 2 + 1) q) [mtm]⊢⁺
        (WallInvariant.Ed (L + v * 7 + 9) out)) := by
  obtain ⟨_, hq, _⟩ := coefficient_parts L q hcoef
  set n := L + v * 2 + 2
  obtain ⟨hmin, hmax⟩ := OddAdjacent.odd_mass_bounds n v L q (by omega) (by omega) hq
  have hlen : L + (n + v * 5 + 6 - L) = n + v * 5 + 6 := by omega
  have hval : CDPasses.value (digits L q) = q := by
    rw [← CounterBits.value_eq_cd]
    exact CounterBits.digits_value L q hq
  obtain ⟨out, _, hmass, hrun⟩ := OddAdjacent.odd_image n v (digits L q)
    (n + v * 5 + 6 - L) (by omega)
    (by rw [digits_length]; exact hmin)
    (by rw [digits_length, hval, hlen]; exact hmax)
  rw [hval] at hmass
  have hany : CDPasses.any (digits L q) = true := by
    apply EdEvenOrbit.any_true
    apply CounterBits.value_nonzero
    rw [CounterBits.digits_value L q hq]
    omega
  rw [hany, EdEvenOrbit.fourth_eq_shifted] at hrun
  have hlow : 2 ^ (L + v * 7 + 6) ≤ OddAdjacent.odd_mass n v + q := by
    have hom := odd_mass_lower n v (by omega)
    rw [show n + v * 5 + 4 = L + v * 7 + 6 by omega] at hom
    omega
  have hmax' : OddAdjacent.odd_mass n v + q < 2 ^ (L + v * 7 + 8) := by
    rwa [show L + v * 7 + 8 = n + v * 5 + 6 by omega]
  have hd := mass_length out (L + v * 7 + 6) _ hmass hlow
    (by rwa [show L + v * 7 + 6 + 2 = L + v * 7 + 8 by omega])
  refine ⟨out, by omega, hlow, hmax', hmass, ?_⟩
  rw [ordinary_source_adjacent L (v * 2 + 1) q hcoef,
    show L + (v * 2 + 1) + 1 = n by omega,
    show L + v * 7 + 9 = n + v * 5 + 7 by omega]
  exact hrun

end TerminalSuccessor

/-! ## TerminalLoose -/

namespace TerminalLoose

theorem initial_gap_three (u z : ℕ) (hz : 0 < z) :
    MarkedDeficit.initial_deficit u z + 3 < 2 ^ (u + 2 + z) := by
  unfold MarkedDeficit.initial_deficit
  rw [Nat.pow_add 2 (u + 2) z]
  have hz2 : 2 ^ 1 ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) hz
  change 2 ≤ 2 ^ z at hz2
  have hu : 4 ≤ 2 ^ (u + 2) := by
    rw [Nat.pow_add 2 u 2]; have := pow2_pos u; change 4 ≤ 2 ^ u * 4; omega
  have hsub : (2 ^ (u + 2) - 3) * 2 ^ z + 3 * 2 ^ z = 2 ^ (u + 2) * 2 ^ z := by
    rw [Nat.sub_mul, Nat.sub_add_cancel (by nlinarith)]
  nlinarith

theorem even_balance (L v : ℕ) (hv : 0 < v) :
    OddImage.first_mass (L + v * 2 + 1) v + MarkedDeficit.initial_deficit (v * 2) (v * 5 - 1) =
      2 ^ (L + v * 7 + 1) := by
  have hb := MarkedDeficit.initial_balance (L + v * 2 + 1) (v * 2) (v * 5 - 1) (by omega)
  unfold OddFuel.grown at hb
  unfold OddImage.first_mass
  have hp := pow2_pos (v * 5 - 1)
  have hpos : 1 ≤ (2 * OddImage.first_fuel (L + v * 2 + 1) (v * 2) + 1) * 2 ^ (v * 5 - 1) :=
    Nat.mul_pos (by omega) hp
  rw [show L + v * 2 + 1 + 1 + (v * 5 - 1) = L + v * 7 + 1 by omega] at hb
  omega

theorem odd_balance (L v : ℕ) :
    OddAdjacent.odd_mass (L + v * 2 + 2) v +
      MarkedDeficit.initial_deficit (v * 2 + 1) (v * 5 + 4) + 3 = 2 ^ (L + v * 7 + 7) := by
  have hb := MarkedDeficit.initial_balance (L + v * 2 + 2) (v * 2 + 1) (v * 5 + 4) (by omega)
  unfold OddFuel.grown at hb
  unfold OddAdjacent.odd_mass
  have hz : 2 ^ 4 ≤ 2 ^ (v * 5 + 4) := Nat.pow_le_pow_right (by decide) (by omega)
  change 16 ≤ 2 ^ (v * 5 + 4) at hz
  have h16 : 16 ≤ (2 * OddImage.first_fuel (L + v * 2 + 2) (v * 2 + 1) + 1) * 2 ^ (v * 5 + 4) := by
    nlinarith
  rw [show L + v * 2 + 2 + 1 + (v * 5 + 4) = L + v * 7 + 7 by omega] at hb
  omega

theorem near_power_marker (out : List Bool) (top gap : ℕ)
    (htop : 3 ≤ top) (hlen : out.length + 1 = top) (hgap : gap < 2 ^ (top - 3))
    (hval : 2 ^ top ≤ CDPasses.value out + 2 ^ out.length + gap) :
    WallInvariant.marked 1 out := by
  apply MagnitudeMarker.magnitude_marker out out.length
  · rw [CounterBits.value_eq_cd]
    exact CDPasses.value_bound out
  · rw [CounterBits.value_eq_cd]
    set b := top - 3
    have ht : top = b + 3 := by omega
    have hl : out.length = b + 2 := by omega
    rw [ht, hl, Nat.pow_add 2 b 3, Nat.pow_add 2 b 2] at hval
    rw [hl, show b + 2 + 1 = b + 3 by omega, Nat.pow_add 2 b 3]
    change 2 ^ b * 8 ≤ CDPasses.value out + 2 ^ b * 4 + gap at hval
    change 2 ^ b * 8 < 3 * CDPasses.value out
    omega

theorem even_loose_marker (L v q : ℕ) (out : List Bool)
    (hL : 3 ≤ L) (hv : 0 < v) (hlen : out.length + 3 = L + v * 7 + 3)
    (hmass : CDPasses.value out + 2 ^ out.length =
      OddImage.first_mass (L + v * 2 + 1) v + (q * 2 + 1)) :
    WallInvariant.marked 1 out := by
  have hbal := even_balance L v hv
  refine near_power_marker out (L + v * 7 + 1)
    (MarkedDeficit.initial_deficit (v * 2) (v * 5 - 1)) (by omega) (by omega) ?_ (by omega)
  exact lt_of_lt_of_le (MarkedDeficit.initial_bound (v * 2) (v * 5 - 1))
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem odd_loose_marker (L v q : ℕ) (out : List Bool)
    (hL : 3 ≤ L) (hlen : out.length + 3 = L + v * 7 + 9)
    (hmass : CDPasses.value out + 2 ^ out.length = OddAdjacent.odd_mass (L + v * 2 + 2) v + q) :
    WallInvariant.marked 1 out := by
  have hbal := odd_balance L v
  refine near_power_marker out (L + v * 7 + 7)
    (MarkedDeficit.initial_deficit (v * 2 + 1) (v * 5 + 4) + 3) (by omega) (by omega) ?_ (by omega)
  exact lt_of_lt_of_le (initial_gap_three (v * 2 + 1) (v * 5 + 4) (by omega))
    (Nat.pow_le_pow_right (by decide) (by omega))

end TerminalLoose

/-! ## OdStrongMarker -/

namespace OdStrongMarker

theorem good_positive (j delta : ℕ) (h : GuardedRoute.good_deficit j delta) : 1 ≤ j := by
  rcases h with ⟨hj, _⟩ | ⟨_, _, hj, _⟩ <;> omega

theorem even_tight_marker (out : List Bool) (L q j delta m a T : ℕ)
    (hL : L = m + 7 * j + 3) (hG : GuardedRoute.good_deficit j delta)
    (hm : m ≤ 4 * a) (hT : 0 < T) (hTb : T ≤ 6 * 2 ^ m)
    (hcap : 2 * (T + q) + delta = 2 ^ L)
    (hlen : out.length + 2 = L + (5 * a + 2) * 7 + 3)
    (hmass : CDPasses.value out + 2 ^ out.length =
      OddImage.first_mass (L + (5 * a + 2) * 2 + 1) (5 * a + 2) + (q * 2 + 1)) :
    WallInvariant.marked 1 out := by
  have hB := TerminalLoose.even_balance L (5 * a + 2) (by omega)
  rw [show L + (5 * a + 2) * 7 + 1 = out.length by omega] at hB
  have hcancel : CounterBits.value out + (2 ^ (10 * a + 6) - 3) * 2 ^ (25 * a + 9) = q * 2 + 1 := by
    rw [CounterBits.value_eq_cd]
    unfold MarkedDeficit.initial_deficit at hB
    rw [show (5 * a + 2) * 2 + 2 = 10 * a + 6 by omega,
      show (5 * a + 2) * 5 - 1 = 25 * a + 9 by omega] at hB
    omega
  rcases hG with ⟨hj, rfl⟩ | ⟨u, c, hj, hu, hc, rfl⟩
  · refine OdDirectMarker.direct_even_marker out a j m T hj hm hT hTb ?_
    rw [hL] at hcap
    omega
  · refine OdEvenMarker.reachable_even_marker out a j m u c T hj hu hm hT hTb hc ?_
    rw [hL] at hcap
    omega

theorem odd_tight_marker (out : List Bool) (L q j delta m a T : ℕ)
    (hL : L = m + 7 * j + 3) (hG : GuardedRoute.good_deficit j delta)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 4 * a + 2) (hT : 0 < T) (hTb : T ≤ 6 * 2 ^ m)
    (hcap : 2 * (T + q) + delta = 2 ^ L)
    (hlen : out.length + 2 = L + (5 * a + 4) * 7 + 9)
    (hmass : CDPasses.value out + 2 ^ out.length =
      OddAdjacent.odd_mass (L + (5 * a + 4) * 2 + 2) (5 * a + 4) + q) :
    WallInvariant.marked 1 out := by
  have hB := TerminalLoose.odd_balance L (5 * a + 4)
  rw [show L + (5 * a + 4) * 7 + 7 = out.length by omega] at hB
  have hcancel : CounterBits.value out + (2 ^ (10 * a + 11) - 3) * 2 ^ (25 * a + 24) + 3 = q := by
    rw [CounterBits.value_eq_cd]
    unfold MarkedDeficit.initial_deficit at hB
    rw [show (5 * a + 4) * 2 + 1 + 2 = 10 * a + 11 by omega,
      show (5 * a + 4) * 5 + 4 = 25 * a + 24 by omega] at hB
    omega
  have hj := good_positive j delta hG
  have hF : 2 ^ (5 * j) = 2 ^ (5 * j - 1) * 2 := by
    conv_lhs => rw [show 5 * j = (5 * j - 1) + 1 by omega, Nat.pow_succ]
  have hP : 2 ^ L = 2 ^ (m + 7 * j + 2) * 2 := by
    rw [hL, show m + 7 * j + 3 = (m + 7 * j + 2) + 1 by omega, Nat.pow_succ]
  rcases hG with ⟨hj0, rfl⟩ | ⟨u, c, hj0, hu, hc, rfl⟩
  · refine OdDirectMarker.direct_odd_marker out a j m T hj0 ⟨hm1, hm2⟩ hT hTb ?_
    rw [hF, hP, ← Nat.mul_assoc] at hcap
    omega
  · rw [hF, hP, ← Nat.mul_assoc] at hcap
    rcases Nat.even_or_odd' c with ⟨c0, rfl | rfl⟩
    · refine OdOddMarker.reachable_odd_marker out a j m u c0 T hj0 hu ⟨hm1, hm2⟩ hT hTb ?_ ?_
      · rw [show 5 * j - 5 = (5 * j - 6) + 1 by omega, Nat.pow_succ] at hc
        omega
      · omega
    · exfalso
      omega

end OdStrongMarker

/-! ## TightMarked -/

namespace TightMarked

open CounterRules

theorem marked_false (bs : List Bool) (h : WallInvariant.marked 1 bs) :
    WallInvariant.marked 0 (false :: bs) := by
  rcases h with ⟨pre, post, rfl, hp⟩
  exact ⟨false :: pre, post, rfl, by simp; omega⟩

theorem marked_true (bs : List Bool) (h : WallInvariant.marked 1 bs) : true ∈ bs := by
  rcases h with ⟨pre, post, rfl, _⟩
  simp

theorem realign (bs : List Bool) :
    ([1, 0, 0, 0] : List Γ) +> (WallInvariant.normal bs +> ([1, 0, 0, 1, 0] +> default)) =
      [1] +> (CDPasses.third bs +> ([0, 0, 0, 1, 0, 0, 1, 0] +> default)) := by
  change ([1] : List Γ) +>
      ([0, 0, 0] +> (WallInvariant.normal bs +> ([1, 0, 0, 1, 0] +> default))) =
    [1] +> (CDPasses.third bs +> ([0, 0, 0, 1, 0, 0, 1, 0] +> default))
  rw [← append_assoc [0, 0, 0] (WallInvariant.normal bs), OddImage.phase_three_word, append_assoc]
  rfl

theorem tight_marked_entry (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ L k rest j,
      bs.length = 2 * j + rest.length ∧ L = n + 5 * j + 1 ∧
      k % 2 = 1 ∧ k + 1 < 2 ^ L ∧ 2 ^ (rest.length + 3) - 1 ≤ k ∧
      ((WallInvariant.Ed n bs) [mtm]⊢⁺
        (rGate (LC L k)
          ([1] +> (CDPasses.third rest +> ([0, 0, 0, 1, 0, 0, 1, 0] +> default))))) := by
  obtain ⟨L, k, rest, j, hlen, hL, ho, hb, hmin, hrun⟩ :=
    OddMarkedEntry.marked_entry n (false :: bs) ([1, 0, 0, 1, 0] +> default)
      ⟨bs, rfl⟩ (marked_false bs hmark) (by simp; omega)
  simp only [List.length_cons] at hlen
  refine ⟨L, k, rest, j, by omega, hL, ho, hb, hmin, ?_⟩
  rw [← realign]
  have hstep := TightEd.tight_Ed_step n bs hn (marked_true bs hmark)
  have heq : TightEd.after n bs =
      OddMarkedEntry.odd_wall n (false :: bs) ([1, 0, 0, 1, 0] +> default) := by
    unfold TightEd.after WallInvariant.wall OddMarkedEntry.odd_wall LocalPasses.lh
    simp only [append_assoc]
  rw [heq] at hstep
  exact stepPlus_trans hstep hrun

theorem tight_marked_cases (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ L k rest j q,
      bs.length = 2 * j + rest.length ∧ L = n + 5 * j + 1 ∧
      k + 1 < 2 ^ L ∧ k + 1 = 2 * (TightPrimer.demand rest + q) ∧ q * 4 + 3 < 2 ^ (L + 1) ∧
      ((∃ w, rest.length = w * 2 ∧
          ((WallInvariant.Ed n bs) [mtm]⊢⁺ (TerminalClosure.even_wall L (w * 5 + 2) q)) ∧
          WallInvariant.invariant (TerminalClosure.even_wall L (w * 5 + 2) q)) ∨
       (∃ w, rest.length = w * 2 + 1 ∧
          ((WallInvariant.Ed n bs) [mtm]⊢⁺ (TerminalClosure.odd_wall L (w * 5 + 6) q)))) := by
  obtain ⟨L, k, rest, j, hlen, hL, ho, hb, hmin, hrun⟩ := tight_marked_entry n bs hn hmark
  have hdemand : 2 * TightPrimer.demand rest ≤ k + 1 := by
    unfold TightPrimer.demand
    rw [Nat.pow_add 2 rest.length 3] at hmin
    change 2 ^ rest.length * 8 - 1 ≤ k at hmin
    have := CDPasses.value_bound rest
    omega
  obtain ⟨q, heq, hcoeff, hcases⟩ :=
    TerminalClosure.tight_counter_cases L k rest (by omega) ho hdemand
  refine ⟨L, k, rest, j, q, hlen, hL, hb, heq, hcoeff, ?_⟩
  rcases hcases with ⟨w, hw, hfin, hinv⟩ | ⟨w, hw, hfin⟩
  · exact Or.inl ⟨w, hw, stepPlus_trans hrun hfin, hinv⟩
  · exact Or.inr ⟨w, hw, stepPlus_trans hrun hfin⟩

end TightMarked

/-! ## TightTrace -/

namespace TightTrace

open CounterRules CounterFinish

theorem terminal_even_strong (L s q : ℕ)
    (hs : 0 < s) (hcoeff : q * 4 + 3 < 2 ^ (L + 1)) :
    StrongInvariant.strong (TerminalClosure.even_wall L s q) := by
  obtain ⟨hL, _⟩ := TerminalSuccessor.coefficient_parts L q hcoeff
  have hval : (q * 4 + 3) * 2 ^ s < 2 ^ (L + s + 1) := by
    rw [show L + s + 1 = (L + 1) + s by omega, Nat.pow_add 2 (L + 1) s]
    exact Nat.mul_lt_mul_of_pos_right hcoeff (pow2_pos s)
  have hwall : TerminalClosure.even_wall L s q =
      WallInvariant.E (L + s + 3) (digits (L + s + 1) ((q * 4 + 3) * 2 ^ s)) := by
    unfold TerminalClosure.even_wall WallInvariant.E WallInvariant.wall LocalPasses.lh
    simp only [append_assoc]
    rw [BlankPasses.digits_shifted (L + s + 1) ((q * 4 + 3) * 2 ^ s) hval]
  rw [hwall]
  refine .StrongE (by rw [digits_length]) ?_
  rw [show L + s + 1 = (L - 1) + s + 2 by omega]
  exact StrongDigits.adjacent_shift_guard (L - 1) q s hs

theorem tight_entry (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ L k rest j,
      MarkedTrace.wall_route n (false :: bs) L k rest ∧
      bs.length = 2 * j + rest.length ∧ L = n + 5 * j + 1 ∧
      k % 2 = 1 ∧ k + 1 < 2 ^ L ∧ 2 ^ (rest.length + 4) - 1 ≤ k ∧
      ((WallInvariant.Ed n bs) [mtm]⊢⁺
        (rGate (LC L k)
          ([1] +> (CDPasses.third rest +> ([0, 0, 0, 1, 0, 0, 1, 0] +> default))))) := by
  obtain ⟨L, k, rest, j, hroute, hlen, hL, ho, hb, hmin, hrun⟩ :=
    MarkedTrace.marked_entry_trace n (false :: bs) ([1, 0, 0, 1, 0] +> default)
      ⟨bs, rfl⟩ (TightMarked.marked_false bs hmark) (by simp; omega)
  simp only [List.length_cons] at hlen
  refine ⟨L, k, rest, j, hroute, by omega, hL, ho, hb, hmin, ?_⟩
  rw [← TightMarked.realign]
  have hstep := TightEd.tight_Ed_step n bs hn (TightMarked.marked_true bs hmark)
  have heq : TightEd.after n bs =
      OddMarkedEntry.odd_wall n (false :: bs) ([1, 0, 0, 1, 0] +> default) := by
    unfold TightEd.after WallInvariant.wall OddMarkedEntry.odd_wall LocalPasses.lh
    simp only [append_assoc]
  rw [heq] at hstep
  exact stepPlus_trans hstep hrun

theorem tight_cases (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ L k rest j q,
      MarkedTrace.wall_route n (false :: bs) L k rest ∧
      bs.length = 2 * j + rest.length ∧ L = n + 5 * j + 1 ∧
      k + 1 < 2 ^ L ∧ 2 ^ (rest.length + 4) - 1 ≤ k ∧
      k + 1 = 2 * (TightPrimer.demand rest + q) ∧ 0 < q ∧ q * 4 + 3 < 2 ^ (L + 1) ∧
      ((∃ w, rest.length = w * 2 ∧
          ((WallInvariant.Ed n bs) [mtm]⊢⁺ (TerminalClosure.even_wall L (w * 5 + 2) q)) ∧
          StrongInvariant.strong (TerminalClosure.even_wall L (w * 5 + 2) q)) ∨
       (∃ w, rest.length = w * 2 + 1 ∧
          ((WallInvariant.Ed n bs) [mtm]⊢⁺ (TerminalClosure.odd_wall L (w * 5 + 6) q)))) := by
  obtain ⟨L, k, rest, j, hroute, hlen, hL, ho, hb, hmin, hrun⟩ := tight_entry n bs hn hmark
  have hmin' := hmin
  rw [Nat.pow_add 2 rest.length 4] at hmin'
  change 2 ^ rest.length * 16 - 1 ≤ k at hmin'
  have hdemand : 2 * TightPrimer.demand rest ≤ k + 1 := by
    unfold TightPrimer.demand
    have := CDPasses.value_bound rest
    omega
  obtain ⟨q, heq, hcoeff, hcases⟩ :=
    TerminalClosure.tight_counter_cases L k rest (by omega) ho hdemand
  have hq : 0 < q := by
    unfold TightPrimer.demand at heq
    have := pow2_pos rest.length
    omega
  refine ⟨L, k, rest, j, q, hroute, hlen, hL, hb, hmin, heq, hq, hcoeff, ?_⟩
  rcases hcases with ⟨w, hw, hfin, _⟩ | ⟨w, hw, hfin⟩
  · exact Or.inl ⟨w, hw, stepPlus_trans hrun hfin,
      terminal_even_strong L (w * 5 + 2) q (by omega) hcoeff⟩
  · exact Or.inr ⟨w, hw, stepPlus_trans hrun hfin⟩

end TightTrace

/-! ## StrongE -/

namespace StrongE

open CounterRules

theorem demand_bound (bs : List Bool) : OddDefectTail.demand bs ≤ 6 * 2 ^ bs.length := by
  unfold OddDefectTail.demand
  split
  · rw [Nat.pow_succ]; omega
  · omega

theorem converted_bounds (bs : List Bool) :
    bs.length + 1 ≤ OddDefectTail.converted_digits bs ∧
    OddDefectTail.converted_digits bs ≤ bs.length + 2 := by
  unfold OddDefectTail.converted_digits
  split <;> omega

theorem ordinary_successor (L : ℕ) (rest : List Bool) (j delta q w : ℕ)
    (hL : L = rest.length + 7 * j + 3) (hG : GuardedRoute.good_deficit j delta)
    (hcap : 2 * (OddDefectTail.demand rest + q) + delta = 2 ^ L)
    (hq : 0 < q) (hcoeff : q * 4 + 3 < 2 ^ (L + 1))
    (hg : OddDefectTail.converted_digits rest = w * 2 + 1) :
    ∃ out, ((TerminalClosure.odd_wall L (w * 5 + 4) q) [mtm]⊢⁺ out) ∧
      StrongInvariant.strong out := by
  have hj := OdStrongMarker.good_positive j delta hG
  have hgb := converted_bounds rest
  have hT := OddDefectFinish.demand_positive rest
  have hTb := demand_bound rest
  have hL3 : 3 ≤ L := by omega
  rcases Nat.even_or_odd' w with ⟨a, rfl | rfl⟩
  · rw [show 2 * a * 5 + 4 = (5 * a + 2) * 2 by omega]
    obtain ⟨out, hlen, _, _, hmass, hrun⟩ :=
      TerminalSuccessor.ordinary_even_image L (5 * a + 2) q (by omega) hcoeff
    refine ⟨WallInvariant.Ed (L + (5 * a + 2) * 7 + 3) out, hrun, .StrongEd hlen ?_⟩
    rcases hlen with hlo | hti
    · exact TerminalLoose.even_loose_marker L (5 * a + 2) q out hL3 (by omega) hlo hmass
    · exact OdStrongMarker.even_tight_marker out L q j delta rest.length a
        (OddDefectTail.demand rest) hL hG (by omega) hT hTb hcap hti hmass
  · rw [show (2 * a + 1) * 5 + 4 = (5 * a + 4) * 2 + 1 by omega]
    obtain ⟨out, hlen, _, _, hmass, hrun⟩ :=
      TerminalSuccessor.ordinary_odd_image L (5 * a + 4) q hq hcoeff
    refine ⟨WallInvariant.Ed (L + (5 * a + 4) * 7 + 9) out, hrun, .StrongEd hlen ?_⟩
    rcases hlen with hlo | hti
    · exact TerminalLoose.odd_loose_marker L (5 * a + 4) q out hL3 hlo hmass
    · exact OdStrongMarker.odd_tight_marker out L q j delta rest.length a
        (OddDefectTail.demand rest) hL hG (by omega) (by omega) hT hTb hcap hti hmass

theorem defect_entry (n : ℕ) (bs : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : MarkedTrace.wall_route n bs L k rest) (hn : bs.length + 1 ≤ n) :
    (WallInvariant.Od n bs) [mtm]⊢⁺
      (rGate (LC L k) ([1] +> (CDPasses.third rest +> ([0, 0, 0, 0, 0, 0, 0, 1] +> default)))) := by
  have hrun := MarkedTrace.route_run n bs L k rest ([0, 0, 0, 0, 1] +> default) hr hn
  have hwall :
      OddMarkedEntry.odd_wall n bs ([0, 0, 0, 0, 1] +> default) = WallInvariant.Od n bs := by
    unfold OddMarkedEntry.odd_wall WallInvariant.Od WallInvariant.wall LocalPasses.lh
    simp only [append_assoc]
  rw [hwall] at hrun
  have hrhs : ([1, 0, 0, 0] : List Γ) +>
      (WallInvariant.normal rest +> ([0, 0, 0, 0, 1] +> default)) =
      [1] +> (CDPasses.third rest +> ([0, 0, 0, 0, 0, 0, 0, 1] +> default)) := by
    change ([1] : List Γ) +>
      ([0, 0, 0] +> (WallInvariant.normal rest +> ([0, 0, 0, 0, 1] +> default))) = _
    rw [OddDefectFinish.third_normal_side]
  rwa [hrhs] at hrun

theorem defect_strong (n : ℕ) (bs : List Bool)
    (hfull : bs.length + 1 = n) (hzero : WallInvariant.first_zero bs)
    (hdata : GuardedRoute.source_data n bs) :
    ∃ out, ((WallInvariant.Od n bs) [mtm]⊢⁺ out) ∧ StrongInvariant.strong out := by
  rcases hdata with ⟨L, k, rest, j, delta, hr, hdim, hL, hD, hG⟩
  have hn : bs.length + 1 ≤ n := by omega
  have hLfull : L = rest.length + 7 * j + 3 := by omega
  obtain ⟨hk, ho⟩ := MarkedTrace.route_bounds n bs L k rest hr hzero hn
  have hmin := MarkedTrace.route_margin4 n bs L k rest hr hzero hn
  have hentry := defect_entry n bs L k rest hr hn
  have hTb := demand_bound rest
  have hpow := pow2_pos rest.length
  rw [Nat.pow_add 2 rest.length 4] at hmin
  change 2 ^ rest.length * 16 - 1 ≤ k at hmin
  have hb : 2 * OddDefectTail.demand rest ≤ k + 1 := by omega
  obtain ⟨q, hbudget, hcoeff, hcases⟩ :=
    TerminalClosure.defect_counter_cases L k rest (by omega) ho hb
  have hq : 0 < q := by omega
  rcases hcases with ⟨w, hg, hfin, _⟩ | ⟨w, hg, hfin⟩
  · refine ⟨TerminalClosure.even_wall L (w * 5) q, stepPlus_trans hentry hfin, ?_⟩
    have hcb := converted_bounds rest
    exact TightTrace.terminal_even_strong L (w * 5) q (by omega) hcoeff
  · obtain ⟨out, hnext, hstrong⟩ := ordinary_successor L rest j delta q w hLfull hG
      (by omega) hq hcoeff hg
    exact ⟨out, stepPlus_trans hentry (stepPlus_trans hfin hnext), hstrong⟩

theorem strong_E (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 ≤ n) (hG : StrongInvariant.digit_guard bs) :
    ∃ out, ((WallInvariant.E n bs) [mtm]⊢⁺ out) ∧ StrongInvariant.strong out := by
  set padded := bs ++ List.replicate (n - bs.length - 2) false
  have hp : padded.length + 2 = n := by unfold padded; simp; omega
  have hpguard : StrongInvariant.digit_guard padded := StrongInvariant.guard_append _ _ hG
  have hdata := GuardedRoute.guard_source n padded (by omega) hpguard
  have hbits : PhaseE.output_bits n bs = false :: padded := rfl
  have htrue : true ∈ bs := by
    rcases StrongInvariant.guard_marked bs hG with ⟨pre, post, rfl, _⟩
    simp
  obtain ⟨out, hnext, hstrong⟩ :=
    defect_strong n (false :: padded) (by simp; omega) ⟨padded, rfl⟩ hdata
  refine ⟨out, stepPlus_trans (PhaseE.phase_E n bs hn htrue) ?_, hstrong⟩
  rwa [hbits]

end StrongE

/-! ## InitialWall & StrongEntry -/

namespace InitialWall

theorem initial_wall :
    (init []) [mtm]⊢* WallInvariant.E 6 [false, true, false, true] := by
  have hstar : (init []) [mtm]⊢* NatCfg.toCfg (K := 6)
      ⟨0, 1, encodeList [0, 1, 1] 0,
        encodeList ([1] ++ ([1, 1] : List Γ) ^ 5 ++
          WallInvariant.shifted [false, true, false, true]) 0⟩ := by
    refine ⟨689, ?_⟩
    have hs := stepsNat_sound mtm 689 ⟨0, 0, 0, 0⟩
      ⟨0, 1, encodeList [0, 1, 1] 0,
        encodeList ([1] ++ ([1, 1] : List Γ) ^ 5 ++
          WallInvariant.shifted [false, true, false, true]) 0⟩
      (by decide +kernel) (by decide +kernel)
    rwa [toCfg_zero] at hs
  have h_rhs : (NatCfg.toCfg (K := 6)
      ⟨0, 1, encodeList [0, 1, 1] 0,
        encodeList ([1] ++ ([1, 1] : List Γ) ^ 5 ++
          WallInvariant.shifted [false, true, false, true]) 0⟩) =
      WallInvariant.E 6 [false, true, false, true] := by
    have hl : decodeHalf (encodeList [0, 1, 1] 0) =
        ([0] : List Γ) +> (([1, 1] : List Γ) +> default) := by
      rw [← decodeHalf_encodeList, decodeHalf_zero]; rfl
    have hr : (1 : Γ) >> decodeHalf (encodeList ([1] ++ ([1, 1] : List Γ) ^ 5 ++
        WallInvariant.shifted [false, true, false, true]) 0) =
        (([1, 1] : List Γ) ^ 6 ++ WallInvariant.shifted [false, true, false, true]) +> default := by
      rw [← decodeHalf_encodeList, decodeHalf_zero]
      rfl
    ext
    · rfl
    · simp only [NatCfg.toCfg, WallInvariant.E, WallInvariant.wall, hl, ← hr,
        ListBlank.head_cons, ListBlank.tail_cons]
      rfl
  rwa [h_rhs] at hstar

theorem initial_wall_invariant :
    WallInvariant.invariant (WallInvariant.E 6 [false, true, false, true]) :=
  .InvE (by decide) ⟨[false], [false, true], rfl, rfl⟩

end InitialWall

namespace StrongEntry

theorem initial_strong :
    StrongInvariant.strong (WallInvariant.E 6 [false, true, false, true]) :=
  .StrongE (by decide) StrongInvariant.initial_guard

theorem closure_nonhalt
    (hclosure : ∀ c, StrongInvariant.strong c → ∃ c', (c [mtm]⊢⁺ c') ∧ StrongInvariant.strong c') :
    IsNotHalt target_tm := by
  have h_init_target : (init []) [target_tm]⊢*
      flipCfg (WallInvariant.E 6 [false, true, false, true]) := by
    have hf := stepStar_flipTM InitialWall.initial_wall
    rw [flipTM_flipTM] at hf
    exact hf
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ w, c = flipCfg w ∧ StrongInvariant.strong w)
    ⟨_, h_init_target, _, rfl, initial_strong⟩ ?_
  rintro _ ⟨w, rfl, hw⟩
  obtain ⟨w', hstep, hw'⟩ := hclosure w hw
  have hf := stepPlus_flipTM hstep
  rw [flipTM_flipTM] at hf
  exact ⟨flipCfg w', hf, w', rfl, hw'⟩

end StrongEntry

/-! ## StrongEdEven -/

namespace StrongEdEven

open CounterRules CounterFinish

theorem even_image_exact (n v width k i q r : ℕ)
    (hv : 0 < v) (hn : v * 2 + 2 ≤ n) (hw : width ≤ n) (hk : k < 2 ^ width)
    (hi : i < v * 5 - 1) (hodd : i % 2 = 1) (hr : r < 2 ^ i)
    (hdecomp : k = (q * 2 + 1) * 2 ^ i + r) :
    ∃ out,
      (out.length + 3 = n + v * 5 + 2 ∨ out.length + 2 = n + v * 5 + 2) ∧
      WallInvariant.marked 1 out ∧
      ((WallInvariant.O n (List.replicate (v * 2) false ++ true :: digits width k)) [mtm]⊢⁺
        (WallInvariant.Ed (n + v * 5 + 2) out)) := by
  obtain ⟨hmin, hmax⟩ := EdEvenOrbit.first_mass_bounds n v width k hv hn hw hk
  have hlen : width + (n + v * 5 + 1 - width) = n + v * 5 + 1 := by omega
  have hval : CDPasses.value (digits width k) = k := by
    rw [← CounterBits.value_eq_cd]
    exact CounterBits.digits_value width k hk
  obtain ⟨out, _, hval_out, hrun⟩ := OddImage.initial_even_image n v (digits width k)
    (n + v * 5 + 1 - width) hv (by omega)
    (by rw [digits_length]; exact hmin)
    (by rw [digits_length, hval, hlen]; exact hmax)
  rw [hval] at hval_out
  have hpi := pow2_pos i
  have hnonzero : k ≠ 0 := by
    have : 1 ≤ (q * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
    omega
  have hany : CDPasses.any (digits width k) = true := by
    apply EdEvenOrbit.any_true
    apply CounterBits.value_nonzero
    rw [CounterBits.digits_value width k hk]
    exact hnonzero
  rw [hany, EdEvenOrbit.fourth_eq_shifted] at hrun
  have hlower : 2 ^ (n + v * 5 - 1) ≤ OddImage.first_mass n v + k := by
    have := TerminalSuccessor.first_mass_lower n v hv hn
    omega
  have hupper : OddImage.first_mass n v + k < 2 ^ ((n + v * 5 - 1) + 2) := by
    rwa [show (n + v * 5 - 1) + 2 = n + v * 5 + 1 by omega]
  have hsizes := TerminalSuccessor.mass_length out (n + v * 5 - 1) _ hval_out hlower hupper
  refine ⟨out, by omega, ?_, hrun⟩
  rw [← hodd]
  refine MarkerArithmetic.low_marker_preserved out k i q r (v * 5 - 1)
    (2 * OddImage.first_fuel n (v * 2) + 1) (by omega) hi hr hdecomp ?_
  rw [CounterBits.value_eq_cd]
  exact hval_out

theorem Ed_even_valuation_exact (n : ℕ) (bs : List Bool) (b : ℕ)
    (hlen : bs.length = 4 * b) (hn : bs.length + 3 ≤ n) (hin : true ∈ bs) :
    ∃ out,
      (out.length + 3 = n + 35 * b + 17 ∨ out.length + 2 = n + 35 * b + 17) ∧
      WallInvariant.marked 1 out ∧
      ((WallInvariant.Ed n bs) [mtm]⊢⁺ (WallInvariant.Ed (n + 35 * b + 17) out)) := by
  set k := 2 ^ n - PhaseEd.fuel bs - 3
  have hk : k < 2 ^ n := PhaseEd.remaining_bound n bs hn
  obtain ⟨q, hdecomp⟩ := PhaseEd.remaining_decomposition n bs hn
  change k = _ at hdecomp
  rw [hlen] at hdecomp
  have hsmall := PhaseEd.value_bound bs
  rw [hlen] at hsmall
  have hr : 2 * PhaseEd.value bs < 2 ^ (4 * b + 1) := by rw [Nat.pow_succ]; omega
  obtain ⟨out, hlen_out, hmark, hrun⟩ :=
    even_image_exact (n + 10 * b + 5) (5 * b + 2) n k (4 * b + 1) q (2 * PhaseEd.value bs)
      (by omega) (by omega) (by omega) hk (by omega) (by omega) hr hdecomp
  rw [show n + 10 * b + 5 + (5 * b + 2) * 5 + 2 = n + 35 * b + 17 by omega] at hlen_out hrun
  refine ⟨out, hlen_out, hmark, ?_⟩
  have hentry := PhaseEd.nonzero_counter_entry n bs hn hin
  change _ [mtm]⊢* rGate (LC n k) _ at hentry
  rw [show bs.length + 1 = (b * 2) * 2 + 1 by omega] at hentry
  have hwall := PhaseEd.gap2_odd_wall n k (b * 2) hk
  have hstart : (WallInvariant.Ed n bs) [mtm]⊢⁺
      ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
        ([1] +> ([1, 1] ^ (n + 10 * b + 5) +> RC ((k * 2 + 1) * 2 ^ ((5 * b + 2) * 2))))) := by
    rw [show n + 10 * b + 5 = n + 1 + ((b * 2) * 5 + 4) by omega,
      show (5 * b + 2) * 2 = (b * 2) * 5 + 4 by omega]
    exact stepStar_stepPlus_trans hentry hwall
  have hwall_eq : ((([0] : List Γ) +> LocalPasses.lh) {{qA}}>
      ([1] +> ([1, 1] ^ (n + 10 * b + 5) +> RC ((k * 2 + 1) * 2 ^ ((5 * b + 2) * 2))))) =
      WallInvariant.O (n + 10 * b + 5)
        (List.replicate ((5 * b + 2) * 2) false ++ true :: digits n k) := by
    unfold WallInvariant.O WallInvariant.wall LocalPasses.lh
    simp only [append_assoc]
    rw [EdEvenOrbit.normal_shift_odd n k ((5 * b + 2) * 2) hk, one_comm_11_side]
  rw [hwall_eq] at hstart
  exact stepPlus_trans hstart hrun

theorem Ed_even_strong (n : ℕ) (bs : List Bool) (b : ℕ)
    (hlen : bs.length = 4 * b) (hn : bs.length + 3 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ c, ((WallInvariant.Ed n bs) [mtm]⊢⁺ c) ∧ StrongInvariant.strong c := by
  have hin : true ∈ bs := TightMarked.marked_true bs hmark
  obtain ⟨out, hslack, hmarker, hrun⟩ := Ed_even_valuation_exact n bs b hlen (by omega) hin
  exact ⟨WallInvariant.Ed (n + 35 * b + 17) out, hrun, .StrongEd hslack hmarker⟩

end StrongEdEven

/-! ## EdOddBounds -/

namespace EdOddBounds

open CounterFinish

theorem digits_true_at (width val i q : ℕ) (hi : i < width) (hq : val / 2 ^ i = q * 2 + 1) :
    (CounterFinish.digits width val).getD i false = true := by
  rw [CounterBits.digits_split width i val (by omega)]
  have hle : (CounterFinish.digits i val).length ≤ i := by rw [digits_length]
  simp only [List.getD, List.getElem?_append_right hle, digits_length, Nat.sub_self, hq]
  rw [show width - i = (width - i - 1) + 1 by omega, digits_odd]
  rfl

theorem source_even_bit (n : ℕ) (bs : List Bool) (hn : bs.length + 5 ≤ n) :
    (CounterFinish.digits n (EdOddOrbit.source_rank n bs)).getD (bs.length + 4) false = true := by
  set d := n - bs.length - 5
  have he : n = bs.length + 5 + d := by omega
  have hfuel := PhaseEd.fuel_value bs
  have hv := PhaseEd.value_bound bs
  have hfits := PhaseEd.fuel_fits n bs (by omega)
  have hp := pow2_pos bs.length
  have hd := pow2_pos d
  have hbig : 2 ^ n = 2 ^ bs.length * 32 * 2 ^ d := by
    rw [he, Nat.pow_add 2 (bs.length + 5) d, Nat.pow_add 2 bs.length 5]
  have hbit : 2 ^ (bs.length + 4) = 2 ^ bs.length * 16 := Nat.pow_add 2 bs.length 4
  have hsmall : 10 * 2 ^ bs.length + 2 * PhaseEd.value bs < 2 ^ (bs.length + 4) := by
    rw [hbit]; omega
  have hdecomp : EdOddOrbit.source_rank n bs =
      ((2 ^ d - 1) * 2 + 1) * 2 ^ (bs.length + 4) +
        (10 * 2 ^ bs.length + 2 * PhaseEd.value bs) := by
    unfold EdOddOrbit.source_rank
    have hdsub : (2 ^ d - 1) * 2 + 1 = 2 ^ d * 2 - 1 := by omega
    rw [hbig, hbit, hdsub]
    have hsub2 : (2 ^ d * 2 - 1) * (2 ^ bs.length * 16) + 2 ^ bs.length * 16 =
        2 ^ bs.length * 32 * 2 ^ d := by
      have hge : 2 ^ bs.length * 16 ≤ (2 ^ d * 2) * (2 ^ bs.length * 16) := by
        simpa using Nat.mul_le_mul_right (2 ^ bs.length * 16) (show 1 ≤ 2 ^ d * 2 by omega)
      rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel hge]
      ring
    generalize (2 ^ d * 2 - 1) * (2 ^ bs.length * 16) = Q at hsub2 ⊢
    generalize 2 ^ bs.length * 32 * 2 ^ d = BIG at hbig hsub2 ⊢
    omega
  refine digits_true_at n (EdOddOrbit.source_rank n bs) (bs.length + 4) (2 ^ d - 1)
    (by omega) ?_
  have hp4 := pow2_pos (bs.length + 4)
  rw [hdecomp, Nat.add_comm, Nat.add_mul_div_right _ _ hp4,
    Nat.div_eq_of_lt hsmall, Nat.zero_add]

theorem first_deficit (n u z : ℕ) (hn : u + 1 ≤ n) :
    OddFuel.grown (OddImage.first_fuel n u) z + (2 ^ (u + 2) - 3) * 2 ^ z + 1 =
      2 ^ (n + 1 + z) := by
  have hd := OdDeficit.initial_deficit n u z hn
  linarith

theorem initial_deficit (n : ℕ) (bs : List Bool) (b : ℕ)
    (_hm : bs.length = 4 * b + 2) (_hn : bs.length + 3 ≤ n) :
    EdOddOrbit.initial_rank n b + (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 23) + 1 =
      2 ^ EdOddOrbit.initial_width n b := by
  unfold EdOddOrbit.initial_rank EdOddOrbit.initial_width
  rw [show 10 * b + 11 = (10 * b + 9) + 2 by omega,
    show n + 35 * b + 34 = (n + 10 * b + 10) + 1 + (25 * b + 23) by omega]
  exact first_deficit (n + 10 * b + 10) (10 * b + 9) (25 * b + 23) (by omega)

theorem marked_drop_pair (bs : List Bool) (h : WallInvariant.marked 1 (false :: false :: bs)) :
    WallInvariant.marked 1 bs := by
  rcases h with ⟨pre, post, he, hp⟩
  rcases pre with _ | ⟨a, _ | ⟨a', pre⟩⟩
  · simp at he
  · simp at he
  · simp only [List.cons_append, List.cons.injEq] at he
    rcases he with ⟨_, _, rfl⟩
    exact ⟨pre, post, rfl, by simp at hp; omega⟩

theorem marked_drop_even_zeros (s : ℕ) (bs : List Bool)
    (h : WallInvariant.marked 1 (List.replicate (s * 2) false ++ bs)) :
    WallInvariant.marked 1 bs := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
    rw [show (s + 1) * 2 = s * 2 + 2 by omega, List.replicate_succ, List.replicate_succ,
      List.cons_append, List.cons_append] at h
    exact ih (marked_drop_pair _ h)

end EdOddBounds

/-! ## EdOddTight -/

namespace EdOddTight

open CounterFinish

theorem value_zeros (n : ℕ) : CDPasses.value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, CDPasses.value, CDPasses.bitval, ih]

theorem correction_small (b j e v w : ℕ)
    (hj : 2 * j ≤ 4 * b + 6) (he : e < 2 ^ (7 * j + 3))
    (hv : v < 2 ^ (4 * b + 2)) (hw : w < 2 ^ (2 * j + 1)) :
    let c := e * 2 ^ (2 * j + 1) + 12 * 2 ^ (4 * b + 2) + 2 * w - 4 * v
    0 < c ∧ c < 2 ^ ((25 * b + 7 * j + 26) - 2) ∧
      c + 4 * v = e * 2 ^ (2 * j + 1) + 12 * 2 ^ (4 * b + 2) + 2 * w := by
  intro c
  have hp := pow2_pos (4 * b + 2)
  have hpos : 0 < c := by unfold c; omega
  have hbal : c + 4 * v = e * 2 ^ (2 * j + 1) + 12 * 2 ^ (4 * b + 2) + 2 * w := by unfold c; omega
  refine ⟨hpos, ?_, hbal⟩
  have hfirst : e * 2 ^ (2 * j + 1) < 2 ^ (9 * j + 4) := by
    rw [show 9 * j + 4 = (7 * j + 3) + (2 * j + 1) by omega,
      Nat.pow_add 2 (7 * j + 3) (2 * j + 1)]
    exact Nat.mul_lt_mul_of_pos_right he (pow2_pos (2 * j + 1))
  have hsecond : 12 * 2 ^ (4 * b + 2) < 2 ^ (4 * b + 6) := by
    rw [show 4 * b + 6 = (4 * b + 2) + 4 by omega, Nat.pow_add 2 (4 * b + 2) 4]
    change 12 * 2 ^ (4 * b + 2) < 2 ^ (4 * b + 2) * 16
    omega
  have hthird : 2 * w < 2 ^ (2 * j + 2) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, Nat.pow_succ 2 (2 * j + 1)]
    omega
  have ha : 2 ^ (9 * j + 4) ≤ 2 ^ (25 * b + 7 * j + 22) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hb : 2 ^ (4 * b + 6) ≤ 2 ^ (25 * b + 7 * j + 22) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hc : 2 ^ (2 * j + 2) ≤ 2 ^ (25 * b + 7 * j + 22) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [show 25 * b + 7 * j + 26 - 2 = (25 * b + 7 * j + 22) + 2 by omega,
    Nat.pow_add 2 (25 * b + 7 * j + 22) 2]
  change c < 2 ^ (25 * b + 7 * j + 22) * 4
  omega

theorem odd_route_tight_marker (n : ℕ) (bs : List Bool) (b L' k' : ℕ) (rest out : List Bool) (t : ℕ)
    (hm : bs.length = 4 * b + 2) (hn : bs.length + 3 ≤ n)
    (hroute : OddRoute.route (EdOddOrbit.initial_width n b) (EdOddOrbit.initial_rank n b)
      (digits n (EdOddOrbit.source_rank n bs)) L' k' rest)
    (ht : t * 2 = k' + 1) (hmass : CDPasses.value out + 2 ^ out.length = t + CDPasses.value rest)
    (htight : out.length + 1 = L') :
    WallInvariant.marked 1 out := by
  set d := (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 23)
  have hd : EdOddOrbit.initial_rank n b + d + 1 = 2 ^ EdOddOrbit.initial_width n b :=
    EdOddBounds.initial_deficit n bs b hm hn
  obtain ⟨j, e, hlen, _, hdef, he⟩ :=
    RouteDeficit.route_deficit _ _ _ _ _ _ hroute d hd
  have hj : 2 * j ≤ 4 * b + 6 := by
    by_cases hwide : bs.length + 5 ≤ n
    · have hbit := EdOddBounds.source_even_bit n bs hwide
      have hpar : (bs.length + 4) % 2 = 0 := by omega
      have := RouteMarkerBound.route_known_even_bound _ _ _ _ _ _ j (bs.length + 4)
        hroute hlen hbit hpar
      omega
    · rw [digits_length] at hlen
      omega
  obtain ⟨pre, hprefix⟩ := RouteDeficit.route_suffix _ _ _ _ _ _ hroute
  have hpre : pre.length = 2 * j + 1 := by
    have hlen' := congrArg List.length hprefix
    simp only [List.length_append] at hlen'
    omega
  have hrank : EdOddOrbit.source_rank n bs < 2 ^ n := PhaseEd.remaining_bound n bs hn
  have hval : CDPasses.value (digits n (EdOddOrbit.source_rank n bs)) =
      EdOddOrbit.source_rank n bs := by
    rw [← CounterBits.value_eq_cd]
    exact CounterBits.digits_value n _ hrank
  rw [hprefix, CDPasses.value_append, hpre] at hval
  have hw := CDPasses.value_bound pre
  rw [hpre] at hw
  have hv := PhaseEd.value_bound bs
  rw [hm] at hv
  obtain ⟨hc, hcsmall, hcbal⟩ :=
    correction_small b j e (PhaseEd.value bs) (CDPasses.value pre) hj he hv hw
  set c := e * 2 ^ (2 * j + 1) + 12 * 2 ^ (4 * b + 2) +
    2 * CDPasses.value pre - 4 * PhaseEd.value bs
  have hsource :
      EdOddOrbit.source_rank n bs + 6 * 2 ^ (4 * b + 2) = 2 ^ n + 2 * PhaseEd.value bs := by
    have hf := PhaseEd.fuel_value bs
    rw [hm] at hf
    have hfits := PhaseEd.fuel_fits n bs hn
    unfold EdOddOrbit.source_rank
    omega
  have hpowtight : 2 ^ L' = 2 ^ out.length * 2 := by rw [← htight, Nat.pow_succ]
  have hcore : 2 * CDPasses.value out + d * 2 ^ (5 * j + 2) + e = 2 * CDPasses.value rest := by
    rw [hpowtight] at hdef
    omega
  have hbig : d * 2 ^ (5 * j + 2) * 2 ^ (2 * j + 1) =
      (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 7 * j + 26) := by
    unfold d
    rw [show 25 * b + 7 * j + 26 = (25 * b + 23) + (5 * j + 2) + (2 * j + 1) by omega,
      Nat.pow_add, Nat.pow_add]
    ring
  have hshift : 2 ^ (2 * j + 2) = 2 ^ (2 * j + 1) * 2 := Nat.pow_succ 2 (2 * j + 1)
  have hright : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
  have hequation : CDPasses.value out * 2 ^ (2 * j + 2) + c +
      (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 7 * j + 26) = 2 ^ (n + 1) := by
    rw [← hbig, hshift, hright]
    have hscaled : CDPasses.value out * (2 ^ (2 * j + 1) * 2) +
        d * 2 ^ (5 * j + 2) * 2 ^ (2 * j + 1) + e * 2 ^ (2 * j + 1) =
        2 * (2 ^ (2 * j + 1) * CDPasses.value rest) := by
      have hs := congrArg (fun x => x * 2 ^ (2 * j + 1)) hcore
      linarith [hs, show (2 * CDPasses.value out + d * 2 ^ (5 * j + 2) + e) * 2 ^ (2 * j + 1) =
          CDPasses.value out * (2 ^ (2 * j + 1) * 2) +
            d * 2 ^ (5 * j + 2) * 2 ^ (2 * j + 1) + e * 2 ^ (2 * j + 1) by ring,
        show 2 * CDPasses.value rest * 2 ^ (2 * j + 1) =
          2 * (2 ^ (2 * j + 1) * CDPasses.value rest) by ring]
    linarith [hscaled, hval, hsource, hcbal]
  have hmarked : WallInvariant.marked 1 (List.replicate (2 * j + 2) false ++ out) := by
    refine GapMarker.small_subtraction_marker (List.replicate (2 * j + 2) false ++ out)
      (n + 1) (10 * b + 11) (25 * b + 7 * j + 26) c (by omega) (by omega) hc hcsmall ?_
    rw [CounterBits.value_eq_cd, CDPasses.value_append, value_zeros, List.length_replicate,
      Nat.zero_add, Nat.mul_comm (2 ^ (2 * j + 2))]
    exact hequation
  rw [show 2 * j + 2 = (j + 1) * 2 by omega] at hmarked
  exact EdOddBounds.marked_drop_even_zeros (j + 1) out hmarked

end EdOddTight

/-! ## EdOddLoose -/

namespace EdOddLoose

open CounterFinish

theorem odd_route_loose_marker (n : ℕ) (bs : List Bool) (b L' k' : ℕ) (rest out : List Bool) (t : ℕ)
    (hm : bs.length = 4 * b + 2) (hn : bs.length + 3 = n)
    (hroute : OddRoute.route (EdOddOrbit.initial_width n b) (EdOddOrbit.initial_rank n b)
      (digits n (EdOddOrbit.source_rank n bs)) L' k' rest)
    (ht : t * 2 = k' + 1) (hmass : CDPasses.value out + 2 ^ out.length = t + CDPasses.value rest)
    (hloose : out.length + 2 = L') :
    WallInvariant.marked 1 out := by
  set d := (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 23)
  have hd : EdOddOrbit.initial_rank n b + d + 1 = 2 ^ EdOddOrbit.initial_width n b :=
    EdOddBounds.initial_deficit n bs b hm (by omega)
  obtain ⟨j, e, hlen, hL, hdef, he⟩ :=
    RouteDeficit.route_deficit _ _ _ _ _ _ hroute d hd
  have hj : 2 * j ≤ 4 * b + 6 := by rw [digits_length] at hlen; omega
  obtain ⟨pre, hprefix⟩ := RouteDeficit.route_suffix _ _ _ _ _ _ hroute
  have hpre : pre.length = 2 * j + 1 := by
    have hlen' := congrArg List.length hprefix
    simp only [List.length_append] at hlen'
    omega
  have hrank : EdOddOrbit.source_rank n bs < 2 ^ n := PhaseEd.remaining_bound n bs (by omega)
  have hval : CDPasses.value (digits n (EdOddOrbit.source_rank n bs)) =
      EdOddOrbit.source_rank n bs := by
    rw [← CounterBits.value_eq_cd]
    exact CounterBits.digits_value n _ hrank
  rw [hprefix, CDPasses.value_append, hpre] at hval
  have hw := CDPasses.value_bound pre
  rw [hpre] at hw
  have hv := PhaseEd.value_bound bs
  rw [hm] at hv
  obtain ⟨hc, hcsmall, hcbal⟩ :=
    EdOddTight.correction_small b j e (PhaseEd.value bs) (CDPasses.value pre) hj he hv hw
  set c := e * 2 ^ (2 * j + 1) + 12 * 2 ^ (4 * b + 2) +
    2 * CDPasses.value pre - 4 * PhaseEd.value bs
  have hsource :
      EdOddOrbit.source_rank n bs + 6 * 2 ^ (4 * b + 2) = 2 ^ n + 2 * PhaseEd.value bs := by
    have hf := PhaseEd.fuel_value bs
    rw [hm] at hf
    have hfits := PhaseEd.fuel_fits n bs (by omega)
    unfold EdOddOrbit.source_rank
    omega
  have hpowloose : 2 ^ L' = 2 ^ out.length * 4 := by
    rw [← hloose, Nat.pow_add 2 out.length 2]
  have hpowhalf : 2 ^ (L' - 1) = 2 ^ out.length * 2 := by
    rw [show L' - 1 = out.length + 1 by omega, Nat.pow_succ]
  have hcore : 2 * CDPasses.value out + d * 2 ^ (5 * j + 2) + e =
      2 ^ (L' - 1) + 2 * CDPasses.value rest := by
    rw [hpowloose] at hdef
    rw [hpowhalf]
    linarith [hdef, hmass, ht]
  have hbig : d * 2 ^ (5 * j + 2) * 2 ^ (2 * j + 1) =
      (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 7 * j + 26) := by
    unfold d
    rw [show 25 * b + 7 * j + 26 = (25 * b + 23) + (5 * j + 2) + (2 * j + 1) by omega,
      Nat.pow_add, Nat.pow_add]
    ring
  have hshift : 2 ^ (2 * j + 2) = 2 ^ (2 * j + 1) * 2 := Nat.pow_succ 2 (2 * j + 1)
  have hright : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
  have hlarge : 2 ^ (L' + 2 * j) = 2 ^ (L' - 1) * 2 ^ (2 * j + 1) := by
    rw [← Nat.pow_add, show L' - 1 + (2 * j + 1) = L' + 2 * j by omega]
  have hequation : CDPasses.value out * 2 ^ (2 * j + 2) + c +
      (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 7 * j + 26) = 2 ^ (L' + 2 * j) + 2 ^ (n + 1) := by
    rw [← hbig, hshift, hright, hlarge]
    have hscaled : CDPasses.value out * (2 ^ (2 * j + 1) * 2) +
        d * 2 ^ (5 * j + 2) * 2 ^ (2 * j + 1) + e * 2 ^ (2 * j + 1) =
        2 ^ (L' - 1) * 2 ^ (2 * j + 1) + 2 * (2 ^ (2 * j + 1) * CDPasses.value rest) := by
      have hs := congrArg (fun x => x * 2 ^ (2 * j + 1)) hcore
      linarith [hs, show (2 * CDPasses.value out + d * 2 ^ (5 * j + 2) + e) * 2 ^ (2 * j + 1) =
          CDPasses.value out * (2 ^ (2 * j + 1) * 2) +
            d * 2 ^ (5 * j + 2) * 2 ^ (2 * j + 1) + e * 2 ^ (2 * j + 1) by ring,
        show (2 ^ (L' - 1) + 2 * CDPasses.value rest) * 2 ^ (2 * j + 1) =
          2 ^ (L' - 1) * 2 ^ (2 * j + 1) + 2 * (2 ^ (2 * j + 1) * CDPasses.value rest) by ring]
    linarith [hscaled, hval, hsource, hcbal]
  have hmarked : WallInvariant.marked 1 (List.replicate (2 * j + 2) false ++ out) := by
    refine SignedGapMarker.signed_small_marker (List.replicate (2 * j + 2) false ++ out)
      (L' + 2 * j) (10 * b + 11) (25 * b + 7 * j + 26) c (2 ^ (n + 1))
      (by omega) (by omega) ?_ hc hcsmall ?_ ?_
    · unfold EdOddOrbit.initial_width at hL
      omega
    · exact (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega)
    · rw [CounterBits.value_eq_cd, CDPasses.value_append, EdOddTight.value_zeros,
        List.length_replicate, Nat.zero_add, Nat.mul_comm (2 ^ (2 * j + 2))]
      exact hequation
  rw [show 2 * j + 2 = (j + 1) * 2 by omega] at hmarked
  exact EdOddBounds.marked_drop_even_zeros (j + 1) out hmarked

end EdOddLoose

/-! ## StrongEdOddFacts -/

namespace StrongEdOddFacts

open CounterFinish

theorem phase_ed_val_eq_cd (bs : List Bool) : PhaseEd.value bs = CDPasses.value bs :=
  CounterBits.value_eq_cd bs

theorem source_rank_exact (n : ℕ) (bs : List Bool) (hn : bs.length + 3 = n) :
    EdOddOrbit.source_rank n bs = 2 ^ (bs.length + 1) + 2 * PhaseEd.value bs := by
  have hf := PhaseEd.fuel_value bs
  have hfits := PhaseEd.fuel_fits n bs (by omega)
  unfold EdOddOrbit.source_rank
  rw [← hn, Nat.pow_add 2 bs.length 3, Nat.pow_succ]
  change 2 ^ bs.length * 8 - PhaseEd.fuel bs - 3 = 2 ^ bs.length * 2 + 2 * PhaseEd.value bs
  omega

theorem source_digits_exact (n : ℕ) (bs : List Bool) (hn : bs.length + 3 = n) :
    CounterFinish.digits n (EdOddOrbit.source_rank n bs) = false :: bs ++ [true, false] := by
  have h := MarkerArithmetic.digits_value_inverse (false :: bs ++ [true, false])
  have hlen : (false :: bs ++ [true, false]).length = n := by simp; omega
  have hval : CounterBits.value (false :: bs ++ [true, false]) = EdOddOrbit.source_rank n bs := by
    rw [CounterBits.value_eq_cd]
    simp only [List.cons_append, CDPasses.value, CDPasses.bitval, CDPasses.value_append,
      ↓reduceIte, Bool.false_eq_true]
    rw [source_rank_exact n bs hn, phase_ed_val_eq_cd, Nat.pow_succ]
    omega
  rwa [hlen, hval] at h

theorem marked_prefix (bs : List Bool) (h : WallInvariant.marked 1 bs) :
    WallInvariant.marked 0 (false :: bs) :=
  TightMarked.marked_false bs h

theorem route_append (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest tail : List Bool)
    (hr : OddRoute.route L k bs L' k' rest) :
    OddRoute.route L k (bs ++ tail) L' k' (rest ++ tail) := by
  induction hr with
  | @RouteEven L k v t =>
    simp only [List.append_assoc, List.cons_append]
    exact .RouteEven
  | @RouteOdd L k v t L' k' rest _ ih =>
    simp only [List.append_assoc, List.cons_append]
    exact .RouteOdd ih

theorem route_mass_large (n : ℕ) (bs : List Bool) (b L k : ℕ) (rest : List Bool) (t : ℕ)
    (hm : bs.length = 4 * b + 2) (hn : bs.length + 3 = n)
    (hroute : OddRoute.route (EdOddOrbit.initial_width n b) (EdOddOrbit.initial_rank n b)
      (digits n (EdOddOrbit.source_rank n bs)) L k rest)
    (ht : t * 2 = k + 1) :
    2 ^ (L - 2) ≤ t := by
  set d := (2 ^ (10 * b + 11) - 3) * 2 ^ (25 * b + 23)
  have hd : EdOddOrbit.initial_rank n b + d + 1 = 2 ^ EdOddOrbit.initial_width n b :=
    EdOddBounds.initial_deficit n bs b hm (by omega)
  obtain ⟨j, e, hlen, hL, hdef, he⟩ :=
    RouteDeficit.route_deficit _ _ _ _ _ _ hroute d hd
  rw [digits_length] at hlen
  unfold EdOddOrbit.initial_width at hL
  have hLpos : 2 ≤ L := by omega
  have hdom : d * 2 ^ (5 * j + 2) < 2 ^ (35 * b + 5 * j + 36) := by
    rw [show 35 * b + 5 * j + 36 = (10 * b + 11) + (25 * b + 23) + (5 * j + 2) by omega,
      Nat.pow_add 2 ((10 * b + 11) + (25 * b + 23)) (5 * j + 2),
      Nat.pow_add 2 (10 * b + 11) (25 * b + 23)]
    unfold d
    have hp1 := pow2_pos (25 * b + 23)
    have hp2 := pow2_pos (5 * j + 2)
    have hB : 4 ≤ 2 ^ (10 * b + 11) := by
      have : 2 ^ 2 ≤ 2 ^ (10 * b + 11) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    generalize 2 ^ (10 * b + 11) = P10 at hB ⊢
    generalize 2 ^ (25 * b + 23) = P25 at hp1 ⊢
    generalize 2 ^ (5 * j + 2) = P5 at hp2 ⊢
    have hlt : (P10 - 3) * P25 < P10 * P25 := Nat.mul_lt_mul_of_pos_right (by omega) hp1
    exact Nat.mul_lt_mul_of_pos_right hlt hp2
  have hsmall : 2 ^ (7 * j + 3) ≤ 2 ^ (35 * b + 5 * j + 36) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdeficit : d * 2 ^ (5 * j + 2) + e < 2 ^ (L - 1) := by
    have hcap : 2 ^ (35 * b + 5 * j + 37) ≤ 2 ^ (L - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [show 35 * b + 5 * j + 37 = (35 * b + 5 * j + 36) + 1 by omega,
      Nat.pow_succ 2 (35 * b + 5 * j + 36)] at hcap
    linarith
  have hpowL : 2 ^ L = 2 ^ (L - 2) * 4 := by
    conv_lhs => rw [show L = (L - 2) + 2 by omega]
    exact Nat.pow_add 2 (L - 2) 2
  have hpowHalf : 2 ^ (L - 1) = 2 ^ (L - 2) * 2 := by
    rw [show L - 1 = (L - 2) + 1 by omega, Nat.pow_succ]
  rw [hpowL] at hdef
  rw [hpowHalf] at hdeficit
  linarith [hdef, hdeficit, ht]

end StrongEdOddFacts

/-! ## StrongEdOdd -/

namespace StrongEdOdd

open CounterRules CounterFinish

theorem strong_ed_odd (n : ℕ) (bs : List Bool) (b : ℕ)
    (hm : bs.length = 4 * b + 2) (hn : bs.length + 3 = n) (hmarked : WallInvariant.marked 1 bs) :
    ∃ c, ((WallInvariant.Ed n bs) [mtm]⊢⁺ c) ∧ StrongInvariant.strong c := by
  have hin : true ∈ bs := TightMarked.marked_true bs hmarked
  have hentry := EdOddOrbit.Ed_odd_valuation_entry n bs b hm (by omega) hin
  obtain ⟨hfuel, hbound, _⟩ := EdOddOrbit.Ed_odd_entry_fuel n bs b hm (by omega)
  have hdigits := StrongEdOddFacts.source_digits_exact n bs hn
  have hmark := StrongEdOddFacts.marked_prefix bs hmarked
  have hprefixfuel : 2 ^ (false :: bs).length - 1 ≤ EdOddOrbit.initial_rank n b := by
    rw [digits_length] at hfuel
    have : 2 ^ (false :: bs).length ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by simp; omega)
    omega
  obtain ⟨L, k, rest, hr, _⟩ :=
    OddRoute.marked_route (EdOddOrbit.initial_width n b) (EdOddOrbit.initial_rank n b)
      (false :: bs) hmark hprefixfuel
  have hroute : OddRoute.route (EdOddOrbit.initial_width n b) (EdOddOrbit.initial_rank n b)
      (digits n (EdOddOrbit.source_rank n bs)) L k (rest ++ [true, false]) := by
    rw [hdigits]
    exact StrongEdOddFacts.route_append _ _ (false :: bs) L k rest [true, false] hr
  obtain ⟨hcap, hpar⟩ := OddRoute.route_bound _ _ _ _ _ _ hroute hbound
  obtain ⟨j, hlen, hL⟩ := OddRoute.route_dimensions _ _ _ _ _ _ hroute
  have hwidth : (rest ++ [true, false]).length + 2 ≤ L := by
    rw [digits_length] at hlen
    unfold EdOddOrbit.initial_width at hL
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  have hrun := OddRoute.route_run _ _ _ _ _ _ default hroute hbound
  rcases Nat.even_or_odd' k with ⟨q, rfl | rfl⟩
  · omega
  · set t := q + 1
    have ht : t * 2 = (2 * q + 1) + 1 := by omega
    have hlarge := StrongEdOddFacts.route_mass_large n bs b L (2 * q + 1)
      (rest ++ [true, false]) t hm hn hroute ht
    have hmin : 2 ^ (rest ++ [true, false]).length ≤ t := by
      have : 2 ^ (rest ++ [true, false]).length ≤ 2 ^ (L - 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hrest := CDPasses.value_bound (rest ++ [true, false])
    have hmax : t + CDPasses.value (rest ++ [true, false]) <
        2 ^ ((rest ++ [true, false]).length + (L - (rest ++ [true, false]).length)) := by
      rw [show (rest ++ [true, false]).length + (L - (rest ++ [true, false]).length) = L by omega]
      omega
    obtain ⟨out, houtlen, hval, hfin⟩ := OddImage.fuel_C_image L (2 * q + 1) t
      (rest ++ [true, false]) (L - (rest ++ [true, false]).length)
      (by omega) ht.symm hmin hmax
    rw [show (rest ++ [true, false]).length + (L - (rest ++ [true, false]).length) = L by omega]
      at houtlen
    have hany : CDPasses.any (rest ++ [true, false]) = true := by
      apply EdEvenOrbit.any_true
      simp
    rw [hany, EdEvenOrbit.fourth_eq_shifted] at hfin
    have hlo : L - 2 ≤ out.length := by
      by_contra hlt
      have hv := CDPasses.value_bound out
      have hp : 2 ^ (out.length + 1) ≤ 2 ^ (L - 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at hp
      omega
    have hcases : out.length + 2 = L ∨ out.length + 1 = L := by omega
    have hmarker : WallInvariant.marked 1 out := by
      rcases hcases with hloose | htight
      · exact EdOddLoose.odd_route_loose_marker n bs b L (2 * q + 1)
          (rest ++ [true, false]) out t hm hn hroute ht hval hloose
      · exact EdOddTight.odd_route_tight_marker n bs b L (2 * q + 1)
          (rest ++ [true, false]) out t hm (by omega) hroute ht hval htight
    refine ⟨WallInvariant.Ed (L + 1) out,
      stepPlus_trans hentry (stepPlus_trans hrun hfin), .StrongEd ?_ hmarker⟩
    omega

end StrongEdOdd

/-! ## StrongEdLoose -/

namespace StrongEdLoose

theorem strong_ed_loose (n : ℕ) (bs : List Bool)
    (hn : bs.length + 3 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ c, ((WallInvariant.Ed n bs) [mtm]⊢⁺ c) ∧ StrongInvariant.strong c := by
  rcases Nat.even_or_odd' bs.length with ⟨a, ha | ha⟩
  · rcases Nat.even_or_odd' a with ⟨b, rfl | rfl⟩
    · exact StrongEdEven.Ed_even_strong n bs b (by omega) hn hmark
    · exact StrongEdOdd.strong_ed_odd n bs b (by omega) hn hmark
  · exact StrongEdDirect.Ed_direct_strong n bs (a + 1) (by omega) (by omega) hmark

end StrongEdLoose

/-! ## TightEquations -/

namespace TightEquations

theorem even_tight_equation (L v q k d T : ℕ) (out : List Bool)
    (hv : 0 < v) (hT : 0 < T) (hdef : k + d + 1 = 2 ^ L) (hfuel : k + 1 = 2 * (T + q))
    (hlen : out.length + 2 = L + v * 7 + 3)
    (hmass : CDPasses.value out + 2 ^ out.length =
      OddImage.first_mass (L + v * 2 + 1) v + (q * 2 + 1)) :
    CDPasses.value out + (2 * T - 1) + d + MarkedDeficit.initial_deficit (v * 2) (v * 5 - 1) =
      2 ^ L := by
  have hbal := TerminalLoose.even_balance L v hv
  rw [show out.length = L + v * 7 + 1 by omega] at hmass
  omega

theorem odd_tight_equation (L v q k half T : ℕ) (out : List Bool)
    (hL : 0 < L) (hdef : k + half * 2 + 1 = 2 ^ L) (hfuel : k + 1 = 2 * (T + q))
    (hlen : out.length + 2 = L + v * 7 + 9)
    (hmass : CDPasses.value out + 2 ^ out.length = OddAdjacent.odd_mass (L + v * 2 + 2) v + q) :
    CDPasses.value out + (T + 3) + half + MarkedDeficit.initial_deficit (v * 2 + 1) (v * 5 + 4) =
      2 ^ (L - 1) := by
  have hbal := TerminalLoose.odd_balance L v
  rw [show out.length = L + v * 7 + 7 by omega] at hmass
  rw [show L = (L - 1) + 1 by omega, Nat.pow_succ] at hdef
  omega

end TightEquations

/-! ## TightInitialMarker -/

namespace TightInitialMarker

theorem even_initial_marker (out : List Bool) (a j T : ℕ)
    (hj : 0 < j) (hT : 0 < T) (hTb : T ≤ 2 ^ (a * 4 + 1))
    (hE : CounterBits.value out + (2 * T - 1) + MarkedDeficit.initial_deficit (j * 2) (j * 5) +
      MarkedDeficit.initial_deficit (a * 10 + 6) (a * 25 + 14) = 2 ^ (j * 7 + a * 4 + 4)) :
    WallInvariant.marked 1 out := by
  unfold MarkedDeficit.initial_deficit at hE
  rw [show a * 10 + 6 + 2 = a * 10 + 8 by omega] at hE
  generalize hJ : j * 5 = J at hE
  generalize hK : a * 25 + 14 = K at hE
  generalize hA : j * 7 + a * 4 + 4 = A at hE
  have hD : 0 < 2 ^ (j * 2 + 2) - 3 := OdEvenMarker.minus_three_positive (j * 2)
  have hEpos : 0 < 2 ^ (a * 10 + 8) - 3 := by
    rw [show a * 10 + 8 = (a * 10 + 6) + 2 by omega]
    exact OdEvenMarker.minus_three_positive (a * 10 + 6)
  generalize hD_def : 2 ^ (j * 2 + 2) - 3 = D at hD hE
  generalize hE_def : 2 ^ (a * 10 + 8) - 3 = E at hEpos hE
  have hF : D * 2 ^ J < 2 ^ (j * 7 + 2) := by
    subst hD_def hJ
    have hs := OdEvenMarker.scaled_minus_three (j * 2) (j * 5)
    rwa [show j * 2 + 2 + j * 5 = j * 7 + 2 by omega] at hs
  generalize hF_def : D * 2 ^ J = F at hF hE
  set c := 2 * T - 1
  have hc : 0 < c := by unfold c; omega
  have hcb : c < 2 ^ (a * 4 + 2) := by
    unfold c
    rw [show a * 4 + 2 = (a * 4 + 1) + 1 by omega, Nat.pow_succ]
    omega
  by_cases hsmall : j ≤ a * 3 + 1
  · have hFsmall : F < 2 ^ (K - 3) :=
      lt_of_lt_of_le hF (Nat.pow_le_pow_right (by decide) (by omega))
    have hcsmall : c < 2 ^ (K - 3) :=
      lt_of_lt_of_le hcb (Nat.pow_le_pow_right (by decide) (by omega))
    refine MultiGapMarker.positive_subtraction_marker out A K E (c + F)
      (by omega) hEpos (Nat.add_pos_left hc F) ?_ (by linarith [hE])
    exact OdEvenMarker.sum_small K c F (by omega) hcsmall hFsmall
  · have hcJ : c < 2 ^ (J - 2) :=
      lt_of_lt_of_le hcb (Nat.pow_le_pow_right (by decide) (by omega))
    have hcK : c < 2 ^ (K - 2) :=
      lt_of_lt_of_le hcb (Nat.pow_le_pow_right (by decide) (by omega))
    rw [← hF_def] at hE
    refine MultiGapMarker.two_gap_marker out A J K D E c hD hEpos (by omega) hc ?_ hE
    by_cases hJK : J ≤ K
    · rw [Nat.min_eq_left hJK]; exact hcJ
    · rw [Nat.min_eq_right (by omega)]; exact hcK

theorem odd_initial_marker (out : List Bool) (a j T : ℕ)
    (hj : 0 < j) (hT : 0 < T) (hTb : T ≤ 2 ^ (a * 4 + 3))
    (hE : CounterBits.value out + (T + 3) + MarkedDeficit.initial_deficit (j * 2) (j * 5 - 1) +
      MarkedDeficit.initial_deficit (a * 10 + 11) (a * 25 + 29) = 2 ^ (j * 7 + a * 4 + 5)) :
    WallInvariant.marked 1 out := by
  unfold MarkedDeficit.initial_deficit at hE
  rw [show a * 10 + 11 + 2 = a * 10 + 13 by omega] at hE
  generalize hJ : j * 5 - 1 = J at hE
  generalize hK : a * 25 + 29 = K at hE
  generalize hA : j * 7 + a * 4 + 5 = A at hE
  have hD : 0 < 2 ^ (j * 2 + 2) - 3 := OdEvenMarker.minus_three_positive (j * 2)
  have hEpos : 0 < 2 ^ (a * 10 + 13) - 3 := by
    rw [show a * 10 + 13 = (a * 10 + 11) + 2 by omega]
    exact OdEvenMarker.minus_three_positive (a * 10 + 11)
  generalize hD_def : 2 ^ (j * 2 + 2) - 3 = D at hD hE
  generalize hE_def : 2 ^ (a * 10 + 13) - 3 = E at hEpos hE
  have hF : D * 2 ^ J < 2 ^ (j * 7 + 1) := by
    subst hD_def hJ
    have hs := OdEvenMarker.scaled_minus_three (j * 2) (j * 5 - 1)
    rwa [show j * 2 + 2 + (j * 5 - 1) = j * 7 + 1 by omega] at hs
  generalize hF_def : D * 2 ^ J = F at hF hE
  set c := T + 3
  have hc : 0 < c := by unfold c; omega
  have hcb : c < 2 ^ (a * 4 + 4) := by
    unfold c
    have h8 : 2 ^ 3 ≤ 2 ^ (a * 4 + 3) := Nat.pow_le_pow_right (by decide) (by omega)
    change 8 ≤ 2 ^ (a * 4 + 3) at h8
    rw [show a * 4 + 4 = (a * 4 + 3) + 1 by omega, Nat.pow_succ]
    omega
  by_cases hsmall : j ≤ a * 3 + 2
  · have hFsmall : F < 2 ^ (K - 3) :=
      lt_of_lt_of_le hF (Nat.pow_le_pow_right (by decide) (by omega))
    have hcsmall : c < 2 ^ (K - 3) :=
      lt_of_lt_of_le hcb (Nat.pow_le_pow_right (by decide) (by omega))
    refine MultiGapMarker.positive_subtraction_marker out A K E (c + F)
      (by omega) hEpos (Nat.add_pos_left hc F) ?_ (by linarith [hE])
    exact OdEvenMarker.sum_small K c F (by omega) hcsmall hFsmall
  · have hcJ : c < 2 ^ (J - 2) :=
      lt_of_lt_of_le hcb (Nat.pow_le_pow_right (by decide) (by omega))
    have hcK : c < 2 ^ (K - 2) :=
      lt_of_lt_of_le hcb (Nat.pow_le_pow_right (by decide) (by omega))
    rw [← hF_def] at hE
    refine MultiGapMarker.two_gap_marker out A J K D E c hD hEpos (by omega) hc ?_ hE
    by_cases hJK : J ≤ K
    · rw [Nat.min_eq_left hJK]; exact hcJ
    · rw [Nat.min_eq_right (by omega)]; exact hcK

end TightInitialMarker

/-! ## TightInitialClosure -/

namespace TightInitialClosure

theorem deficit_halved (j : ℕ) (hj : 0 < j) :
    MarkedDeficit.initial_deficit (j * 2) (j * 5) =
      MarkedDeficit.initial_deficit (j * 2) (j * 5 - 1) * 2 := by
  unfold MarkedDeficit.initial_deficit
  conv_lhs => rw [show j * 5 = (j * 5 - 1) + 1 by omega]
  rw [Nat.pow_succ 2 (j * 5 - 1)]
  ring

theorem ordinary_initial_close (L j : ℕ) (rest : List Bool) (k q w : ℕ)
    (hj : 0 < j) (hL : L = j * 7 + rest.length + 3) (hm : rest.length = w * 2 + 1)
    (hdef : k + MarkedDeficit.initial_deficit (j * 2) (j * 5) + 1 = 2 ^ L)
    (hfuel : k + 1 = 2 * (TightPrimer.demand rest + q))
    (hq : 0 < q) (hcoef : q * 4 + 3 < 2 ^ (L + 1)) :
    ∃ out, ((TerminalClosure.odd_wall L (w * 5 + 6) q) [mtm]⊢⁺ out) ∧
      StrongInvariant.strong out := by
  have hL3 : 3 ≤ L := by omega
  have hT1 : 0 < TightPrimer.demand rest := by
    unfold TightPrimer.demand
    have := CDPasses.value_bound rest
    omega
  have hT2 : TightPrimer.demand rest ≤ 2 ^ rest.length := Nat.sub_le _ _
  rcases Nat.even_or_odd' w with ⟨a, rfl | rfl⟩
  · rw [show 2 * a * 5 + 6 = (a * 5 + 3) * 2 by omega]
    obtain ⟨out, hlen, _, _, hmass, hrun⟩ :=
      TerminalSuccessor.ordinary_even_image L (a * 5 + 3) q (by omega) hcoef
    refine ⟨WallInvariant.Ed (L + (a * 5 + 3) * 7 + 3) out, hrun, .StrongEd hlen ?_⟩
    rcases hlen with hloose | htight
    · exact TerminalLoose.even_loose_marker L (a * 5 + 3) q out hL3 (by omega) hloose hmass
    · have hE := TightEquations.even_tight_equation L (a * 5 + 3) q k
        (MarkedDeficit.initial_deficit (j * 2) (j * 5)) (TightPrimer.demand rest) out
        (by omega) hT1 hdef hfuel htight hmass
      rw [← CounterBits.value_eq_cd,
        show (a * 5 + 3) * 2 = a * 10 + 6 by omega,
        show (a * 5 + 3) * 5 - 1 = a * 25 + 14 by omega,
        show L = j * 7 + a * 4 + 4 by omega] at hE
      refine TightInitialMarker.even_initial_marker out a j (TightPrimer.demand rest) hj hT1 ?_ hE
      rwa [show a * 4 + 1 = rest.length by omega]
  · rw [show (2 * a + 1) * 5 + 6 = (a * 5 + 5) * 2 + 1 by omega]
    obtain ⟨out, hlen, _, _, hmass, hrun⟩ :=
      TerminalSuccessor.ordinary_odd_image L (a * 5 + 5) q hq hcoef
    refine ⟨WallInvariant.Ed (L + (a * 5 + 5) * 7 + 9) out, hrun, .StrongEd hlen ?_⟩
    rcases hlen with hloose | htight
    · exact TerminalLoose.odd_loose_marker L (a * 5 + 5) q out hL3 hloose hmass
    · rw [deficit_halved j hj] at hdef
      have hE := TightEquations.odd_tight_equation L (a * 5 + 5) q k
        (MarkedDeficit.initial_deficit (j * 2) (j * 5 - 1)) (TightPrimer.demand rest) out
        (by omega) hdef hfuel htight hmass
      rw [← CounterBits.value_eq_cd,
        show (a * 5 + 5) * 2 + 1 = a * 10 + 11 by omega,
        show (a * 5 + 5) * 5 + 4 = a * 25 + 29 by omega,
        show L - 1 = j * 7 + a * 4 + 5 by omega] at hE
      refine TightInitialMarker.odd_initial_marker out a j (TightPrimer.demand rest) hj hT1 ?_ hE
      rwa [show a * 4 + 3 = rest.length by omega]

end TightInitialClosure

/-! ## TightDirect -/

namespace TightDirect

open CounterRules

theorem tight_direct (n : ℕ) (bs : List Bool) (v : ℕ) (tail : List Bool)
    (hn : bs.length + 2 = n) (hmark : WallInvariant.marked 1 bs)
    (hword : false :: bs = List.replicate (v * 2) false ++ true :: tail) :
    ∃ out, ((WallInvariant.Ed n bs) [mtm]⊢⁺ out) ∧ StrongInvariant.strong out := by
  have hzero : WallInvariant.first_zero (false :: bs) := ⟨bs, rfl⟩
  have hv : 0 < v := by
    rw [hword] at hzero
    have := MarkedTrace.first_zero_prefix (v * 2) tail hzero
    omega
  have hn' : n = v * 2 + tail.length + 2 := by
    have hlen := congrArg List.length hword
    simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
    omega
  set L := n + 1 + v * 5
  set k := OddFuel.grown (OddImage.first_fuel n (v * 2)) (v * 5)
  have hroute : MarkedTrace.wall_route n (false :: bs) L k tail := by
    rw [hword]
    exact .WallEven
  obtain ⟨hb, ho⟩ := MarkedTrace.route_bounds n (false :: bs) L k tail hroute hzero (by simp; omega)
  have hmin := MarkedTrace.route_margin4 n (false :: bs) L k tail hroute hzero (by simp; omega)
  have hrun : (WallInvariant.Ed n bs) [mtm]⊢⁺
      (rGate (LC L k) ([1] +> (CDPasses.third tail +> ([0, 0, 0, 1, 0, 0, 1, 0] +> default)))) := by
    rw [← TightMarked.realign]
    have hstep := TightEd.tight_Ed_step n bs hn (TightMarked.marked_true bs hmark)
    have heq : TightEd.after n bs =
        OddMarkedEntry.odd_wall n (false :: bs) ([1, 0, 0, 1, 0] +> default) := by
      unfold TightEd.after WallInvariant.wall OddMarkedEntry.odd_wall LocalPasses.lh
      simp only [append_assoc]
    rw [heq] at hstep
    exact stepPlus_trans hstep
      (MarkedTrace.route_run n (false :: bs) L k tail ([1, 0, 0, 1, 0] +> default) hroute
        (by simp; omega))
  rw [Nat.pow_add 2 tail.length 4] at hmin
  change 2 ^ tail.length * 16 - 1 ≤ k at hmin
  have hdemand : 2 * TightPrimer.demand tail ≤ k + 1 := by
    unfold TightPrimer.demand
    have := CDPasses.value_bound tail
    omega
  obtain ⟨q, hfuel, hcoef, hcases⟩ :=
    TerminalClosure.tight_counter_cases L k tail (by omega) ho hdemand
  have hq : 0 < q := by
    unfold TightPrimer.demand at hfuel
    have := pow2_pos tail.length
    omega
  rcases hcases with ⟨w, hw, hfin, _⟩ | ⟨w, hw, hfin⟩
  · exact ⟨TerminalClosure.even_wall L (w * 5 + 2) q, stepPlus_trans hrun hfin,
      TightTrace.terminal_even_strong L (w * 5 + 2) q (by omega) hcoef⟩
  · have hdef : k + MarkedDeficit.initial_deficit (v * 2) (v * 5) + 1 = 2 ^ L :=
      MarkedDeficit.initial_balance n (v * 2) (v * 5) (by omega)
    obtain ⟨out, hlast, hstrong⟩ :=
      TightInitialClosure.ordinary_initial_close L v tail k q w hv
        (by unfold L; omega) hw hdef hfuel hq hcoef
    exact ⟨out, stepPlus_trans hrun (stepPlus_trans hfin hlast), hstrong⟩

end TightDirect

/-! ## TightDeficitClass -/

namespace TightDeficitClass

def final_deficit (d v : ℕ) : ℕ := (2 * d + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5 + 1)

theorem exact_step (L k d u z : ℕ) (h : k + (2 ^ (u + 1) - 1) + d + 1 = 2 ^ L) :
    OddFuel.grown k z + (2 * d + 2 ^ (u + 2) - 1) * 2 ^ z + 1 = 2 ^ (L + 1 + z) := by
  have hE := OdDeficit.step_deficit L k d u z (by omega)
  rw [Nat.pow_succ 2 z] at hE
  have hp := pow2_pos (u + 2)
  have hz := pow2_pos z
  have hadd : (2 * d + (2 ^ (u + 2) - 1)) * 2 ^ z =
      d * (2 ^ z * 2) + (2 ^ (u + 2) - 1) * 2 ^ z := by
    ring
  rw [show 2 * d + 2 ^ (u + 2) - 1 = 2 * d + (2 ^ (u + 2) - 1) by omega, hadd]
  linarith

theorem route_final (L k : ℕ) (bs : List Bool) (L' k' : ℕ) (rest : List Bool)
    (hr : OddRoute.route L k bs L' k' rest) :
    ∀ d, DeficitResidues.pre_deficit d → k + d + 1 = 2 ^ L →
      ∃ previous v,
        DeficitResidues.pre_deficit previous ∧ k' + final_deficit previous v + 1 = 2 ^ L' := by
  induction hr with
  | @RouteEven L k v tail =>
    intro d hd hbal
    exact ⟨d, v, hd, exact_step L k d (v * 2) (v * 5 + 1) hbal⟩
  | @RouteOdd L k v tail L' k' rest _ ih =>
    intro d hd hbal
    refine ih ((2 * d + 2 ^ (v * 2 + 3) - 1) * 2 ^ (v * 5 + 4)) ?_ ?_
    · rw [Nat.mul_comm v 2, Nat.mul_comm v 5]
      exact .PreOdd d v hd
    · have hE := exact_step L k d (v * 2 + 1) (v * 5 + 4)
        (by rwa [show (v * 2 + 1) + 1 = v * 2 + 2 by omega])
      rwa [show (v * 2 + 1) + 2 = v * 2 + 3 by omega] at hE

theorem initial_odd_final (n v : ℕ) (tail : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : OddRoute.route (n + 1 + (v * 5 + 3))
      (OddFuel.grown (OddImage.first_fuel n (v * 2 + 1)) (v * 5 + 3)) tail L k rest)
    (hn : v * 2 + 2 ≤ n) :
    ∃ previous last,
      DeficitResidues.pre_deficit previous ∧ k + final_deficit previous last + 1 = 2 ^ L := by
  refine route_final _ _ tail L k rest hr ((2 ^ (v * 2 + 3) - 3) * 2 ^ (v * 5 + 3)) ?_ ?_
  · rw [Nat.mul_comm v 2, Nat.mul_comm v 5]
    exact .PreInitial v
  · have hb := MarkedDeficit.initial_balance n (v * 2 + 1) (v * 5 + 3) (by omega)
    unfold MarkedDeficit.initial_deficit at hb
    rwa [show (v * 2 + 1) + 2 = v * 2 + 3 by omega] at hb

theorem first_index_unique (u v : ℕ) (tail rest : List Bool)
    (h : List.replicate u false ++ true :: tail = List.replicate v false ++ true :: rest) :
    u = v ∧ tail = rest := by
  induction u generalizing v with
  | zero =>
    rcases v with _ | v
    · simp only [List.replicate_zero, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    · simp [List.replicate_succ] at h
  | succ u ih =>
    rcases v with _ | v
    · simp [List.replicate_succ] at h
    · simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := ih v h
      exact ⟨rfl, rfl⟩

theorem wall_odd_final (n u : ℕ) (tail : List Bool) (L k : ℕ) (rest : List Bool)
    (hr : MarkedTrace.wall_route n (List.replicate (u * 2 + 1) false ++ true :: tail) L k rest)
    (hn : u * 2 + 2 ≤ n) :
    ∃ previous last,
      DeficitResidues.pre_deficit previous ∧ k + final_deficit previous last + 1 = 2 ^ L := by
  generalize hword : List.replicate (u * 2 + 1) false ++ true :: tail = word at hr
  cases hr with
  | @WallEven v _ =>
    have := (first_index_unique (u * 2 + 1) (v * 2) tail rest hword).1
    omega
  | @WallOdd v tail' L k rest h =>
    obtain ⟨hu, rfl⟩ := first_index_unique (u * 2 + 1) (v * 2 + 1) tail tail' hword
    have hv : v = u := by omega
    subst hv
    exact initial_odd_final n v tail L k rest h hn

end TightDeficitClass

/-! ## TightRecursiveMarker -/

namespace TightRecursiveMarker

theorem positive_coefficient (b : ℕ) (hb : 2 ≤ b) : 0 < 2 ^ b - 3 := by
  have h4 : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
  change 4 ≤ 2 ^ b at h4
  omega

theorem multiple_width (v S E K A : ℕ) (hE : 0 < E) (heq : v + S + E * 2 ^ K = 2 ^ A) :
    K ≤ A := by
  by_contra hgt
  have hpow : 2 ^ A < 2 ^ K := (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega)
  have hmul : 1 * 2 ^ K ≤ E * 2 ^ K := Nat.mul_le_mul_right _ hE
  omega

theorem even_recursive_marker (out : List Bool) (a L D v T : ℕ)
    (hD : DeficitResidues.pre_deficit D) (hT : 0 < T) (hTb : T ≤ 2 ^ (a * 4 + 1))
    (hE : CounterBits.value out + (2 * T - 1) + TightDeficitClass.final_deficit D v +
      MarkedDeficit.initial_deficit (a * 10 + 6) (a * 25 + 14) = 2 ^ L) :
    WallInvariant.marked 1 out := by
  unfold MarkedDeficit.initial_deficit at hE
  rw [show a * 10 + 6 + 2 = a * 10 + 8 by omega] at hE
  generalize hK : a * 25 + 14 = K at hE
  have hcoeff : 0 < 2 ^ (a * 10 + 8) - 3 := positive_coefficient _ (by omega)
  generalize hE_def : 2 ^ (a * 10 + 8) - 3 = E at hcoeff hE
  have hc : 2 * T - 2 < 2 ^ (a * 4 + 2) := by
    rw [show a * 4 + 2 = (a * 4 + 1) + 1 by omega, Nat.pow_succ]
    omega
  obtain ⟨i, hlo, hhi, hpar, hbit⟩ :=
    DeficitWindow.final_window D v (a * 4 + 2) 1 (2 * T - 2) hD (by omega) (by omega) hc
  have hi : i < K := by omega
  have hS : 0 < TightDeficitClass.final_deficit D v + (2 * T - 1) :=
    Nat.add_pos_right _ (by omega)
  have hSbit : (TightDeficitClass.final_deficit D v + (2 * T - 1)) - 1 =
      (2 * D + 2 ^ (2 * v + 2) - 1) * 2 ^ (5 * v + 1) + (2 * T - 2) := by
    unfold TightDeficitClass.final_deficit
    rw [Nat.mul_comm v 2, Nat.mul_comm v 5]
    generalize (2 * D + 2 ^ (2 * v + 2) - 1) * 2 ^ (5 * v + 1) = G
    omega
  generalize hS_def : TightDeficitClass.final_deficit D v + (2 * T - 1) = S at hS hSbit
  have hE' : CounterBits.value out + S + E * 2 ^ K = 2 ^ L := by linarith [hE, hS_def]
  have hwidth := multiple_width (CounterBits.value out) S E K L hcoeff hE'
  refine ZeroComplement.zero_complement_multiple out L K E S i
    hS (by omega) hi hpar ?_ hE'
  rw [hSbit]
  exact hbit

theorem odd_recursive_marker (out : List Bool) (a L D v T : ℕ)
    (hD : DeficitResidues.pre_deficit D) (hT : 0 < T) (hTb : T ≤ 2 ^ (a * 4 + 3))
    (hE : CounterBits.value out + (T + 3) + (2 * D + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5) +
      MarkedDeficit.initial_deficit (a * 10 + 11) (a * 25 + 29) = 2 ^ L) :
    WallInvariant.marked 1 out := by
  unfold MarkedDeficit.initial_deficit at hE
  rw [show a * 10 + 11 + 2 = a * 10 + 13 by omega] at hE
  generalize hK : a * 25 + 29 = K at hE
  have hcoeff : 0 < 2 ^ (a * 10 + 13) - 3 := positive_coefficient _ (by omega)
  generalize hE_def : 2 ^ (a * 10 + 13) - 3 = E at hcoeff hE
  have hc : T + 2 < 2 ^ (a * 4 + 4) := by
    have h8 : 2 ^ 3 ≤ 2 ^ (a * 4 + 3) := Nat.pow_le_pow_right (by decide) (by omega)
    change 8 ≤ 2 ^ (a * 4 + 3) at h8
    rw [show a * 4 + 4 = (a * 4 + 3) + 1 by omega, Nat.pow_succ]
    omega
  obtain ⟨i, hlo, hhi, hpar, hbit⟩ :=
    DeficitWindow.half_window D v (a * 4 + 4) 1 (T + 2) hD (by omega) (by omega) hc
  have hi : i < K := by omega
  have hS : 0 < (2 * D + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5) + (T + 3) :=
    Nat.add_pos_right _ (by omega)
  have hSbit : ((2 * D + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5) + (T + 3)) - 1 =
      (2 * D + 2 ^ (2 * v + 2) - 1) * 2 ^ (5 * v) + (T + 2) := by
    rw [Nat.mul_comm v 2, Nat.mul_comm v 5]
    generalize (2 * D + 2 ^ (2 * v + 2) - 1) * 2 ^ (5 * v) = G
    omega
  generalize hS_def : (2 * D + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5) + (T + 3) = S at hS hSbit
  have hE' : CounterBits.value out + S + E * 2 ^ K = 2 ^ L := by linarith [hE, hS_def]
  have hwidth := multiple_width (CounterBits.value out) S E K L hcoeff hE'
  refine ZeroComplement.zero_complement_multiple out L K E S i
    hS (by omega) hi hpar ?_ hE'
  rw [hSbit]
  exact hbit

end TightRecursiveMarker

/-! ## TightRecursiveClosure -/

namespace TightRecursiveClosure

theorem final_halved (d v : ℕ) :
    TightDeficitClass.final_deficit d v = ((2 * d + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5)) * 2 := by
  unfold TightDeficitClass.final_deficit
  rw [Nat.pow_succ 2 (v * 5)]
  ring

theorem ordinary_recursive_close (L d v : ℕ) (rest : List Bool) (k q w : ℕ)
    (hL : 3 ≤ L) (hd : DeficitResidues.pre_deficit d) (hm : rest.length = w * 2 + 1)
    (hdef : k + TightDeficitClass.final_deficit d v + 1 = 2 ^ L)
    (hfuel : k + 1 = 2 * (TightPrimer.demand rest + q))
    (hq : 0 < q) (hcoef : q * 4 + 3 < 2 ^ (L + 1)) :
    ∃ out, ((TerminalClosure.odd_wall L (w * 5 + 6) q) [mtm]⊢⁺ out) ∧
      StrongInvariant.strong out := by
  have hT1 : 0 < TightPrimer.demand rest := by
    unfold TightPrimer.demand
    have := CDPasses.value_bound rest
    omega
  have hT2 : TightPrimer.demand rest ≤ 2 ^ rest.length := Nat.sub_le _ _
  rcases Nat.even_or_odd' w with ⟨a, rfl | rfl⟩
  · rw [show 2 * a * 5 + 6 = (a * 5 + 3) * 2 by omega]
    obtain ⟨out, hlen, _, _, hmass, hrun⟩ :=
      TerminalSuccessor.ordinary_even_image L (a * 5 + 3) q (by omega) hcoef
    refine ⟨WallInvariant.Ed (L + (a * 5 + 3) * 7 + 3) out, hrun, .StrongEd hlen ?_⟩
    rcases hlen with hloose | htight
    · exact TerminalLoose.even_loose_marker L (a * 5 + 3) q out hL (by omega) hloose hmass
    · have hE := TightEquations.even_tight_equation L (a * 5 + 3) q k
        (TightDeficitClass.final_deficit d v) (TightPrimer.demand rest) out
        (by omega) hT1 hdef hfuel htight hmass
      rw [← CounterBits.value_eq_cd,
        show (a * 5 + 3) * 2 = a * 10 + 6 by omega,
        show (a * 5 + 3) * 5 - 1 = a * 25 + 14 by omega] at hE
      refine TightRecursiveMarker.even_recursive_marker out a L d v (TightPrimer.demand rest)
        hd hT1 ?_ hE
      rwa [show a * 4 + 1 = rest.length by omega]
  · rw [show (2 * a + 1) * 5 + 6 = (a * 5 + 5) * 2 + 1 by omega]
    obtain ⟨out, hlen, _, _, hmass, hrun⟩ :=
      TerminalSuccessor.ordinary_odd_image L (a * 5 + 5) q hq hcoef
    refine ⟨WallInvariant.Ed (L + (a * 5 + 5) * 7 + 9) out, hrun, .StrongEd hlen ?_⟩
    rcases hlen with hloose | htight
    · exact TerminalLoose.odd_loose_marker L (a * 5 + 5) q out hL hloose hmass
    · rw [final_halved] at hdef
      have hE := TightEquations.odd_tight_equation L (a * 5 + 5) q k
        ((2 * d + 2 ^ (v * 2 + 2) - 1) * 2 ^ (v * 5)) (TightPrimer.demand rest) out
        (by omega) hdef hfuel htight hmass
      rw [← CounterBits.value_eq_cd,
        show (a * 5 + 5) * 2 + 1 = a * 10 + 11 by omega,
        show (a * 5 + 5) * 5 + 4 = a * 25 + 29 by omega] at hE
      refine TightRecursiveMarker.odd_recursive_marker out a (L - 1) d v (TightPrimer.demand rest)
        hd hT1 ?_ hE
      rwa [show a * 4 + 3 = rest.length by omega]

end TightRecursiveClosure

/-! ## TightStrong -/

namespace TightStrong

theorem tight_strong (n : ℕ) (bs : List Bool)
    (hn : bs.length + 2 = n) (hmark : WallInvariant.marked 1 bs) :
    ∃ out, ((WallInvariant.Ed n bs) [mtm]⊢⁺ out) ∧ StrongInvariant.strong out := by
  obtain ⟨L, k, rest, j, q, hroute, hlen, hL, hb, hmin, hfuel, hq, hcoef, hcases⟩ :=
    TightTrace.tight_cases n bs hn hmark
  rcases hcases with ⟨w, _, hrun, hstrong⟩ | ⟨w, hw, hrun⟩
  · exact ⟨_, hrun, hstrong⟩
  · obtain ⟨u, tail, hword⟩ :=
      OddRoute.first_true (false :: bs) (OddRoute.marked_true _ (TightMarked.marked_false bs hmark))
    rcases Nat.even_or_odd' u with ⟨v, rfl | rfl⟩
    · rw [Nat.mul_comm 2 v] at hword
      exact TightDirect.tight_direct n bs v tail hn hmark hword
    · rw [show 2 * v + 1 = v * 2 + 1 by omega] at hword
      have hroute' : MarkedTrace.wall_route n (List.replicate (v * 2 + 1) false ++ true :: tail)
          L k rest := by rwa [← hword]
      have hcap : v * 2 + 2 ≤ n := by
        have hlen' := congrArg List.length hword
        simp only [List.length_append, List.length_replicate, List.length_cons] at hlen'
        omega
      obtain ⟨d, last, hd, hbal⟩ :=
        TightDeficitClass.wall_odd_final n v tail L k rest hroute' hcap
      obtain ⟨out, hlast, hstrong⟩ :=
        TightRecursiveClosure.ordinary_recursive_close L d last rest k q w
          (by omega) hd hw hbal hfuel hq hcoef
      exact ⟨out, stepPlus_trans hrun hlast, hstrong⟩

end TightStrong

/-! ## StrongClosure & Public Theorem -/

namespace StrongClosure

theorem strong_progress (c : Cfg Γ Λ) (h : StrongInvariant.strong c) :
    ∃ c', (c [mtm]⊢⁺ c') ∧ StrongInvariant.strong c' := by
  rcases h with ⟨h1, h2⟩ | ⟨hslack, hmarker⟩
  · exact StrongE.strong_E _ _ h1 h2
  · rcases hslack with hloose | htight
    · exact StrongEdLoose.strong_ed_loose _ _ hloose hmarker
    · exact TightStrong.tight_strong _ _ htight hmarker

end StrongClosure

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := StrongEntry.closure_nonhalt
  StrongClosure.strong_progress


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC
