/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RA---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 1 = step M c := rfl

@[simp] lemma multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  simp only [multiStep, Function.iterate_succ_apply']

lemma multiStep_add (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) :
    c₁ [M]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

@[simp] lemma pow_zero_list (u : List (Fin 2)) : u ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
@[simp] lemma nil_append_list (l : List (Fin 2)) : ([] : List (Fin 2)) ++ l = l := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

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

lemma multiStep_step_isSome {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₀ cfg cfg' : Cfg Γ Λ) (n m : Nat)
    (hn : multiStep M c₀ n = some cfg)
    (hnm : multiStep M c₀ (n + (1 + m)) = some cfg') :
    (step M cfg).isSome := by
  rw [multiStep_add M c₀ n (1 + m), hn] at hnm
  dsimp [Option.bind] at hnm
  rw [multiStep_add M cfg 1 m, multiStep_one] at hnm
  cases hs : step M cfg with
  | none =>
    rw [hs] at hnm
    nomatch hnm
  | some c₁ => rfl

lemma inv_reaches_beyond {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ cfg₀, ((init []) [M]⊢* cfg₀) ∧ Inv cfg₀)
    (h_step : ∀ cfg, Inv cfg → ∃ cfg', (cfg [M]⊢⁺ cfg') ∧ Inv cfg')
    (N : Nat) :
    ∃ (m : Nat) (cfg' : Cfg Γ Λ), multiStep M (init []) (N + m) = some cfg' ∧ Inv cfg' := by
  induction N with
  | zero =>
    obtain ⟨cfg₀, ⟨n₀, hn₀⟩, h_inv₀⟩ := h_init
    refine ⟨n₀, cfg₀, ?_, h_inv₀⟩
    rwa [Nat.zero_add]
  | succ N ih =>
    obtain ⟨m, cfg₁, hm, h_inv₁⟩ := ih
    cases m with
    | zero =>
      obtain ⟨cfg₂, ⟨k, hk_pos, hk⟩, h_inv₂⟩ := h_step cfg₁ h_inv₁
      cases k with
      | zero => omega
      | succ k' =>
        refine ⟨k', cfg₂, ?_, h_inv₂⟩
        have h_trans := multiStep_trans M (init []) cfg₁ cfg₂ N (k' + 1) hm hk
        have h_eq : (N + 1) + k' = N + (k' + 1) := by omega
        rwa [h_eq]
    | succ m' =>
      refine ⟨m', cfg₁, ?_, h_inv₁⟩
      have h_eq : (N + 1) + m' = N + (m' + 1) := by omega
      rwa [h_eq]

theorem closed_inv_does_not_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ cfg₀, ((init []) [M]⊢* cfg₀) ∧ Inv cfg₀)
    (h_step : ∀ cfg, Inv cfg → ∃ cfg', (cfg [M]⊢⁺ cfg') ∧ Inv cfg') :
    IsNotHalt M := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, cfg', hnm, _⟩ := inv_reaches_beyond M Inv h_init h_step (n + 1)
  have h_eq : (n + 1) + m = n + (1 + m) := by omega
  rw [h_eq] at hnm
  exact multiStep_step_isSome M (init []) cfg cfg' n m hn hnm

def B00 (m l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l <{{C}} ([0, 0] +> m)

def F11 (m l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ([1, 1] +> l) {{A}}> m

def A0 (m l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((0 : Fin 2) >> l) {{B}}> m

lemma rule_B00_111 (m l : ListBlank (Fin 2)) :
    (B00 m ([1, 1, 1] +> l)) [target_tm]⊢⁺ (B00 ([0, 0, 0] +> m) l) := by
  dsimp [B00, ListBlank.append]; execute

lemma rule_B00_011 (m l : ListBlank (Fin 2)) :
    (B00 m ([0, 1, 1] +> l)) [target_tm]⊢⁺ (B00 ([1, 1, 0] +> m) l) := by
  dsimp [B00, ListBlank.append]; execute

lemma rule_B00_00 (m l : ListBlank (Fin 2)) :
    (B00 m ([0, 0] +> l)) [target_tm]⊢⁺ (A0 m ([0, 1, 1] +> l)) := by
  dsimp [B00, A0, ListBlank.append]; execute

lemma rule_B00_nil (m : ListBlank (Fin 2)) :
    (B00 m default) [target_tm]⊢⁺ (A0 m ([0, 1, 1] +> default)) := by
  dsimp [B00, A0, ListBlank.append]; execute

lemma rule_F11_000 (m l : ListBlank (Fin 2)) :
    (F11 ([0, 0, 0] +> m) l) [target_tm]⊢⁺ (B00 ([0, 1, 0] +> m) l) := by
  dsimp [F11, B00, ListBlank.append]; execute

lemma rule_F11_010 (m l : ListBlank (Fin 2)) :
    (F11 ([0, 1, 0] +> m) l) [target_tm]⊢⁺ (F11 m ([1, 1, 1] +> l)) := by
  dsimp [F11, ListBlank.append]; execute

lemma rule_F11_110 (m l : ListBlank (Fin 2)) :
    (F11 ([1, 1, 0] +> m) l) [target_tm]⊢⁺ (F11 m ([0, 1, 1] +> l)) := by
  dsimp [F11, ListBlank.append]; execute

lemma rule_F11_01 (m l : ListBlank (Fin 2)) :
    (F11 ([0, 1] +> m) l) [target_tm]⊢⁺ (A0 m ([1, 1, 1] +> l)) := by
  dsimp [F11, A0, ListBlank.append]; execute

lemma rule_A0_000 (m l : ListBlank (Fin 2)) :
    (A0 ([0, 0, 0] +> m) l) [target_tm]⊢⁺ (B00 ([0, 1] +> m) l) := by
  dsimp [A0, B00, ListBlank.append]; execute

lemma rule_A0_010 (m l : ListBlank (Fin 2)) :
    (A0 ([0, 1, 0] +> m) l) [target_tm]⊢⁺ (A0 m ([0, 1, 1] +> l)) := by
  dsimp [A0, ListBlank.append]; execute

lemma rule_A0_110 (m l : ListBlank (Fin 2)) :
    (A0 ([1, 1, 0] +> m) l) [target_tm]⊢⁺ (F11 m ([0, 0] +> l)) := by
  dsimp [A0, F11, ListBlank.append]; execute

abbrev RoundF (m m' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2), (F11 m l) [target_tm]⊢⁺ (B00 m' l)

abbrev RoundA (m m' : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2), (A0 m l) [target_tm]⊢⁺ (B00 m' l)

lemma roundF_000 (m : ListBlank (Fin 2)) :
    RoundF ([0, 0, 0] +> m) ([0, 1, 0] +> m) :=
  fun l => rule_F11_000 m l

lemma roundF_010 {m m' : ListBlank (Fin 2)} (h : RoundF m m') :
    RoundF ([0, 1, 0] +> m) ([0, 0, 0] +> m') :=
  fun l => stepPlus_trans (rule_F11_010 m l) (stepPlus_trans (h ([1, 1, 1] +> l)) (rule_B00_111 m' l))

lemma roundF_110 {m m' : ListBlank (Fin 2)} (h : RoundF m m') :
    RoundF ([1, 1, 0] +> m) ([1, 1, 0] +> m') :=
  fun l => stepPlus_trans (rule_F11_110 m l) (stepPlus_trans (h ([0, 1, 1] +> l)) (rule_B00_011 m' l))

lemma roundF_01 {m m' : ListBlank (Fin 2)} (h : RoundA m m') :
    RoundF ([0, 1] +> m) ([0, 0, 0] +> m') :=
  fun l => stepPlus_trans (rule_F11_01 m l) (stepPlus_trans (h ([1, 1, 1] +> l)) (rule_B00_111 m' l))

lemma roundA_000 (m : ListBlank (Fin 2)) :
    RoundA ([0, 0, 0] +> m) ([0, 1] +> m) :=
  fun l => rule_A0_000 m l

lemma roundA_010 {m m' : ListBlank (Fin 2)} (h : RoundA m m') :
    RoundA ([0, 1, 0] +> m) ([1, 1, 0] +> m') :=
  fun l => stepPlus_trans (rule_A0_010 m l) (stepPlus_trans (h ([0, 1, 1] +> l)) (rule_B00_011 m' l))

lemma roundA_110 {m m₁ m₂ : ListBlank (Fin 2)} (h₁ : RoundF m m₁) (h₂ : RoundA m₁ m₂) :
    RoundA ([1, 1, 0] +> m) ([1, 1, 0] +> m₂) :=
  fun l => stepPlus_trans (rule_A0_110 m l)
    (stepPlus_trans (h₁ ([0, 0] +> l))
      (stepPlus_trans (rule_B00_00 m₁ l)
        (stepPlus_trans (h₂ ([0, 1, 1] +> l)) (rule_B00_011 m₂ l))))

inductive SweepsF : Nat → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | zero (r : ListBlank (Fin 2)) : SweepsF 0 r r
  | succ {n : Nat} {r r₁ r₂ : ListBlank (Fin 2)} :
      RoundF r r₁ → SweepsF n r₁ r₂ → SweepsF (n + 1) r r₂

lemma SweepsF.trans {a b : Nat} {r₁ r₂ r₃ : ListBlank (Fin 2)}
    (h₁ : SweepsF a r₁ r₂) (h₂ : SweepsF b r₂ r₃) : SweepsF (a + b) r₁ r₃ := by
  induction h₁ with
  | zero _ => simpa using h₂
  | succ hr _ ih =>
    rw [Nat.succ_add]
    exact SweepsF.succ hr (ih h₂)

lemma sweepsF_split_last {n : Nat} {r r' : ListBlank (Fin 2)} (h : SweepsF (n + 1) r r') :
    ∃ r₁ : ListBlank (Fin 2), SweepsF n r r₁ ∧ RoundF r₁ r' := by
  induction n generalizing r with
  | zero =>
    cases h with
    | succ hr h0 =>
      cases h0 with
      | zero _ => exact ⟨r, SweepsF.zero r, hr⟩
  | succ m ih =>
    cases h with
    | succ hr hs =>
      obtain ⟨r₁, hs₁, hr₁⟩ := ih hs
      exact ⟨r₁, SweepsF.succ hr hs₁, hr₁⟩

lemma sweepsF_110 {n : Nat} {r r' : ListBlank (Fin 2)} (h : SweepsF n r r') :
    SweepsF n ([1, 1, 0] +> r) ([1, 1, 0] +> r') := by
  induction h with
  | zero r => exact SweepsF.zero _
  | succ hr _ ih => exact SweepsF.succ (roundF_110 hr) ih

lemma sweepsF_000_even {k : Nat} {r r' : ListBlank (Fin 2)} (h : SweepsF k r r') :
    SweepsF (2 * k) ([0, 0, 0] +> r) ([0, 0, 0] +> r') := by
  induction h with
  | zero r => exact SweepsF.zero _
  | @succ m r₀ r₁ r₂ hr _ ih =>
    have h2 : SweepsF 2 ([0, 0, 0] +> r₀) ([0, 0, 0] +> r₁) :=
      SweepsF.succ (roundF_000 r₀) (SweepsF.succ (roundF_010 hr) (SweepsF.zero _))
    have htr := SweepsF.trans h2 ih
    rw [show 2 + 2 * m = 2 * (m + 1) by omega] at htr
    exact htr

lemma sweepsF_000_odd {k : Nat} {r r' : ListBlank (Fin 2)} (h : SweepsF k r r') :
    SweepsF (2 * k + 1) ([0, 0, 0] +> r) ([0, 1, 0] +> r') := by
  have he := sweepsF_000_even h
  have h1 : SweepsF 1 ([0, 0, 0] +> r') ([0, 1, 0] +> r') :=
    SweepsF.succ (roundF_000 r') (SweepsF.zero _)
  exact SweepsF.trans he h1

def SweepsFA (n : Nat) (r r' : ListBlank (Fin 2)) : Prop :=
  ∃ r₁ : ListBlank (Fin 2), SweepsF n r r₁ ∧ RoundA r₁ r'

lemma sweepsFA_succ {n : Nat} {r r₁ r₂ : ListBlank (Fin 2)}
    (hr : RoundF r r₁) (hs : SweepsFA n r₁ r₂) : SweepsFA (n + 1) r r₂ := by
  obtain ⟨r_m, hs_m, ha⟩ := hs
  exact ⟨r_m, SweepsF.succ hr hs_m, ha⟩

lemma sweepsFA_110 {n : Nat} {r r' : ListBlank (Fin 2)} (h : SweepsFA (n + 1) r r') :
    SweepsFA n ([1, 1, 0] +> r) ([1, 1, 0] +> r') := by
  obtain ⟨r₁, hs, ha⟩ := h
  obtain ⟨r₀, hs₀, hr₀⟩ := sweepsF_split_last hs
  exact ⟨[1, 1, 0] +> r₀, sweepsF_110 hs₀, roundA_110 hr₀ ha⟩

lemma sweepsFA_000_odd {k : Nat} {r r' : ListBlank (Fin 2)} (h : SweepsFA k r r') :
    SweepsFA (2 * k + 1) ([0, 0, 0] +> r) ([1, 1, 0] +> r') := by
  obtain ⟨r₁, hs, ha⟩ := h
  exact ⟨[0, 1, 0] +> r₁, sweepsF_000_odd hs, roundA_010 ha⟩

lemma sweepsFA_000_even {k : Nat} {r r_m : ListBlank (Fin 2)} (hs : SweepsF k r r_m) :
    SweepsFA (2 * k) ([0, 0, 0] +> r) ([0, 1] +> r_m) :=
  ⟨[0, 0, 0] +> r_m, sweepsF_000_even hs, roundA_000 r_m⟩

lemma default_eq_b000 :
    (default : ListBlank (Fin 2)) = [0, 0, 0] +> default := by
  simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]

lemma b01_default_eq :
    ([0, 1] +> default : ListBlank (Fin 2)) = [0, 1, 0] +> default := by
  simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]

lemma roundA_default :
    RoundA default ([0, 1] +> default) := by
  have h := roundA_000 default
  rwa [← default_eq_b000] at h

inductive Valid : Nat → ListBlank (Fin 2) → Prop
  | bot (n : Nat) :
      Valid n ([0, 1] +> default)
  | t_110 {n : Nat} {r : ListBlank (Fin 2)} (hr : Valid (n + 1) r) :
      Valid n ([1, 1, 0] +> r)
  | t_01 {n : Nat} {r_k r₁ : ListBlank (Fin 2)} (hn : n ≥ 1)
      (hround : RoundA r_k r₁) (hr : Valid ((n - 1) / 2) r₁) :
      Valid n ([0, 1] +> r_k)

lemma Valid.mono {n : Nat} {r : ListBlank (Fin 2)} (h : Valid n r) {n' : Nat} (hle : n ≤ n') :
    Valid n' r := by
  induction h generalizing n' with
  | bot _ => exact Valid.bot n'
  | t_110 _ ih => exact Valid.t_110 (ih (by omega))
  | t_01 hn hround _ ih => exact Valid.t_01 (by omega) hround (ih (by omega))

lemma valid_sweeps_bot : ∀ n : Nat,
    ∃ r' : ListBlank (Fin 2), Valid n r' ∧ SweepsFA n ([0, 1] +> default) r' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases (by omega : n = 0 ∨ (n ≥ 1 ∧ (n - 1) % 2 = 1) ∨ (n ≥ 1 ∧ (n - 1) % 2 = 0)) with rfl | ⟨hn1, hod⟩ | ⟨hn1, hev⟩
    · refine ⟨[1, 1, 0] +> ([0, 1] +> default), Valid.t_110 (Valid.bot 1), ?_⟩
      refine ⟨[0, 1] +> default, SweepsF.zero _, ?_⟩
      have h0 := roundA_010 roundA_default
      rwa [← b01_default_eq] at h0
    · obtain ⟨r₂, hr₂, hs₂⟩ := ih ((n - 1) / 2) (by omega)
      refine ⟨[1, 1, 0] +> r₂, Valid.t_110 (hr₂.mono (by omega)), ?_⟩
      have hs_odd := sweepsFA_000_odd hs₂
      rw [show 2 * ((n - 1) / 2) + 1 = n - 1 by omega] at hs_odd
      have hs_all := sweepsFA_succ (roundF_01 roundA_default) hs_odd
      rwa [show (n - 1) + 1 = n by omega] at hs_all
    · obtain ⟨r₂, hr₂, hs₂⟩ := ih ((n - 1) / 2) (by omega)
      obtain ⟨r_m, hs_m, hround₂⟩ := hs₂
      refine ⟨[0, 1] +> r_m, Valid.t_01 hn1 hround₂ hr₂, ?_⟩
      have hs_even := sweepsFA_000_even hs_m
      rw [show 2 * ((n - 1) / 2) = n - 1 by omega] at hs_even
      have hs_all := sweepsFA_succ (roundF_01 roundA_default) hs_even
      rwa [show (n - 1) + 1 = n by omega] at hs_all

lemma valid_sweeps {n : Nat} {r : ListBlank (Fin 2)} (h : Valid n r) :
    ∃ r' : ListBlank (Fin 2), Valid n r' ∧ SweepsFA n r r' := by
  induction h with
  | bot n => exact valid_sweeps_bot n
  | t_110 _ ih =>
    obtain ⟨r', hr', hs'⟩ := ih
    exact ⟨[1, 1, 0] +> r', Valid.t_110 hr', sweepsFA_110 hs'⟩
  | @t_01 n r_k r₁ hn hround _ ih =>
    obtain ⟨r₂, hr₂, hs₂⟩ := ih
    rcases (by omega : (n - 1) % 2 = 1 ∨ (n - 1) % 2 = 0) with hod | hev
    · refine ⟨[1, 1, 0] +> r₂, Valid.t_110 (hr₂.mono (by omega)), ?_⟩
      have hs_odd := sweepsFA_000_odd hs₂
      rw [show 2 * ((n - 1) / 2) + 1 = n - 1 by omega] at hs_odd
      have hs_all := sweepsFA_succ (roundF_01 hround) hs_odd
      rwa [show (n - 1) + 1 = n by omega] at hs_all
    · obtain ⟨r_m, hs_m, hround₂⟩ := hs₂
      refine ⟨[0, 1] +> r_m, Valid.t_01 hn hround₂ hr₂, ?_⟩
      have hs_even := sweepsFA_000_even hs_m
      rw [show 2 * ((n - 1) / 2) = n - 1 by omega] at hs_even
      have hs_all := sweepsFA_succ (roundF_01 hround) hs_even
      rwa [show (n - 1) + 1 = n by omega] at hs_all

lemma era_step {r : ListBlank (Fin 2)} (h : Valid 0 r) :
    ∃ r' : ListBlank (Fin 2), Valid 0 r' ∧ ((B00 r default) [target_tm]⊢⁺ (B00 r' default)) := by
  obtain ⟨r', hr', hs'⟩ := valid_sweeps h
  obtain ⟨r₁, hs₁, ha⟩ := hs'
  cases hs₁ with
  | zero _ =>
    refine ⟨[1, 1, 0] +> r', Valid.t_110 (hr'.mono (by omega)), ?_⟩
    exact stepPlus_trans (rule_B00_nil r)
      (stepPlus_trans (ha ([0, 1, 1] +> default)) (rule_B00_011 r' default))

def era0_m : ListBlank (Fin 2) :=
  [1, 1, 0] +> ([0, 1] +> default)

lemma init_reaches_era0 :
    (init []) [target_tm]⊢* (B00 era0_m default) := by
  apply stepPlus_stepStar
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  dsimp [era0_m, B00, ListBlank.append]
  execute

end Solution

open Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine closed_inv_does_not_halt target_tm
    (fun cfg => ∃ r : ListBlank (Fin 2), Valid 0 r ∧ cfg = B00 r default)
    ⟨B00 era0_m default, init_reaches_era0, ⟨era0_m, Valid.t_110 (Valid.bot 1), rfl⟩⟩ ?_
  intro cfg ⟨r, hr, hcfg⟩
  subst hcfg
  obtain ⟨r', hr', hstep⟩ := era_step hr
  exact ⟨B00 r' default, hstep, ⟨r', hr', rfl⟩⟩

end BusyBeaver.M_1RB1RD_1LC0RB_0RD0LC_1LB0LE_1RF0RE_1RAHHH
