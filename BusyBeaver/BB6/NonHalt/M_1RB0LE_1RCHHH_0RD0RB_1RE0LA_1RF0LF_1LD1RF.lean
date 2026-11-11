/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Longitudinal
import BusyBeaver.Calculi.SegCount
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0LE_1RCHHH_0RD0RB_1RE0LA_1RF0LF_1LD1RF

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1RCHHH_0RD0RB_1RE0LA_1RF0LF_1LD1RF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace SegCount

open BusyBeaver.Longitudinal

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

export BusyBeaver.SegCount (runSteps runSteps_spec)

inductive BDigit where
  | BA
  | BB
  deriving DecidableEq, Repr

open BDigit

def digit_word (A8 B8 : List Γ) : BDigit → List Γ
  | BA => A8
  | BB => B8

def digits_word (A8 B8 : List Γ) : List BDigit → List Γ
  | [] => []
  | d :: ds' => digit_word A8 B8 d ++ digits_word A8 B8 ds'

def digits_value : List BDigit → ℕ
  | [] => 0
  | BA :: ds' => 2 * digits_value ds'
  | BB :: ds' => 1 + 2 * digits_value ds'

def bfinish_count : List BDigit → ℕ → ℕ
  | [], out => out
  | BA :: ds', out => 2 * bfinish_count ds' out + 1
  | BB :: ds', out => 2 * bfinish_count ds' out

omit [Inhabited Γ] [Inhabited Λ] in
theorem bfinish_repeat_BA_formula (w out : ℕ) :
    bfinish_count (List.replicate w BA) out = (out + 1) * 2 ^ w - 1 := by
  induction w with
  | zero =>
    simp [bfinish_count]
  | succ w ih =>
    simp only [List.replicate_succ, bfinish_count, ih, Nat.pow_succ]
    have hpos : 1 ≤ (out + 1) * 2 ^ w := Nat.mul_pos (by omega) Nat.one_le_two_pow
    have hmul : (out + 1) * (2 ^ w * 2) = 2 * ((out + 1) * 2 ^ w) := by ring
    omega

theorem bfinish_spec {M : Machine Γ Λ} {hashes : List (DH0 Γ Λ × DH0 Γ Λ)} {A8 B8 : List Γ}
    (hash_A_finish : ∀ k, SegRLs M (hashes ^ (2 * k + 1)) (hashes ^ k) A8 B8)
    (hash_B_finish : ∀ k, SegRLs M (hashes ^ (2 * k)) (hashes ^ k) B8 B8)
    (ds : List BDigit) (out : ℕ) :
    SegRLs M (hashes ^ (bfinish_count ds out)) (hashes ^ out)
      (digits_word A8 B8 ds) (B8 ^ ds.length) := by
  induction ds generalizing out with
  | nil =>
    exact SegRLs.empty M (hashes ^ out)
  | cons d ds ih =>
    rw [List.length_cons, pow_succ_list B8 ds.length]
    rcases d with _ | _
    · exact (hash_A_finish (bfinish_count ds out)).concat (ih out)
    · exact (hash_B_finish (bfinish_count ds out)).concat (ih out)

end SegCount

section

open BusyBeaver.SixState BusyBeaver.Longitudinal SegCount

set_option maxRecDepth 100000

-- ============================================================================
-- 1. Symmetry Reduction (`target_tm` -> `source_tm = SOBCv10.tm` at `default {{D}}> default`)
-- ============================================================================

/-- `SOBCv10.tm` (`1LB0RD_1LC0RC_1RA1LC_1LE0RB_1LF---_0LA0LE`). -/
def source_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => none
  | 5, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

/-- State permutation `phi` mapping `flipTM target_tm` to `source_tm` (`PR_SOBCv10.v` line 2892). -/
def phi : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2

def mapFlipCfg_12 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map phi, ⟨c.tape.head, c.tape.right, c.tape.left⟩⟩

theorem step_mapFlipCfg_12 (c : Cfg (Fin 2) (Fin 6)) :
    step source_tm (mapFlipCfg_12 c) = (step target_tm c).map mapFlipCfg_12 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    (try rfl) <;>
    omega

theorem multiStep_mapFlipCfg_12 (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep source_tm (mapFlipCfg_12 c) n = (multiStep target_tm c n).map mapFlipCfg_12 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [BusyBeaver.multiStep_succ', BusyBeaver.multiStep_succ', ih]
    rcases multiStep target_tm c n with _ | c'
    · rfl
    · exact step_mapFlipCfg_12 c'

theorem neverHaltsFrom_of_mapFlipCfg_12 {c₀ : Cfg (Fin 2) (Fin 6)}
    (h : NeverHaltsFrom source_tm (mapFlipCfg_12 c₀)) : NeverHaltsFrom target_tm c₀ := by
  intro cfg ⟨n, hn⟩
  have hm : (mapFlipCfg_12 c₀) [source_tm]⊢* (mapFlipCfg_12 cfg) := by
    refine ⟨n, ?_⟩
    rw [multiStep_mapFlipCfg_12, hn]
    rfl
  have hstep := h (mapFlipCfg_12 cfg) hm
  rcases hst : step target_tm cfg with _ | c'
  · rw [step_mapFlipCfg_12, hst] at hstep
    cases hstep
  · rfl

theorem neverHaltsFrom_of_reachesStar {M : Machine (Fin 2) (Fin 6)} {c₁ c₀ : Cfg (Fin 2) (Fin 6)}
    (hinit : c₁ [M]⊢* c₀) (h_never : NeverHaltsFrom M c₀) : NeverHaltsFrom M c₁ := by
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M c₁ k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, BusyBeaver.multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never cfg ⟨k - k₀, hk⟩

-- ============================================================================
-- 2. Bounded Stepping Helpers (`runSteps`, `run_r0inf`, `check_r0inf`)
-- ============================================================================

theorem run1Steps_spec (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (x x' : BoundedConfig.BCfg (Fin 2) (Fin 6))
    (h : runSteps M (n + 1) x = x') (hneq : x ≠ x') (l₀ r₀ : ListBlank (Fin 2)) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢⁺ (BoundedConfig.toCfg x' l₀ r₀) := by
  dsimp [runSteps] at h
  rcases hstep : BoundedConfig.step M x with _ | y <;> rw [hstep] at h
  · exact False.elim (hneq h)
  · exact stepPlus_stepStar_trans ⟨1, by decide, BoundedConfig.step_spec M x hstep l₀ r₀⟩
      (runSteps_spec M n y x' h l₀ r₀)

def run_r0inf (M : Machine (Fin 2) (Fin 6)) : ℕ → BoundedConfig.BCfg (Fin 2) (Fin 6) →
    Option (BoundedConfig.BCfg (Fin 2) (Fin 6))
  | 0, x => some x
  | n + 1, x =>
    match BoundedConfig.step_r0inf M x with
    | none => none
    | some x' => run_r0inf M n x'

theorem run_r0inf_spec (M : Machine (Fin 2) (Fin 6)) :
    ∀ (n : ℕ) (x x' : BoundedConfig.BCfg (Fin 2) (Fin 6)),
      run_r0inf M n x = some x' →
      ∀ l₀ : ListBlank (Fin 2),
        (BoundedConfig.toCfg x l₀ default) [M]⊢* (BoundedConfig.toCfg x' l₀ default)
  | 0, x, x', h, l₀ => by cases h; exact ⟨0, rfl⟩
  | n + 1, x, x', h, l₀ => by
    dsimp [run_r0inf] at h
    rcases hstep : BoundedConfig.step_r0inf M x with _ | y <;> rw [hstep] at h
    · cases h
    · exact stepStar_trans ⟨1, BoundedConfig.step_r0inf_spec M x hstep l₀⟩
        (run_r0inf_spec M n y x' h l₀)

theorem run1_r0inf_spec (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (x x' : BoundedConfig.BCfg (Fin 2) (Fin 6))
    (h : run_r0inf M (n + 1) x = some x') (l₀ : ListBlank (Fin 2)) :
    (BoundedConfig.toCfg x l₀ default) [M]⊢⁺ (BoundedConfig.toCfg x' l₀ default) := by
  dsimp [run_r0inf] at h
  rcases hstep : BoundedConfig.step_r0inf M x with _ | y <;> rw [hstep] at h
  · cases h
  · exact stepPlus_stepStar_trans ⟨1, by decide, BoundedConfig.step_r0inf_spec M x hstep l₀⟩
      (run_r0inf_spec M n y x' h l₀)

def check_r0inf (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (l₁ r₁ l₂ r₂ : List (Fin 2)) (q₁ q₂ : Fin 6) (d₁ d₂ : Dir) : Bool :=
  match run_r0inf M (n + 1) ⟨l₁, r₁, q₁, d₁⟩ with
  | some ⟨l', r', q', .right⟩ =>
    (d₂ == .right) && (q' == q₂) && (l' == l₂) && BoundedConfig.eqAppR0inf r' r₂
  | some ⟨l', r', q', .left⟩ =>
    (d₂ == .left) && (q' == q₂) && (r' == r₂) && BoundedConfig.eqAppR0inf l' l₂
  | none => false

theorem check_r0inf_spec {M : Machine (Fin 2) (Fin 6)} {n : ℕ}
    {l₁ r₁ l₂ r₂ : List (Fin 2)} {q₁ q₂ : Fin 6} {d₁ d₂ : Dir}
    (h : check_r0inf M n l₁ r₁ l₂ r₂ q₁ q₂ d₁ d₂ = true) (l₀ : ListBlank (Fin 2)) :
    (BoundedConfig.toCfg ⟨l₁, r₁, q₁, d₁⟩ l₀ default) [M]⊢⁺
      (BoundedConfig.toCfg ⟨l₂, r₂, q₂, d₂⟩ l₀ default) := by
  dsimp [check_r0inf] at h
  rcases hstep : run_r0inf M (n + 1) ⟨l₁, r₁, q₁, d₁⟩ with _ | ⟨l', r', q', _ | _⟩ <;>
    rw [hstep] at h
  · cases h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hd, hq⟩, hr⟩, hl⟩
    subst hd hq hr
    have hrun := run1_r0inf_spec M n ⟨l₁, r₁, q₁, d₁⟩ _ hstep l₀
    have hl_eq := BoundedConfig.eqAppR0inf_spec hl
    simpa only [BoundedConfig.toCfg, hl_eq] using hrun
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hd, hq⟩, hl⟩, hr⟩
    subst hd hq hl
    have hrun := run1_r0inf_spec M n ⟨l₁, r₁, q₁, d₁⟩ _ hstep l₀
    have hr_eq := BoundedConfig.eqAppR0inf_spec hr
    simpa only [BoundedConfig.toCfg, hr_eq] using hrun

-- ============================================================================
-- 3. `SOBCv10` Words, Boundary Signals & Core Rules (`sobc_needed.v`)
-- ============================================================================

abbrev U : List (Fin 2) := [1, 0, 1, 1]
abbrev A8 : List (Fin 2) := [1, 1, 1, 1, 1, 0, 1, 1]
abbrev B8 : List (Fin 2) := [1, 1, 1, 0, 1, 1, 1, 1]
abbrev C8 : List (Fin 2) := [1, 1, 1, 1, 1, 1, 1, 0]
abbrev D8 : List (Fin 2) := [1, 1, 1, 0, 1, 1, 1, 0]
abbrev E8 : List (Fin 2) := [1, 1, 1, 1, 1, 0, 1, 0]

abbrev hash : DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6) := ((B, []), (F, []))
abbrev hashes : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [hash]

theorem hash_U : SegRLs source_tm hashes hashes U U :=
  BoundedConfig.segRLs_c_spec source_tm (T := 100) (by decide)

theorem hash_A : SegRLs source_tm hashes [] A8 B8 :=
  BoundedConfig.segRLs_c_spec source_tm (T := 100) (by decide)

theorem hash_B : SegRLs source_tm hashes hashes B8 A8 :=
  BoundedConfig.segRLs_c_spec source_tm (T := 100) (by decide)

theorem hash_CAUU : SegRLs source_tm hashes [] (C8 ++ A8 ++ U ++ U) (D8 ++ C8 ++ A8) :=
  BoundedConfig.segRLs_c_spec source_tm (T := 200) (by decide)

theorem hash_E : SegRLs source_tm hashes [] E8 D8 :=
  BoundedConfig.segRLs_c_spec source_tm (T := 100) (by decide)

theorem hash_D : SegRLs source_tm hashes [] D8 A8 :=
  BoundedConfig.segRLs_c_spec source_tm (T := 100) (by decide)


open SegCount.BDigit

theorem hash_A_cycle : SegRLs source_tm (hashes ^ 2) hashes A8 A8 :=
  hash_A.trans hash_B

theorem hash_B_cycle : SegRLs source_tm (hashes ^ 2) hashes B8 B8 :=
  hash_B.trans hash_A

theorem hash_A_finish (k : ℕ) :
    SegRLs source_tm (hashes ^ (2 * k + 1)) (hashes ^ k) A8 B8 := by
  have h := SegRLs.addmul_v2 (x := k) (a := 2) (a' := 1) (b := 1) (b' := 0) hash_A hash_B_cycle
  simpa only [Nat.mul_comm k 2, Nat.mul_one, Nat.add_zero] using h

theorem hash_B_finish (k : ℕ) :
    SegRLs source_tm (hashes ^ (2 * k)) (hashes ^ k) B8 B8 := by
  have h := SegRLs.addmul_v2 (x := k) (a := 2) (a' := 1) (b := 0) (b' := 0) (.nil B8) hash_B_cycle
  simpa only [Nat.mul_comm k 2, Nat.mul_one, Nat.add_zero] using h

theorem hash_A_cycles (k : ℕ) :
    SegRLs source_tm (hashes ^ (2 * k)) (hashes ^ k) A8 A8 := by
  have h := SegRLs.addmul_v2 (x := k) (a := 2) (a' := 1) (b := 0) (b' := 0) (.nil A8) hash_A_cycle
  simpa only [Nat.mul_comm k 2, Nat.mul_one, Nat.add_zero] using h

theorem hash_E_even (n : ℕ) :
    SegRLs source_tm (hashes ^ (2 * n + 2)) (hashes ^ n) E8 A8 := by
  rw [show 2 * n + 2 = 1 + (1 + 2 * n) by omega,
      pow_add_list hashes 1, pow_add_list hashes 1, pow_one_list]
  simpa only [List.nil_append] using hash_E.trans (hash_D.trans (hash_A_cycles n))

theorem hash_E_odd (n : ℕ) :
    SegRLs source_tm (hashes ^ (2 * n + 3)) (hashes ^ n) E8 B8 := by
  rw [show 2 * n + 3 = 1 + (1 + (2 * n + 1)) by omega,
      pow_add_list hashes 1, pow_add_list hashes 1, pow_one_list]
  simpa only [List.nil_append] using hash_E.trans (hash_D.trans (hash_A_finish n))

theorem hashes_U (n : ℕ) : SegRLs source_tm (hashes ^ n) (hashes ^ n) U U :=
  SegRLs.wall_pow hash_U n

theorem hashes_U_run (signals width : ℕ) :
    SegRLs source_tm (hashes ^ signals) (hashes ^ signals) (U ^ width) (U ^ width) := by
  induction width with
  | zero => exact SegRLs.empty source_tm (hashes ^ signals)
  | succ width ih =>
    rw [pow_succ_list]
    exact (hashes_U signals).concat ih

theorem segRLs_0inf {hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {input output : List (Fin 2)}
    (h : SegRLs source_tm hs [] input output) :
    SideRLs source_tm hs (input +> default) (output +> default) :=
  h.sideRLs_concat (.nil default)

def Q8 : List (Fin 2) := [0, 0, 1, 0, 0, 1, 0, 1]

def common_left_wall : ListBlank (Fin 2) := Q8 +> default

-- Helper 1D scan lemmas for `sobc1_hash_CAB1110` and `fossil_scan`
def W_C : List (Fin 2) := [0, 0, 0, 1, 0, 0, 1]
def W_A : List (Fin 2) := [0, 0, 1, 0, 1, 0, 0, 1]

theorem scan_C8_fwd (l r : ListBlank (Fin 2)) :
    (l {{B}}> (C8 +> r)) [source_tm]⊢⁺ (([1] +> (W_C +> l)) {{A}}> r) := by
  have h :=
      run1Steps_spec source_tm 11 ⟨[], C8, B, .right⟩ ⟨[1] ++ W_C, [], A,
      .right⟩ (by decide) (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

theorem scan_A8_fwd_one (l r : ListBlank (Fin 2)) :
    (([1] +> l) {{A}}> (A8 +> ([1] +> r))) [source_tm]⊢*
      (([1] +> (W_A +> l)) {{A}}> ([1] +> r)) := by
  have h :=
      runSteps_spec source_tm 14 ⟨[1], A8 ++ [1], A, .right⟩ ⟨[1] ++ W_A, [1], A,
      .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

theorem scan_A8_fwd_pow (k : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> l) {{A}}> ((A8 ^ k) +> ([1] +> r))) [source_tm]⊢*
      (([1] +> ((W_A ^ k) +> l)) {{A}}> ([1] +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, append_nil]
    exact stepStar_refl source_tm _
  | succ k ih =>
    rw [pow_succ_list' A8 k, append_assoc]
    have ha : (A8 +> ([1] +> r)) = ([1] +> (([1, 1, 1, 1, 0, 1, 1] ++ [1]) +> r)) := rfl
    rw [ha]
    refine stepStar_trans (ih l (([1, 1, 1, 1, 0, 1, 1] ++ [1]) +> r)) ?_
    rw [← ha]
    have h1 := scan_A8_fwd_one (W_A ^ k +> l) r
    simpa only [pow_succ_list W_A k, append_assoc] using h1

theorem scan_A8_ret_one (l r : ListBlank (Fin 2)) :
    (([1] +> (W_A +> l)) <{{F}} r) [source_tm]⊢*
      (([1] +> l) <{{F}} (C8 +> r)) := by
  have h :=
      runSteps_spec source_tm 18 ⟨[], [1] ++ W_A, F, .left⟩ ⟨C8, [1], F, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

theorem scan_A8_ret_pow (k : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> ((W_A ^ k) +> l)) <{{F}} r) [source_tm]⊢*
      (([1] +> l) <{{F}} ((C8 ^ k) +> r)) := by
  induction k generalizing r with
  | zero =>
    simp only [pow_zero_list, append_nil]
    exact stepStar_refl source_tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (scan_A8_ret_one _ r) ?_
    have hrec := ih (C8 +> r)
    simpa only [pow_succ_list', append_assoc] using hrec

theorem scan_C8_ret (l r : ListBlank (Fin 2)) :
    (([1] +> (W_C +> l)) <{{F}} r) [source_tm]⊢*
      (l <{{F}} (D8 +> r)) := by
  have h := runSteps_spec source_tm 16 ⟨[], [1] ++ W_C, F, .left⟩ ⟨D8, [], F, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

theorem sobc1_hash_CAB1110 (k : ℕ) :
    SegRLs source_tm hashes []
      (C8 ++ A8 ^ k ++ B8 ++ [1, 1, 1, 0])
      (D8 ++ C8 ^ k ++ B8 ++ U) := by
  refine .cons (fun l r => ?_) (.nil _)
  simp only [toDHCfg, List.append_assoc, append_assoc, append_nil]
  refine stepPlus_stepStar_trans (scan_C8_fwd l _) ?_
  have hturn : (∀ l', (([1] +> l') {{A}}> (B8 +> ([1, 1, 1, 0] +> r))) [source_tm]⊢*
      (([1] +> l') <{{F}} ((B8 ++ U) +> r))) := by
    intro l'
    have h :=
        runSteps_spec source_tm 41 ⟨[1], B8 ++ [1, 1, 1, 0], A, .right⟩ ⟨B8 ++ U, [1], F,
        .left⟩ (by decide) l' r
    simpa only [BoundedConfig.toCfg, List.append_assoc, append_assoc, append_nil] using h
  have hb : (B8 +> ([1, 1, 1, 0] +> r)) = ([1] +> ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0] +> r)) := rfl
  rw [hb]
  refine stepStar_trans (scan_A8_fwd_pow k (W_C +> l) ([1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0] +> r)) ?_
  rw [← hb]
  refine stepStar_trans (hturn _) ?_
  refine stepStar_trans (scan_A8_ret_pow k (W_C +> l) ((B8 ++ U) +> r)) ?_
  simpa only [append_assoc] using scan_C8_ret l ((C8 ^ k) +> (B8 +> (U +> r)))

def pow2 (k : ℕ) : ℤ := (2 : ℤ) ^ k

theorem pow2_pos (k : ℕ) : 0 < pow2 k := by
  unfold pow2; positivity

theorem pow2_succ (k : ℕ) : pow2 (k + 1) = 2 * pow2 k := by
  unfold pow2; ring

theorem pow2_Zpow (k : ℕ) : pow2 k = (2 : ℤ) ^ k := rfl

theorem pow2_nat (k : ℕ) : pow2 k = ((2 ^ k : ℕ) : ℤ) := by
  unfold pow2; simp

def initial_u_pair_calls (primary : ℕ) : ℕ → ℕ
  | 0 => 0
  | pairs' + 1 => 2 * 2 ^ primary + initial_u_pair_calls (primary + 1) pairs'

theorem standard_mixed_to_binary_out_spec (e : ℕ) (ds : List BDigit) (out : ℕ)
    (hlen : ds.length = e + 1) :
    SegRLs source_tm
      (hashes ^ ((out + 1) * 2 ^ (e + 1) - 2 + digits_value ds))
      (hashes ^ out)
      (E8 ^ e ++ A8)
      ((digits_word A8 B8) ds) := by
  induction e generalizing ds out with
  | zero =>
    rcases ds with _ | ⟨d, _ | _⟩
    · cases hlen
    · rcases d with _ | _
      · have heq : (out + 1) * 2 ^ 1 - 2 + digits_value [BA] = 2 * out := by
          dsimp [digits_value]; omega
        rw [heq]
        simpa [digits_word, digit_word] using hash_A_cycles out
      · have heq : (out + 1) * 2 ^ 1 - 2 + digits_value [BB] = 2 * out + 1 := by
          dsimp [digits_value]; omega
        rw [heq]
        simpa [digits_word, digit_word] using hash_A_finish out
    · cases hlen
  | succ e ih =>
    rcases ds with _ | ⟨d, ds⟩
    · cases hlen
    · have htail : ds.length = e + 1 := by simp at hlen; omega
      have hrun := ih ds out htail
      have hpow : 2 ≤ 2 ^ (e + 1) := by
        have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
        rw [Nat.pow_succ]
        omega
      have hge2 : 2 ≤ (out + 1) * 2 ^ (e + 1) := by nlinarith
      rcases d with _ | _
      · rw [pow_succ_list E8 e, List.append_assoc]
        have heq : (out + 1) * 2 ^ (e + 1 + 1) - 2 + digits_value (BA :: ds) =
            2 * ((out + 1) * 2 ^ (e + 1) - 2 + digits_value ds) + 2 := by
          dsimp [digits_value]
          rw [Nat.pow_succ]
          have hmul : (out + 1) * (2 ^ (e + 1) * 2) = 2 * ((out + 1) * 2 ^ (e + 1)) := by ring
          omega
        rw [heq]
        exact (hash_E_even _).concat hrun
      · rw [pow_succ_list E8 e, List.append_assoc]
        have heq : (out + 1) * 2 ^ (e + 1 + 1) - 2 + digits_value (BB :: ds) =
            2 * ((out + 1) * 2 ^ (e + 1) - 2 + digits_value ds) + 3 := by
          dsimp [digits_value]
          rw [Nat.pow_succ]
          have hmul : (out + 1) * (2 ^ (e + 1) * 2) = 2 * ((out + 1) * 2 ^ (e + 1)) := by ring
          omega
        rw [heq]
        exact (hash_E_odd _).concat hrun

theorem prefix_E_even (k n : ℕ) (input output : List (Fin 2)) (carries : ℕ)
    (hrun : SegRLs source_tm (hashes ^ n) (hashes ^ carries) input output) :
    SegRLs source_tm (hashes ^ (2 ^ k * n + 2 * (2 ^ k - 1))) (hashes ^ carries)
      (E8 ^ k ++ input) (A8 ^ k ++ output) := by
  induction k with
  | zero =>
    simpa using hrun
  | succ k ih =>
    rw [pow_succ_list, pow_succ_list, List.append_assoc, List.append_assoc]
    have h1 := (hash_E_even (2 ^ k * n + 2 * (2 ^ k - 1))).concat ih
    have heq : 2 * (2 ^ k * n + 2 * (2 ^ k - 1)) + 2 = 2 ^ (k + 1) * n + 2 * (2 ^ (k + 1) - 1) := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      have hmul : (2 ^ k * 2) * n = 2 * (2 ^ k * n) := by ring
      omega
    rwa [heq] at h1

abbrev X4 : List (Fin 2) := [0, 0, 1, 0]
abbrev V4 : List (Fin 2) := [0, 1, 0, 0]

def exception_pre_left (n : ℕ) : ListBlank (Fin 2) :=
  ([1, 0, 1, 0] ++ V4 ^ (2 * n + 2) ++ [1, 0, 1]) +> default

def exception_call_left (remaining finished : ℕ) : ListBlank (Fin 2) :=
  (X4 ^ (2 * finished + 5) ++ V4 ^ (2 * remaining) ++ [1, 0, 1]) +> default

theorem raw_U_to_X : SegRR source_tm (B, []) (B, []) U X4 := by
  intro l r
  have h := runSteps_spec source_tm 4 ⟨[], U, B, .right⟩ ⟨X4, [], B, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, toDHCfg, append_nil] using h

theorem segRR_lpow_same (h : DH0 (Fin 2) (Fin 6)) (w v : List (Fin 2)) (k : ℕ)
    (hstep : SegRR source_tm h h w v) :
    SegRR source_tm h h (w ^ k) (v ^ k) := by
  induction k with
  | zero =>
    intro l r
    simp only [pow_zero_list, append_nil]
    exact stepStar_refl source_tm _
  | succ k ih =>
    intro l r
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (hstep l ((w ^ k) +> r)) ?_
    have hrec := ih (v +> l) r
    simpa only [pow_succ_list', append_assoc] using hrec

theorem raw_Us_to_Xs (k : ℕ) : SegRR source_tm (B, []) (B, []) (U ^ k) (X4 ^ k) :=
  segRR_lpow_same (B, []) U X4 k raw_U_to_X

theorem raw_B_forward : SegRR source_tm (B, []) (B, []) B8 Q8 := by
  intro l r
  have h := runSteps_spec source_tm 14 ⟨[], B8, B, .right⟩ ⟨Q8, [], B, .right⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, toDHCfg, append_nil] using h

theorem raw_B_return (l r : ListBlank (Fin 2)) :
    (([1, 0, 1] +> (Q8 +> l)) <{{F}} r) [source_tm]⊢⁺
      (([1, 0, 1] +> l) <{{F}} (E8 +> r)) := by
  have h :=
      run1Steps_spec source_tm 15 ⟨[], [1, 0, 1] ++ Q8, F, .left⟩ ⟨E8, [1, 0, 1], F,
      .left⟩ (by decide) (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil, append_assoc] using h

private theorem x4_pow_zero_shift (k : ℕ) :
    X4 ^ k ++ [0] = [0] ++ V4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, List.append_assoc, ih, ← List.append_assoc X4 [0],
        show X4 ++ [0] = [0] ++ V4 from rfl, List.append_assoc, ← pow_succ_list V4 k]

theorem exception_pre_left_direct (n : ℕ) :
    ([1, 0, 1] +> (X4 ^ (2 * n + 1) +> (Q8 +> default))) = exception_pre_left n := by
  unfold exception_pre_left
  rw [← append_assoc, ← append_assoc]
  congr 1
  have hq : Q8 = [0] ++ (V4 ++ [1, 0, 1]) := rfl
  calc [1, 0, 1] ++ (X4 ^ (2 * n + 1) ++ Q8)
      = [1, 0, 1] ++ ((X4 ^ (2 * n + 1) ++ [0]) ++ (V4 ++ [1, 0, 1])) := by
        rw [hq, List.append_assoc (X4 ^ (2 * n + 1))]
    _ = [1, 0, 1] ++ (([0] ++ V4 ^ (2 * n + 1)) ++ (V4 ++ [1, 0, 1])) := by
        rw [x4_pow_zero_shift]
    _ = [1, 0, 1, 0] ++ (V4 ^ (2 * n + 1) ++ V4) ++ [1, 0, 1] := by
        simp only [List.append_assoc]; rfl
    _ = [1, 0, 1, 0] ++ V4 ^ (2 * n + 2) ++ [1, 0, 1] := by
        rw [← pow_succ_list' V4 (2 * n + 1), show 2 * n + 1 + 1 = 2 * n + 2 by omega]

abbrev left_hash : DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6) := ((F, []), (B, []))

theorem left_hash_XX :
    SegRLs (flipTM source_tm) [left_hash] [left_hash] (X4 ^ 2) (X4 ^ 2) :=
  BoundedConfig.segRLs_c_spec (flipTM source_tm) (T := 200) (by decide)

theorem left_relaunch_base :
    SegRLs (flipTM source_tm) [left_hash] [] (X4 ^ 5 ++ V4 ^ 2) (X4 ^ 7) :=
  BoundedConfig.segRLs_c_spec (flipTM source_tm) (T := 500) (by decide)

theorem left_hash_X_pairs (k : ℕ) :
    SegRLs (flipTM source_tm) [left_hash] [left_hash] (X4 ^ (2 * k)) (X4 ^ (2 * k)) := by
  induction k with
  | zero => exact SegRLs.empty (flipTM source_tm) [left_hash]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add_list]
    exact ih.concat left_hash_XX

theorem left_launch_segment :
    SegRLs (flipTM source_tm) [left_hash] [] ([1, 0, 1, 0] ++ V4 ^ 4) (X4 ^ 5) :=
  BoundedConfig.segRLs_c_spec (flipTM source_tm) (T := 500) (by decide)

theorem exception_launch (k : ℕ) :
    SideRLs (flipTM source_tm) [left_hash]
      (exception_pre_left (k + 1)) (exception_call_left k 0) := by
  unfold exception_pre_left exception_call_left
  rw [show 2 * (k + 1) + 2 = 4 + 2 * k by omega, pow_add_list]
  have h := left_launch_segment.sideRLs_concat
    (SideRLs.nil (M := flipTM source_tm) ((V4 ^ (2 * k) ++ [1, 0, 1]) +> default))
  simpa only [Nat.mul_zero, Nat.zero_add, List.append_assoc, append_assoc] using h

theorem exception_relaunch_side (remaining finished : ℕ) :
    SideRLs (flipTM source_tm) [left_hash]
      (exception_call_left (remaining + 1) finished)
      (exception_call_left remaining (finished + 1)) := by
  have hseg := (left_hash_X_pairs finished).concat left_relaunch_base
  have hside := hseg.sideRLs_concat
    (SideRLs.nil (M := flipTM source_tm) ((V4 ^ (2 * remaining) ++ [1, 0, 1]) +> default))
  unfold exception_call_left
  rw [show 2 * (remaining + 1) = 2 + 2 * remaining by omega,
      show 2 * (finished + 1) + 5 = 2 * finished + 7 by omega,
      pow_add_list V4 2 (2 * remaining),
      pow_add_list X4 (2 * finished) 5,
      pow_add_list X4 (2 * finished) 7]
  simpa only [List.append_assoc, append_assoc] using hside

theorem exception_relaunches (k finished : ℕ) :
    SideRLs (flipTM source_tm) ([left_hash] ^ k)
      (exception_call_left k finished)
      (exception_call_left 0 (finished + k)) := by
  induction k generalizing finished with
  | zero =>
    simp only [pow_zero_list, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    rw [pow_succ_list]
    have h := (exception_relaunch_side k finished).trans (ih (finished + 1))
    simpa only [Nat.add_right_comm finished 1 k, Nat.add_assoc] using h

theorem exception_calls (k : ℕ) (input output : List (Fin 2))
    (hseg : SegRLs source_tm (hashes ^ (k + 1)) [] input output) :
    ((exception_call_left k 0) {{B}}> (input +> default)) [source_tm]⊢⁺
      ((exception_call_left 0 k) <{{F}} (output +> default)) := by
  have hright : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ k) (F, []))
      (input +> default) (output +> default) := by
    rw [lrcons_same]
    exact segRLs_0inf hseg
  have hleft : SideRLs (flipTM source_tm) ([left_hash] ^ k)
      (exception_call_left k 0) (exception_call_left 0 k) := by
    simpa only [Nat.zero_add] using exception_relaunches k 0
  exact SideRLs.concat hleft hright

def exception_done (n : ℕ) (output : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  common_left_wall {{B}}> ((C8 ++ A8 ++ U ^ (2 * n) ++ output) +> default)

theorem raw_XX_return (l r : ListBlank (Fin 2)) :
    ((X4 ^ 2 +> l) <{{F}} r) [source_tm]⊢* (l <{{F}} (U ^ 2 +> r)) := by
  have h := runSteps_spec source_tm 20 ⟨[], X4 ^ 2, F, .left⟩ ⟨U ^ 2, [], F, .left⟩ (by decide) l r
  simpa only [BoundedConfig.toCfg, append_nil] using h

theorem raw_XX_returns (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((X4 ^ (2 * k) +> l) <{{F}} r) [source_tm]⊢* (l <{{F}} (U ^ (2 * k) +> r)) := by
  induction k generalizing r with
  | zero =>
    simp only [Nat.mul_zero, pow_zero_list, append_nil]
    exact stepStar_refl source_tm _
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add_list X4 2 (2 * k), append_assoc]
    refine stepStar_trans (raw_XX_return _ r) ?_
    have hrec := ih (U ^ 2 +> r)
    rw [show 2 + 2 * k = 2 * k + 2 by omega, pow_add_list U (2 * k) 2, append_assoc]
    exact hrec

theorem exception_exit_base (r : ListBlank (Fin 2)) :
    (((X4 ^ 5 ++ [1, 0, 1]) +> default) <{{F}} r) [source_tm]⊢⁺
      (common_left_wall {{B}}> ((C8 ++ A8 ++ U ^ 2) +> r)) := by
  have h0 : (([0] : List (Fin 2)) ^ 9 +> (default : ListBlank (Fin 2))) = default :=
    BoundedConfig.all0_spec (a := ([0] : List (Fin 2)) ^ 9) (by decide)
  have h := run1Steps_spec source_tm 118
    ⟨[], X4 ^ 5 ++ [1, 0, 1] ++ ([0] : List (Fin 2)) ^ 9, F, .left⟩
    ⟨Q8, C8 ++ A8 ++ U ^ 2, B, .right⟩
    (by decide) (by decide) default r
  simpa only [BoundedConfig.toCfg, common_left_wall, List.append_assoc, append_assoc, h0,
      append_nil] using h

theorem exception_exit (k : ℕ) (output : List (Fin 2)) :
    ((exception_call_left 0 k) <{{F}} (output +> default)) [source_tm]⊢⁺
      exception_done (k + 1) output := by
  unfold exception_call_left exception_done
  rw [Nat.mul_zero, pow_zero_list, List.append_nil, pow_add_list X4 (2 * k) 5,
      List.append_assoc, append_assoc]
  refine stepStar_stepPlus_trans (raw_XX_returns k ((X4 ^ 5 ++ [1, 0,
      1]) +> default) (output +> default)) ?_
  have hbase := exception_exit_base (U ^ (2 * k) +> (output +> default))
  rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add_list U 2 (2 * k)]
  simpa only [List.append_assoc, append_assoc] using hbase

theorem exception_launch_progress (k : ℕ) (r : ListBlank (Fin 2)) :
    ((exception_pre_left (k + 1)) <{{F}} r) [source_tm]⊢⁺
      ((exception_call_left k 0) {{B}}> r) :=
  (exception_launch k).elim_single_left r

theorem exception_exit_zero (output : List (Fin 2)) :
    ((exception_pre_left 0) <{{F}} (output +> default)) [source_tm]⊢⁺
      exception_done 0 output := by
  unfold exception_pre_left exception_done
  have h0 : (([0] : List (Fin 2)) ^ 9 +> (default : ListBlank (Fin 2))) = default :=
    BoundedConfig.all0_spec (a := ([0] : List (Fin 2)) ^ 9) (by decide)
  have h := run1Steps_spec source_tm 114
    ⟨[], [1, 0, 1, 0] ++ V4 ^ 2 ++ [1, 0, 1] ++ ([0] : List (Fin 2)) ^ 9, F, .left⟩
    ⟨Q8, C8 ++ A8, B, .right⟩
    (by decide) (by decide) default (output +> default)
  simpa only [BoundedConfig.toCfg, common_left_wall, Nat.mul_zero, Nat.zero_add, pow_zero_list,
    List.append_nil, List.append_assoc, append_assoc, append_nil, h0] using h

theorem exception_pre_from_seg (n : ℕ) (input output : List (Fin 2))
    (hseg : SegRLs source_tm (hashes ^ n) [] input output) :
    ((exception_pre_left n) <{{F}} (input +> default)) [source_tm]⊢⁺
      exception_done n output := by
  rcases n with _ | k
  · cases hseg
    exact exception_exit_zero _
  · exact stepPlus_trans (exception_launch_progress k (input +> default))
      (stepPlus_trans (exception_calls k input output hseg) (exception_exit k output))

-- Residue & LineagePhase calculus (`sobc_needed.v` lines 499–770)
def even_residue : ℕ → ℤ
  | 0 => 3
  | n' + 1 => 4 * even_residue n' + 1

def odd_residue : ℕ → ℤ
  | 0 => 26
  | n' + 1 => 4 * odd_residue n' - 2

def even_residue_width (n : ℕ) : ℕ := 2 * n + 4
def odd_residue_width (n : ℕ) : ℕ := 2 * n + 5

theorem even_residue_bounds (n : ℕ) :
    3 ≤ even_residue n ∧ even_residue n ≤ pow2 (even_residue_width n) - 6 := by
  induction n with
  | zero =>
    dsimp [even_residue, even_residue_width, pow2]
    omega
  | succ n ih =>
    dsimp [even_residue, even_residue_width] at ih ⊢
    rw [show 2 * (n + 1) + 4 = (2 * n + 4) + 1 + 1 by omega, pow2_succ, pow2_succ]
    omega

theorem even_residue_S_lower (n : ℕ) : 13 ≤ even_residue (n + 1) := by
  have := even_residue_bounds n
  dsimp [even_residue]
  omega

theorem odd_residue_bounds (n : ℕ) :
    3 ≤ odd_residue n ∧ odd_residue n ≤ pow2 (odd_residue_width n) - 6 := by
  induction n with
  | zero =>
    dsimp [odd_residue, odd_residue_width, pow2]
    omega
  | succ n ih =>
    dsimp [odd_residue, odd_residue_width] at ih ⊢
    rw [show 2 * (n + 1) + 5 = (2 * n + 5) + 1 + 1 by omega, pow2_succ, pow2_succ]
    omega

theorem odd_residue_complement (n : ℕ) :
    odd_residue n = 2 * (pow2 (even_residue_width n) - even_residue n) := by
  induction n with
  | zero =>
    dsimp [odd_residue, even_residue, even_residue_width, pow2]
  | succ n ih =>
    dsimp [odd_residue, even_residue, even_residue_width] at ih ⊢
    rw [show 2 * (n + 1) + 4 = (2 * n + 4) + 1 + 1 by omega, pow2_succ, pow2_succ]
    omega

theorem even_residue_complement (n : ℕ) :
    even_residue (n + 1) = 2 * (pow2 (odd_residue_width n) - odd_residue n) + 1 := by
  have hodd := odd_residue_complement n
  dsimp [even_residue, odd_residue_width, even_residue_width] at hodd ⊢
  rw [show 2 * n + 5 = (2 * n + 4) + 1 by omega, pow2_succ]
  omega

theorem low_step_odd_to_even (n : ℕ) :
    pow2 (even_residue_width n) - odd_residue n / 2 = even_residue n := by
  rw [odd_residue_complement]
  omega

theorem low_step_even_to_odd (n : ℕ) :
    pow2 (odd_residue_width n) - even_residue (n + 1) / 2 = odd_residue n := by
  rw [even_residue_complement]
  omega

def z_birth_value (n : ℕ) : ℤ :=
  2 * (pow2 (even_residue_width (n + 1)) - even_residue (n + 1)) + 1

def z_birth_width (n : ℕ) : ℕ := 2 * n + 7

theorem z_birth_complement (n : ℕ) :
    z_birth_value n = 2 * (pow2 (even_residue_width (n + 1)) - even_residue (n + 1)) + 1 := rfl

theorem z_birth_succ (n : ℕ) :
    z_birth_value (n + 1) = 4 * z_birth_value n - 5 := by
  unfold z_birth_value even_residue_width
  dsimp [even_residue]
  rw [show 2 * (n + 1 + 1) + 4 = (2 * (n + 1) + 4) + 1 + 1 by omega, pow2_succ, pow2_succ]
  omega

theorem z_birth_bounds (n : ℕ) :
    3 ≤ z_birth_value n ∧ z_birth_value n ≤ pow2 (z_birth_width n) - 6 := by
  have he := even_residue_bounds (n + 1)
  have he13 := even_residue_S_lower n
  unfold z_birth_value z_birth_width even_residue_width at *
  rw [show 2 * n + 7 = (2 * (n + 1) + 4) + 1 by omega, pow2_succ (2 * (n + 1) + 4)]
  omega

theorem z_birth_first_low_step (n : ℕ) :
    pow2 (even_residue_width (n + 1)) - z_birth_value n / 2 = even_residue (n + 1) := by
  rw [z_birth_complement]
  omega

def low_slice (total : ℤ) (m : ℕ) (r v : ℤ) : Prop :=
  ∃ high capacity : ℤ,
    total = capacity * pow2 m ∧
    v = high * pow2 m + r ∧
    0 ≤ high ∧ high < capacity

theorem low_slice_safe (total : ℤ) (m : ℕ) (r v : ℤ)
    (hslice : low_slice total m r v)
    (hr : 3 ≤ r ∧ r ≤ pow2 m - 6) :
    3 ≤ v ∧ v ≤ total - 6 := by
  rcases hslice with ⟨high, capacity, htotal, hv, hhigh0, hhigh1⟩
  have hpos := pow2_pos m
  have hle : high + 1 ≤ capacity := by omega
  have hmul1 : 0 ≤ high * pow2 m := mul_nonneg hhigh0 (le_of_lt hpos)
  have hmul2 : (high + 1) * pow2 m ≤ capacity * pow2 m :=
    mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
  constructor <;> linarith

theorem low_slice_step (total : ℤ) (m : ℕ) (r v : ℤ) (right_odd : Bool)
    (hslice : low_slice total (m + 1) r v)
    (hr : 3 ≤ r ∧ r < pow2 (m + 1)) :
    low_slice total m (pow2 m - r / 2)
      ((if right_odd then total / 2 else total) - v / 2) := by
  rcases hslice with ⟨high, capacity, htotal, hv, hhigh0, hhigh1⟩
  rw [pow2_succ] at htotal hv hr
  have hpos := pow2_pos m
  have htotal_half : total / 2 = capacity * pow2 m := by
    rw [htotal, show capacity * (2 * pow2 m) = (capacity * pow2 m) * 2 by ring,
        Int.mul_ediv_cancel _ (by decide)]
  have hv_half : v / 2 = high * pow2 m + r / 2 := by
    rw [hv, show high * (2 * pow2 m) + r = r + (high * pow2 m) * 2 by ring,
        Int.add_mul_ediv_right _ _ (by decide)]
    ring
  have hrhalf : 1 ≤ r / 2 ∧ r / 2 < pow2 m := by omega
  rcases right_odd with _ | _
  · dsimp
    refine ⟨2 * capacity - high - 1, 2 * capacity, ?_, ?_, ?_, ?_⟩
    · linarith
    · rw [htotal, hv_half]; ring
    · omega
    · omega
  · dsimp
    refine ⟨capacity - high - 1, 2 * capacity, ?_, ?_, ?_, ?_⟩
    · linarith
    · rw [htotal_half, hv_half]; ring
    · omega
    · omega

theorem z_birth_low_slice (n : ℕ) :
    low_slice (pow2 (z_birth_width n)) (z_birth_width n)
      (z_birth_value n) (z_birth_value n) :=
  ⟨0, 1, by ring, by ring, by omega, by omega⟩

inductive LineagePhase where
  | LBirth (n : ℕ)
  | LEven (n : ℕ)
  | LOdd (n : ℕ)
  deriving DecidableEq, Repr

open LineagePhase

def lineage_width : LineagePhase → ℕ
  | LBirth n => z_birth_width n
  | LEven n => even_residue_width n
  | LOdd n => odd_residue_width n

def lineage_residue : LineagePhase → ℤ
  | LBirth n => z_birth_value n
  | LEven n => even_residue n
  | LOdd n => odd_residue n

inductive lineage_next : LineagePhase → LineagePhase → Prop where
  | lineage_birth (n : ℕ) : lineage_next (LBirth n) (LEven (n + 1))
  | lineage_even (n : ℕ) : lineage_next (LEven (n + 1)) (LOdd n)
  | lineage_odd (n : ℕ) : lineage_next (LOdd n) (LEven n)

def arbitrary_column_step (total : ℤ) (right_odd : Bool) (v : ℤ) : ℤ :=
  (if right_odd then total / 2 else total) - v / 2

theorem lineage_residue_bounds (p : LineagePhase) :
    3 ≤ lineage_residue p ∧ lineage_residue p ≤ pow2 (lineage_width p) - 6 := by
  rcases p with n | n | n
  · exact z_birth_bounds n
  · exact even_residue_bounds n
  · exact odd_residue_bounds n

theorem lineage_next_width (p p' : LineagePhase) (h : lineage_next p p') :
    lineage_width p = lineage_width p' + 1 := by
  cases h <;> dsimp [lineage_width, z_birth_width, even_residue_width, odd_residue_width] <;> omega

theorem lineage_next_low_step (p p' : LineagePhase) (h : lineage_next p p') :
    pow2 (lineage_width p') - lineage_residue p / 2 = lineage_residue p' := by
  cases h
  · exact z_birth_first_low_step _
  · exact low_step_even_to_odd _
  · exact low_step_odd_to_even _

theorem lineage_step_preserves_slice (total : ℤ) (p p' : LineagePhase) (v : ℤ) (right_odd : Bool)
    (hnext : lineage_next p p')
    (hslice : low_slice total (lineage_width p) (lineage_residue p) v) :
    low_slice total (lineage_width p') (lineage_residue p')
      (arbitrary_column_step total right_odd v) := by
  have hwidth := lineage_next_width p p' hnext
  have hres := lineage_next_low_step p p' hnext
  have hbounds := lineage_residue_bounds p
  unfold arbitrary_column_step
  rw [hwidth] at hslice hbounds
  rw [← hres]
  exact low_slice_step total (lineage_width p') (lineage_residue p) v right_odd hslice
    ⟨hbounds.1, by omega⟩

def lineage_fuel : LineagePhase → ℕ
  | LBirth n => 2 * n + 3
  | LEven n => 2 * n
  | LOdd n => 2 * n + 1

def ordinary_left (u : ℕ) : ListBlank (Fin 2) := X4 ^ u +> common_left_wall

theorem left_emit_zero :
    SideRLs (flipTM source_tm) [left_hash] (ordinary_left 0) (ordinary_left 1) := by
  unfold ordinary_left common_left_wall
  have h := BoundedConfig.sideRLs_c_spec (flipTM source_tm)
    (hs := [left_hash]) (r := Q8) (r' := X4 ++ Q8) (T := 500) (by decide)
  simpa only [pow_zero_list, pow_one_list, append_nil, append_assoc] using h

theorem left_emit_one :
    SideRLs (flipTM source_tm) [left_hash] (ordinary_left 1) (ordinary_left 2) := by
  unfold ordinary_left common_left_wall
  have h := BoundedConfig.sideRLs_c_spec (flipTM source_tm)
    (hs := [left_hash]) (r := X4 ++ Q8) (r' := X4 ^ 2 ++ Q8) (T := 500) (by decide)
  simpa only [pow_one_list, append_assoc] using h

theorem left_emit_call (u : ℕ) :
    SideRLs (flipTM source_tm) [left_hash] (ordinary_left u) (ordinary_left (u + 1)) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    rcases u with _ | _ | u
    · exact left_emit_zero
    · exact left_emit_one
    · have hrec := ih u (by omega)
      have h := left_hash_XX.sideRLs_concat hrec
      unfold ordinary_left at h ⊢
      rw [show u + 1 + 1 = 2 + u by omega, show 2 + u + 1 = 2 + (u + 1) by omega,
          pow_add_list, pow_add_list, append_assoc, append_assoc]
      exact h

theorem left_emit_calls (k u : ℕ) :
    SideRLs (flipTM source_tm) ([left_hash] ^ k) (ordinary_left u) (ordinary_left (u + k)) := by
  induction k generalizing u with
  | zero =>
    simp only [pow_zero_list, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    rw [pow_succ_list]
    have h := (left_emit_call u).trans (ih (u + 1))
    simpa only [Nat.add_right_comm u 1 k, Nat.add_assoc] using h

theorem ordinary_emit_progress (u : ℕ) (r : ListBlank (Fin 2)) :
    ((ordinary_left u) <{{F}} r) [source_tm]⊢⁺ ((ordinary_left (u + 1)) {{B}}> r) :=
  (left_emit_call u).elim_single_left r

theorem ordinary_seg_return (k u : ℕ) (input output : List (Fin 2)) (r : ListBlank (Fin 2))
    (hseg : SegRLs source_tm (hashes ^ (k + 1)) [] input output) :
    ((ordinary_left u) {{B}}> (input +> r)) [source_tm]⊢⁺
      ((ordinary_left (u + k)) <{{F}} (output +> r)) := by
  have hright : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ k) (F, []))
      (input +> r) (output +> r) := by
    rw [lrcons_same]
    exact hseg.sideRLs_concat (.nil r)
  exact SideRLs.concat (left_emit_calls k u) hright

theorem ordinary_seg_run (k u : ℕ) (input output : List (Fin 2)) (r : ListBlank (Fin 2))
    (hseg : SegRLs source_tm (hashes ^ (k + 1)) [] input output) :
    ((ordinary_left u) {{B}}> (input +> r)) [source_tm]⊢⁺
      ((ordinary_left (u + (k + 1))) {{B}}> (output +> r)) := by
  refine stepPlus_trans (ordinary_seg_return k u input output r hseg) ?_
  simpa only [Nat.add_assoc] using ordinary_emit_progress (u + k) (output +> r)

theorem ordinary_seg_run_pos (calls u : ℕ) (input output : List (Fin 2)) (r : ListBlank (Fin 2))
    (hcalls : 1 ≤ calls)
    (hseg : SegRLs source_tm (hashes ^ calls) [] input output) :
    ((ordinary_left u) {{B}}> (input +> r)) [source_tm]⊢⁺
      ((ordinary_left (u + calls)) {{B}}> (output +> r)) := by
  have hsplit : calls = (calls - 1) + 1 := by omega
  rw [hsplit] at hseg ⊢
  exact ordinary_seg_run (calls - 1) u input output r hseg

theorem ordinary_side_run (calls u : ℕ) (input output : ListBlank (Fin 2))
    (hside : SideRLs source_tm (hashes ^ calls) input output) :
    ((ordinary_left u) {{B}}> input) [source_tm]⊢*
      ((ordinary_left (u + calls)) {{B}}> output) := by
  rcases calls with _ | k
  · cases hside
    simp only [Nat.add_zero]
    exact stepStar_refl source_tm _
  · refine stepPlus_to_stepStar ?_
    have hright : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ k) (F, [])) input output := by
      rwa [lrcons_same]
    refine stepPlus_trans (SideRLs.concat (left_emit_calls k u) hright) ?_
    simpa only [toDHCfg, append_nil, Nat.add_assoc] using ordinary_emit_progress (u + k) output


def z_tail_digits : ℕ → List BDigit
  | 0 => [BA, BA, BB, BB]
  | n' + 1 => BA :: BB :: z_tail_digits n'

def z_digits (n : ℕ) : List BDigit :=
  BB :: BB :: BB :: z_tail_digits n

theorem z_tail_digits_length (n : ℕ) : (z_tail_digits n).length = 2 * n + 4 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [z_tail_digits, ih]; omega

theorem z_digits_length (n : ℕ) : (z_digits n).length = z_birth_width n := by
  unfold z_digits z_birth_width
  simp only [List.length_cons, z_tail_digits_length]

theorem z_digits_value_succ (n : ℕ) :
    digits_value (z_digits (n + 1)) + 5 = 4 * digits_value (z_digits n) := by
  unfold z_digits
  dsimp [z_tail_digits, digits_value]
  omega

theorem z_digits_value (n : ℕ) :
    (digits_value (z_digits n) : ℤ) = z_birth_value n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep := z_digits_value_succ n
    rw [z_birth_succ]
    omega

theorem digits_exist (width value : ℕ) (hval : value < 2 ^ width) :
    ∃ ds : List BDigit, ds.length = width ∧ digits_value ds = value := by
  induction width generalizing value with
  | zero =>
    have : value = 0 := by simp at hval; omega
    subst this
    exact ⟨[], rfl, rfl⟩
  | succ width ih =>
    rw [Nat.pow_succ] at hval
    obtain ⟨ds, hlen, hdig⟩ := ih (value / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one value with hmod | hmod
    · refine ⟨BA :: ds, ?_, ?_⟩
      · simp [hlen]
      · dsimp [digits_value]; omega
    · refine ⟨BB :: ds, ?_, ?_⟩
      · simp [hlen]
      · dsimp [digits_value]; omega

theorem cd_start :
    SegRLs source_tm (hashes ^ 2) [] (C8 ++ A8 ++ U ^ 2) (A8 ++ C8 ++ A8) :=
  BoundedConfig.segRLs_c_spec source_tm (T := 200) (by decide)

def cd_calls (n : ℕ) : ℕ := 2 * (2 ^ n - 1)
def cd_input (n : ℕ) : List (Fin 2) := C8 ++ A8 ++ U ^ (2 * n)
def cd_output (n : ℕ) : List (Fin 2) := A8 ^ n ++ C8 ++ A8

theorem cd_batch (n : ℕ) :
    SegRLs source_tm (hashes ^ cd_calls n) [] (cd_input n) (cd_output n) := by
  induction n with
  | zero =>
    exact .nil _
  | succ n ih =>
    have hstart := cd_start.concat (SegRLs.nil (M := source_tm) (U ^ (2 * n)))
    have hrest := (hash_A_cycles (cd_calls n)).concat ih
    have hcomb := hstart.trans hrest
    dsimp [cd_calls, cd_input, cd_output] at hcomb ⊢
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, pow_add_list U 2 (2 * n)]
    have hcalls : hashes ^ 2 ++ hashes ^ (2 * (2 * (2 ^ n - 1))) =
        hashes ^ (2 * (2 ^ (n + 1) - 1)) := by
      rw [← pow_add_list]
      congr 1
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega
    rw [← hcalls]
    convert hcomb using 1 <;>
      simp only [pow_succ_list, pow_zero_list, hashes, U,
        List.cons_append, List.nil_append, List.append_nil]

def after_cd (n : ℕ) (tail : List (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (ordinary_left (cd_calls n)) {{B}}> ((cd_output n ++ tail) +> default)

theorem cd_calls_positive (n : ℕ) (hn : 1 ≤ n) : 1 ≤ cd_calls n := by
  unfold cd_calls
  rcases n with _ | n
  · omega
  · have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

theorem exception_done_cd (n : ℕ) (tail : List (Fin 2)) (hn : 1 ≤ n) :
    (exception_done n tail) [source_tm]⊢⁺ (after_cd n tail) := by
  unfold exception_done after_cd
  have hseg := (cd_batch n).concat (SegRLs.nil (M := source_tm) tail)
  have hrun := ordinary_seg_run_pos (cd_calls n) 0 (cd_input n ++ tail) (cd_output n ++ tail)
    default (cd_calls_positive n hn) hseg
  dsimp [cd_input, ordinary_left] at hrun ⊢
  simpa only [pow_zero_list, Nat.zero_add, append_nil, List.append_assoc] using hrun

theorem all_A_cycles (width signals : ℕ) :
    SegRLs source_tm (hashes ^ (signals * 2 ^ width)) (hashes ^ signals)
      (A8 ^ width) (A8 ^ width) := by
  induction width generalizing signals with
  | zero =>
    simp only [Nat.pow_zero, Nat.mul_one, pow_zero_list]
    exact SegRLs.empty source_tm (hashes ^ signals)
  | succ width ih =>
    rw [pow_succ_list, Nat.pow_succ, ← Nat.mul_assoc]
    have h := (hash_A_cycles (signals * 2 ^ width)).concat (ih signals)
    rwa [Nat.mul_comm 2 (signals * 2 ^ width)] at h

theorem primary_lift (signals width : ℕ) (input output : List (Fin 2))
    (h : SegRLs source_tm (hashes ^ signals) [] input output) :
    SegRLs source_tm (hashes ^ (signals * 2 ^ width)) []
      (A8 ^ width ++ input) (A8 ^ width ++ output) :=
  (all_A_cycles width signals).concat h

theorem primary_one_rule (p : ℕ) (w₁ w₂ : List (Fin 2))
    (hrule : SegRLs source_tm hashes [] w₁ w₂) :
    SegRLs source_tm (hashes ^ (2 ^ p)) [] (A8 ^ p ++ w₁) (A8 ^ p ++ w₂) := by
  have h := primary_lift 1 p w₁ w₂ (by simpa only [pow_one_list] using hrule)
  simpa only [Nat.one_mul] using h

def ca_pair_calls (width : ℕ) : ℕ := 2 * 2 ^ width

theorem ca_pair0 : SegRLs source_tm (hashes ^ 2) [] (C8 ++ C8) (A8 ^ 2) :=
  BoundedConfig.segRLs_c_spec source_tm (T := 200) (by decide)

theorem ca_pair (width : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ ca_pair_calls width) []
      (A8 ^ width ++ C8 ++ C8 ++ rest)
      (A8 ^ (width + 2) ++ rest) := by
  unfold ca_pair_calls
  rw [pow_add_list A8 width 2]
  have h := (primary_lift 2 width (C8 ++ C8) (A8 ^ 2) ca_pair0).concat
    (SegRLs.nil (M := source_tm) rest)
  simpa only [List.append_assoc] using h

def c_sweep_calls (width : ℕ) : ℕ → ℕ
  | 0 => 0
  | pairs' + 1 => ca_pair_calls width + c_sweep_calls (width + 2) pairs'

theorem c_sweep (width pairs : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ c_sweep_calls width pairs) []
      (A8 ^ width ++ C8 ^ (2 * pairs + 1) ++ rest)
      (A8 ^ (width + 2 * pairs) ++ C8 ++ rest) := by
  induction pairs generalizing width with
  | zero =>
    simp only [c_sweep_calls, Nat.mul_zero, Nat.add_zero, pow_zero_list,
        List.append_assoc]
    exact .nil _
  | succ pairs ih =>
    rw [show 2 * (pairs + 1) + 1 = 2 + (2 * pairs + 1) by omega,
        pow_add_list C8 2 (2 * pairs + 1),
        show width + 2 * (pairs + 1) = (width + 2) + 2 * pairs by omega]
    dsimp [c_sweep_calls]
    have hpair := ca_pair width (C8 ^ (2 * pairs + 1) ++ rest)
    have htail := ih (width + 2)
    rw [List.append_assoc] at htail
    have hcomb := hpair.trans htail
    rw [← pow_add_list] at hcomb
    convert hcomb using 1 <;>
      simp only [pow_succ_list, C8, A8,
        List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

def ca_finish_calls (width : ℕ) : ℕ := 4 * 2 ^ width

theorem ca_finish0 :
    SegRLs source_tm (hashes ^ 4) []
      (C8 ++ B8 ++ U ++ [1, 1, 1, 1] ++ A8 ++ B8 ++ A8)
      (A8 ^ 3 ++ U ^ 2 ++ B8 ++ B8) :=
  BoundedConfig.segRLs_c_spec source_tm (T := 500) (by decide)

theorem ca_finish (width : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ ca_finish_calls width) []
      (A8 ^ width ++ C8 ++ B8 ++ U ++ [1, 1, 1, 1] ++ A8 ++ B8 ++ A8 ++ rest)
      (A8 ^ (width + 3) ++ U ^ 2 ++ B8 ++ B8 ++ rest) := by
  unfold ca_finish_calls
  rw [pow_add_list A8 width 3]
  have h := (primary_lift 4 width _ _ ca_finish0).concat (SegRLs.nil (M := source_tm) rest)
  simpa only [List.append_assoc] using h

def ca_start_calls (width : ℕ) : ℕ := 2 * 2 ^ width

theorem ca_start0 (k : ℕ) :
    SegRLs source_tm (hashes ^ 2) []
      (C8 ++ A8 ^ k ++ B8 ++ B8 ++ A8 ++ B8 ++ A8)
      (A8 ++ C8 ^ k ++ B8 ++ U ++ [1, 1, 1, 1] ++ A8 ++ B8 ++ A8) := by
  have h1 := (sobc1_hash_CAB1110 k).concat
    (SegRLs.nil (M := source_tm) ([1, 1, 1, 1] ++ A8 ++ B8 ++ A8))
  have h2 := hash_D.concat
    (SegRLs.nil (M := source_tm) (C8 ^ k ++ B8 ++ U ++ [1, 1, 1, 1] ++ A8 ++ B8 ++ A8))
  have h1' : SegRLs source_tm hashes []
      (C8 ++ (A8 ^ k ++ (B8 ++ (B8 ++ (A8 ++ (B8 ++ A8))))))
      (D8 ++ (C8 ^ k ++ (B8 ++ (U ++ ([1, 1, 1, 1] ++ (A8 ++ (B8 ++ A8))))))) := by
    have hsplit : B8 ++ (A8 ++ (B8 ++ A8)) = [1, 1, 1, 0] ++ ([1, 1, 1, 1] ++ (A8 ++ (B8 ++ A8))) :=
        rfl
    simpa only [List.append_assoc, hsplit] using h1
  have h2' : SegRLs source_tm hashes []
      (D8 ++ (C8 ^ k ++ (B8 ++ (U ++ ([1, 1, 1, 1] ++ (A8 ++ (B8 ++ A8)))))))
      (A8 ++ (C8 ^ k ++ (B8 ++ (U ++ ([1, 1, 1, 1] ++ (A8 ++ (B8 ++ A8))))))) := by
    simpa only [List.append_assoc] using h2
  have hcomb := h1'.trans h2'
  simpa only [pow_succ_list, pow_zero_list, List.append_nil, List.nil_append,
      List.append_assoc] using hcomb

theorem ca_start (width k : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ ca_start_calls width) []
      (A8 ^ width ++ C8 ++ A8 ^ k ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest)
      (A8 ^ (width + 1) ++ C8 ^ k ++ B8 ++ U ++ [1, 1, 1, 1] ++ A8 ++ B8 ++ A8 ++ rest) := by
  unfold ca_start_calls
  rw [pow_add_list A8 width 1, pow_one_list]
  have h := (primary_lift 2 width _ _ (ca_start0 k)).concat (SegRLs.nil (M := source_tm) rest)
  simpa only [List.append_assoc] using h

def ca_calls (primary pairs : ℕ) : ℕ :=
  ca_start_calls primary +
    (c_sweep_calls (primary + 1) pairs + ca_finish_calls (primary + 1 + 2 * pairs))

theorem ca_batch (primary pairs : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ ca_calls primary pairs) []
      (A8 ^ primary ++ C8 ++ A8 ^ (2 * pairs + 1) ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest)
      (A8 ^ (primary + 2 * pairs + 4) ++ U ^ 2 ++ B8 ++ B8 ++ rest) := by
  have hstart := ca_start primary (2 * pairs + 1) rest
  have hsweep := c_sweep (primary + 1) pairs (B8 ++ U ++ [1, 1, 1, 1] ++ A8 ++ B8 ++ A8 ++ rest)
  have hfinish := ca_finish (primary + 1 + 2 * pairs) rest
  unfold ca_calls
  rw [pow_add_list, pow_add_list,
      show primary + 2 * pairs + 4 = (primary + 1 + 2 * pairs) + 3 by omega]
  have h1 : SegRLs source_tm (hashes ^ ca_start_calls primary) []
      (A8 ^ primary ++ (C8 ++ (A8 ^ (2 * pairs + 1) ++ (B8 ++ (B8 ++ (A8 ++ (B8 ++ (A8 ++
          rest))))))))
      (A8 ^ (primary + 1) ++ (C8 ^ (2 * pairs + 1) ++ (B8 ++ (U ++ ([1, 1, 1,
          1] ++ (A8 ++ (B8 ++ (A8 ++ rest)))))))) := by
    simpa only [List.append_assoc] using hstart
  have h2 : SegRLs source_tm (hashes ^ c_sweep_calls (primary + 1) pairs) []
      (A8 ^ (primary + 1) ++ (C8 ^ (2 * pairs + 1) ++ (B8 ++ (U ++ ([1, 1, 1,
          1] ++ (A8 ++ (B8 ++ (A8 ++ rest))))))))
      (A8 ^ (primary + 1 + 2 * pairs) ++ (C8 ++ (B8 ++ (U ++ ([1, 1, 1,
          1] ++ (A8 ++ (B8 ++ (A8 ++ rest)))))))) := by
    simpa only [List.append_assoc] using hsweep
  have h3 : SegRLs source_tm (hashes ^ ca_finish_calls (primary + 1 + 2 * pairs)) []
      (A8 ^ (primary + 1 + 2 * pairs) ++ (C8 ++ (B8 ++ (U ++ ([1, 1, 1,
          1] ++ (A8 ++ (B8 ++ (A8 ++ rest))))))))
      (A8 ^ (primary + 1 + 2 * pairs + 3) ++ (U ^ 2 ++ (B8 ++ (B8 ++ rest)))) := by
    simpa only [List.append_assoc] using hfinish
  simpa only [List.nil_append, List.append_assoc] using h1.trans (h2.trans h3)

structure BinaryColumn where
  column_e : ℕ
  column_digits : List BDigit
  column_length : column_digits.length = column_e + 1

def mixed_column_word (c : BinaryColumn) : List (Fin 2) :=
  E8 ^ c.column_e ++ A8

def binary_column_word (c : BinaryColumn) : List (Fin 2) :=
  (digits_word A8 B8) c.column_digits

def column_required (out : ℕ) (c : BinaryColumn) : ℕ :=
  (out + 1) * 2 ^ (c.column_e + 1) - 2 + digits_value c.column_digits

def spaced_words : List (List (Fin 2)) → List (Fin 2)
  | [] => []
  | [word] => word
  | word :: w₂ :: words' => word ++ U ^ 2 ++ spaced_words (w₂ :: words')

theorem mixed_column_spec (c : BinaryColumn) (out : ℕ) :
    SegRLs source_tm (hashes ^ column_required out c) (hashes ^ out)
      (mixed_column_word c) (binary_column_word c) :=
  standard_mixed_to_binary_out_spec c.column_e c.column_digits out c.column_length

def columns_widths (columns : List BinaryColumn) : List ℕ :=
  (columns.map BinaryColumn.column_e).map (· + 1)

def columns_width_sum (columns : List BinaryColumn) : ℕ :=
  (columns_widths columns).foldr (· + ·) 0

theorem columns_width_sum_cons (c : BinaryColumn) (columns : List BinaryColumn) :
    columns_width_sum (c :: columns) = (c.column_e + 1) + columns_width_sum columns := rfl

def geom4n : ℕ → ℕ
  | 0 => 0
  | n' + 1 => 1 + 4 * geom4n n'

def half_parameter (n : ℕ) : ℕ := 2 * n + 6

def round_primary_width (current previous : ℕ) : ℕ :=
  half_parameter current + half_parameter previous + 6

def round_outer_suffix (previous : ℕ) : List BDigit :=
  [BB, BB, BA, BB, BA, BB] ++ z_tail_digits previous

def round_outer_digits (current previous : ℕ) : List BDigit :=
  List.replicate (half_parameter current + 2) BA ++ round_outer_suffix previous

def round_post_unary (current previous : ℕ) : ℕ :=
  cd_calls (half_parameter current) + ca_calls (half_parameter current) (previous + 4)

theorem geom4n_succ (n : ℕ) : geom4n (n + 1) = 1 + 4 * geom4n n := rfl

theorem c_sweep_calls_formula (width pairs : ℕ) :
    c_sweep_calls width pairs = 2 ^ (width + 1) * geom4n pairs := by
  induction pairs generalizing width with
  | zero => simp [c_sweep_calls, geom4n]
  | succ pairs ih =>
    dsimp [c_sweep_calls, geom4n, ca_pair_calls]
    rw [ih (width + 2), show width + 2 + 1 = (width + 1) + 2 by omega,
        Nat.pow_add 2 (width + 1) 2, Nat.pow_succ 2 width]
    ring

theorem ca_calls_formula (primary pairs : ℕ) :
    ca_calls primary pairs =
      2 ^ (primary + 1) + (2 ^ (primary + 2) * geom4n pairs + 2 ^ (primary + 2 * pairs + 3)) := by
  unfold ca_calls ca_start_calls ca_finish_calls
  rw [c_sweep_calls_formula,
      show 2 * 2 ^ primary = 2 ^ (primary + 1) by rw [Nat.pow_succ]; ring,
      show primary + 1 + 1 = primary + 2 by omega,
      show 4 * 2 ^ (primary + 1 + 2 * pairs) = 2 ^ (primary + 2 * pairs + 3) by
        rw [show primary + 2 * pairs + 3 = (primary + 1 + 2 * pairs) + 2 by omega,
            Nat.pow_add]; ring]

theorem cd_calls_formula (n : ℕ) (_hn : 1 ≤ n) : cd_calls n = 2 ^ (n + 1) - 2 := by
  unfold cd_calls
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [Nat.pow_succ]
  omega

theorem round_post_unary_formula (current previous : ℕ) :
    round_post_unary current previous =
      2 ^ (half_parameter current + 2) *
        (1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1)) - 2 := by
  unfold round_post_unary
  rw [cd_calls_formula _ (by unfold half_parameter; omega), ca_calls_formula]
  have hstep : 2 ^ (half_parameter current + 2) = 2 * 2 ^ (half_parameter current + 1) := by
    rw [show half_parameter current + 2 = (half_parameter current + 1) + 1 by omega, Nat.pow_succ]
    ring
  have h2 : 2 ^ (half_parameter current + 2 * (previous + 4) + 3) =
      (2 * 2 ^ (half_parameter current + 1)) * 2 ^ (2 * (previous + 4) + 1) := by
    rw [← hstep, ← Nat.pow_add]
    congr 1; omega
  have hpos : 2 ≤ 2 ^ (half_parameter current + 1) := by
    have : 1 ≤ 2 ^ (half_parameter current) := Nat.one_le_two_pow
    rw [Nat.pow_succ]; omega
  rw [hstep, h2]
  have hmul : 2 * 2 ^ (half_parameter current + 1) *
      (1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1)) =
      2 * 2 ^ (half_parameter current + 1) +
        2 * 2 ^ (half_parameter current + 1) * geom4n (previous + 4) +
        2 * 2 ^ (half_parameter current + 1) * 2 ^ (2 * (previous + 4) + 1) := by ring
  omega

theorem digits_value_app (ds₁ ds₂ : List BDigit) :
    digits_value (ds₁ ++ ds₂) = digits_value ds₁ + 2 ^ ds₁.length * digits_value ds₂ := by
  induction ds₁ with
  | nil => simp [digits_value]
  | cons d ds₁ ih =>
    rcases d with _ | _ <;> dsimp [digits_value, List.length] <;> rw [ih, Nat.pow_succ] <;> ring

theorem digits_value_repeat_BA (n : ℕ) : digits_value (List.replicate n BA) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, digits_value, ih]

theorem round_outer_suffix_length (previous : ℕ) :
    (round_outer_suffix previous).length = 2 * previous + 10 := by
  unfold round_outer_suffix
  simp only [List.length_append, z_tail_digits_length, List.length]
  omega

theorem round_outer_digits_length (current previous : ℕ) :
    (round_outer_digits current previous).length = round_primary_width current previous := by
  unfold round_outer_digits round_primary_width half_parameter
  simp only [List.length_append, List.length_replicate, round_outer_suffix_length]
  omega

theorem round_outer_suffix_succ (previous : ℕ) :
    digits_value (round_outer_suffix (previous + 1)) + 1 =
      4 * digits_value (round_outer_suffix previous) := by
  unfold round_outer_suffix
  rw [digits_value_app, digits_value_app]
  dsimp [z_tail_digits, digits_value, List.length]
  omega

theorem round_outer_suffix_formula (previous : ℕ) :
    2 * digits_value (round_outer_suffix previous) =
      1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1) + 2 ^ (2 * (previous + 4) + 2) := by
  induction previous with
  | zero => rfl
  | succ previous ih =>
    have hstep := round_outer_suffix_succ previous
    rw [show previous + 1 + 4 = (previous + 4) + 1 by omega, geom4n_succ,
        show 2 * (previous + 4 + 1) + 1 = (2 * (previous + 4) + 1) + 2 by omega,
        show 2 * (previous + 4 + 1) + 2 = (2 * (previous + 4) + 2) + 2 by omega,
        Nat.pow_add 2 (2 * (previous + 4) + 1) 2,
        Nat.pow_add 2 (2 * (previous + 4) + 2) 2]
    omega

theorem round_outer_digits_value (current previous : ℕ) :
    digits_value (round_outer_digits current previous) =
      2 ^ (half_parameter current + 1) *
        (1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1) + 2 ^ (2 * (previous + 4) + 2)) :=
            by
  unfold round_outer_digits
  rw [digits_value_app, digits_value_repeat_BA, List.length_replicate, Nat.zero_add,
      show half_parameter current + 2 = (half_parameter current + 1) + 1 by omega,
      Nat.pow_succ, Nat.mul_assoc, round_outer_suffix_formula]

theorem round_unary_decodes_outer (current previous : ℕ) :
    round_post_unary current previous / 2 + 1 + 2 ^ (round_primary_width current previous - 1) =
      digits_value (round_outer_digits current previous) := by
  rw [round_post_unary_formula, round_outer_digits_value]
  have hhalf : ∀ n q, 1 ≤ q → (2 ^ (n + 2) * q - 2) / 2 + 1 = 2 ^ (n + 1) * q := by
    intro n q hq
    have hpow : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.pow_succ]; ring
    have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have hmul : 1 ≤ 2 ^ (n + 1) * q := Nat.mul_pos hpos hq
    have hmul2 : 2 * 2 ^ (n + 1) * q = (2 ^ (n + 1) * q) * 2 := by ring
    rw [hpow, hmul2, show (2 ^ (n + 1) * q) * 2 - 2 = (2 ^ (n + 1) * q - 1) * 2 by omega,
        Nat.mul_div_cancel _ (by decide)]
    omega
  have hq : 1 ≤ 1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1) := by
    rw [Nat.add_assoc]; exact Nat.le_add_right 1 _
  rw [hhalf (half_parameter current) _ hq]
  have hp : 2 ^ (round_primary_width current previous - 1) =
      2 ^ (half_parameter current + 1) * 2 ^ (2 * (previous + 4) + 2) := by
    rw [← Nat.pow_add]
    congr 1
    unfold round_primary_width half_parameter; omega
  rw [hp]
  ring

theorem digits_word_repeat_BA (n : ℕ) : (digits_word A8 B8) (List.replicate n BA) = A8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, digits_word, digit_word, ih]

theorem digits_word_app (ds₁ ds₂ : List BDigit) :
    (digits_word A8 B8) (ds₁ ++ ds₂) = (digits_word A8 B8) ds₁ ++ (digits_word A8 B8) ds₂ := by
  induction ds₁ with
  | nil => rfl
  | cons d ds₁ ih => simp [digits_word, ih, List.append_assoc]

theorem round_outer_digits_word (current previous : ℕ) :
    (digits_word A8 B8) (round_outer_digits current previous) =
      A8 ^ (half_parameter current + 2) ++
        B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ B8 ++ (digits_word A8 B8) (z_tail_digits previous) := by
  unfold round_outer_digits round_outer_suffix
  rw [digits_word_app, digits_word_app, digits_word_repeat_BA]
  have h6 : (digits_word A8 B8) [BB, BB, BA, BB, BA, BB] = B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ B8 := rfl
  rw [h6]
  simp only [List.append_assoc]

theorem z_digits_word_split (previous : ℕ) :
    (digits_word A8 B8) (z_digits previous) =
      B8 ++ B8 ++ B8 ++ (digits_word A8 B8) (z_tail_digits previous) := rfl

theorem raw_separator_return (l r : ListBlank (Fin 2)) :
    (([1, 0, 1] +> (X4 ^ 2 +> (Q8 +> l))) <{{F}} r) [source_tm]⊢⁺
      (([1, 0, 1] +> l) <{{F}} ((A8 ++ U ^ 2) +> r)) := by
  have h := run1Steps_spec source_tm 57
    ⟨[], [1, 0, 1] ++ X4 ^ 2 ++ Q8, F, .left⟩
    ⟨A8 ++ U ^ 2, [1, 0, 1], F, .left⟩ (by decide) (by decide) l r
  simpa only [BoundedConfig.toCfg, List.append_assoc, append_assoc, append_nil] using h

theorem raw_Bs_to_Qs (k : ℕ) : SegRR source_tm (B, []) (B, []) (B8 ^ k) (Q8 ^ k) :=
  segRR_lpow_same (B, []) B8 Q8 k raw_B_forward

theorem raw_B_returns (k : ℕ) (l r : ListBlank (Fin 2)) :
    (([1, 0, 1] +> (Q8 ^ k +> l)) <{{F}} r) [source_tm]⊢*
      (([1, 0, 1] +> l) <{{F}} (E8 ^ k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [pow_zero_list, append_nil]
    exact stepStar_refl source_tm _
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (stepPlus_to_stepStar (raw_B_return (Q8 ^ k +> l) r)) ?_
    have hrec := ih l (E8 +> r)
    simpa only [pow_succ_list', append_assoc] using hrec

theorem primary_D_absorb (primary : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ (2 ^ primary)) []
      (A8 ^ primary ++ D8 ++ rest)
      (A8 ^ (primary + 1) ++ rest) := by
  have h := primary_one_rule primary (D8 ++ rest) (A8 ++ rest)
    (hash_D.concat (SegRLs.nil (M := source_tm) rest))
  rw [pow_succ_list' A8 primary]
  simpa only [List.append_assoc] using h

theorem initial_u_pairs (primary pairs : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ initial_u_pair_calls primary pairs) []
      (A8 ^ primary ++ C8 ++ A8 ++ U ^ (2 * pairs) ++ rest)
      (A8 ^ (primary + pairs) ++ C8 ++ A8 ++ rest) := by
  induction pairs generalizing primary with
  | zero =>
    simp only [initial_u_pair_calls, Nat.mul_zero, Nat.add_zero, pow_zero_list, List.append_nil]
    exact .nil _
  | succ pairs ih =>
    dsimp [initial_u_pair_calls]
    have hca := primary_one_rule primary
      (C8 ++ A8 ++ U ++ U ++ (U ^ (2 * pairs) ++ rest))
      (D8 ++ C8 ++ A8 ++ (U ^ (2 * pairs) ++ rest))
      (hash_CAUU.concat (SegRLs.nil (M := source_tm) (U ^ (2 * pairs) ++ rest)))
    have hd := primary_D_absorb primary (C8 ++ A8 ++ U ^ (2 * pairs) ++ rest)
    have hrec := ih (primary + 1)
    rw [show 2 * 2 ^ primary + initial_u_pair_calls (primary + 1) pairs =
        2 ^ primary + (2 ^ primary + initial_u_pair_calls (primary + 1) pairs) by omega,
        pow_add_list, pow_add_list,
        show 2 * (pairs + 1) = 2 + 2 * pairs by omega,
        pow_add_list U 2 (2 * pairs),
        show primary + (pairs + 1) = (primary + 1) + pairs by omega]
    have hca' : SegRLs source_tm (hashes ^ (2 ^ primary)) []
        (A8 ^ primary ++ (C8 ++ (A8 ++ (U ^ 2 ++ (U ^ (2 * pairs) ++ rest)))))
        (A8 ^ primary ++ (D8 ++ (C8 ++ (A8 ++ (U ^ (2 * pairs) ++ rest))))) := by
      simpa only [pow_succ_list, pow_zero_list, List.append_nil, List.append_assoc] using hca
    have hd' : SegRLs source_tm (hashes ^ (2 ^ primary)) []
        (A8 ^ primary ++ (D8 ++ (C8 ++ (A8 ++ (U ^ (2 * pairs) ++ rest)))))
        (A8 ^ (primary + 1) ++ (C8 ++ (A8 ++ (U ^ (2 * pairs) ++ rest)))) := by
      simpa only [List.append_assoc] using hd
    have hrec' : SegRLs source_tm (hashes ^ initial_u_pair_calls (primary + 1) pairs) []
        (A8 ^ (primary + 1) ++ (C8 ++ (A8 ++ (U ^ (2 * pairs) ++ rest))))
        (A8 ^ (primary + 1 + pairs) ++ (C8 ++ (A8 ++ rest))) := by
      simpa only [List.append_assoc] using hrec
    simpa only [List.nil_append, List.append_assoc] using hca'.trans (hd'.trans hrec')

theorem zero_primary_finish_seg (width : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ (2 ^ width - 1)) []
      (A8 ^ width ++ rest) (B8 ^ width ++ rest) := by
  have h :=
      ((bfinish_spec hash_A_finish hash_B_finish) (List.replicate width BA) 0).concat (SegRLs.nil
      (M := source_tm) rest)
  rw [bfinish_repeat_BA_formula, digits_word_repeat_BA, List.length_replicate] at h
  simpa only [Nat.zero_add, Nat.one_mul, pow_zero_list, List.append_nil] using h

theorem bfinish_count_value (ds : List BDigit) (out : ℕ) :
    bfinish_count ds out + digits_value ds + 1 = (out + 1) * 2 ^ ds.length := by
  induction ds generalizing out with
  | nil => simp [bfinish_count, digits_value]
  | cons d ds ih =>
    have hrec := ih out
    rcases d with _ | _ <;> dsimp [bfinish_count, digits_value, List.length] <;>
      rw [Nat.pow_succ] <;> linarith

theorem digits_value_bound (ds : List BDigit) : digits_value ds < 2 ^ ds.length := by
  induction ds with
  | nil => simp [digits_value]
  | cons d ds ih =>
    rcases d with _ | _ <;> dsimp [digits_value, List.length] <;> rw [Nat.pow_succ] <;> omega

theorem binary_column_value_bound (c : BinaryColumn) :
    digits_value c.column_digits < 2 ^ (c.column_e + 1) := by
  have h := digits_value_bound c.column_digits
  rwa [c.column_length] at h

def column_value (c : BinaryColumn) : ℕ := digits_value c.column_digits
def column_width (c : BinaryColumn) : ℕ := c.column_e + 1

def column_safe (c : BinaryColumn) : Prop :=
  3 ≤ column_value c ∧ column_value c ≤ 2 ^ (column_width c) - 6

theorem column_safe_lower (c : BinaryColumn) (h : column_safe c) : 3 ≤ column_value c := h.1

def column_next_value (right_odd : Bool) (c : BinaryColumn) : ℕ :=
  (if right_odd then 2 ^ c.column_e else 2 ^ (c.column_e + 1)) - column_value c / 2

def column_step (right_odd : Bool) (c c' : BinaryColumn) : Prop :=
  c'.column_e = c.column_e ∧ column_value c' = column_next_value right_odd c

theorem column_next_value_bound (right_odd : Bool) (c : BinaryColumn) (hlower : 3 ≤ column_value c)
    :
    column_next_value right_odd c < 2 ^ (column_width c) := by
  unfold column_next_value column_width
  have hpos : 1 ≤ 2 ^ c.column_e := Nat.one_le_two_pow
  rcases right_odd with _ | _ <;> dsimp <;> rw [Nat.pow_succ] <;> omega

theorem column_step_exists (right_odd : Bool) (c : BinaryColumn) (hlower : 3 ≤ column_value c) :
    ∃ c', column_step right_odd c c' := by
  have hbound := column_next_value_bound right_odd c hlower
  obtain ⟨ds, hlen, hval⟩ := digits_exist (column_width c) (column_next_value right_odd c) hbound
  exact ⟨⟨c.column_e, ds, hlen⟩, rfl, hval⟩

def ceil_half (n : ℕ) : ℕ := (n + 1) / 2

theorem ceil_half_scaled_sub (t w v : ℕ) (ht : 1 ≤ t) (hw : 1 ≤ w) (hv : v < 2 ^ w) :
    ceil_half (t * 2 ^ w - v) = t * 2 ^ (w - 1) - v / 2 := by
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    conv_lhs => rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    ring
  have hmul : 2 ^ w ≤ t * 2 ^ w := Nat.le_mul_of_pos_left _ ht
  unfold ceil_half
  rw [hpow] at hv hmul ⊢
  have hrewrite : t * (2 * 2 ^ (w - 1)) = 2 * (t * 2 ^ (w - 1)) := by ring
  rw [hrewrite] at hmul ⊢
  omega

theorem round_primary_width_positive (current previous : ℕ) :
    1 ≤ round_primary_width current previous := by
  unfold round_primary_width half_parameter; omega

def round_outer_column (current previous : ℕ) : BinaryColumn :=
  ⟨round_primary_width current previous - 1,
   round_outer_digits current previous,
   by
     rw [round_outer_digits_length]
     have := round_primary_width_positive current previous
     omega⟩

theorem round_outer_column_word (current previous : ℕ) :
    binary_column_word (round_outer_column current previous) =
      A8 ^ (half_parameter current + 2) ++
        B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ B8 ++ (digits_word A8 B8) (z_tail_digits previous) :=
  round_outer_digits_word current previous

theorem round_post_unary_half_formula (current previous : ℕ) :
    round_post_unary current previous / 2 =
      2 ^ (half_parameter current + 1) *
        (1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1)) - 1 := by
  rw [round_post_unary_formula]
  set h := half_parameter current
  set body := 1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1)
  have hbody : 1 ≤ body := by dsimp [body]; rw [Nat.add_assoc]; exact Nat.le_add_right 1 _
  have hpow : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
  have hmul : 1 ≤ 2 ^ (h + 1) * body := Nat.mul_pos hpow hbody
  have hmul2 : (2 ^ (h + 1) * 2) * body = (2 ^ (h + 1) * body) * 2 := by ring
  rw [show h + 2 = (h + 1) + 1 by omega, Nat.pow_succ, hmul2,
      show (2 ^ (h + 1) * body) * 2 - 2 = (2 ^ (h + 1) * body - 1) * 2 by omega,
      Nat.mul_div_cancel _ (by decide)]

def frontier_es (current previous : ℕ) (columns : List BinaryColumn) : List ℕ :=
  (round_primary_width current previous - 1) :: columns.map BinaryColumn.column_e

def z_column (previous : ℕ) : BinaryColumn :=
  ⟨half_parameter previous,
   z_digits previous,
   by rw [z_digits_length]; unfold z_birth_width half_parameter; omega⟩

theorem z_column_word (previous : ℕ) :
    binary_column_word (z_column previous) = (digits_word A8 B8) (z_digits previous) := rfl

theorem z_column_e (previous : ℕ) :
    (z_column previous).column_e = half_parameter previous := rfl

theorem ca_calls_positive (primary pairs : ℕ) : 1 ≤ ca_calls primary pairs := by
  unfold ca_calls ca_start_calls
  have : 1 ≤ 2 ^ primary := Nat.one_le_two_pow
  omega

theorem exception_done_ca (n pairs : ℕ) (rest : List (Fin 2)) (hn : 1 ≤ n) :
    (exception_done n (A8 ^ (2 * pairs) ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest)) [source_tm]⊢⁺
      ((ordinary_left (cd_calls n + ca_calls n pairs)) {{B}}>
        ((A8 ^ (n + 2 * pairs + 4) ++ U ^ 2 ++ B8 ++ B8 ++ rest) +> default)) := by
  refine stepPlus_trans (exception_done_cd n _ hn) ?_
  unfold after_cd
  have heq : cd_output n ++ (A8 ^ (2 * pairs) ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest) =
      A8 ^ n ++ C8 ++ A8 ^ (2 * pairs + 1) ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest := by
    unfold cd_output
    rw [show 2 * pairs + 1 = 1 + 2 * pairs by omega, pow_add_list A8 1 (2 * pairs), pow_one_list]
    simp only [List.append_assoc]
  rw [heq]
  exact ordinary_seg_run_pos (ca_calls n pairs) (cd_calls n) _ _ default
    (ca_calls_positive n pairs) (ca_batch n pairs rest)

theorem pow2_linear_margin (n : ℕ) : 2 * n + 8 ≤ 2 ^ (n + 5) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 5 = (n + 5) + 1 by omega, Nat.pow_succ]
    omega

theorem z_column_width (previous : ℕ) :
    column_width (z_column previous) = z_birth_width previous := by
  unfold column_width z_birth_width
  rw [z_column_e]
  unfold half_parameter; omega

theorem z_column_value (previous : ℕ) :
    (column_value (z_column previous) : ℤ) = z_birth_value previous :=
  z_digits_value previous

theorem z_birth_value_odd (n : ℕ) : z_birth_value n % 2 = 1 := by
  rw [z_birth_complement]; omega

theorem z_column_odd (previous : ℕ) : column_value (z_column previous) % 2 = 1 := by
  have h := z_column_value previous
  have hodd := z_birth_value_odd previous
  omega

@[ext]
structure AbstractColumn where
  abstract_width : ℕ
  abstract_value : ℤ

def abstract_of_column (c : BinaryColumn) : AbstractColumn :=
  ⟨column_width c, (column_value c : ℤ)⟩

def abstract_safe (c : AbstractColumn) : Prop :=
  3 ≤ c.abstract_value ∧ c.abstract_value ≤ pow2 c.abstract_width - 6

def abstract_step (right_odd : Bool) (c : AbstractColumn) : AbstractColumn :=
  ⟨c.abstract_width,
   arbitrary_column_step (pow2 c.abstract_width) right_odd c.abstract_value⟩

theorem column_safe_abstract (c : BinaryColumn) :
    column_safe c ↔ abstract_safe (abstract_of_column c) := by
  unfold column_safe abstract_safe abstract_of_column
  dsimp
  rw [pow2_nat]
  rcases h : column_width c with _ | _ | _ | k
  · unfold column_width at h; omega
  · omega
  · omega
  · have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [show k + 1 + 1 + 1 = k + 3 by omega, Nat.pow_add]
    omega

theorem abstract_column_step (c c' : BinaryColumn) (right_odd : Bool)
    (hsafe : column_safe c) (hstep : column_step right_odd c c') :
    abstract_of_column c' = abstract_step right_odd (abstract_of_column c) := by
  rcases hstep with ⟨he, hv⟩
  unfold abstract_of_column abstract_step
  ext
  · dsimp; unfold column_width; omega
  · dsimp
    rw [hv]
    unfold arbitrary_column_step column_next_value
    have hhalf : column_value c / 2 ≤ 2 ^ c.column_e := by
      rcases hsafe with ⟨_, h2⟩
      unfold column_width at h2
      rw [Nat.pow_succ] at h2
      omega
    rcases right_odd with _ | _
    · dsimp
      rw [pow2_nat, column_width, Nat.pow_succ]
      omega
    · dsimp
      rw [pow2_nat, column_width, Nat.pow_succ]
      omega

-- ============================================================================
-- 4. `W61Exit` Translated Cycler, Raw Tail Pass & Nested Exit (`PR_SOBCv10.v` lines 64–399)
-- ============================================================================

def y_after : ℕ → List (Fin 2)
  | 0 => A8
  | 1 => B8
  | 2 => E8 ++ [1, 1]
  | 3 => D8 ++ [1, 1]
  | 4 => A8 ++ [1, 1]
  | _ => B8 ++ [1, 1]

def tail_word (k : ℕ) : List (Fin 2) :=
  U ^ (2 * k + 1) ++ B8 ++ [1, 1]

theorem raw_tail_base (k : ℕ) (l : ListBlank (Fin 2)) (hk : k ≤ 5) :
    (l {{B}}> ((B8 ++ U ^ (2 * k + 1) ++ B8 ++ [1, 1]) +> default)) [source_tm]⊢⁺
      (([1, 0, 1] +> l) <{{F}} ((U ^ (2 * k + 3) ++ y_after k) +> default)) := by
  rcases k with _ | _ | _ | _ | _ | _ | k
  · have h := check_r0inf_spec (M := source_tm) (n := 97)
      (l₁ := []) (r₁ := B8 ++ U ^ 1 ++ B8 ++ [1, 1]) (l₂ := U ^ 3 ++ y_after 0) (r₂ := [1, 0, 1])
      (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
    simpa only [BoundedConfig.toCfg, append_nil] using h
  · have h := check_r0inf_spec (M := source_tm) (n := 199)
      (l₁ := []) (r₁ := B8 ++ U ^ 3 ++ B8 ++ [1, 1]) (l₂ := U ^ 5 ++ y_after 1) (r₂ := [1, 0, 1])
      (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
    simpa only [BoundedConfig.toCfg, append_nil] using h
  · have h := check_r0inf_spec (M := source_tm) (n := 343)
      (l₁ := []) (r₁ := B8 ++ U ^ 5 ++ B8 ++ [1, 1]) (l₂ := U ^ 7 ++ y_after 2) (r₂ := [1, 0, 1])
      (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
    simpa only [BoundedConfig.toCfg, append_nil] using h
  · have h := check_r0inf_spec (M := source_tm) (n := 501)
      (l₁ := []) (r₁ := B8 ++ U ^ 7 ++ B8 ++ [1, 1]) (l₂ := U ^ 9 ++ y_after 3) (r₂ := [1, 0, 1])
      (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
    simpa only [BoundedConfig.toCfg, append_nil] using h
  · have h := check_r0inf_spec (M := source_tm) (n := 695)
      (l₁ := []) (r₁ := B8 ++ U ^ 9 ++ B8 ++ [1, 1]) (l₂ := U ^ 11 ++ y_after 4) (r₂ := [1, 0, 1])
      (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
    simpa only [BoundedConfig.toCfg, append_nil] using h
  · have h := check_r0inf_spec (M := source_tm) (n := 909)
      (l₁ := []) (r₁ := B8 ++ U ^ 11 ++ B8 ++ [1, 1]) (l₂ := U ^ 13 ++ y_after 5) (r₂ := [1, 0, 1])
      (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
    simpa only [BoundedConfig.toCfg, append_nil] using h
  · omega

theorem raw_tail_column (k e : ℕ) (l : ListBlank (Fin 2)) (hk : k ≤ 5) :
    (l {{B}}> ((B8 ^ (e + 1) ++ tail_word k) +> default)) [source_tm]⊢⁺
      (([1, 0, 1] +> l) <{{F}} ((E8 ^ e ++ U ^ (2 * k + 3) ++ y_after k) +> default)) := by
  induction e generalizing l with
  | zero =>
    unfold tail_word
    rw [Nat.zero_add, pow_one_list, pow_zero_list, List.nil_append]
    simpa only [List.append_assoc] using raw_tail_base k l hk
  | succ e ih =>
    rw [pow_succ_list B8 (e + 1), List.append_assoc, append_assoc]
    refine stepStar_stepPlus_trans (raw_B_forward l ((B8 ^ (e + 1) ++ tail_word k) +> default)) ?_
    refine stepPlus_trans (ih (Q8 +> l)) ?_
    have hret := raw_B_return l ((E8 ^ e ++ U ^ (2 * k + 3) ++ y_after k) +> default)
    rw [pow_succ_list E8 e]
    simpa only [List.append_assoc, append_assoc] using hret

def full_tail (es : List ℕ) (e k : ℕ) : List (Fin 2) :=
  spaced_words (es.map (fun e => B8 ^ (e + 1)) ++ [B8 ^ (e + 1)]) ++ tail_word k

def mixed_tail (es : List ℕ) (e k : ℕ) : List (Fin 2) :=
  spaced_words (es.map (fun e => E8 ^ e ++ A8) ++ [E8 ^ e]) ++ U ^ (2 * k + 3) ++ y_after k

theorem spaced_snoc_cons (w : List (Fin 2)) (ws : List (List (Fin 2))) (x : List (Fin 2)) :
    spaced_words ((w :: ws) ++ [x]) = w ++ U ^ 2 ++ spaced_words (ws ++ [x]) := by
  rcases ws with _ | ⟨w₂, ws⟩ <;> rfl

theorem full_tail_cons (e₀ : ℕ) (es : List ℕ) (e k : ℕ) :
    full_tail (e₀ :: es) e k = B8 ^ (e₀ + 1) ++ U ^ 2 ++ full_tail es e k := by
  unfold full_tail
  rw [List.map_cons, spaced_snoc_cons]
  simp only [List.append_assoc]

theorem mixed_tail_cons (e₀ : ℕ) (es : List ℕ) (e k : ℕ) :
    mixed_tail (e₀ :: es) e k = E8 ^ e₀ ++ A8 ++ U ^ 2 ++ mixed_tail es e k := by
  unfold mixed_tail
  rw [List.map_cons, spaced_snoc_cons]
  simp only [List.append_assoc]

theorem raw_tail_columns (es : List ℕ) (e k : ℕ) (l : ListBlank (Fin 2)) (hk : k ≤ 5) :
    (l {{B}}> (full_tail es e k +> default)) [source_tm]⊢⁺
      (([1, 0, 1] +> l) <{{F}} (mixed_tail es e k +> default)) := by
  induction es generalizing l with
  | nil =>
    exact raw_tail_column k e l hk
  | cons e₀ es ih =>
    rw [full_tail_cons, mixed_tail_cons, List.append_assoc, append_assoc]
    refine stepStar_stepPlus_trans
      (raw_Bs_to_Qs (e₀ + 1) l ((U ^ 2 ++ full_tail es e k) +> default)) ?_
    rw [append_assoc (U ^ 2)]
    refine stepStar_stepPlus_trans
      (raw_Us_to_Xs 2 (Q8 ^ (e₀ + 1) +> l) (full_tail es e k +> default)) ?_
    refine stepPlus_trans (ih (X4 ^ 2 +> (Q8 ^ (e₀ + 1) +> l))) ?_
    rw [pow_succ_list Q8 e₀, append_assoc Q8 (Q8 ^ e₀)]
    refine stepPlus_stepStar_trans
      (raw_separator_return (Q8 ^ e₀ +> l) (mixed_tail es e k +> default)) ?_
    have hret := raw_B_returns e₀ l ((A8 ++ U ^ 2 ++ mixed_tail es e k) +> default)
    simpa only [List.append_assoc, append_assoc] using hret

def Yw : List (Fin 2) :=
  [1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,
   1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,1,0,1,0,0,1,0,0]

theorem cycler_step (L : ListBlank (Fin 2)) :
    ((Yw.reverse +> L) {{B}}> default) [source_tm]⊢⁺
      ((Yw.reverse +> ([0, 0, 1] +> L)) {{B}}> default) := by
  have h := check_r0inf_spec (M := source_tm) (n := 918)
    (l₁ := Yw.reverse) (r₁ := []) (l₂ := Yw.reverse ++ [0, 0, 1]) (r₂ := [])
    (q₁ := B) (q₂ := B) (d₁ := .right) (d₂ := .right) (by decide) L
  simpa only [BoundedConfig.toCfg, List.append_assoc, append_assoc, append_nil] using h

theorem cycler_nonhalt (L : ListBlank (Fin 2)) :
    NeverHaltsFrom source_tm ((Yw.reverse +> L) {{B}}> default) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant
    (P := fun c => ∃ L', c = ((Yw.reverse +> L') {{B}}> default)) ?_ ⟨L, rfl⟩
  rintro _ ⟨L', rfl⟩
  exact ⟨(Yw.reverse +> ([0, 0, 1] +> L')) {{B}}> default, cycler_step L', [0, 0, 1] +> L', rfl⟩

theorem overflow_base (l : ListBlank (Fin 2)) :
    (l {{B}}> ((B8 ++ tail_word 6) +> default)) [source_tm]⊢⁺
      ((Yw.reverse +> ([0, 1, 0, 1] +> l)) {{B}}> default) := by
  have h := check_r0inf_spec (M := source_tm) (n := 1207)
    (l₁ := []) (r₁ := B8 ++ tail_word 6) (l₂ := Yw.reverse ++ [0, 1, 0, 1]) (r₂ := [])
    (q₁ := B) (q₂ := B) (d₁ := .right) (d₂ := .right) (by decide) l
  simpa only [BoundedConfig.toCfg, List.append_assoc, append_assoc, append_nil] using h

theorem overflow_column (e : ℕ) (l : ListBlank (Fin 2)) :
    ∃ l', (l {{B}}> ((B8 ^ (e + 1) ++ tail_word 6) +> default)) [source_tm]⊢⁺
      ((Yw.reverse +> l') {{B}}> default) := by
  induction e generalizing l with
  | zero =>
    refine ⟨[0, 1, 0, 1] +> l, ?_⟩
    rw [Nat.zero_add, pow_one_list]
    exact overflow_base l
  | succ e ih =>
    obtain ⟨l', h⟩ := ih (Q8 +> l)
    refine ⟨l', ?_⟩
    rw [pow_succ_list B8 (e + 1), List.append_assoc, append_assoc]
    exact stepStar_stepPlus_trans (raw_B_forward l ((B8 ^ (e + 1) ++ tail_word 6) +> default)) h

theorem overflow_columns (es : List ℕ) (e : ℕ) (l : ListBlank (Fin 2)) :
    ∃ l', (l {{B}}> (full_tail es e 6 +> default)) [source_tm]⊢⁺
      ((Yw.reverse +> l') {{B}}> default) := by
  induction es generalizing l with
  | nil =>
    exact overflow_column e l
  | cons e₀ es ih =>
    obtain ⟨l', h⟩ := ih (X4 ^ 2 +> (Q8 ^ (e₀ + 1) +> l))
    refine ⟨l', ?_⟩
    rw [full_tail_cons, List.append_assoc, append_assoc]
    refine stepStar_stepPlus_trans
      (raw_Bs_to_Qs (e₀ + 1) l ((U ^ 2 ++ full_tail es e 6) +> default)) ?_
    rw [append_assoc (U ^ 2)]
    exact stepStar_stepPlus_trans
      (raw_Us_to_Xs 2 (Q8 ^ (e₀ + 1) +> l) (full_tail es e 6 +> default)) h

def pre_left_far (n : ℕ) (far : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ([1, 0, 1, 0] ++ V4 ^ (2 * n + 2)) +> far

def call_left_far (remaining finished : ℕ) (far : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  (X4 ^ (2 * finished + 5) ++ V4 ^ (2 * remaining)) +> far

theorem pre_rotate_list (m : ℕ) :
    [1, 0, 1] ++ X4 ^ (m + 1) = [1, 0, 1, 0] ++ V4 ^ m ++ [0, 1, 0] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_list' X4 (m + 1), ← List.append_assoc, ih, pow_succ_list' V4 m]
    simp only [List.append_assoc]
    rfl

theorem nested_pre_left (c f : ℕ) :
    ([1, 0, 1] +> exception_call_left c f) =
      pre_left_far (f + 1) ([0, 1, 0] +> (V4 ^ (2 * c) +> ([1, 0, 1] +> default))) := by
  unfold exception_call_left pre_left_far
  rw [← append_assoc, ← append_assoc, ← append_assoc, ← append_assoc]
  congr 1
  rw [show 2 * f + 5 = (2 * f + 4) + 1 by omega,
      show 2 * (f + 1) + 2 = 2 * f + 4 by omega,
      ← List.append_assoc [1, 0, 1], ← List.append_assoc [1, 0, 1],
      pre_rotate_list (2 * f + 4)]

theorem launch_far (k : ℕ) (far : ListBlank (Fin 2)) :
    SideRLs (flipTM source_tm) [left_hash]
      (pre_left_far (k + 1) far) (call_left_far k 0 far) := by
  unfold pre_left_far call_left_far
  rw [show 2 * (k + 1) + 2 = 4 + 2 * k by omega, pow_add_list V4 4 (2 * k)]
  have h := left_launch_segment.sideRLs_concat
    (SideRLs.nil (M := flipTM source_tm) (V4 ^ (2 * k) +> far))
  simpa only [Nat.mul_zero, Nat.zero_add, List.append_assoc, append_assoc] using h

theorem relaunch_far (remaining finished : ℕ) (far : ListBlank (Fin 2)) :
    SideRLs (flipTM source_tm) [left_hash]
      (call_left_far (remaining + 1) finished far)
      (call_left_far remaining (finished + 1) far) := by
  have hseg := (left_hash_X_pairs finished).concat left_relaunch_base
  have hside := hseg.sideRLs_concat
    (SideRLs.nil (M := flipTM source_tm) (V4 ^ (2 * remaining) +> far))
  unfold call_left_far
  rw [show 2 * (remaining + 1) = 2 + 2 * remaining by omega,
      show 2 * (finished + 1) + 5 = 2 * finished + 7 by omega,
      pow_add_list V4 2 (2 * remaining),
      pow_add_list X4 (2 * finished) 5,
      pow_add_list X4 (2 * finished) 7]
  simpa only [List.append_assoc, append_assoc] using hside

theorem relaunches_far (k r finished : ℕ) (far : ListBlank (Fin 2)) :
    SideRLs (flipTM source_tm) ([left_hash] ^ k)
      (call_left_far (k + r) finished far)
      (call_left_far r (finished + k) far) := by
  induction k generalizing finished with
  | zero =>
    simp only [pow_zero_list, Nat.zero_add, Nat.add_zero]
    exact .nil _
  | succ k ih =>
    rw [pow_succ_list, show k + 1 + r = (k + r) + 1 by omega]
    have h := (relaunch_far (k + r) finished far).trans (ih (finished + 1))
    simpa only [Nat.add_right_comm finished 1 k, Nat.add_assoc] using h

theorem nested_launch (h r : ℕ) (far : ListBlank (Fin 2)) (inp out : List (Fin 2))
    (hseg : SegRLs source_tm (hashes ^ h) [] inp out) :
    ((pre_left_far (h + r + 1) far) <{{F}} (inp +> default)) [source_tm]⊢⁺
      ((call_left_far r h far) {{B}}> (out +> default)) := by
  refine stepPlus_stepStar_trans ((launch_far (h + r) far).elim_single_left (inp +> default)) ?_
  rcases h with _ | h
  · cases hseg
    simp only [Nat.zero_add]
    exact stepStar_refl source_tm _
  · refine stepPlus_to_stepStar ?_
    have hright : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ h) (F, []))
        (inp +> default) (out +> default) := by
      rw [lrcons_same]
      exact segRLs_0inf hseg
    have hleft : SideRLs (flipTM source_tm) ([left_hash] ^ h)
        (call_left_far (h + 1 + r) 0 far) (call_left_far (1 + r) h far) := by
      simpa only [Nat.add_assoc, Nat.zero_add] using relaunches_far h (1 + r) 0 far
    refine stepPlus_trans (SideRLs.concat hleft hright) ?_
    rw [show 1 + r = r + 1 by omega]
    exact (relaunch_far r h far).elim_single_left (out +> default)

theorem E_to_B (m : ℕ) : SegRLs source_tm (hashes ^ (3 * (2 ^ m - 1))) [] (E8 ^ m) (B8 ^ m) := by
  induction m with
  | zero =>
    exact .nil _
  | succ m ih =>
    rw [pow_succ_list E8 m, pow_succ_list B8 m]
    have h := (hash_E_odd (3 * (2 ^ m - 1))).concat ih
    have heq : 2 * (3 * (2 ^ m - 1)) + 3 = 3 * (2 ^ (m + 1) - 1) := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega
    rwa [heq] at h

theorem digits_word_repeat_BB (n : ℕ) : (digits_word A8 B8) (List.replicate n BB) = B8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, digits_word, digit_word, ih]

theorem digits_value_repeat_BB (n : ℕ) : digits_value (List.replicate n BB) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, digits_value, ih, Nat.pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

def nested_required : List ℕ → ℕ → ℕ
  | [], e => 3 * (2 ^ (e + 1) - 1)
  | e₀ :: es', e =>
      (nested_required es' e + 1) * 2 ^ (e₀ + 1) - 2 + (2 ^ (e₀ + 1) - 1)

theorem nested_counter (es : List ℕ) (e : ℕ) :
    SegRLs source_tm (hashes ^ nested_required es e) []
      (spaced_words (es.map (fun e => E8 ^ e ++ A8) ++ [E8 ^ (e + 1)]))
      (spaced_words (es.map (fun e => B8 ^ (e + 1)) ++ [B8 ^ (e + 1)])) := by
  induction es with
  | nil =>
    exact E_to_B (e + 1)
  | cons e₀ es ih =>
    dsimp only [nested_required]
    rw [List.map_cons, List.map_cons, spaced_snoc_cons, spaced_snoc_cons]
    have h0 := standard_mixed_to_binary_out_spec e₀ (List.replicate (e₀ + 1) BB)
      (nested_required es e) (List.length_replicate)
    rw [digits_word_repeat_BB, digits_value_repeat_BB] at h0
    simpa only [List.append_assoc] using h0.concat ((hashes_U_run (nested_required es e) 2).concat
        ih)

theorem mixed_tail_5_eq (es : List ℕ) (e : ℕ) :
    mixed_tail es (e + 1) 5 =
      spaced_words (es.map (fun e => E8 ^ e ++ A8) ++ [E8 ^ (e + 1)]) ++ tail_word 6 := by
  unfold mixed_tail tail_word y_after
  simp only [List.append_assoc]

theorem nested_exit_to_cycler (c f : ℕ) (es : List ℕ) (e : ℕ)
    (hle : nested_required es e ≤ f) :
    ∃ l',
      ((exception_call_left c f) {{B}}> (full_tail es (e + 1) 5 +> default)) [source_tm]⊢⁺
        ((Yw.reverse +> l') {{B}}> default) := by
  set h := nested_required es e
  set far := [0, 1, 0] +> (V4 ^ (2 * c) +> ([1, 0, 1] +> default))
  have hraw := raw_tail_columns es (e + 1) 5 (exception_call_left c f) (by decide)
  rw [nested_pre_left c f, mixed_tail_5_eq es e] at hraw
  have hseg := (nested_counter es e).concat (SegRLs.nil (M := source_tm) (tail_word 6))
  have hlaunch := nested_launch h (f - h) far _ _ hseg
  rw [show h + (f - h) + 1 = f + 1 by omega] at hlaunch
  obtain ⟨l', hover⟩ := overflow_columns es e (call_left_far (f - h) h far)
  exact ⟨l', stepPlus_trans hraw (stepPlus_trans hlaunch hover)⟩

-- ============================================================================
-- 5. `TailState`, `FiniteColumns`, `FiniteRound` & `OpeningEarly` (`PR_SOBCv10.v` lines 401–798)
-- ============================================================================

inductive SDigit where
  | SE | SD | SA | SB
  deriving DecidableEq, Repr

open SDigit

def sdigit_word : SDigit → List (Fin 2)
  | SE => E8
  | SD => D8
  | SA => A8
  | SB => B8

def sdigit_value : SDigit → ℤ
  | SE => -2
  | SD => -1
  | SA => 0
  | SB => 1

def sdigits_word : List SDigit → List (Fin 2)
  | [] => []
  | d :: ds' => sdigit_word d ++ sdigits_word ds'

def sdigits_value : List SDigit → ℤ
  | [] => 0
  | d :: ds' => sdigit_value d + 2 * sdigits_value ds'

def tail_layout (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv : ℕ) : List (Fin
    2) :=
  A8 ^ primary ++ U ^ 2 ++
    spaced_words (zs.map binary_column_word ++ [sdigits_word last]) ++
    U ^ (2 * k + 1) ++ y_after lv

def post_ca_tail (unary primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv : ℕ) :
    Cfg (Fin 2) (Fin 6) :=
  (ordinary_left unary) {{B}}> (tail_layout primary zs last k lv +> default)

def zs_value (o : ℕ) : List BinaryColumn → ℤ
  | [] => 0
  | c :: zs' => (2 : ℤ) ^ o * (column_value c : ℤ) + zs_value (o + column_width c) zs'

def tail_W (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) : ℕ :=
  primary + columns_width_sum zs + last.length

def tail_V (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ) : ℤ :=
  zs_value primary zs +
    (2 : ℤ) ^ (primary + columns_width_sum zs) * sdigits_value last +
    (2 : ℤ) ^ (tail_W primary zs last) * ((lv : ℤ) - 1)

def trigger_hash (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ) : ℤ :=
  5 * (2 : ℤ) ^ (tail_W primary zs last) - tail_V primary zs last lv

def tail_next_half (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ) :
    ℤ :=
  ((round_post_unary current previous : ℤ) +
    trigger_hash (round_primary_width current previous) zs last lv - 1) / 2

def tail_next_index (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ) :
    ℕ :=
  ((tail_next_half current previous zs last lv - 6) / 2).toNat

def column_budget (n : ℕ) (c : BinaryColumn) : Prop :=
  ∃ phase,
    n ≤ lineage_fuel phase ∧
    low_slice (pow2 (column_width c)) (lineage_width phase)
      (lineage_residue phase) (column_value c : ℤ)

theorem column_budget_safe (n : ℕ) (c : BinaryColumn) (h : column_budget n c) : column_safe c := by
  rcases h with ⟨phase, _, hslice⟩
  rw [column_safe_abstract]
  exact low_slice_safe _ _ _ _ hslice (lineage_residue_bounds phase)

theorem lineage_next_fuel (phase : LineagePhase) (h : 1 ≤ lineage_fuel phase) :
    ∃ phase', lineage_next phase phase' ∧ lineage_fuel phase' + 1 = lineage_fuel phase := by
  match phase with
  | LBirth n =>
    exact ⟨LEven (n + 1), .lineage_birth n, by dsimp [lineage_fuel]; omega⟩
  | LEven 0 =>
    dsimp [lineage_fuel] at h; omega
  | LEven (n + 1) =>
    exact ⟨LOdd n, .lineage_even n, by dsimp [lineage_fuel]; omega⟩
  | LOdd n =>
    exact ⟨LEven n, .lineage_odd n, rfl⟩

theorem column_budget_step (n : ℕ) (c c' : BinaryColumn) (b : Bool)
    (hbudget : column_budget (n + 1) c) (hstep : column_step b c c') :
    column_budget n c' := by
  have hsafe := column_budget_safe (n + 1) c hbudget
  rcases hbudget with ⟨phase, hfuel, hslice⟩
  obtain ⟨phase', hnext, hleft⟩ := lineage_next_fuel phase (by omega)
  refine ⟨phase', by omega, ?_⟩
  have hab := abstract_column_step c c' b hsafe hstep
  have hw : column_width c' = column_width c := congrArg AbstractColumn.abstract_width hab
  have hv : (column_value c' : ℤ) =
      arbitrary_column_step (pow2 (column_width c)) b (column_value c : ℤ) :=
    congrArg AbstractColumn.abstract_value hab
  rw [hw, hv]
  exact lineage_step_preserves_slice _ _ _ _ b hnext hslice

theorem z_column_budget (previous : ℕ) : column_budget 3 (z_column previous) := by
  refine ⟨LBirth previous, by dsimp [lineage_fuel]; omega, ?_⟩
  dsimp [lineage_width, lineage_residue]
  rw [z_column_width, z_column_value]
  exact z_birth_low_slice previous

def next_column_odd (right_odd : Bool) : List BinaryColumn → Bool
  | [] => right_odd
  | d :: _ => decide (column_value d % 2 = 1)

def tail_columns_step (right_odd : Bool) : List BinaryColumn → List BinaryColumn → Prop
  | [], [] => True
  | c :: rest, c' :: rest' =>
      column_step (next_column_odd right_odd rest) c c' ∧
      tail_columns_step right_odd rest rest'
  | _, _ => False

theorem tail_columns_budget_step (n : ℕ) (cs : List BinaryColumn) (b : Bool)
    (h : ∀ c ∈ cs, column_budget (n + 1) c) :
    ∃ cs', tail_columns_step b cs cs' ∧ (∀ c' ∈ cs', column_budget n c') := by
  induction cs with
  | nil =>
    exact ⟨[], trivial, by intro _ hmem; cases hmem⟩
  | cons c rest ih =>
    obtain ⟨cs', hstep, hbudget⟩ := ih (fun x hx => h x (List.mem_cons_of_mem c hx))
    have hc : column_budget (n + 1) c := h c (List.Mem.head _)
    obtain ⟨c', hcstep⟩ := column_step_exists (next_column_odd b rest) c
      (column_safe_lower c (column_budget_safe (n + 1) c hc))
    refine ⟨c' :: cs', ⟨hcstep, hstep⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact column_budget_step n c x (next_column_odd b rest) hc hcstep
    · exact hbudget x hmem

theorem column_budget_weaken (n m : ℕ) (c : BinaryColumn) (hnm : n ≤ m) (hb : column_budget m c) :
    column_budget n c := by
  rcases hb with ⟨phase, hfuel, hslice⟩
  exact ⟨phase, by omega, hslice⟩

theorem tail_columns_round_budget (k previous : ℕ) (cs : List BinaryColumn) (b : Bool)
    (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hcs : ∀ c ∈ cs, column_budget (4 - k) c) :
    ∃ cs', tail_columns_step b cs cs' ∧
      (∀ c' ∈ z_column previous :: cs', column_budget (4 - (k + 1)) c') := by
  have hcs' : ∀ c ∈ cs, column_budget ((4 - (k + 1)) + 1) c := by
    intro c hc
    rw [show (4 - (k + 1)) + 1 = 4 - k by omega]
    exact hcs c hc
  obtain ⟨cs', hstep, hbudget⟩ := tail_columns_budget_step (4 - (k + 1)) cs b hcs'
  refine ⟨cs', hstep, ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hmem
  · exact column_budget_weaken (4 - (k + 1)) 3 (z_column previous) (by omega) (z_column_budget
      previous)
  · exact hbudget x hmem

def phase_width (k : ℕ) : ℕ := 30 - k

def phase_value : ℕ → ℤ
  | 1 => 391468375
  | 2 => -195734187
  | 3 => 97867094
  | _ => -116042411

def phase_lv : ℕ → ℕ
  | 1 => 4
  | 2 => 1
  | 3 => 5
  | _ => 3

structure finite_round_pre (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ) : Prop where
  fr_stage : 1 ≤ k ∧ k ≤ 4
  fr_columns : ∀ c ∈ zs, column_budget (4 - k) c
  fr_head_odd : match zs with
    | c :: _ => column_value c % 2 = 1
    | [] => sdigits_value last % 2 = 1
  fr_width :
    2 * (columns_width_sum zs + last.length) + 4 ≤ half_parameter previous + 1 ∧
    2 * (half_parameter previous + 1 + columns_width_sum zs + last.length) + 4 ≤
      half_parameter current + 1
  fr_last_len : last.length = phase_width k
  fr_last_value : sdigits_value last = phase_value k
  fr_lv : lv = phase_lv k

theorem finite_pre_safe (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv :
    ℕ)
    (h : finite_round_pre current previous zs last k lv) :
    ∀ c ∈ zs, column_safe c := by
  intro c hc
  exact column_budget_safe (4 - k) c (h.fr_columns c hc)

def early_tail : List (Fin 2) := U ^ 3 ++ A8 ++ B8 ^ 2 ++ [1, 1]
def fourth_tail : List (Fin 2) := C8 ++ [1, 1] ++ C8 ++ A8 ^ 2 ++ [1, 1, 1, 1]

theorem opening_D_step1 :
    (default {{D}}> default) [source_tm]⊢*
      ((ordinary_left 1) {{B}}> ((B8 ++ U ++ D8 ++ C8 ++ U ^ 2) +> default)) := by
  have hl0 : (([0] : List (Fin 2)) ^ 40 +> (default : ListBlank (Fin 2))) = default :=
    BoundedConfig.all0_spec (a := ([0] : List (Fin 2)) ^ 40) (by decide)
  have hr0 : (([0] : List (Fin 2)) ^ 8 +> (default : ListBlank (Fin 2))) = default :=
    BoundedConfig.all0_spec (a := ([0] : List (Fin 2)) ^ 8) (by decide)
  have h := runSteps_spec source_tm 556
    ⟨([0] : List (Fin 2)) ^ 40, ([0] : List (Fin 2)) ^ 8, D, .right⟩
    ⟨X4 ++ Q8, B8 ++ U ++ D8 ++ C8 ++ U ^ 2, B, .right⟩
    (by decide) default default
  simpa only [BoundedConfig.toCfg, ordinary_left, common_left_wall, pow_one_list,
    List.append_assoc, append_assoc, hl0, hr0] using h

theorem opening_D_step2_side :
    SideRLs source_tm (hashes ^ 56)
      ((B8 ++ U ++ D8 ++ C8 ++ U ^ 2) +> default)
      ((B8 ++ U ++ B8 ^ 3 ++ [1, 1]) +> default) :=
  BoundedConfig.sideRLs_c_spec source_tm (T := 20000) (by decide)

theorem opening_D_step2 :
    ((ordinary_left 1) {{B}}> ((B8 ++ U ++ D8 ++ C8 ++ U ^ 2) +> default)) [source_tm]⊢*
      ((ordinary_left 57) {{B}}> ((B8 ++ U ++ B8 ^ 3 ++ [1, 1]) +> default)) := by
  have h := ordinary_side_run 56 1
    ((B8 ++ U ++ D8 ++ C8 ++ U ^ 2) +> default)
    ((B8 ++ U ++ B8 ^ 3 ++ [1, 1]) +> default)
    opening_D_step2_side
  simpa only [show 1 + 56 = 57 by omega] using h

theorem opening_D_step3 :
    ((ordinary_left 57) {{B}}> ((B8 ++ U ++ B8 ^ 3 ++ [1, 1]) +> default)) [source_tm]⊢⁺
      ((exception_pre_left 28) <{{F}} ((U ^ 3 ++ E8 ++ E8 ++ A8) +> default)) := by
  have h := check_r0inf_spec (M := source_tm) (n := 157)
    (l₁ := []) (r₁ := B8 ++ U ++ B8 ^ 3 ++ [1, 1])
    (l₂ := U ^ 3 ++ E8 ++ E8 ++ A8) (r₂ := [1, 0, 1])
    (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) (ordinary_left 57)
  have hpre : ([1, 0, 1] +> ordinary_left 57) = exception_pre_left 28 := by
    simpa only [ordinary_left, common_left_wall, show 2 * 28 + 1 = 57 by omega,
      List.append_assoc, append_assoc] using exception_pre_left_direct 28
  simpa only [BoundedConfig.toCfg, append_nil, hpre] using h

theorem opening_D_step4_side :
    SideRLs source_tm (hashes ^ 28)
      ((U ^ 3 ++ E8 ++ E8 ++ A8) +> default)
      (early_tail +> default) :=
  BoundedConfig.sideRLs_c_spec source_tm (T := 20000) (by decide)

theorem opening_D_to_third_done :
    (default {{D}}> default) [source_tm]⊢* exception_done 28 early_tail := by
  refine stepStar_trans opening_D_step1 ?_
  refine stepStar_trans opening_D_step2 ?_
  refine stepPlus_to_stepStar (stepPlus_trans opening_D_step3 ?_)
  have hright : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ 27) (F, []))
      ((U ^ 3 ++ E8 ++ E8 ++ A8) +> default) (early_tail +> default) := by
    rw [lrcons_same]
    exact opening_D_step4_side
  have hleft : SideRLs (flipTM source_tm) ([left_hash] ^ 27)
      (exception_call_left 27 0) (exception_call_left 0 27) := by
    simpa only [Nat.zero_add] using exception_relaunches 27 0
  exact stepPlus_trans (exception_launch_progress 27 ((U ^ 3 ++ E8 ++ E8 ++ A8) +> default))
    (stepPlus_trans (SideRLs.concat hleft hright) (exception_exit 27 early_tail))

theorem opening_local_hash :
    SegRLs source_tm hashes []
      (C8 ++ A8 ++ U ++ A8 ++ B8 ^ 2 ++ [1, 1])
      (D8 ++ fourth_tail) :=
  BoundedConfig.segRLs_c_spec source_tm (T := 300) (by decide)

def opening_after_cd_calls (p : ℕ) : ℕ :=
  initial_u_pair_calls p 1 + (2 ^ (p + 1) + (2 ^ (p + 1) + (2 ^ (p + 2) - 1)))

theorem opening_after_cd_side (p : ℕ) :
    SideRLs source_tm (hashes ^ opening_after_cd_calls p)
      ((A8 ^ p ++ C8 ++ A8 ++ early_tail) +> default)
      ((B8 ^ (p + 2) ++ fourth_tail) +> default) := by
  have hfirst := segRLs_0inf (initial_u_pairs p 1 (U ++ A8 ++ B8 ^ 2 ++ [1, 1]))
  have hbridge := segRLs_0inf (primary_one_rule (p + 1) _ _ opening_local_hash)
  have hd := segRLs_0inf (primary_D_absorb (p + 1) fourth_tail)
  have hfinish := segRLs_0inf (zero_primary_finish_seg (p + 2) fourth_tail)
  have hfirst' : SideRLs source_tm (hashes ^ initial_u_pair_calls p 1)
      ((A8 ^ p ++ (C8 ++ (A8 ++ early_tail))) +> default)
      ((A8 ^ (p + 1) ++ (C8 ++ (A8 ++ (U ++ (A8 ++ (B8 ^ 2 ++ [1, 1])))))) +> default) := by
    unfold early_tail
    have hu3 : U ^ 3 = U ^ (2 * 1) ++ U := rfl
    rw [hu3]
    simpa only [List.append_assoc, append_assoc] using hfirst
  have hbridge' : SideRLs source_tm (hashes ^ (2 ^ (p + 1)))
      ((A8 ^ (p + 1) ++ (C8 ++ (A8 ++ (U ++ (A8 ++ (B8 ^ 2 ++ [1, 1])))))) +> default)
      ((A8 ^ (p + 1) ++ (D8 ++ fourth_tail)) +> default) := by
    simpa only [List.append_assoc, append_assoc] using hbridge
  have hd' : SideRLs source_tm (hashes ^ (2 ^ (p + 1)))
      ((A8 ^ (p + 1) ++ (D8 ++ fourth_tail)) +> default)
      ((A8 ^ (p + 2) ++ fourth_tail) +> default) := by
    simpa only [List.append_assoc, append_assoc] using hd
  have hcomb := hfirst'.trans (hbridge'.trans (hd'.trans hfinish))
  unfold opening_after_cd_calls
  rw [pow_add_list, pow_add_list, pow_add_list]
  simpa only [List.append_assoc, append_assoc] using hcomb

def opening_n4 : ℕ := 3 * 2 ^ 29 - 2

theorem opening_total_count_general (p : ℕ) :
    cd_calls p + opening_after_cd_calls p = 2 * (3 * 2 ^ (p + 1) - 2) + 1 := by
  unfold cd_calls opening_after_cd_calls
  dsimp [initial_u_pair_calls]
  have : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  rw [show p + 2 = (p + 1) + 1 by omega, Nat.pow_succ 2 (p + 1), Nat.pow_succ 2 p]
  omega

theorem opening_total_count :
    cd_calls 28 + opening_after_cd_calls 28 = 2 * opening_n4 + 1 :=
  opening_total_count_general 28

theorem opening_D_to_fourth_frontier :
    (default {{D}}> default) [source_tm]⊢*
      ((ordinary_left (2 * opening_n4 + 1)) {{B}}> ((B8 ^ 30 ++ fourth_tail) +> default)) := by
  refine stepStar_trans opening_D_to_third_done ?_
  refine stepStar_trans (stepPlus_to_stepStar (exception_done_cd 28 early_tail (by decide))) ?_
  unfold after_cd cd_output
  have h := ordinary_side_run (opening_after_cd_calls 28) (cd_calls 28)
    ((A8 ^ 28 ++ C8 ++ A8 ++ early_tail) +> default)
    ((B8 ^ 30 ++ fourth_tail) +> default)
    (opening_after_cd_side 28)
  rw [opening_total_count] at h
  simpa only [List.append_assoc, append_assoc] using h

-- ============================================================================
-- 6. `SignedFrontier` (`PR_SOBCv10.v` lines 799–1014)
-- ============================================================================

def sfinish_count : List SDigit → ℕ → ℕ
  | [], out => out
  | d :: rest, out =>
      2 * sfinish_count rest out +
      match d with | SE => 3 | SD => 2 | SA => 1 | SB => 0

theorem hash_D_finish (n : ℕ) :
    SegRLs source_tm (hashes ^ (2 * n + 2)) (hashes ^ n) D8 B8 := by
  rw [show 2 * n + 2 = 1 + (2 * n + 1) by omega, pow_add_list, pow_one_list]
  simpa only [List.nil_append] using hash_D.trans (hash_A_finish n)

theorem sfinish_spec (ds : List SDigit) (out : ℕ) :
    SegRLs source_tm (hashes ^ sfinish_count ds out) (hashes ^ out)
      (sdigits_word ds) (B8 ^ ds.length) := by
  induction ds with
  | nil =>
    exact SegRLs.empty source_tm (hashes ^ out)
  | cons d ds ih =>
    rw [List.length_cons, pow_succ_list B8 ds.length]
    dsimp only [sdigits_word, sdigit_word, sfinish_count]
    rcases d with _ | _ | _ | _
    · exact (hash_E_odd (sfinish_count ds out)).concat ih
    · exact (hash_D_finish (sfinish_count ds out)).concat ih
    · exact (hash_A_finish (sfinish_count ds out)).concat ih
    · rw [Nat.add_zero]
      exact (hash_B_finish (sfinish_count ds out)).concat ih

theorem sfinish_value (ds : List SDigit) (out : ℕ) :
    (sfinish_count ds out : ℤ) + sdigits_value ds + 1 =
      ((out : ℤ) + 1) * pow2 ds.length := by
  induction ds with
  | nil =>
    simp [sfinish_count, sdigits_value, pow2]
  | cons d ds ih =>
    rw [List.length_cons, pow2_succ]
    rcases d with _ | _ | _ | _ <;>
      { dsimp [sfinish_count, sdigits_value, sdigit_value]
        linarith }

theorem tail_level_finish (lv : ℕ) (hlv : lv ≤ 5) :
    SideRLs source_tm (hashes ^ (5 - lv))
      (y_after lv +> default) ((B8 ++ [1, 1]) +> default) := by
  rcases lv with _ | _ | _ | _ | _ | _ | lv
  · exact BoundedConfig.sideRLs_c_spec source_tm (T := 1000) (by decide)
  · exact BoundedConfig.sideRLs_c_spec source_tm (T := 1000) (by decide)
  · exact BoundedConfig.sideRLs_c_spec source_tm (T := 1000) (by decide)
  · exact BoundedConfig.sideRLs_c_spec source_tm (T := 1000) (by decide)
  · exact BoundedConfig.sideRLs_c_spec source_tm (T := 1000) (by decide)
  · exact .nil _
  · omega

def last_finish_count (last : List SDigit) (lv : ℕ) : ℕ :=
  sfinish_count last (5 - lv)

theorem last_to_frontier (last : List SDigit) (k lv : ℕ) (hlv : lv ≤ 5) :
    SideRLs source_tm (hashes ^ last_finish_count last lv)
      ((sdigits_word last ++ U ^ (2 * k + 1) ++ y_after lv) +> default)
      ((B8 ^ last.length ++ U ^ (2 * k + 1) ++ B8 ++ [1, 1]) +> default) := by
  have hp := (sfinish_spec last (5 - lv)).concat (hashes_U_run (5 - lv) (2 * k + 1))
  have h := hp.sideRLs_concat (tail_level_finish lv hlv)
  unfold last_finish_count
  simpa only [List.append_assoc, append_assoc] using h

def columns_with_tail : List BinaryColumn → List (Fin 2) → List (Fin 2)
  | [], tail => tail
  | c :: rest, tail => binary_column_word c ++ U ^ 2 ++ columns_with_tail rest tail

def all_B_with_tail : List BinaryColumn → List (Fin 2) → List (Fin 2)
  | [], tail => tail
  | c :: rest, tail => B8 ^ column_width c ++ U ^ 2 ++ all_B_with_tail rest tail

def columns_finish_count : List BinaryColumn → ℕ → ℕ
  | [], out => out
  | c :: rest, out => bfinish_count c.column_digits (columns_finish_count rest out)

theorem columns_finish_tail (zs : List BinaryColumn) (out : ℕ) (input output : List (Fin 2))
    (htail : SideRLs source_tm (hashes ^ out) (input +> default) (output +> default)) :
    SideRLs source_tm (hashes ^ columns_finish_count zs out)
      (columns_with_tail zs input +> default)
      (all_B_with_tail zs output +> default) := by
  induction zs with
  | nil => exact htail
  | cons c zs ih =>
    dsimp only [columns_finish_count, columns_with_tail, all_B_with_tail]
    have hc :=
        (bfinish_spec hash_A_finish hash_B_finish) c.column_digits (columns_finish_count zs out)
    rw [c.column_length] at hc
    have hp := hc.concat (hashes_U_run (columns_finish_count zs out) 2)
    have h := hp.sideRLs_concat ih
    unfold binary_column_word column_width
    simpa only [List.append_assoc, append_assoc] using h

def tail_finish_count (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ) : ℕ :=
  bfinish_count (List.replicate primary BA) (columns_finish_count zs (last_finish_count last lv))

def tail_frontier (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k : ℕ) : List (Fin
    2) :=
  B8 ^ primary ++ U ^ 2 ++
    all_B_with_tail zs (B8 ^ last.length ++ U ^ (2 * k + 1) ++ B8 ++ [1, 1])

theorem tail_layout_chain (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv : ℕ) :
    tail_layout primary zs last k lv =
      A8 ^ primary ++ U ^ 2 ++
        columns_with_tail zs (sdigits_word last ++ U ^ (2 * k + 1) ++ y_after lv) := by
  unfold tail_layout
  rw [List.append_assoc (A8 ^ primary ++ U ^ 2), List.append_assoc (A8 ^ primary ++ U ^ 2)]
  congr 1
  induction zs with
  | nil =>
    simp [columns_with_tail, spaced_words, List.append_assoc]
  | cons c zs ih =>
    rw [List.map_cons, spaced_snoc_cons]
    dsimp only [columns_with_tail]
    rw [← ih]
    simp only [List.append_assoc]

theorem tail_to_frontier (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv : ℕ)
    (hlv : lv ≤ 5) :
    SideRLs source_tm (hashes ^ tail_finish_count primary zs last lv)
      (tail_layout primary zs last k lv +> default)
      (tail_frontier primary zs last k +> default) := by
  have htail := columns_finish_tail zs _ _ _ (last_to_frontier last k lv hlv)
  have hprimary := (bfinish_spec hash_A_finish hash_B_finish) (List.replicate primary BA)
    (columns_finish_count zs (last_finish_count last lv))
  rw [digits_word_repeat_BA, List.length_replicate] at hprimary
  have hp := hprimary.concat
    (hashes_U_run (columns_finish_count zs (last_finish_count last lv)) 2)
  have h := hp.sideRLs_concat htail
  unfold tail_finish_count tail_frontier
  rw [tail_layout_chain]
  simpa only [List.append_assoc, append_assoc] using h

theorem pow2_add_local (a b : ℕ) : pow2 (a + b) = pow2 a * pow2 b := by
  unfold pow2
  rw [pow_add]

theorem bfinish_value_Z (ds : List BDigit) (out : ℕ) :
    (bfinish_count ds out : ℤ) + (digits_value ds : ℤ) + 1 =
      ((out : ℤ) + 1) * pow2 ds.length := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (bfinish_count_value ds out)
  push_cast at h
  rw [pow2_Zpow]
  linarith

def columns_value_Z : List BinaryColumn → ℤ
  | [] => 0
  | c :: rest => (column_value c : ℤ) + pow2 (column_width c) * columns_value_Z rest

theorem zs_value_shift (o : ℕ) (zs : List BinaryColumn) :
    zs_value o zs = pow2 o * columns_value_Z zs := by
  induction zs generalizing o with
  | nil => simp [zs_value, columns_value_Z]
  | cons c zs ih =>
    dsimp [zs_value, columns_value_Z]
    rw [ih, pow2_add_local, ← pow2_Zpow]
    ring

theorem columns_finish_value (zs : List BinaryColumn) (out : ℕ) :
    (columns_finish_count zs out : ℤ) + columns_value_Z zs + 1 =
      ((out : ℤ) + 1) * pow2 (columns_width_sum zs) := by
  induction zs with
  | nil =>
    simp [columns_finish_count, columns_value_Z, columns_width_sum, columns_widths,
        pow2]
  | cons c zs ih =>
    dsimp only [columns_finish_count, columns_value_Z]
    rw [columns_width_sum_cons, pow2_add_local]
    have h := bfinish_value_Z c.column_digits (columns_finish_count zs out)
    rw [c.column_length] at h
    change (bfinish_count c.column_digits (columns_finish_count zs out) : ℤ) +
      (column_value c : ℤ) + 1 =
      ((columns_finish_count zs out : ℤ) + 1) * pow2 (c.column_e + 1) at h
    unfold column_width
    nlinarith

theorem trigger_hash_count (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ)
    (hlv : lv ≤ 5) :
    ((tail_finish_count primary zs last lv + 1 : ℕ) : ℤ) =
      trigger_hash primary zs last lv := by
  have hp := bfinish_value_Z (List.replicate primary BA)
    (columns_finish_count zs (last_finish_count last lv))
  rw [List.length_replicate, digits_value_repeat_BA] at hp
  change (tail_finish_count primary zs last lv : ℤ) + 0 + 1 =
    ((columns_finish_count zs (last_finish_count last lv) : ℤ) + 1) * pow2 primary at hp
  have hc := columns_finish_value zs (last_finish_count last lv)
  have hl := sfinish_value last (5 - lv)
  change (last_finish_count last lv : ℤ) + sdigits_value last + 1 =
    (((5 - lv : ℕ) : ℤ) + 1) * pow2 last.length at hl
  have hsub : ((5 - lv : ℕ) : ℤ) = 5 - (lv : ℤ) := by omega
  rw [hsub] at hl
  unfold trigger_hash tail_V tail_W
  rw [zs_value_shift, ← pow2_Zpow, ← pow2_Zpow,
      pow2_add_local (primary + columns_width_sum zs) last.length,
      pow2_add_local primary (columns_width_sum zs)]
  have hp' : (tail_finish_count primary zs last lv : ℤ) + 1 =
      ((columns_finish_count zs (last_finish_count last lv) : ℤ) + 1) * pow2 primary := by linarith
  have hc' : (columns_finish_count zs (last_finish_count last lv) : ℤ) + 1 =
      ((last_finish_count last lv : ℤ) + 1) * pow2 (columns_width_sum zs) - columns_value_Z zs := by
        linarith
  have hl' : (last_finish_count last lv : ℤ) + 1 =
      (5 - (lv : ℤ) + 1) * pow2 last.length - sdigits_value last := by linarith
  push_cast
  rw [hp', hc', hl']
  ring

-- ============================================================================
-- 7. `SignedDecode` & `OpeningDecode` (`PR_SOBCv10.v` lines 1016–1185)
-- ============================================================================

def E_digit (n : ℕ) : SDigit :=
  if n == 0 then SE
  else if n == 1 then SD
  else if n % 2 == 0 then SA
  else SB

def E_carry (n : ℕ) : ℕ :=
  (n - 2) / 2

def E_decode : ℕ → ℕ → List SDigit × ℕ
  | 0, n => ([], n)
  | w + 1, n =>
      let (ds, out) := E_decode w (E_carry n)
      (E_digit n :: ds, out)

theorem E_digit_spec (n : ℕ) :
    SegRLs source_tm (hashes ^ n) (hashes ^ E_carry n) E8 (sdigit_word (E_digit n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact .nil E8
  · rcases Nat.eq_or_lt_of_le hpos with h1 | hgt1
    · subst h1
      exact hash_E
    · rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · have hdig : E_digit n = SA := by
          unfold E_digit
          have h0 : (n == 0) = false := beq_false_of_ne (by omega)
          have h1 : (n == 1) = false := beq_false_of_ne (by omega)
          have hm : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [h0, h1, hm]
          rfl
        rw [hdig, sdigit_word]
        set c := E_carry n
        have hc : E_carry n = c := rfl
        have hn : n = 2 * c + 2 := by unfold E_carry at hc; omega
        rw [hn]
        exact hash_E_even c
      · have hdig : E_digit n = SB := by
          unfold E_digit
          have h0 : (n == 0) = false := beq_false_of_ne (by omega)
          have h1 : (n == 1) = false := beq_false_of_ne (by omega)
          have hm : (n % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [h0, h1, hm]
          rfl
        rw [hdig, sdigit_word]
        set c := E_carry n
        have hc : E_carry n = c := rfl
        have hn : n = 2 * c + 3 := by unfold E_carry at hc; omega
        rw [hn]
        exact hash_E_odd c

theorem E_decode_spec (width n : ℕ) :
    SegRLs source_tm (hashes ^ n) (hashes ^ (E_decode width n).2)
      (E8 ^ width) (sdigits_word (E_decode width n).1) := by
  induction width generalizing n with
  | zero =>
    exact SegRLs.empty source_tm (hashes ^ n)
  | succ w ih =>
    dsimp only [E_decode, sdigits_word]
    rw [pow_succ_list E8 w]
    exact (E_digit_spec n).concat (ih (E_carry n))

def opening_call_base : ℕ := 462424812206

def opening_digits : List SDigit :=
  [SA,SA,SA,SA,SB,SB,SA,SB,SA,SB,SA,SB,SA,SB,SA,SB,SA,SB,
   SA,SB,SA,SB,SA,SB,SA,SB,SA,SB,SA,SB,SA,SB,SB,SB,SA,SB]

theorem opening_decode_exact :
    E_decode 36 opening_call_base = (opening_digits, 4) := by
  decide

theorem opening_tail_four :
    SideRLs source_tm (hashes ^ 4) (A8 +> default) ((A8 ++ [1, 1]) +> default) :=
  BoundedConfig.sideRLs_c_spec source_tm (T := 500) (by decide)

theorem opening_decode_base :
    SideRLs source_tm (hashes ^ opening_call_base)
      ((E8 ^ 36 ++ U ^ 3 ++ A8) +> default)
      ((sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1]) +> default) := by
  have h := E_decode_spec 36 opening_call_base
  rw [opening_decode_exact] at h
  have hp := h.concat (hashes_U_run 4 3)
  have hfull := hp.sideRLs_concat opening_tail_four
  simpa only [List.append_assoc, append_assoc] using hfull

def opening_decode_calls (k : ℕ) : ℕ :=
  2 ^ k * opening_call_base + 2 * (2 ^ k - 1)

theorem opening_decode (k : ℕ) :
    SideRLs source_tm (hashes ^ opening_decode_calls k)
      ((E8 ^ (k + 36) ++ U ^ 3 ++ A8) +> default)
      ((A8 ^ k ++ sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1]) +> default) := by
  have hprefix := prefix_E_even k opening_call_base [] [] opening_call_base
    (SegRLs.empty source_tm (hashes ^ opening_call_base))
  rw [List.append_nil, List.append_nil] at hprefix
  have h := hprefix.sideRLs_concat opening_decode_base
  unfold opening_decode_calls
  rw [pow_add_list E8 k 36]
  simpa only [List.append_assoc, append_assoc] using h

theorem opening_call_base_formula :
    opening_call_base = (1292 * 2 ^ 30 + 4) / 3 + 2 := by
  decide

theorem opening_decode_calls_formula (k : ℕ) :
    opening_decode_calls k = 2 ^ (k + 2) - 2 + 2 ^ k * ((1292 * 2 ^ 30 + 4) / 3) := by
  unfold opening_decode_calls
  rw [opening_call_base_formula, Nat.pow_add]
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  change 2 ^ k * ((1292 * 2 ^ 30 + 4) / 3 + 2) + 2 * (2 ^ k - 1) =
    2 ^ k * 4 - 2 + 2 ^ k * ((1292 * 2 ^ 30 + 4) / 3)
  omega

-- ============================================================================
-- 8. `OpeningEntry`, `Fossil`, `RoundCaller` & `OpeningLate` (`PR_SOBCv10.v` lines 1187–1762)
-- ============================================================================

def entry_rest : List SDigit := opening_digits.drop 9
def entry_last : List SDigit := SB :: SB :: entry_rest
def entry_state_of (cur prev : ℕ) : Cfg (Fin 2) (Fin 6) :=
  post_ca_tail
    (round_post_unary cur prev)
    (round_primary_width cur prev) [] entry_last 1 4

theorem opening_n4_even_large :
    (∃ q, opening_n4 = 2 * q) ∧ 64 ≤ opening_n4 := by
  refine ⟨⟨3 * 2 ^ 28 - 1, by decide⟩, by decide⟩

theorem n4_binary : opening_n4 = 1610612734 := by decide
theorem n4_large : 10 ≤ opening_n4 := by decide

theorem even_index_half (n : ℕ) (h : ∃ q, n = 2 * q ∧ 6 ≤ 2 * q) :
    half_parameter ((n - 6) / 2) = n := by
  rcases h with ⟨q, rfl, hge⟩
  unfold half_parameter
  omega

theorem opening_decode_even_ge6 (k : ℕ) (hk : 2 ≤ k) :
    ∃ q, opening_decode_calls k = 2 * q ∧ 6 ≤ 2 * q := by
  unfold opening_decode_calls
  have hbase : opening_call_base = 2 * 231212406103 := by decide
  rw [hbase]
  have hpow : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  refine ⟨2 ^ k * 231212406103 + (2 ^ k - 1), by omega, by omega⟩

theorem opening_entry_growth (n : ℕ) (hn : 64 ≤ n) :
    2 * (n + 30) + 4 ≤ opening_decode_calls (n - 2) + 1 := by
  have hpow := pow2_linear_margin (n - 8)
  rw [show n - 8 + 5 = n - 3 by omega] at hpow
  have heq : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by omega, Nat.pow_succ]
    ring
  unfold opening_decode_calls opening_call_base
  rw [heq]
  omega

theorem entry_last_facts :
    entry_last.length = 29 ∧ sdigits_value entry_last = 391468375 ∧
      sdigits_value entry_last % 2 = 1 := by
  decide

theorem entry_opening_word_generic (n4 : ℕ) (hn4 : ∃ q, n4 = 2 * q ∧ 6 ≤ 2 * q) :
    A8 ^ (n4 - 2) ++ sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1] =
      A8 ^ (2 * ((n4 - 6) / 2 + 4)) ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++
        (sdigits_word entry_rest ++ U ^ 3 ++ A8 ++ [1, 1]) := by
  have hsplit : sdigits_word opening_digits =
      A8 ^ 4 ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ sdigits_word entry_rest := rfl
  have hhalf := even_index_half n4 hn4
  unfold half_parameter at hhalf
  have hexp : n4 - 2 + 4 = 2 * ((n4 - 6) / 2 + 4) := by omega
  rw [hsplit]
  simp only [← List.append_assoc]
  rw [← pow_add_list A8 (n4 - 2) 4, hexp]

theorem opening_exception_to_entry_generic (n4 n5 : ℕ)
    (hn4 : ∃ q, n4 = 2 * q ∧ 6 ≤ 2 * q)
    (hn5 : ∃ q, n5 = 2 * q ∧ 6 ≤ 2 * q) :
    (exception_done n5
      (A8 ^ (n4 - 2) ++ sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1]))
      [source_tm]⊢⁺ entry_state_of ((n5 - 6) / 2) ((n4 - 6) / 2) := by
  rw [entry_opening_word_generic n4 hn4]
  unfold entry_state_of post_ca_tail tail_layout round_post_unary round_primary_width
  rw [even_index_half n5 hn5, even_index_half n4 hn4]
  have hhalf := even_index_half n4 hn4
  unfold half_parameter at hhalf
  have hwidth : n5 + n4 + 6 = n5 + 2 * ((n4 - 6) / 2 + 4) + 4 := by omega
  rw [hwidth]
  rcases hn5 with ⟨q, hq, hge6⟩
  have hpos : 1 ≤ n5 := by omega
  have hca := exception_done_ca n5 ((n4 - 6) / 2 + 4)
    (sdigits_word entry_rest ++ U ^ 3 ++ A8 ++ [1, 1]) hpos
  have hsw : spaced_words (List.map binary_column_word [] ++ [sdigits_word entry_last]) =
      B8 ++ B8 ++ sdigits_word entry_rest := rfl
  rw [hsw]
  dsimp only [y_after] at hca ⊢
  simpa only [pow_succ_list, pow_zero_list, List.nil_append, List.append_nil,
    List.append_assoc, append_assoc] using hca

theorem entry_pre_generic (n4 n5 : ℕ)
    (hn4 : ∃ q, n4 = 2 * q ∧ 6 ≤ 2 * q)
    (hn5 : ∃ q, n5 = 2 * q ∧ 6 ≤ 2 * q)
    (hge64 : 64 ≤ n4)
    (hgrow : 2 * (n4 + 30) + 4 ≤ n5 + 1) :
    finite_round_pre ((n5 - 6) / 2) ((n4 - 6) / 2) [] entry_last 1 4 := by
  obtain ⟨hlen, hval, hodd⟩ := entry_last_facts
  refine ⟨⟨by omega, by omega⟩, ?_, hodd, ?_, hlen, hval, rfl⟩
  · intro _ hmem; cases hmem
  · rw [even_index_half n4 hn4, even_index_half n5 hn5, hlen]
    change 2 * (0 + 29) + 4 ≤ n4 + 1 ∧
      2 * (n4 + 1 + 0 + 29) + 4 ≤ n5 + 1
    exact ⟨by omega, by omega⟩

def fossil_tail : List (Fin 2) := C8 ++ [1, 1] ++ C8 ++ U ++ [1, 1] ++ U
def fossil_start (m : ℕ) : List (Fin 2) := C8 ++ A8 ^ m ++ D8 ++ D8 ++ A8 ++ U ++ E8 ++ A8

theorem fossil_scan (m : ℕ) :
    SegRLs source_tm hashes [] (fossil_start m)
      (D8 ++ C8 ^ m ++ D8 ++ D8 ++ fossil_tail) := by
  refine .cons (fun l r => ?_) (.nil _)
  unfold fossil_start
  simp only [toDHCfg, List.append_assoc, append_assoc, append_nil]
  refine stepPlus_stepStar_trans (scan_C8_fwd l _) ?_
  have hd : (D8 +> (D8 +> (A8 +> (U +> (E8 +> (A8 +> r)))))) =
      ([1] +> (([1, 1, 0, 1, 1, 1, 0] ++ D8 ++ A8 ++ U ++ E8 ++ A8) +> r)) := rfl
  rw [hd]
  refine stepStar_trans (scan_A8_fwd_pow m (W_C +> l)
    (([1, 1, 0, 1, 1, 1, 0] ++ D8 ++ A8 ++ U ++ E8 ++ A8) +> r)) ?_
  rw [← hd]
  have hturn : (([1] +> ((W_A ^ m) +> (W_C +> l))) {{A}}>
      (D8 +> (D8 +> (A8 +> (U +> (E8 +> (A8 +> r))))))) [source_tm]⊢*
      (([1] +> ((W_A ^ m) +> (W_C +> l))) <{{F}} ((D8 ++ D8 ++ fossil_tail) +> r)) := by
    have h := runSteps_spec source_tm 91
      ⟨[1], D8 ++ D8 ++ A8 ++ U ++ E8 ++ A8, A, .right⟩
      ⟨D8 ++ D8 ++ fossil_tail, [1], F, .left⟩
      (by decide) ((W_A ^ m) +> (W_C +> l)) r
    simpa only [BoundedConfig.toCfg, List.append_assoc, append_assoc, append_nil] using h
  refine stepStar_trans hturn ?_
  refine stepStar_trans (scan_A8_ret_pow m (W_C +> l) ((D8 ++ D8 ++ fossil_tail) +> r)) ?_
  simpa only [List.append_assoc, append_assoc] using
    scan_C8_ret l ((C8 ^ m) +> ((D8 ++ D8 ++ fossil_tail) +> r))

theorem fossil_tail_finish :
    SideRLs source_tm (hashes ^ 25)
      (fossil_tail +> default) ((B8 ^ 2 ++ U ++ B8 ++ [1, 1]) +> default) :=
  BoundedConfig.sideRLs_c_spec source_tm (T := 2000) (by decide)

theorem c_sweep_even (width pairs : ℕ) (rest : List (Fin 2)) :
    SegRLs source_tm (hashes ^ c_sweep_calls width pairs) []
      (A8 ^ width ++ C8 ^ (2 * pairs) ++ rest)
      (A8 ^ (width + 2 * pairs) ++ rest) := by
  induction pairs generalizing width with
  | zero =>
    simp only [c_sweep_calls, Nat.mul_zero, Nat.add_zero, pow_zero_list, List.append_nil]
    exact .nil _
  | succ pairs ih =>
    rw [show width + 2 * (pairs + 1) = (width + 2) + 2 * pairs by omega,
        show 2 * (pairs + 1) = 2 + 2 * pairs by omega,
        pow_add_list C8 2 (2 * pairs)]
    dsimp [c_sweep_calls]
    have hpair := ca_pair width (C8 ^ (2 * pairs) ++ rest)
    have htail := ih (width + 2)
    rw [List.append_assoc] at htail
    have hcomb := hpair.trans htail
    rw [← pow_add_list] at hcomb
    convert hcomb using 1 <;>
      simp only [C8, A8,
        List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

theorem fossil_tail_lift (width : ℕ) :
    SideRLs source_tm (hashes ^ (25 * 2 ^ width + (2 ^ width - 1)))
      ((A8 ^ width ++ fossil_tail) +> default)
      ((B8 ^ (width + 2) ++ U ++ B8 ++ [1, 1]) +> default) := by
  have htail := (all_A_cycles width 25).sideRLs_concat fossil_tail_finish
  have htail' : SideRLs source_tm (hashes ^ (25 * 2 ^ width))
      ((A8 ^ width ++ fossil_tail) +> default)
      ((A8 ^ width ++ (B8 ^ 2 ++ U ++ B8 ++ [1, 1])) +> default) := by
    simpa only [List.append_assoc, append_assoc] using htail
  have hlow := segRLs_0inf (zero_primary_finish_seg width (B8 ^ 2 ++ U ++ B8 ++ [1, 1]))
  have hcomb := htail'.trans hlow
  simp only [← List.append_assoc] at hcomb
  rw [← pow_add_list, ← pow_add_list B8 width 2] at hcomb
  simpa only [List.append_assoc, append_assoc] using hcomb

def fossil_calls (p k : ℕ) : ℕ :=
  2 ^ p + 2 ^ p + c_sweep_calls (p + 1) k +
    2 ^ (p + 1 + 2 * k) + 2 ^ (p + 2 + 2 * k) +
    (25 * 2 ^ (p + 3 + 2 * k) + (2 ^ (p + 3 + 2 * k) - 1))

theorem fossil_run (p k : ℕ) :
    SideRLs source_tm (hashes ^ fossil_calls p k)
      ((A8 ^ p ++ fossil_start (2 * k)) +> default)
      ((B8 ^ (p + 2 * k + 5) ++ U ++ B8 ++ [1, 1]) +> default) := by
  have hscan : SideRLs source_tm (hashes ^ (2 ^ p))
      ((A8 ^ p ++ fossil_start (2 * k)) +> default)
      ((A8 ^ p ++ (D8 ++ (C8 ^ (2 * k) ++ (D8 ++ (D8 ++ fossil_tail))))) +> default) := by
    simpa only [List.append_assoc, append_assoc] using
      segRLs_0inf (primary_one_rule p _ _ (fossil_scan (2 * k)))
  have hd : SideRLs source_tm (hashes ^ (2 ^ p))
      ((A8 ^ p ++ (D8 ++ (C8 ^ (2 * k) ++ (D8 ++ (D8 ++ fossil_tail))))) +> default)
      ((A8 ^ (p + 1) ++ (C8 ^ (2 * k) ++ (D8 ++ (D8 ++ fossil_tail)))) +> default) := by
    simpa only [List.append_assoc, append_assoc] using
      segRLs_0inf (primary_D_absorb p (C8 ^ (2 * k) ++ D8 ++ D8 ++ fossil_tail))
  have hsweep : SideRLs source_tm (hashes ^ c_sweep_calls (p + 1) k)
      ((A8 ^ (p + 1) ++ (C8 ^ (2 * k) ++ (D8 ++ (D8 ++ fossil_tail)))) +> default)
      ((A8 ^ (p + 1 + 2 * k) ++ (D8 ++ (D8 ++ fossil_tail))) +> default) := by
    simpa only [List.append_assoc, append_assoc] using
      segRLs_0inf (c_sweep_even (p + 1) k (D8 ++ D8 ++ fossil_tail))
  have hd1 : SideRLs source_tm (hashes ^ (2 ^ (p + 1 + 2 * k)))
      ((A8 ^ (p + 1 + 2 * k) ++ (D8 ++ (D8 ++ fossil_tail))) +> default)
      ((A8 ^ (p + 2 + 2 * k) ++ (D8 ++ fossil_tail)) +> default) := by
    rw [show p + 2 + 2 * k = (p + 1 + 2 * k) + 1 by omega]
    simpa only [List.append_assoc, append_assoc] using
      segRLs_0inf (primary_D_absorb (p + 1 + 2 * k) (D8 ++ fossil_tail))
  have hd2 : SideRLs source_tm (hashes ^ (2 ^ (p + 2 + 2 * k)))
      ((A8 ^ (p + 2 + 2 * k) ++ (D8 ++ fossil_tail)) +> default)
      ((A8 ^ (p + 3 + 2 * k) ++ fossil_tail) +> default) := by
    rw [show p + 3 + 2 * k = (p + 2 + 2 * k) + 1 by omega]
    simpa only [List.append_assoc, append_assoc] using
      segRLs_0inf (primary_D_absorb (p + 2 + 2 * k) fossil_tail)
  have htail : SideRLs source_tm (hashes ^ (25 * 2 ^ (p + 3 + 2 * k) + (2 ^ (p + 3 + 2 * k) - 1)))
      ((A8 ^ (p + 3 + 2 * k) ++ fossil_tail) +> default)
      ((B8 ^ (p + 2 * k + 5) ++ (U ++ (B8 ++ [1, 1]))) +> default) := by
    rw [show p + 2 * k + 5 = (p + 3 + 2 * k) + 2 by omega]
    simpa only [List.append_assoc, append_assoc] using fossil_tail_lift (p + 3 + 2 * k)
  have hcomb := hscan.trans (hd.trans (hsweep.trans (hd1.trans (hd2.trans htail))))
  unfold fossil_calls
  rw [pow_add_list, pow_add_list, pow_add_list, pow_add_list, pow_add_list]
  simpa only [List.append_assoc, append_assoc] using hcomb

theorem geom4n_power (k : ℕ) : 3 * geom4n k + 1 = 2 ^ (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [geom4n_succ, show 2 * (k + 1) = 2 * k + 2 by omega, Nat.pow_add]
    have h4 : (2 : ℕ) ^ 2 = 4 := rfl
    rw [h4]
    omega

theorem fossil_count_formula (n k : ℕ) :
    fossil_calls (n + 1) k = 2 ^ n * ((1292 * 2 ^ (2 * k) + 4) / 3) - 1 := by
  have hg := geom4n_power k
  have hdiv : (1292 * 2 ^ (2 * k) + 4) / 3 = 1292 * geom4n k + 432 := by
    have hmul : 1292 * 2 ^ (2 * k) + 4 = (1292 * geom4n k + 432) * 3 := by omega
    rw [hmul, Nat.mul_div_cancel _ (by decide)]
  rw [hdiv]
  unfold fossil_calls
  rw [c_sweep_calls_formula]
  have hp1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
  have hp2 : 2 ^ (n + 1 + 1) = 4 * 2 ^ n := by rw [Nat.pow_succ, hp1]; ring
  have hp25 : 2 ^ (n + 1 + 1 + 1) = 8 * 2 ^ n := by rw [Nat.pow_succ, hp2]; ring
  have hp3 : 2 ^ (n + 1 + 1 + 2 * k) = 4 * 2 ^ n * (3 * geom4n k + 1) := by
    rw [Nat.pow_add, hp2, ← hg]
  have hp4 : 2 ^ (n + 1 + 2 + 2 * k) = 8 * 2 ^ n * (3 * geom4n k + 1) := by
    rw [Nat.pow_add, show n + 1 + 2 = (n + 1 + 1) + 1 by omega, Nat.pow_succ, hp2, ← hg]; ring
  have hp5 : 2 ^ (n + 1 + 3 + 2 * k) = 16 * 2 ^ n * (3 * geom4n k + 1) := by
    rw [Nat.pow_add, show n + 1 + 3 = (n + 1 + 1) + 2 by omega, Nat.pow_add, hp2, ← hg]; ring
  rw [hp1, hp25, hp3, hp4, hp5]
  set P := 2 ^ n
  set G := geom4n k
  have hP : 1 ≤ P := Nat.one_le_two_pow
  have hring : 2 * P + 2 * P + 8 * P * G + 4 * P * (3 * G + 1) + 8 * P * (3 * G + 1) +
      (25 * (16 * P * (3 * G + 1)) + 16 * P * (3 * G + 1)) = P * (1292 * G + 432) := by ring
  have hpos : 1 ≤ 16 * P * (3 * G + 1) := by nlinarith
  omega

-- `RoundCaller`
def exception_done_side (n : ℕ) (output : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  common_left_wall {{B}}> ((C8 ++ A8 ++ U ^ (2 * n)) +> output)

theorem exception_exit_side (k : ℕ) (output : ListBlank (Fin 2)) :
    ((exception_call_left 0 k) <{{F}} output) [source_tm]⊢⁺
      exception_done_side (k + 1) output := by
  unfold exception_call_left exception_done_side
  rw [Nat.mul_zero, pow_zero_list, List.append_nil, pow_add_list X4 (2 * k) 5,
      List.append_assoc, append_assoc]
  refine stepStar_stepPlus_trans (raw_XX_returns k ((X4 ^ 5 ++ [1, 0, 1]) +> default) output) ?_
  have hbase := exception_exit_base (U ^ (2 * k) +> output)
  rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add_list U 2 (2 * k)]
  simpa only [List.append_assoc, append_assoc] using hbase

theorem exception_exit_zero_side (output : ListBlank (Fin 2)) :
    ((exception_pre_left 0) <{{F}} output) [source_tm]⊢⁺
      exception_done_side 0 output := by
  unfold exception_pre_left exception_done_side
  have h0 : (([0] : List (Fin 2)) ^ 9 +> (default : ListBlank (Fin 2))) = default :=
    BoundedConfig.all0_spec (a := ([0] : List (Fin 2)) ^ 9) (by decide)
  have h := run1Steps_spec source_tm 114
    ⟨[], [1, 0, 1, 0] ++ V4 ^ 2 ++ [1, 0, 1] ++ ([0] : List (Fin 2)) ^ 9, F, .left⟩
    ⟨Q8, C8 ++ A8, B, .right⟩
    (by decide) (by decide) default output
  simpa only [BoundedConfig.toCfg, common_left_wall, Nat.mul_zero, Nat.zero_add, pow_zero_list,
    List.append_nil, List.append_assoc, append_assoc, append_nil, h0] using h

theorem exception_calls_side (k : ℕ) (input output : ListBlank (Fin 2))
    (hright : SideRLs source_tm (hashes ^ (k + 1)) input output) :
    ((exception_call_left k 0) {{B}}> input) [source_tm]⊢⁺
      ((exception_call_left 0 k) <{{F}} output) := by
  have hright' : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ k) (F, [])) input output := by
    rw [lrcons_same]
    exact hright
  have hleft : SideRLs (flipTM source_tm) ([left_hash] ^ k)
      (exception_call_left k 0) (exception_call_left 0 k) := by
    simpa only [Nat.zero_add] using exception_relaunches k 0
  exact SideRLs.concat hleft hright'

theorem exception_pre_from_side (n : ℕ) (input output : ListBlank (Fin 2))
    (hright : SideRLs source_tm (hashes ^ n) input output) :
    ((exception_pre_left n) <{{F}} input) [source_tm]⊢⁺
      exception_done_side n output := by
  rcases n with _ | k
  · cases hright
    exact exception_exit_zero_side _
  · exact stepPlus_trans (exception_launch_progress k input)
      (stepPlus_trans (exception_calls_side k input output hright) (exception_exit_side k output))

theorem exception_pre_from_side_word (n : ℕ) (input output : List (Fin 2))
    (hright : SideRLs source_tm (hashes ^ n) (input +> default) (output +> default)) :
    ((exception_pre_left n) <{{F}} (input +> default)) [source_tm]⊢⁺
      exception_done n output := by
  have h := exception_pre_from_side n (input +> default) (output +> default) hright
  unfold exception_done_side at h
  unfold exception_done
  simpa only [List.append_assoc, append_assoc] using h

theorem ordinary_raw_pre_left (n : ℕ) :
    ([1, 0, 1] +> ordinary_left (2 * n + 1)) = exception_pre_left n := by
  simpa only [ordinary_left, common_left_wall, List.append_assoc, append_assoc] using
    exception_pre_left_direct n

theorem ordinary_raw_pre_left_count (tally n : ℕ) (ht : tally = 2 * n + 1) :
    ([1, 0, 1] +> ordinary_left tally) = exception_pre_left n := by
  rw [ht, ordinary_raw_pre_left]

theorem exception_relaunches_partial (h r finished : ℕ) :
    SideRLs (flipTM source_tm) ([left_hash] ^ h)
      (exception_call_left (h + r) finished)
      (exception_call_left r (finished + h)) := by
  induction h generalizing finished with
  | zero =>
    simp only [pow_zero_list, Nat.zero_add, Nat.add_zero]
    exact .nil _
  | succ h ih =>
    rw [pow_succ_list, show h + 1 + r = (h + r) + 1 by omega]
    have hstep := (exception_relaunch_side (h + r) finished).trans (ih (finished + 1))
    simpa only [Nat.add_right_comm finished 1 h, Nat.add_assoc] using hstep

theorem exception_partial_side (h r finished : ℕ) (input output : ListBlank (Fin 2))
    (hright : SideRLs source_tm (hashes ^ h) input output) :
    ((exception_call_left (h + r) finished) {{B}}> input) [source_tm]⊢*
      ((exception_call_left r (finished + h)) {{B}}> output) := by
  rcases h with _ | h
  · cases hright
    simp only [Nat.zero_add, Nat.add_zero]
    exact stepStar_refl source_tm _
  · refine stepPlus_to_stepStar ?_
    have hright' : SideRLs source_tm (lrcons (B, []) ([left_hash] ^ h) (F, [])) input output := by
      rw [lrcons_same]
      exact hright
    have hleft : SideRLs (flipTM source_tm) ([left_hash] ^ h)
        (exception_call_left (h + 1 + r) finished)
        (exception_call_left (1 + r) (finished + h)) := by
      simpa only [Nat.add_assoc] using exception_relaunches_partial h (1 + r) finished
    refine stepPlus_trans (SideRLs.concat hleft hright') ?_
    rw [show 1 + r = r + 1 by omega, show finished + (h + 1) = (finished + h) + 1 by omega]
    exact (exception_relaunch_side r (finished + h)).elim_single_left output

theorem exception_launch_partial_side (h r : ℕ) (input output : ListBlank (Fin 2))
    (hright : SideRLs source_tm (hashes ^ h) input output) :
    ((exception_pre_left (h + r + 1)) <{{F}} input) [source_tm]⊢⁺
      ((exception_call_left r h) {{B}}> output) := by
  refine stepPlus_stepStar_trans (exception_launch_progress (h + r) input) ?_
  simpa only [Nat.zero_add] using exception_partial_side h r 0 input output hright

-- `OpeningLate`
def fourth_output : List (Fin 2) := A8 ^ 29 ++ D8 ++ D8 ++ A8 ++ U ++ E8 ++ A8
def fourth_raw_output : List (Fin 2) := E8 ^ 30 ++ D8 ++ A8 ++ U ++ E8 ++ A8

theorem fourth_raw (l : ListBlank (Fin 2)) :
    (l {{B}}> ((B8 ^ 30 ++ fourth_tail) +> default)) [source_tm]⊢⁺
      (([1, 0, 1] +> l) <{{F}} (fourth_raw_output +> default)) := by
  have h := check_r0inf_spec (M := source_tm) (n := 1079)
    (l₁ := []) (r₁ := B8 ^ 30 ++ fourth_tail)
    (l₂ := fourth_raw_output) (r₂ := [1, 0, 1])
    (q₁ := B) (q₂ := F) (d₁ := .right) (d₂ := .left) (by decide) l
  simpa only [BoundedConfig.toCfg, append_nil] using h

theorem fourth_decode :
    SegRLs source_tm (hashes ^ opening_n4) [] fourth_raw_output fourth_output := by
  have h := E_decode_spec 30 1610612734
  have he : E_decode 30 1610612734 = (List.replicate 29 SA ++ [SD], 0) := by decide
  rw [he, ← n4_binary] at h
  have hwords : sdigits_word (List.replicate 29 SA ++ [SD]) = A8 ^ 29 ++ D8 := rfl
  rw [hwords] at h
  have hfull := h.concat (SegRLs.nil (M := source_tm) (D8 ++ A8 ++ U ++ E8 ++ A8))
  unfold fourth_raw_output fourth_output
  simpa only [List.append_assoc] using hfull

theorem fourth_frontier_to_done :
    ((ordinary_left (2 * opening_n4 + 1)) {{B}}> ((B8 ^ 30 ++ fourth_tail) +> default))
      [source_tm]⊢⁺ exception_done opening_n4 fourth_output := by
  refine stepPlus_trans (fourth_raw (ordinary_left (2 * opening_n4 + 1))) ?_
  rw [ordinary_raw_pre_left]
  exact exception_pre_from_seg opening_n4 fourth_raw_output fourth_output fourth_decode

theorem fourth_cd_to_fossil :
    (exception_done opening_n4 fourth_output) [source_tm]⊢⁺
      ((ordinary_left (cd_calls opening_n4)) {{B}}>
        ((A8 ^ opening_n4 ++ fossil_start 30) +> default)) := by
  have hw : cd_output opening_n4 ++ fourth_output = A8 ^ opening_n4 ++ fossil_start 30 := by
    unfold cd_output fourth_output fossil_start
    have ha30 : A8 ^ 30 = A8 ++ A8 ^ 29 := rfl
    rw [ha30]
    simp only [List.append_assoc]
  have h := exception_done_cd opening_n4 fourth_output (by
    have hge := n4_large
    generalize opening_n4 = n4 at hge
    omega)
  unfold after_cd at h
  rwa [hw] at h

theorem fossil_calls_positive_formula (p k : ℕ) (hp : 1 ≤ p) :
    fossil_calls p k = 2 ^ (p - 1) * ((1292 * 2 ^ (2 * k) + 4) / 3) - 1 := by
  rcases p with _ | p
  · omega
  · simpa using fossil_count_formula p k

theorem fifth_total_tally_generic (n : ℕ) (hn : 2 ≤ n) :
    cd_calls n + fossil_calls n 15 = 2 * opening_decode_calls (n - 2) + 1 := by
  unfold cd_calls
  rw [fossil_calls_positive_formula n 15 (by omega),
      opening_decode_calls_formula (n - 2),
      show n - 2 + 2 = n by omega,
      show 2 * 15 = 30 by omega]
  have h1 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hn2 : n = (n - 2) + 2 := by omega
    conv_lhs => rw [hn2]
    rw [Nat.pow_add]
    ring
  have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have hn1 : n - 1 = (n - 2) + 1 := by omega
    conv_lhs => rw [hn1]
    rw [Nat.pow_succ]
    ring
  rw [h1, h2]
  set P := 2 ^ (n - 2)
  set Q := (1292 * 2 ^ 30 + 4) / 3
  have hpow : 1 ≤ P := Nat.one_le_two_pow
  have hq : 1 ≤ Q := by decide
  have hPQ : 2 * P * Q = 2 * (P * Q) := by ring
  have hpos : 1 ≤ P * Q := Nat.mul_pos hpow hq
  omega

theorem fifth_total_tally :
    cd_calls opening_n4 + fossil_calls opening_n4 15 =
      2 * opening_decode_calls (opening_n4 - 2) + 1 :=
  fifth_total_tally_generic opening_n4 (by
    have hge := n4_large
    generalize opening_n4 = n4 at hge
    omega)

def fifth_output : List (Fin 2) :=
  A8 ^ (opening_n4 - 2) ++ sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1]

theorem fossil_to_fifth_frontier :
    ((ordinary_left (cd_calls opening_n4)) {{B}}>
      ((A8 ^ opening_n4 ++ fossil_start 30) +> default)) [source_tm]⊢*
      ((ordinary_left (2 * opening_decode_calls (opening_n4 - 2) + 1)) {{B}}>
        ((B8 ^ (opening_n4 + 35) ++ U ++ B8 ++ [1, 1]) +> default)) := by
  have h := ordinary_side_run (fossil_calls opening_n4 15) (cd_calls opening_n4)
    ((A8 ^ opening_n4 ++ fossil_start 30) +> default)
    ((B8 ^ (opening_n4 + 2 * 15 + 5) ++ U ++ B8 ++ [1, 1]) +> default)
    (fossil_run opening_n4 15)
  have hexp : opening_n4 + 2 * 15 + 5 = opening_n4 + 35 := by
    generalize opening_n4 = n4
    omega
  rw [fifth_total_tally, hexp] at h
  exact h

theorem fifth_frontier_to_done_generic (n : ℕ) (hn : 2 ≤ n) :
    ((ordinary_left (2 * opening_decode_calls (n - 2) + 1)) {{B}}>
      ((B8 ^ (n + 35) ++ U ++ B8 ++ [1, 1]) +> default)) [source_tm]⊢⁺
      exception_done (opening_decode_calls (n - 2))
        (A8 ^ (n - 2) ++ sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1]) := by
  have hraw := raw_tail_column 0 (n + 34)
    (ordinary_left (2 * opening_decode_calls (n - 2) + 1)) (by decide)
  unfold tail_word y_after at hraw
  rw [show n + 34 + 1 = n + 35 by omega, pow_one_list] at hraw
  have hraw' : ((ordinary_left (2 * opening_decode_calls (n - 2) + 1)) {{B}}>
      ((B8 ^ (n + 35) ++ U ++ B8 ++ [1, 1]) +> default)) [source_tm]⊢⁺
      ((exception_pre_left (opening_decode_calls (n - 2))) <{{F}}
        ((E8 ^ (n + 34) ++ U ^ 3 ++ A8) +> default)) := by
    rw [← ordinary_raw_pre_left]
    simpa only [List.append_assoc, append_assoc] using hraw
  refine stepPlus_trans hraw' ?_
  have hdec := opening_decode (n - 2)
  rw [show n - 2 + 36 = n + 34 by omega] at hdec
  exact exception_pre_from_side_word (opening_decode_calls (n - 2)) _ _ hdec

theorem fifth_frontier_to_done :
    ((ordinary_left (2 * opening_decode_calls (opening_n4 - 2) + 1)) {{B}}>
      ((B8 ^ (opening_n4 + 35) ++ U ++ B8 ++ [1, 1]) +> default)) [source_tm]⊢⁺
      exception_done (opening_decode_calls (opening_n4 - 2)) fifth_output :=
  fifth_frontier_to_done_generic opening_n4 (by
    have hge := n4_large
    generalize opening_n4 = n4 at hge
    omega)

theorem opening_D_to_fifth_done :
    (default {{D}}> default) [source_tm]⊢*
      exception_done (opening_decode_calls (opening_n4 - 2)) fifth_output := by
  refine stepStar_trans opening_D_to_fourth_frontier ?_
  refine stepPlus_to_stepStar ?_
  refine stepPlus_trans fourth_frontier_to_done ?_
  refine stepPlus_trans fourth_cd_to_fossil ?_
  exact stepStar_stepPlus_trans fossil_to_fifth_frontier fifth_frontier_to_done

-- ============================================================================
-- 9. `RoundDecode`, `TailCases` & `FiniteDecode` (`PR_SOBCv10.v` lines 1764–2119)
-- ============================================================================

def decode_budget (r : ℕ) : ℕ := ceil_half r - 2

theorem column_decode_budget (c c' : BinaryColumn) (r : ℕ)
    (hr : 4 ≤ r) (hstep : column_step (decide (r % 2 = 1)) c c') :
    column_required (decode_budget r) c' =
      decode_budget (r * 2 ^ column_width c - column_value c) := by
  rcases hstep with ⟨he, hv⟩
  have hbound := binary_column_value_bound c
  unfold column_required column_next_value column_width column_value at *
  rw [he, hv]
  unfold decode_budget
  rw [ceil_half_scaled_sub r (c.column_e + 1) (digits_value c.column_digits)
    (by omega) (by omega) hbound]
  rw [show c.column_e + 1 - 1 = c.column_e by omega]
  rw [Nat.pow_succ] at hbound ⊢
  set b := 2 ^ c.column_e
  have hb : 1 ≤ b := Nat.one_le_two_pow
  rcases Nat.mod_two_eq_zero_or_one r with hmod | hmod
  · have hdec : decide (r % 2 = 1) = false := decide_eq_false (by omega)
    rw [hdec]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hceil : ceil_half r = r / 2 := by unfold ceil_half; omega
    rw [hceil]
    have hr2 : 2 * (r / 2) = r := by omega
    have hsub : (r / 2 - 2 + 1) * (b * 2) = r * b - 2 * b := by
      rw [show r / 2 - 2 + 1 = r / 2 - 1 by omega, Nat.sub_mul, Nat.one_mul,
          show (r / 2) * (b * 2) = (2 * (r / 2)) * b by ring, hr2, Nat.mul_comm b 2]
    have hrb : 4 * b ≤ r * b := by nlinarith
    have hdiv : digits_value c.column_digits / 2 < b := by omega
    rw [hsub]
    omega
  · have hdec : decide (r % 2 = 1) = true := decide_eq_true hmod
    rw [hdec]
    simp only [↓reduceIte]
    have hceil : ceil_half r = r / 2 + 1 := by unfold ceil_half; omega
    rw [hceil]
    have hr2 : 2 * (r / 2) + 1 = r := by omega
    have hr2' : 2 * (r / 2) = r - 1 := by omega
    have hsub : (r / 2 + 1 - 2 + 1) * (b * 2) = r * b - b := by
      rw [show r / 2 + 1 - 2 + 1 = r / 2 by omega,
          show (r / 2) * (b * 2) = (2 * (r / 2)) * b by ring,
          hr2', Nat.sub_mul, Nat.one_mul]
    have hrb : 4 * b ≤ r * b := by nlinarith
    have hdiv : digits_value c.column_digits / 2 < b := by omega
    rw [hsub]
    omega

def right_remaining : List BinaryColumn → ℕ → ℕ
  | [], r => r
  | c :: rest, r => right_remaining rest r * 2 ^ column_width c - column_value c

def columns_input_count : List BinaryColumn → ℕ → ℕ
  | [], out => out
  | c :: rest, out => column_required (columns_input_count rest out) c

theorem right_remaining_lower (cs : List BinaryColumn) (r : ℕ) (hr : 1 ≤ r) :
    r ≤ right_remaining cs r := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih =>
    dsimp only [right_remaining]
    have hv := binary_column_value_bound c
    change column_value c < 2 ^ column_width c at hv
    have hpow : 2 ≤ 2 ^ column_width c := by
      unfold column_width
      have : 1 ≤ 2 ^ c.column_e := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega
    have hge : r + column_value c ≤ right_remaining cs r * 2 ^ column_width c := by nlinarith
    omega

theorem right_remaining_head_parity (c : BinaryColumn) (cs : List BinaryColumn) (r : ℕ)
    (hr : 1 ≤ r) :
    decide (right_remaining (c :: cs) r % 2 = 1) = decide (column_value c % 2 = 1) := by
  have hlower := right_remaining_lower cs r hr
  have hv := binary_column_value_bound c
  change column_value c < 2 ^ column_width c at hv
  have heq : right_remaining (c :: cs) r + column_value c =
      2 * (right_remaining cs r * 2 ^ c.column_e) := by
    dsimp only [right_remaining]
    unfold column_width at hv ⊢
    rw [Nat.pow_succ] at hv ⊢
    have hge : column_value c ≤ right_remaining cs r * (2 ^ c.column_e * 2) := by nlinarith
    have hm : right_remaining cs r * (2 ^ c.column_e * 2) =
        2 * (right_remaining cs r * 2 ^ c.column_e) := by ring
    omega
  have hmod : (right_remaining (c :: cs) r % 2 = 1) ↔ (column_value c % 2 = 1) := by omega
  exact decide_eq_decide.mpr hmod

theorem columns_decode_budget (cs cs' : List BinaryColumn) (r : ℕ)
    (hr : 4 ≤ r) (hstep : tail_columns_step (decide (r % 2 = 1)) cs cs') :
    columns_input_count cs' (decode_budget r) = decode_budget (right_remaining cs r) := by
  induction cs generalizing cs' with
  | nil =>
    rcases cs' with _ | ⟨c', cs'⟩
    · rfl
    · cases hstep
  | cons c cs ih =>
    rcases cs' with _ | ⟨c', cs'⟩
    · cases hstep
    · rcases hstep with ⟨hc, hrest⟩
      dsimp [columns_input_count, right_remaining]
      rw [ih cs' hrest]
      apply column_decode_budget
      · have := right_remaining_lower cs r (by omega)
        omega
      · rcases cs with _ | ⟨d, rest⟩
        · exact hc
        · rw [right_remaining_head_parity d rest r (by omega)]
          exact hc

theorem right_remaining_finish (cs : List BinaryColumn) (last : List SDigit) (lv : ℕ) :
    right_remaining cs (last_finish_count last lv + 1) =
      columns_finish_count cs (last_finish_count last lv) + 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    dsimp [right_remaining, columns_finish_count]
    rw [ih]
    have h := bfinish_count_value c.column_digits
      (columns_finish_count cs (last_finish_count last lv))
    rw [c.column_length] at h
    change bfinish_count c.column_digits (columns_finish_count cs (last_finish_count last lv)) +
      column_value c + 1 =
      (columns_finish_count cs (last_finish_count last lv) + 1) * 2 ^ column_width c at h
    omega

def mixed_with_tail : List BinaryColumn → List (Fin 2) → List (Fin 2)
  | [], tail => tail
  | c :: rest, tail => mixed_column_word c ++ U ^ 2 ++ mixed_with_tail rest tail

theorem mixed_with_tail_spec (cs : List BinaryColumn) (out : ℕ) (input output : List (Fin 2))
    (h : SideRLs source_tm (hashes ^ out) (input +> default) (output +> default)) :
    SideRLs source_tm (hashes ^ columns_input_count cs out)
      (mixed_with_tail cs input +> default)
      (columns_with_tail cs output +> default) := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    dsimp only [columns_input_count, mixed_with_tail, columns_with_tail]
    have hp := (mixed_column_spec c (columns_input_count cs out)).concat
      (hashes_U_run (columns_input_count cs out) 2)
    have hfull := hp.sideRLs_concat ih
    simpa only [List.append_assoc, append_assoc] using hfull

theorem mixed_with_tail_same_width (b : Bool) (cs cs' : List BinaryColumn) (input : List (Fin 2))
    (hstep : tail_columns_step b cs cs') :
    mixed_with_tail cs input = mixed_with_tail cs' input := by
  induction cs generalizing cs' with
  | nil =>
    rcases cs' with _ | _
    · rfl
    · cases hstep
  | cons c cs ih =>
    rcases cs' with _ | ⟨c', cs'⟩
    · cases hstep
    · rcases hstep with ⟨⟨he, _⟩, hrest⟩
      dsimp only [mixed_with_tail]
      have hw : mixed_column_word c = mixed_column_word c' := by
        unfold mixed_column_word
        rw [he]
      rw [hw, ih cs' hrest]

theorem tail_columns_decode (cs cs' : List BinaryColumn) (r : ℕ) (input output : List (Fin 2))
    (hr : 4 ≤ r) (hstep : tail_columns_step (decide (r % 2 = 1)) cs cs')
    (htail : SideRLs source_tm (hashes ^ decode_budget r) (input +> default) (output +> default)) :
    SideRLs source_tm (hashes ^ decode_budget (right_remaining cs r))
      (mixed_with_tail cs input +> default)
      (columns_with_tail cs' output +> default) := by
  rw [← columns_decode_budget cs cs' r hr hstep,
      mixed_with_tail_same_width _ cs cs' input hstep]
  exact mixed_with_tail_spec cs' (decode_budget r) input output htail

theorem post_unary_even (current previous : ℕ) :
    round_post_unary current previous = 2 * (round_post_unary current previous / 2) := by
  rw [round_post_unary_half_formula, round_post_unary_formula]
  set h := half_parameter current
  set body := 1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1)
  have hp : 2 ^ (h + 2) = 2 * 2 ^ (h + 1) := by
    rw [show h + 2 = (h + 1) + 1 by omega, Nat.pow_succ]; ring
  rw [hp]
  have hpos : 1 ≤ 2 ^ (h + 1) * body := by
    have : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    have : 1 ≤ body := by
      dsimp only [body]
      have := Nat.zero_le (geom4n (previous + 4))
      have := Nat.zero_le (2 ^ (2 * (previous + 4) + 1))
      omega
    nlinarith
  have hm : 2 * 2 ^ (h + 1) * body = 2 * (2 ^ (h + 1) * body) := by ring
  omega

theorem primary_decode_tally (current previous r : ℕ) (hr : 4 ≤ r) (hodd : r % 2 = 1) :
    round_post_unary current previous + (r * 2 ^ round_primary_width current previous - 1) =
      2 * column_required (decode_budget r) (round_outer_column current previous) + 1 := by
  have hv := round_unary_decodes_outer current previous
  have hu := post_unary_even current previous
  have hp := round_primary_width_positive current previous
  unfold column_required round_outer_column
  dsimp only
  rw [show round_primary_width current previous - 1 + 1 =
      round_primary_width current previous by omega]
  set P := round_primary_width current previous
  have hpow : 2 ^ P = 2 * 2 ^ (P - 1) := by
    have hp1 : P = (P - 1) + 1 := by omega
    conv_lhs => rw [hp1]
    rw [Nat.pow_succ]; ring
  have hb : 1 ≤ 2 ^ (P - 1) := Nat.one_le_two_pow
  unfold decode_budget ceil_half
  rw [hpow]
  have h1 : ((r + 1) / 2 - 2 + 1) * (2 * 2 ^ (P - 1)) = r * 2 ^ (P - 1) - 2 ^ (P - 1) := by
    have hr2 : 2 * ((r + 1) / 2 - 2 + 1) = r - 1 := by omega
    rw [show ((r + 1) / 2 - 2 + 1) * (2 * 2 ^ (P - 1)) =
        (2 * ((r + 1) / 2 - 2 + 1)) * 2 ^ (P - 1) by ring,
        hr2, Nat.sub_mul, Nat.one_mul]
  rw [h1]
  have hrb : 4 * 2 ^ (P - 1) ≤ r * 2 ^ (P - 1) := Nat.mul_le_mul_right _ hr
  have hm : r * (2 * 2 ^ (P - 1)) = 2 * (r * 2 ^ (P - 1)) := by ring
  omega

-- `TailCases`
def decoded_last7 : List SDigit := (E_decode 28 341136723).1
def decoded_last8 : List SDigit := (E_decode 27 768955732).1
def decoded_last9 : List SDigit := (E_decode 26 18175315).1

theorem decode_last7 : E_decode 28 341136723 = (decoded_last7, 0) := by decide
theorem decode_last8 : E_decode 27 768955732 = (decoded_last8, 3) := by decide
theorem decode_last9 : E_decode 26 18175315 = (decoded_last9, 0) := by decide
theorem decode_trigger_frontier : E_decode 25 134217725 = (List.replicate 25 SB, 1) := by decide

theorem decoded_last_checkpoints :
    decoded_last7.length = 28 ∧ sdigits_value decoded_last7 = -195734187 ∧
    decoded_last8.length = 27 ∧ sdigits_value decoded_last8 = 97867094 ∧
    decoded_last9.length = 26 ∧ sdigits_value decoded_last9 = -116042411 := by
  decide

theorem E_decode_tail_run (width calls : ℕ) (ds : List SDigit) (out k lv : ℕ)
    (hdecode : E_decode width calls = (ds, out))
    (htail : SideRLs source_tm (hashes ^ out) (y_after k +> default) (y_after lv +> default)) :
    SideRLs source_tm (hashes ^ calls)
      ((E8 ^ width ++ U ^ (2 * k + 3) ++ y_after k) +> default)
      ((sdigits_word ds ++ U ^ (2 * k + 3) ++ y_after lv) +> default) := by
  have hdigits := E_decode_spec width calls
  rw [hdecode] at hdigits
  have hprefix := hdigits.concat (hashes_U_run out (2 * k + 3))
  have hfull := hprefix.sideRLs_concat htail
  simpa only [List.append_assoc, append_assoc] using hfull

theorem last_case6_return :
    SideRLs source_tm (hashes ^ 341136723)
      ((E8 ^ 28 ++ U ^ 5 ++ y_after 1) +> default)
      ((sdigits_word decoded_last7 ++ U ^ 5 ++ y_after 1) +> default) :=
  E_decode_tail_run 28 341136723 decoded_last7 0 1 1 decode_last7 (.nil _)

theorem last_case7_return :
    SideRLs source_tm (hashes ^ 768955732)
      ((E8 ^ 27 ++ U ^ 7 ++ y_after 2) +> default)
      ((sdigits_word decoded_last8 ++ U ^ 7 ++ y_after 5) +> default) :=
  E_decode_tail_run 27 768955732 decoded_last8 3 2 5 decode_last8 (tail_level_finish 2 (by decide))

theorem last_case8_return :
    SideRLs source_tm (hashes ^ 18175315)
      ((E8 ^ 26 ++ U ^ 9 ++ y_after 3) +> default)
      ((sdigits_word decoded_last9 ++ U ^ 9 ++ y_after 3) +> default) :=
  E_decode_tail_run 26 18175315 decoded_last9 0 3 3 decode_last9 (.nil _)

theorem sdigits_word_replicate_SB (n : ℕ) : sdigits_word (List.replicate n SB) = B8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, sdigits_word, sdigit_word, ih]

theorem last_case9_frontier :
    SideRLs source_tm (hashes ^ 134217725)
      ((E8 ^ 25 ++ U ^ 11 ++ y_after 4) +> default)
      ((B8 ^ 25 ++ U ^ 11 ++ y_after 5) +> default) := by
  have h := E_decode_tail_run 25 134217725 (List.replicate 25 SB) 1 4 5
    decode_trigger_frontier (tail_level_finish 4 (by decide))
  rwa [sdigits_word_replicate_SB 25] at h

-- `FiniteDecode`
def phase_R : ℕ → ℕ
  | 1 => 682273449
  | 2 => 1537911467
  | 3 => 36350634
  | _ => 317369003

theorem phase_R_value (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (6 - (phase_lv k : ℤ)) * pow2 (phase_width k) - phase_value k = (phase_R k : ℤ) := by
  rcases k with _ | _ | _ | _ | _ | k <;> try omega
  all_goals decide

theorem finite_last_R (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv :
    ℕ)
    (hpre : finite_round_pre current previous zs last k lv) :
    last_finish_count last lv + 1 = phase_R k := by
  rcases hpre with ⟨⟨hk1, hk4⟩, _, _, _, hlen, hval, hlv⟩
  have hlvbound : lv ≤ 5 := by
    rw [hlv]
    rcases k with _ | _ | _ | _ | _ | k <;> try omega
    all_goals decide
  have h := sfinish_value last (5 - lv)
  change (last_finish_count last lv : ℤ) + sdigits_value last + 1 =
    (((5 - lv : ℕ) : ℤ) + 1) * pow2 last.length at h
  have hsub : ((5 - lv : ℕ) : ℤ) = 5 - (lv : ℤ) := by omega
  rw [hsub, hlen, hval, hlv, show (5 - (phase_lv k : ℤ) + 1) = 6 - (phase_lv k : ℤ) by ring] at h
  have hr := phase_R_value k hk1 hk4
  have hZ : ((last_finish_count last lv + 1 : ℕ) : ℤ) = (phase_R k : ℤ) := by
    rw [hlv]
    push_cast
    linarith
  exact Int.ofNat.inj hZ

theorem phase_R_large (k : ℕ) : 4 ≤ phase_R k := by
  unfold phase_R
  split <;> decide

def next_last : ℕ → List SDigit
  | 1 => decoded_last7
  | 2 => decoded_last8
  | _ => decoded_last9

def phase_budget_val : ℕ → ℕ
  | 1 => 341136723
  | 2 => 768955732
  | _ => 18175315

theorem phase_decode_budget (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    decode_budget (phase_R k) = phase_budget_val k := by
  rcases k with _ | _ | _ | _ | k <;> try omega
  all_goals decide

theorem finite_last_decode (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    SideRLs source_tm (hashes ^ decode_budget (phase_R k))
      ((E8 ^ (phase_width k - 1) ++ U ^ (2 * k + 3) ++ y_after k) +> default)
      ((sdigits_word (next_last k) ++ U ^ (2 * k + 3) ++ y_after (phase_lv (k + 1))) +> default) :=
          by
  rw [phase_decode_budget k hk1 hk3]
  rcases k with _ | _ | _ | _ | k <;> try omega
  · exact last_case6_return
  · exact last_case7_return
  · exact last_case8_return

theorem next_last_checkpoints (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (next_last k).length = phase_width (k + 1) ∧
      sdigits_value (next_last k) = phase_value (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := decoded_last_checkpoints
  rcases k with _ | _ | _ | _ | k <;> try omega
  · exact ⟨h1, h2⟩
  · exact ⟨h3, h4⟩
  · exact ⟨h5, h6⟩

theorem phase_R_parity (k : ℕ) :
    (phase_R k % 2 = 1) ↔ (phase_value k % 2 = 1) := by
  rcases k with _ | _ | _ | _ | k
  · decide
  · decide
  · decide
  · decide
  · have h1 : phase_R (k + 4) = 317369003 := rfl
    have h2 : phase_value (k + 4) = -116042411 := rfl
    rw [h1, h2]
    decide

theorem finite_suffix_odd (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k
    lv : ℕ)
    (hpre : finite_round_pre current previous zs last k lv) :
    right_remaining zs (phase_R k) % 2 = 1 := by
  rcases hpre with ⟨_, _, hodd, _, _, hval, _⟩
  rcases zs with _ | ⟨c, zs⟩
  · dsimp [right_remaining]
    rw [phase_R_parity, ← hval]
    exact hodd
  · have hp := right_remaining_head_parity c zs (phase_R k) (by have := phase_R_large k; omega)
    exact of_decide_eq_true (hp.trans (decide_eq_true hodd))

theorem finite_columns_decode (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ)
    (hpre : finite_round_pre current previous zs last k lv) (hk3 : k ≤ 3) :
    ∃ zs',
      tail_columns_step (decide (phase_R k % 2 = 1)) zs zs' ∧
      (∀ c' ∈ z_column previous :: zs', column_budget (4 - (k + 1)) c') ∧
      SideRLs source_tm (hashes ^ decode_budget (right_remaining zs (phase_R k)))
        (mixed_with_tail zs (E8 ^ (phase_width k - 1) ++ U ^ (2 * k + 3) ++ y_after k) +> default)
        (columns_with_tail zs'
          (sdigits_word (next_last k) ++ U ^ (2 * k + 3) ++ y_after (phase_lv (k + 1))) +>
              default) := by
  obtain ⟨zs', hstep, hbudget⟩ := tail_columns_round_budget k previous zs
    (decide (phase_R k % 2 = 1)) hpre.fr_stage.1 hk3 hpre.fr_columns
  refine ⟨zs', hstep, hbudget, ?_⟩
  exact tail_columns_decode zs zs' (phase_R k) _ _ (phase_R_large k) hstep
    (finite_last_decode k hpre.fr_stage.1 hk3)

-- ============================================================================
-- 10. `FrontierBridge`, `RoundAssembly`, `WidthBounds`, `FiniteComplete`, `FinalTrigger` &
-- `FiniteOrbit`
-- ============================================================================

def tail_frontier_state (unary primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k : ℕ) :
    Cfg (Fin 2) (Fin 6) :=
  (ordinary_left unary) {{B}}> (tail_frontier primary zs last k +> default)

theorem post_tail_to_frontier (unary primary : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ) (hlv : lv ≤ 5) :
    (post_ca_tail unary primary zs last k lv) [source_tm]⊢*
      tail_frontier_state (unary + tail_finish_count primary zs last lv) primary zs last k :=
  ordinary_side_run (tail_finish_count primary zs last lv) unary
    (tail_layout primary zs last k lv +> default)
    (tail_frontier primary zs last k +> default)
    (tail_to_frontier primary zs last k lv hlv)

theorem all_B_tail_full (zs : List BinaryColumn) (last k : ℕ) :
    all_B_with_tail zs (B8 ^ (last + 1) ++ tail_word k) =
      full_tail (zs.map BinaryColumn.column_e) last k := by
  induction zs with
  | nil => rfl
  | cons c zs ih =>
    dsimp only [all_B_with_tail]
    rw [List.map_cons, ih, full_tail_cons]
    rfl

theorem tail_frontier_full (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k e : ℕ)
    (hlen : last.length = e + 1) :
    tail_frontier (primary + 1) zs last k =
      full_tail (primary :: zs.map BinaryColumn.column_e) e k := by
  unfold tail_frontier
  rw [hlen, full_tail_cons, ← all_B_tail_full]
  unfold tail_word
  simp only [List.append_assoc]

theorem post_tail_raw (unary primary : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv e : ℕ) (hlv : lv ≤ 5) (hk : k ≤ 5) (hlen : last.length = e + 1) :
    (post_ca_tail unary (primary + 1) zs last k lv) [source_tm]⊢⁺
      (([1, 0, 1] +> ordinary_left (unary + tail_finish_count (primary + 1) zs last lv)) <{{F}}
        (mixed_tail (primary :: zs.map BinaryColumn.column_e) e k +> default)) := by
  refine stepStar_stepPlus_trans (post_tail_to_frontier unary (primary + 1) zs last k lv hlv) ?_
  unfold tail_frontier_state
  rw [tail_frontier_full primary zs last k e hlen]
  exact raw_tail_columns (primary :: zs.map BinaryColumn.column_e) e k _ hk

theorem mixed_tail_chain (cs : List BinaryColumn) (e k : ℕ) :
    mixed_tail (cs.map BinaryColumn.column_e) e k =
      mixed_with_tail cs (E8 ^ e ++ U ^ (2 * k + 3) ++ y_after k) := by
  induction cs with
  | nil =>
    unfold mixed_tail mixed_with_tail
    simp [spaced_words, List.append_assoc]
  | cons c cs ih =>
    rw [List.map_cons, mixed_tail_cons, ih]
    dsimp only [mixed_with_tail, mixed_column_word]

theorem tail_finish_equation (primary : ℕ) (zs : List BinaryColumn) (last : List SDigit) (lv : ℕ) :
    tail_finish_count primary zs last lv + 1 =
      (columns_finish_count zs (last_finish_count last lv) + 1) * 2 ^ primary := by
  have h := bfinish_count_value (List.replicate primary BA)
    (columns_finish_count zs (last_finish_count last lv))
  rw [List.length_replicate, digits_value_repeat_BA] at h
  change tail_finish_count primary zs last lv + 0 + 1 =
    (columns_finish_count zs (last_finish_count last lv) + 1) * 2 ^ primary at h
  omega

def finite_decode_count (current previous : ℕ) (zs : List BinaryColumn) (k : ℕ) : ℕ :=
  column_required (decode_budget (right_remaining zs (phase_R k)))
    (round_outer_column current previous)

def finite_decode_input (current previous : ℕ) (zs : List BinaryColumn) (k : ℕ) : List (Fin 2) :=
  mixed_with_tail (round_outer_column current previous :: zs)
    (E8 ^ (phase_width k - 1) ++ U ^ (2 * k + 3) ++ y_after k)

def finite_decode_output (current previous : ℕ) (zs' : List BinaryColumn) (k : ℕ) : List (Fin 2) :=
  columns_with_tail (round_outer_column current previous :: zs')
    (sdigits_word (next_last k) ++ U ^ (2 * k + 3) ++ y_after (phase_lv (k + 1)))

theorem finite_raw_to_pre (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k
    lv : ℕ)
    (hpre : finite_round_pre current previous zs last k lv) :
    (post_ca_tail (round_post_unary current previous)
      (round_primary_width current previous) zs last k lv) [source_tm]⊢⁺
      ((exception_pre_left (finite_decode_count current previous zs k)) <{{F}}
        (finite_decode_input current previous zs k +> default)) := by
  have hr := finite_last_R current previous zs last k lv hpre
  have hodd := finite_suffix_odd current previous zs last k lv hpre
  rcases hpre with ⟨⟨hk1, hk4⟩, _, _, _, hlen, _, hlv⟩
  have hlvbound : lv ≤ 5 := by
    rw [hlv]
    rcases k with _ | _ | _ | _ | _ | k <;> try omega
    all_goals decide
  have hp := round_primary_width_positive current previous
  have hlen' : last.length = (phase_width k - 1) + 1 := by
    rw [hlen]; unfold phase_width; omega
  have hraw := post_tail_raw (round_post_unary current previous)
    (round_primary_width current previous - 1) zs last k lv (phase_width k - 1)
    hlvbound (by omega) hlen'
  rw [show round_primary_width current previous - 1 + 1 =
      round_primary_width current previous by omega] at hraw
  have htally : round_post_unary current previous +
      tail_finish_count (round_primary_width current previous) zs last lv =
      2 * finite_decode_count current previous zs k + 1 := by
    have hcount := tail_finish_equation (round_primary_width current previous) zs last lv
    rw [← right_remaining_finish, hr] at hcount
    have hbase := phase_R_large k
    have hlower := right_remaining_lower zs (phase_R k) (by omega)
    have ht := primary_decode_tally current previous (right_remaining zs (phase_R k))
      (by omega) hodd
    unfold finite_decode_count
    omega
  rw [ordinary_raw_pre_left_count _ _ htally] at hraw
  unfold finite_decode_input
  have hmap : ((round_primary_width current previous - 1) :: zs.map BinaryColumn.column_e) =
      (round_outer_column current previous :: zs).map BinaryColumn.column_e := rfl
  rw [hmap, mixed_tail_chain] at hraw
  exact hraw

theorem finite_decode_side (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ) (zs' : List BinaryColumn)
    (hpre : finite_round_pre current previous zs last k lv) (hk3 : k ≤ 3)
    (hstep : tail_columns_step (decide (phase_R k % 2 = 1)) zs zs') :
    SideRLs source_tm (hashes ^ finite_decode_count current previous zs k)
      (finite_decode_input current previous zs k +> default)
      (finite_decode_output current previous zs' k +> default) := by
  have htail := tail_columns_decode zs zs' (phase_R k) _ _ (phase_R_large k) hstep
    (finite_last_decode k hpre.fr_stage.1 hk3)
  have hp := (mixed_column_spec (round_outer_column current previous)
      (decode_budget (right_remaining zs (phase_R k)))).concat
    (hashes_U_run (decode_budget (right_remaining zs (phase_R k))) 2)
  have hfull := hp.sideRLs_concat htail
  unfold finite_decode_count finite_decode_input finite_decode_output
  dsimp only [mixed_with_tail, columns_with_tail]
  simpa only [List.append_assoc, append_assoc] using hfull

theorem finite_exception_done (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ) (hpre : finite_round_pre current previous zs last k lv) (hk3 : k ≤ 3) :
    ∃ zs',
      tail_columns_step (decide (phase_R k % 2 = 1)) zs zs' ∧
      (∀ c' ∈ z_column previous :: zs', column_budget (4 - (k + 1)) c') ∧
      ((post_ca_tail (round_post_unary current previous)
        (round_primary_width current previous) zs last k lv) [source_tm]⊢⁺
        exception_done (finite_decode_count current previous zs k)
          (finite_decode_output current previous zs' k)) := by
  obtain ⟨zs', hstep, hbudget, _⟩ := finite_columns_decode current previous zs last k lv hpre hk3
  refine ⟨zs', hstep, hbudget, ?_⟩
  refine stepPlus_trans (finite_raw_to_pre current previous zs last k lv hpre) ?_
  exact exception_pre_from_side_word _ _ _
    (finite_decode_side current previous zs last k lv zs' hpre hk3 hstep)

theorem finite_done_to_next_post (current previous : ℕ) (zs' : List BinaryColumn) (k next : ℕ) :
    (exception_done (half_parameter next)
      (finite_decode_output current previous zs' k)) [source_tm]⊢⁺
      post_ca_tail (round_post_unary next current) (round_primary_width next current)
        (z_column previous :: zs') (next_last k) (k + 1) (phase_lv (k + 1)) := by
  set tail := sdigits_word (next_last k) ++ U ^ (2 * k + 3) ++ y_after (phase_lv (k + 1))
  set rest :=
      B8 ++ (digits_word A8 B8) (z_tail_digits previous) ++ U ^ 2 ++ columns_with_tail zs' tail
  have hca := exception_done_ca (half_parameter next) (current + 4) rest
    (by unfold half_parameter; omega)
  have hlhs : exception_done (half_parameter next) (finite_decode_output current previous zs' k) =
      exception_done (half_parameter next)
        (A8 ^ (2 * (current + 4)) ++ B8 ++ B8 ++ A8 ++ B8 ++ A8 ++ rest) := by
    unfold finite_decode_output exception_done
    dsimp only [columns_with_tail]
    rw [round_outer_column_word]
    dsimp only [rest, tail]
    have hexp1 : half_parameter current + 2 = 2 * (current + 4) := by unfold half_parameter; omega
    rw [hexp1]
    simp only [List.append_assoc]
  have hrhs : ((ordinary_left (cd_calls (half_parameter next) + ca_calls (half_parameter next)
      (current + 4))) {{B}}>
        ((A8 ^ (half_parameter next + 2 * (current + 4) + 4) ++ U ^ 2 ++ B8 ++ B8 ++ rest) +>
            default)) =
      post_ca_tail (round_post_unary next current) (round_primary_width next current)
        (z_column previous :: zs') (next_last k) (k + 1) (phase_lv (k + 1)) := by
    unfold post_ca_tail round_post_unary round_primary_width
    rw [tail_layout_chain]
    dsimp only [columns_with_tail]
    rw [z_column_word, z_digits_word_split, show 2 * (k + 1) + 1 = 2 * k + 3 by omega]
    unfold rest tail
    have hexp2 : half_parameter next + 2 * (current + 4) + 4 =
        half_parameter next + half_parameter current + 6 := by unfold half_parameter; omega
    rw [hexp2]
    simp only [List.append_assoc, append_assoc]
  rw [hlhs, ← hrhs]
  exact hca

-- `WidthBounds`
theorem outer_decode_even_ge6 (current previous out : ℕ) :
    ∃ q, column_required out (round_outer_column current previous) = 2 * q ∧ 6 ≤ 2 * q := by
  have hp := round_primary_width_positive current previous
  unfold column_required round_outer_column
  dsimp only
  rw [show round_primary_width current previous - 1 + 1 =
      round_primary_width current previous by omega,
      round_outer_digits_value]
  set P := round_primary_width current previous
  have hp3 : 3 ≤ P := by dsimp [P]; unfold round_primary_width half_parameter; omega
  have hsplit : 2 ^ P = 2 * 2 ^ (P - 1) := by
    have hp1 : P = (P - 1) + 1 := by omega
    conv_lhs => rw [hp1]
    rw [Nat.pow_succ]; ring
  have ha : 4 ≤ 2 ^ (P - 1) := by
    rw [show P - 1 = (P - 3) + 2 by omega, Nat.pow_add]
    have : 1 ≤ 2 ^ (P - 3) := Nat.one_le_two_pow
    have h4 : (2 : ℕ) ^ 2 = 4 := rfl
    rw [h4]
    omega
  have hh : 2 ^ (half_parameter current + 1) = 2 * 2 ^ (half_parameter current) := by
    rw [Nat.pow_succ]; ring
  rw [hh, hsplit]
  set a := 2 ^ (P - 1)
  set body :=
      1 + geom4n (previous + 4) + 2 ^ (2 * (previous + 4) + 1) + 2 ^ (2 * (previous + 4) + 2)
  set b := 2 ^ (half_parameter current) * body
  have hoa : 4 ≤ (out + 1) * a := Nat.le_mul_of_pos_left a (by omega) |>.trans' ha
  have hm1 : (out + 1) * (2 * a) = 2 * ((out + 1) * a) := by ring
  have hm2 : 2 * 2 ^ (half_parameter current) * body = 2 * b := by dsimp only [b]; ring
  refine ⟨(out + 1) * a - 1 + b, by omega, by omega⟩

theorem outer_decode_parameter (current previous out : ℕ) :
    half_parameter ((column_required out (round_outer_column current previous) - 6) / 2) =
      column_required out (round_outer_column current previous) := by
  obtain ⟨q, hq, hge⟩ := outer_decode_even_ge6 current previous out
  unfold half_parameter
  omega

theorem outer_decode_lower (current previous out : ℕ) :
    2 ^ round_primary_width current previous - 2 ≤
      column_required out (round_outer_column current previous) := by
  have hp := round_primary_width_positive current previous
  unfold column_required round_outer_column
  dsimp only
  rw [show round_primary_width current previous - 1 + 1 =
      round_primary_width current previous by omega]
  set P := round_primary_width current previous
  have h1 : 2 ^ P ≤ (out + 1) * 2 ^ P := Nat.le_mul_of_pos_left (2 ^ P) (by omega)
  omega

theorem outer_decode_growth (current previous out suffix_width : ℕ)
    (hwidth : 2 * suffix_width + 4 ≤ half_parameter previous + 1) :
    2 * (half_parameter current + 1 + half_parameter previous + suffix_width) + 4 ≤
      column_required out (round_outer_column current previous) + 1 := by
  have hlower := outer_decode_lower current previous out
  have hpow := pow2_linear_margin (half_parameter current + half_parameter previous)
  unfold round_primary_width at hlower
  rw [show half_parameter current + half_parameter previous + 6 =
      (half_parameter current + half_parameter previous + 5) + 1 by omega,
      Nat.pow_succ] at hlower
  omega

theorem tail_columns_step_width_sum (b : Bool) (cs cs' : List BinaryColumn)
    (hstep : tail_columns_step b cs cs') :
    columns_width_sum cs' = columns_width_sum cs := by
  induction cs generalizing cs' with
  | nil =>
    rcases cs' with _ | _
    · rfl
    · cases hstep
  | cons c cs ih =>
    rcases cs' with _ | ⟨c', cs'⟩
    · cases hstep
    · rcases hstep with ⟨⟨he, _⟩, hrest⟩
      rw [columns_width_sum_cons, columns_width_sum_cons, ih cs' hrest, he]

theorem tail_width_dominance_step (current previous next out : ℕ) (cs cs' : List BinaryColumn)
    (last last' : List SDigit) (b : Bool)
    (hstep : tail_columns_step b cs cs')
    (hlast : last.length = last'.length + 1)
    (hnext : half_parameter next = column_required out (round_outer_column current previous))
    (hw : 2 * (columns_width_sum cs + last.length) + 4 ≤ half_parameter previous + 1 ∧
      2 * (half_parameter previous + 1 + columns_width_sum cs + last.length) + 4 ≤
        half_parameter current + 1) :
    2 * (columns_width_sum (z_column previous :: cs') + last'.length) + 4 ≤
      half_parameter current + 1 ∧
    2 * (half_parameter current + 1 + columns_width_sum (z_column previous :: cs') + last'.length) +
        4 ≤
      half_parameter next + 1 := by
  rcases hw with ⟨hprev, hcur⟩
  rw [columns_width_sum_cons, tail_columns_step_width_sum b cs cs' hstep, z_column_e, hnext]
  have hgrowth := outer_decode_growth current previous out
    (columns_width_sum cs + last.length) hprev
  omega

theorem tail_next_half_tally (current previous : ℕ) (cs : List BinaryColumn) (last : List SDigit)
    (lv n : ℕ) (hlv : lv ≤ 5)
    (htally : round_post_unary current previous +
      tail_finish_count (round_primary_width current previous) cs last lv = 2 * n + 1) :
    tail_next_half current previous cs last lv = (n : ℤ) := by
  unfold tail_next_half
  rw [← trigger_hash_count (round_primary_width current previous) cs last lv hlv]
  have hcast : (round_post_unary current previous : ℤ) +
      ((tail_finish_count (round_primary_width current previous) cs last lv + 1 : ℕ) : ℤ) - 1 =
      2 * (n : ℤ) + 1 := by omega
  rw [hcast]
  omega

theorem tail_next_parameter (current previous : ℕ) (cs : List BinaryColumn) (last : List SDigit)
    (lv out : ℕ) (hlv : lv ≤ 5)
    (htally : round_post_unary current previous +
      tail_finish_count (round_primary_width current previous) cs last lv =
        2 * column_required out (round_outer_column current previous) + 1) :
    half_parameter (tail_next_index current previous cs last lv) =
      column_required out (round_outer_column current previous) := by
  unfold tail_next_index
  rw [tail_next_half_tally current previous cs last lv _ hlv htally]
  obtain ⟨q, hq, hge⟩ := outer_decode_even_ge6 current previous out
  set n := column_required out (round_outer_column current previous)
  have hto : (((n : ℤ) - 6) / 2).toNat = (n - 6) / 2 := by omega
  rw [hto]
  exact outer_decode_parameter current previous out

-- `FiniteComplete`
theorem finite_tally (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit) (k lv : ℕ)
    (hpre : finite_round_pre current previous zs last k lv) :
    round_post_unary current previous +
      tail_finish_count (round_primary_width current previous) zs last lv =
      2 * finite_decode_count current previous zs k + 1 := by
  have hr := finite_last_R current previous zs last k lv hpre
  have hodd := finite_suffix_odd current previous zs last k lv hpre
  have hcount := tail_finish_equation (round_primary_width current previous) zs last lv
  rw [← right_remaining_finish, hr] at hcount
  have hbase := phase_R_large k
  have hlower := right_remaining_lower zs (phase_R k) (by omega)
  have ht := primary_decode_tally current previous (right_remaining zs (phase_R k))
    (by omega) hodd
  unfold finite_decode_count
  omega

theorem finite_next_parameter (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ)
    (hpre : finite_round_pre current previous zs last k lv) :
    half_parameter (tail_next_index current previous zs last lv) =
      finite_decode_count current previous zs k := by
  have htally := finite_tally current previous zs last k lv hpre
  have hlv : lv ≤ 5 := by
    rcases hpre.fr_stage with ⟨hk1, hk4⟩
    rw [hpre.fr_lv]
    rcases k with _ | _ | _ | _ | _ | k <;> try omega
    all_goals decide
  exact tail_next_parameter current previous zs last lv _ hlv htally

theorem finite_round_proved (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (k lv : ℕ) (hpre : finite_round_pre current previous zs last k lv) (hk3 : k ≤ 3) :
    ∃ zs' last' lv',
      ((post_ca_tail (round_post_unary current previous)
        (round_primary_width current previous) zs last k lv) [source_tm]⊢⁺
        post_ca_tail
          (round_post_unary (tail_next_index current previous zs last lv) current)
          (round_primary_width (tail_next_index current previous zs last lv) current)
          (z_column previous :: zs') last' (k + 1) lv') ∧
      finite_round_pre (tail_next_index current previous zs last lv) current
        (z_column previous :: zs') last' (k + 1) lv' := by
  obtain ⟨zs', hstep, hbudget, hdone⟩ :=
      finite_exception_done current previous zs last k lv hpre hk3
  have hnext := finite_next_parameter current previous zs last k lv hpre
  obtain ⟨hlen', hval'⟩ := next_last_checkpoints k hpre.fr_stage.1 hk3
  refine ⟨zs', next_last k, phase_lv (k + 1), ?_, ?_⟩
  · refine stepPlus_trans hdone ?_
    rw [← hnext]
    exact finite_done_to_next_post current previous zs' k
      (tail_next_index current previous zs last lv)
  · refine ⟨⟨by omega, by omega⟩, hbudget, z_column_odd previous, ?_, hlen', hval', rfl⟩
    refine tail_width_dominance_step current previous
      (tail_next_index current previous zs last lv)
      (decode_budget (right_remaining zs (phase_R k)))
      zs zs' last (next_last k) _ hstep ?_ hnext hpre.fr_width
    rw [hpre.fr_last_len, hlen']
    unfold phase_width
    omega

-- `FinalTrigger` & `FiniteOrbit`
def full_finish_count : List ℕ → ℕ → ℕ
  | [], out => out
  | e :: rest, out => (full_finish_count rest out + 2) * 2 ^ (e + 1) - 3

theorem full_finish_prefix (es : List ℕ) (out : ℕ) (input output : List (Fin 2))
    (htail : SideRLs source_tm (hashes ^ out) (input +> default) (output +> default)) :
    SideRLs source_tm (hashes ^ full_finish_count es out)
      (spaced_words (es.map (fun e => E8 ^ e ++ A8) ++ [input]) +> default)
      (spaced_words (es.map (fun e => B8 ^ (e + 1)) ++ [output]) +> default) := by
  induction es with
  | nil => exact htail
  | cons e es ih =>
    dsimp only [full_finish_count]
    rw [List.map_cons, List.map_cons, spaced_snoc_cons, spaced_snoc_cons]
    have hc := standard_mixed_to_binary_out_spec e (List.replicate (e + 1) BB)
      (full_finish_count es out) (List.length_replicate)
    rw [digits_word_repeat_BB, digits_value_repeat_BB] at hc
    have hpow : 2 ≤ 2 ^ (e + 1) := by
      have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    have heq : (full_finish_count es out + 1) * 2 ^ (e + 1) - 2 + (2 ^ (e + 1) - 1) =
        (full_finish_count es out + 2) * 2 ^ (e + 1) - 3 := by
      set X := 2 ^ (e + 1)
      have hX : 2 ≤ X := hpow
      have h1 : (full_finish_count es out + 1) * X + X = (full_finish_count es out + 2) * X := by
        ring
      have h2 : 2 ≤ (full_finish_count es out + 1) * X :=
          Nat.le_mul_of_pos_left X (by omega) |>.trans' hX
      omega
    rw [heq] at hc
    have hp := hc.concat (hashes_U_run (full_finish_count es out) 2)
    have hfull := hp.sideRLs_concat ih
    simpa only [List.append_assoc, append_assoc] using hfull

theorem spaced_tail_append (ws : List (List (Fin 2))) (x suffix : List (Fin 2)) :
    spaced_words (ws ++ [x ++ suffix]) = spaced_words (ws ++ [x]) ++ suffix := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [spaced_snoc_cons, spaced_snoc_cons, ih]
    simp only [List.append_assoc]

def trigger_finish (es : List ℕ) : ℕ := full_finish_count es 134217725

theorem raw_four_to_frontier (es : List ℕ) :
    SideRLs source_tm (hashes ^ trigger_finish es)
      (mixed_tail es 25 4 +> default)
      (full_tail es 24 5 +> default) := by
  have h := full_finish_prefix es 134217725
    (E8 ^ 25 ++ U ^ 11 ++ y_after 4)
    (B8 ^ 25 ++ U ^ 11 ++ y_after 5)
    last_case9_frontier
  rw [spaced_tail_append, spaced_tail_append, spaced_tail_append, spaced_tail_append] at h
  unfold y_after at h
  unfold trigger_finish mixed_tail full_tail tail_word y_after
  simpa only [List.append_assoc, append_assoc] using h

theorem full_finish_monotone (es : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    full_finish_count es a ≤ full_finish_count es b := by
  induction es with
  | nil => exact hab
  | cons e es ih =>
    dsimp only [full_finish_count]
    have hle : (full_finish_count es a + 2) * 2 ^ (e + 1) ≤ (full_finish_count es b + 2) * 2 ^ (e +
        1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem nested_required_finish (es : List ℕ) (e : ℕ) :
    nested_required es e = full_finish_count es (3 * (2 ^ (e + 1) - 1)) := by
  induction es with
  | nil => rfl
  | cons a es ih =>
    dsimp only [nested_required, full_finish_count]
    rw [ih]
    have hpow : 2 ≤ 2 ^ (a + 1) := by
      have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    set X := 2 ^ (a + 1)
    have hX : 2 ≤ X := hpow
    set F := full_finish_count es (3 * (2 ^ (e + 1) - 1))
    have h1 : (F + 1) * X + X = (F + 2) * X := by ring
    have h2 : 2 ≤ (F + 1) * X := Nat.le_mul_of_pos_left X (by omega) |>.trans' hX
    omega

theorem trigger_finish_sufficient (es : List ℕ) :
    nested_required es 23 ≤ trigger_finish es := by
  rw [nested_required_finish]
  exact full_finish_monotone es _ _ (by decide)

theorem full_finish_less_than_decode (cs : List BinaryColumn) (out small : ℕ) (h : small < out) :
    full_finish_count (cs.map BinaryColumn.column_e) small < columns_input_count cs out := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    rw [List.map_cons]
    dsimp only [full_finish_count, columns_input_count]
    unfold column_required
    have hpow : 2 ≤ 2 ^ (c.column_e + 1) := by
      have : 1 ≤ 2 ^ c.column_e := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    set X := 2 ^ (c.column_e + 1)
    have hX : 2 ≤ X := hpow
    set F := full_finish_count (cs.map BinaryColumn.column_e) small
    set C := columns_input_count cs out
    have hle : (F + 2) * X ≤ (C + 1) * X := Nat.mul_le_mul_right X (by omega)
    have hge : 4 ≤ (F + 2) * X := by nlinarith
    omega

theorem safe_tail_steps (b : Bool) (cs : List BinaryColumn) (hsafe : ∀ c ∈ cs, column_safe c) :
    ∃ cs', tail_columns_step b cs cs' := by
  induction cs with
  | nil => exact ⟨[], trivial⟩
  | cons c cs ih =>
    obtain ⟨cs', hrest⟩ := ih (fun x hx => hsafe x (List.mem_cons_of_mem c hx))
    obtain ⟨c', hc'⟩ := column_step_exists (next_column_odd b cs) c
      (column_safe_lower c (hsafe c (List.Mem.head _)))
    exact ⟨c' :: cs', ⟨hc', hrest⟩⟩

theorem tail_steps_es (b : Bool) (cs cs' : List BinaryColumn) (hstep : tail_columns_step b cs cs') :
    cs'.map BinaryColumn.column_e = cs.map BinaryColumn.column_e := by
  induction cs generalizing cs' with
  | nil =>
    rcases cs' with _ | _
    · rfl
    · cases hstep
  | cons c cs ih =>
    rcases cs' with _ | ⟨c', cs'⟩
    · cases hstep
    · rcases hstep with ⟨⟨he, _⟩, hrest⟩
      simp only [List.map_cons, he, ih cs' hrest]

theorem final_last_budget_gap : 134217725 < decode_budget (phase_R 4) := by
  decide

theorem final_decode_budget_gap (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (lv : ℕ)
    (hpre : finite_round_pre current previous zs last 4 lv) :
    trigger_finish (frontier_es current previous zs) < finite_decode_count current previous zs 4 :=
        by
  obtain ⟨zs', hstep⟩ := safe_tail_steps (decide (phase_R 4 % 2 = 1)) zs
    (finite_pre_safe current previous zs last 4 lv hpre)
  have hgap := full_finish_less_than_decode (round_outer_column current previous :: zs')
    (decode_budget (phase_R 4)) 134217725 final_last_budget_gap
  dsimp only [columns_input_count] at hgap
  rw [columns_decode_budget zs zs' (phase_R 4) (phase_R_large 4) hstep,
      List.map_cons, tail_steps_es _ zs zs' hstep] at hgap
  exact hgap

theorem final_decode_input_raw (current previous : ℕ) (zs : List BinaryColumn) :
    finite_decode_input current previous zs 4 =
      mixed_tail (frontier_es current previous zs) 25 4 := by
  unfold finite_decode_input frontier_es
  exact (mixed_tail_chain (round_outer_column current previous :: zs) 25 4).symm

theorem finite_trigger_proved (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (lv : ℕ)
    (hpre : finite_round_pre current previous zs last 4 lv) :
    ∃ c f es e,
      ((post_ca_tail (round_post_unary current previous)
        (round_primary_width current previous) zs last 4 lv) [source_tm]⊢⁺
        ((exception_call_left c f) {{B}}> (full_tail es (e + 1) 5 +> default))) ∧
      nested_required es e ≤ f := by
  have hgap := final_decode_budget_gap current previous zs last lv hpre
  set es := frontier_es current previous zs
  set f := trigger_finish es
  set n := finite_decode_count current previous zs 4
  refine ⟨n - (f + 1), f, es, 23, ?_, trigger_finish_sufficient es⟩
  refine stepPlus_trans (finite_raw_to_pre current previous zs last 4 lv hpre) ?_
  rw [final_decode_input_raw]
  have hrun := exception_launch_partial_side f (n - (f + 1)) _ _ (raw_four_to_frontier es)
  rw [show f + (n - (f + 1)) + 1 = n by omega] at hrun
  exact hrun

theorem finite_entry_to_cycler (current previous : ℕ) (zs : List BinaryColumn) (last : List SDigit)
    (lv : ℕ)
    (hpre : finite_round_pre current previous zs last 1 lv) :
    ∃ L₀ : ListBlank (Fin 2),
      ((post_ca_tail (round_post_unary current previous)
        (round_primary_width current previous) zs last 1 lv) [source_tm]⊢⁺
        ((Yw.reverse +> L₀) {{B}}> default)) := by
  obtain ⟨zs1, last1, lv1, h1, p1⟩ :=
      finite_round_proved current previous zs last 1 lv hpre (by decide)
  obtain ⟨zs2, last2, lv2, h2, p2⟩ := finite_round_proved _ _ _ last1 2 lv1 p1 (by decide)
  obtain ⟨zs3, last3, lv3, h3, p3⟩ := finite_round_proved _ _ _ last2 3 lv2 p2 (by decide)
  obtain ⟨c, f, es, e, h4, hbound⟩ := finite_trigger_proved _ _ _ last3 lv3 p3
  obtain ⟨L₀, h5⟩ := nested_exit_to_cycler c f es e hbound
  exact ⟨L₀, stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 (stepPlus_trans h4 h5)))⟩

theorem fifth_done_to_cycler_generic (n4 n5 : ℕ)
    (hn4 : ∃ q, n4 = 2 * q ∧ 6 ≤ 2 * q)
    (hn5 : ∃ q, n5 = 2 * q ∧ 6 ≤ 2 * q)
    (hge64 : 64 ≤ n4)
    (hgrow : 2 * (n4 + 30) + 4 ≤ n5 + 1) :
    ∃ L₀ : ListBlank (Fin 2),
      ((exception_done n5
        (A8 ^ (n4 - 2) ++ sdigits_word opening_digits ++ U ^ 3 ++ A8 ++ [1, 1]))
        [source_tm]⊢⁺ ((Yw.reverse +> L₀) {{B}}> default)) := by
  have hentry := opening_exception_to_entry_generic n4 n5 hn4 hn5
  have hpre := entry_pre_generic n4 n5 hn4 hn5 hge64 hgrow
  obtain ⟨L₀, hcycler⟩ := finite_entry_to_cycler ((n5 - 6) / 2) ((n4 - 6) / 2) [] entry_last 4 hpre
  exact ⟨L₀, stepPlus_trans hentry hcycler⟩

theorem blank_D_to_cycler :
    ∃ L₀ : ListBlank (Fin 2),
      ((default {{D}}> default) [source_tm]⊢* ((Yw.reverse +> L₀) {{B}}> default)) := by
  obtain ⟨⟨q4, hq4⟩, hge64⟩ := opening_n4_even_large
  have hn4 : ∃ q, opening_n4 = 2 * q ∧ 6 ≤ 2 * q := ⟨q4, hq4, by omega⟩
  have hn5 : ∃ q, opening_decode_calls (opening_n4 - 2) = 2 * q ∧ 6 ≤ 2 * q :=
    opening_decode_even_ge6 (opening_n4 - 2) (by omega)
  have hgrow : 2 * (opening_n4 + 30) + 4 ≤ opening_decode_calls (opening_n4 - 2) + 1 :=
    opening_entry_growth opening_n4 hge64
  obtain ⟨L₀, hcycler⟩ := fifth_done_to_cycler_generic
    opening_n4 (opening_decode_calls (opening_n4 - 2)) hn4 hn5 hge64 hgrow
  exact ⟨L₀, stepStar_trans opening_D_to_fifth_done (stepPlus_to_stepStar hcycler)⟩

theorem sobc_D_nonhalt : NeverHaltsFrom source_tm (default {{D}}> default) := by
  obtain ⟨L₀, hreach⟩ := blank_D_to_cycler
  exact neverHaltsFrom_of_reachesStar hreach (cycler_nonhalt L₀)

end

public section

theorem is_not_halt : IsNotHalt target :=
  neverHaltsFrom_of_mapFlipCfg_12 sobc_D_nonhalt

end

end BusyBeaver.M_1RB0LE_1RCHHH_0RD0RB_1RE0LA_1RF0LF_1LD1RF

