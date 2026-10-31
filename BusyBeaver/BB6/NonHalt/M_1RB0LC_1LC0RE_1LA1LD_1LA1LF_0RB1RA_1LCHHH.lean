/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open BusyBeaver.Longitudinal
open BusyBeaver.Longitudinal.BoundedConfig (toCfg all0_spec steps_spec steps1_spec_true
  segRLs_c_spec sideRLs_c_spec)

abbrev tm : Machine (Fin 2) (Fin 6) := flipTM target_tm

inductive Digit where
  | U
  | Z
  | O
deriving DecidableEq

open Digit

def word : Digit → List (Fin 2)
  | U => [1, 1, 0]
  | Z => [0, 0]
  | O => [1, 0]

def tape : List Digit → ListBlank (Fin 2)
  | [] => default
  | d :: r => word d +> tape r

def potential : List Digit → ℕ
  | [] => 0
  | U :: r => max 2 (potential r - 2)
  | Z :: r => potential r * 2
  | O :: r => 1 + potential r * 2

def prepend (k : ℕ) (r : List Digit) : List Digit :=
  List.replicate k U ++ r

abbrev hR : DH0 (Fin 2) (Fin 6) := (A, [1])
abbrev hL : DH0 (Fin 2) (Fin 6) := (E, [0])
abbrev h : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [(hR, hL)]

def left1 (a b : ℕ) : ListBlank (Fin 2) :=
  ([1, 0, 1] ^ b) +> (([1, 1, 1] ^ a) +> ([1] +> default))

def left2 (a b : ℕ) : ListBlank (Fin 2) :=
  ([1, 0, 1] ^ b) +> (([1, 1, 1] ^ a) +> ([1, 1] +> default))

def stateCfg (n : ℕ) (r : List Digit) : Cfg (Fin 2) (Fin 6) :=
  toDHCfg (hL, .left) (left1 0 n) (tape r)

lemma tape_prepend (k : ℕ) (r : List Digit) :
    tape (prepend k r) = (word U) ^ k +> tape r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change word U +> tape (prepend k r) = (word U ++ (word U) ^ k) +> tape r
    rw [ih, append_assoc]

lemma potential_prepend (k : ℕ) (r : List Digit) :
    potential (prepend (1 + k) r) = max 2 (potential r - (1 + k) * 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_step : prepend (1 + (k + 1)) r = U :: prepend (1 + k) r := by
      unfold prepend
      have hk : 1 + (k + 1) = (1 + k) + 1 := by omega
      rw [hk, List.replicate_succ, List.cons_append]
    rw [h_step]
    change max 2 (potential (prepend (1 + k) r) - 2) = max 2 (potential r - (1 + (k + 1)) * 2)
    rw [ih]
    omega

lemma potential_bound (k : ℕ) (r : List Digit) :
    potential r ≤ potential (prepend k r) + k * 2 := by
  rcases k with _ | k
  · simp [prepend]
  · have hk : k + 1 = 1 + k := by omega
    rw [hk, potential_prepend]
    omega

lemma prepend_U (k : ℕ) (r : List Digit) :
    prepend k (U :: r) = prepend (1 + k) r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : prepend (k + 1) (U :: r) = U :: prepend k (U :: r) := by
      unfold prepend; rw [List.replicate_succ, List.cons_append]
    have h2 : prepend (1 + (k + 1)) r = U :: prepend (1 + k) r := by
      unfold prepend
      have hk : 1 + (k + 1) = (1 + k) + 1 := by omega
      rw [hk, List.replicate_succ, List.cons_append]
    rw [h1, h2, ih]

inductive Inc : List Digit → List Digit → Prop where
  | nil : Inc [] [O]
  | Z (r : List Digit) : Inc (Z :: r) (O :: r)
  | O {r r' : List Digit} : Inc r r' → Inc (O :: r) (Z :: r')
  | U {r r' : List Digit} : Inc r r' → Inc (U :: r) (U :: r')

lemma Inc_total (r : List Digit) :
    ∃ r', Inc r r' ∧ potential r' ≤ 1 + potential r ∧ O ∈ r' := by
  induction r with
  | nil =>
    exact ⟨[O], .nil, by simp [potential], List.Mem.head _⟩
  | cons d r ih =>
    obtain ⟨r', h_inc, h_pot, h_mem⟩ := ih
    cases d with
    | U =>
      refine ⟨U :: r', .U h_inc, ?_, List.Mem.tail _ h_mem⟩
      simp only [potential]; omega
    | Z =>
      refine ⟨O :: r, .Z r, ?_, List.Mem.head _⟩
      simp only [potential]; omega
    | O =>
      refine ⟨Z :: r', .O h_inc, ?_, List.Mem.tail _ h_mem⟩
      simp only [potential]; omega

-- Elementary 2D tiles & multi-step transitions for `tm = flipTM target_tm`

lemma rule_U : SegRLs tm h h (word U) (word U) :=
  segRLs_c_spec tm (T := 100) (by decide)

lemma rule_Z : SegRLs tm h [] (word Z) (word O) :=
  segRLs_c_spec tm (T := 100) (by decide)

lemma rule_O : SegRLs tm h h (word O) (word Z) :=
  segRLs_c_spec tm (T := 100) (by decide)

lemma rule_nil : SideRLs tm h default (word O +> default) :=
  sideRLs_c_spec tm (hs := h) (r := []) (r' := word O) (T := 100) (by decide)

lemma rule_shortO : SegRLs tm h [] ([0] ++ word O) (word U) :=
  segRLs_c_spec tm (T := 100) (by decide)

lemma one_comm_111_pow (k : ℕ) (L : ListBlank (Fin 2)) :
    (1 : Fin 2) >> ([1, 1, 1] ^ k +> L) = [1, 1, 1] ^ k +> ((1 : Fin 2) >> L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, append_assoc]
    dsimp [append_cons]
    rw [ih]

lemma step_L_101 (L r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) ([1, 0, 1] +> L) r) [tm]⊢*
      (toDHCfg (hL, .left) L ([1, 1, 0] +> r)) := by
  have hs := steps_spec tm 10 ⟨[0], [1, 0, 1], E, .left⟩
    (x' := ⟨[0, 1, 1, 0], [], E, .left⟩) (by decide) L r
  simpa [toCfg, toDHCfg, append_nil, append_cons] using hs

lemma steps_L_101 (b : ℕ) (L r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) ([1, 0, 1] ^ b +> L) r) [tm]⊢*
      (toDHCfg (hL, .left) L ([1, 1, 0] ^ b +> r)) := by
  induction b generalizing r with
  | zero => exact stepStar_refl tm _
  | succ b ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (step_L_101 ([1, 0, 1] ^ b +> L) r) ?_
    have h_ih := ih ([1, 1, 0] +> r)
    rw [← append_assoc, ← pow_succ_list'] at h_ih
    exact h_ih

lemma step_R_A_110 (L r : ListBlank (Fin 2)) :
    (toDHCfg (hR, .right) L ([1, 1, 0] +> r)) [tm]⊢*
      (toDHCfg (hR, .right) ([1, 0, 1] +> L) r) := by
  have hs := steps_spec tm 10 ⟨[1], [1, 1, 0], A, .right⟩
    (x' := ⟨[1, 1, 0, 1], [], A, .right⟩) (by decide) L r
  simpa [toCfg, toDHCfg, append_nil, append_cons] using hs

lemma steps_R_A_110 (b : ℕ) (L r : ListBlank (Fin 2)) :
    (toDHCfg (hR, .right) L ([1, 1, 0] ^ b +> r)) [tm]⊢*
      (toDHCfg (hR, .right) ([1, 0, 1] ^ b +> L) r) := by
  induction b generalizing L with
  | zero => exact stepStar_refl tm _
  | succ b ih =>
    rw [pow_succ_list [1, 1, 0] b, append_assoc]
    refine stepStar_trans (step_R_A_110 L ([1, 1, 0] ^ b +> r)) ?_
    have h_ih := ih ([1, 0, 1] +> L)
    rw [← append_assoc, ← pow_succ_list' [1, 0, 1] b] at h_ih
    exact h_ih

lemma step_R_C_110 (L r : ListBlank (Fin 2)) :
    (L {{C}}> ([1, 1, 0] +> r)) [tm]⊢* (([1, 1, 1] +> L) {{C}}> r) := by
  have hs := steps_spec tm 10 ⟨[], [1, 1, 0], C, .right⟩
    (x' := ⟨[1, 1, 1], [], C, .right⟩) (by decide) L r
  simpa [toCfg, append_nil, append_cons] using hs

lemma steps_R_C_110 (k : ℕ) (L r : ListBlank (Fin 2)) :
    (L {{C}}> ([1, 1, 0] ^ k +> r)) [tm]⊢* (([1, 1, 1] ^ k +> L) {{C}}> r) := by
  induction k generalizing L with
  | zero => exact stepStar_refl tm _
  | succ k ih =>
    rw [pow_succ_list [1, 1, 0] k, append_assoc]
    refine stepStar_trans (step_R_C_110 L ([1, 1, 0] ^ k +> r)) ?_
    have h_ih := ih ([1, 1, 1] +> L)
    rw [← append_assoc, ← pow_succ_list' [1, 1, 1] k] at h_ih
    exact h_ih

lemma step_L_111_turn (L r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) ([1, 1, 1] +> L) r) [tm]⊢*
      (toDHCfg (hR, .right) ([1, 0, 1] +> L) r) := by
  have hs := steps_spec tm 10 ⟨[0], [1, 1, 1], E, .left⟩
    (x' := ⟨[1, 1, 0, 1], [], A, .right⟩) (by decide) L r
  simpa [toCfg, toDHCfg, append_nil, append_cons] using hs

lemma segLR_step (a b : ℕ) (s : List (Fin 2)) :
    SegLR tm hL hR
      ([1, 0, 1] ^ b ++ [1, 1, 1] ^ (1 + a) ++ s)
      ([1, 0, 1] ^ (1 + b) ++ [1, 1, 1] ^ a ++ s) := by
  intro l r
  have ha : 1 + a = a + 1 := by omega
  have hb : 1 + b = b + 1 := by omega
  rw [ha, hb, pow_succ_list [1, 1, 1] a, pow_succ_list' [1, 0, 1] b]
  simp only [List.append_assoc, append_assoc]
  refine stepStar_trans (steps_L_101 b ([1, 1, 1] +> ([1, 1, 1] ^ a +> (s +> l))) r) ?_
  refine stepStar_trans
    (step_L_111_turn ([1, 1, 1] ^ a +> (s +> l)) ([1, 1, 0] ^ b +> r)) ?_
  exact steps_R_A_110 b ([1, 0, 1] +> ([1, 1, 1] ^ a +> (s +> l))) r

lemma emissions (a b : ℕ) (s : List (Fin 2)) :
    SegLRs tm ([(hL, hR)] ^ a)
      ([1, 0, 1] ^ b ++ [1, 1, 1] ^ a ++ s)
      ([1, 0, 1] ^ (a + b) ++ s) := by
  induction a generalizing b with
  | zero =>
    rw [Nat.zero_add, pow_zero_list, pow_zero_list, List.append_nil]
    exact .nil _
  | succ a ih =>
    have h_add : (a + 1) + b = a + (1 + b) := by omega
    have ha : a + 1 = 1 + a := by omega
    rw [pow_succ_list [(hL, hR)] a, h_add, ha]
    exact .cons (segLR_step a b s) (ih (1 + b))

lemma bounce (k : ℕ) (w1 w2 w3 w4 : List (Fin 2))
    (h_rr : SegRR tm hR hR w1 w3)
    (h_lr : SegLRs tm ([(hL, hR)] ^ k) w3 w4)
    (h_ll : SegLL tm hL hL w4 w2) :
    SegRLs tm h (h ^ (1 + k)) w1 w2 := by
  have hk : 1 + k = k + 1 := by omega
  rw [hk, ← lrcons_same hR hL k, ← List.append_nil (lrcons hR ([(hL, hR)] ^ k) hL)]
  exact SegRLs.lrcons h_rr h_ll h_lr (.nil w2)

lemma segRL_0_to_1 (s : List (Fin 2)) :
    SegRL tm hR hL ([0] ++ s) ([1] ++ s) := by
  intro l r
  have hs := steps1_spec_true tm 10 ⟨[1], [0], A, .right⟩
    (x' := ⟨[0, 1], [], E, .left⟩) (by decide) l (s +> r)
  simpa [toCfg, toDHCfg, append_nil, append_cons] using hs

lemma segRR_shiftZ (k : ℕ) :
    SegRR tm hR hR ([1] ++ (word U) ^ k ++ [0]) ([1, 1, 1] ^ k ++ [0, 1]) := by
  intro l r
  simp only [word, List.append_assoc, append_assoc]
  have h1 := steps_spec tm 10 ⟨[1], [1], A, .right⟩
    (x' := ⟨[0, 1], [], C, .right⟩) (by decide) l ([1, 1, 0] ^ k +> ([0] +> r))
  have h2 := steps_R_C_110 k ([0, 1] +> l) ([0] +> r)
  have h3 := steps_spec tm 10 ⟨[], [0], C, .right⟩
    (x' := ⟨[1], [], A, .right⟩) (by decide) ([1, 1, 1] ^ k +> ([0, 1] +> l)) r
  simp only [toCfg, toDHCfg, append_nil, append_cons] at h1 h2 h3 ⊢
  exact stepStar_trans h1 (stepStar_trans h2 h3)

lemma segLL_shiftZ (k : ℕ) :
    SegLL tm hL hL ([1, 0, 1] ^ k ++ [0, 1]) (word Z ++ (word U) ^ k) := by
  intro l r
  simp only [word, append_assoc]
  refine stepStar_trans (steps_L_101 k ([0, 1] +> l) r) ?_
  have hs := steps_spec tm 10 ⟨[0], [0, 1], E, .left⟩
    (x' := ⟨[0, 0, 0], [], E, .left⟩) (by decide) l ([1, 1, 0] ^ k +> r)
  simpa [toCfg, toDHCfg, append_nil, append_cons] using hs

lemma rule_shiftZ (k : ℕ) :
    SegRLs tm (h ^ 2) (h ^ (1 + k)) ([0] ++ (word U) ^ k ++ [0]) (word Z ++ (word U) ^ k) := by
  change SegRLs tm ((hR, hL) :: h) (h ^ (1 + k))
    ([0] ++ ((word U) ^ k ++ [0])) (word Z ++ (word U) ^ k)
  refine .cons (segRL_0_to_1 ((word U) ^ k ++ [0])) ?_
  refine bounce k ([1] ++ (word U) ^ k ++ [0]) (word Z ++ (word U) ^ k)
    ([1, 1, 1] ^ k ++ [0, 1]) ([1, 0, 1] ^ k ++ [0, 1])
    (segRR_shiftZ k) ?_ (segLL_shiftZ k)
  exact emissions k 0 [0, 1]

lemma segRR_shiftO (k : ℕ) :
    SegRR tm hR hR ([1] ++ (word U) ^ k ++ word O) ([1, 1, 1] ^ k ++ [1, 0, 1]) := by
  intro l r
  simp only [word, List.append_assoc, append_assoc]
  have h1 := steps_spec tm 10 ⟨[1], [1], A, .right⟩
    (x' := ⟨[0, 1], [], C, .right⟩) (by decide) l ([1, 1, 0] ^ k +> ([1, 0] +> r))
  have h2 := steps_R_C_110 k ([0, 1] +> l) ([1, 0] +> r)
  have h3 := steps_spec tm 10 ⟨[], [1, 0], C, .right⟩
    (x' := ⟨[1, 1], [], A, .right⟩) (by decide) ([1, 1, 1] ^ k +> ([0, 1] +> l)) r
  simp only [toCfg, toDHCfg, append_nil, append_cons] at h1 h2 h3 ⊢
  rw [one_comm_111_pow k (0 >> 1 >> l)] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

lemma segLL_shiftO (k : ℕ) :
    SegLL tm hL hL ([1, 0, 1] ^ k ++ [1, 0, 1]) ((word U) ^ (1 + k)) := by
  intro l r
  have hk : 1 + k = k + 1 := by omega
  rw [hk, ← pow_succ_list' [1, 0, 1] k]
  simpa [word] using steps_L_101 (k + 1) l r

lemma rule_shiftO (k : ℕ) :
    SegRLs tm (h ^ 2) (h ^ (1 + k)) ([0] ++ (word U) ^ k ++ word O) ((word U) ^ (1 + k)) := by
  change SegRLs tm ((hR, hL) :: h) (h ^ (1 + k))
    ([0] ++ ((word U) ^ k ++ word O)) ((word U) ^ (1 + k))
  refine .cons (segRL_0_to_1 ((word U) ^ k ++ word O)) ?_
  refine bounce k ([1] ++ (word U) ^ k ++ word O) ((word U) ^ (1 + k))
    ([1, 1, 1] ^ k ++ [1, 0, 1]) ([1, 0, 1] ^ k ++ [1, 0, 1])
    (segRR_shiftO k) ?_ (segLL_shiftO k)
  exact emissions k 0 [1, 0, 1]

lemma rule_L1 (a b : ℕ) (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) (left1 (1 + a) b) r) [tm]⊢*
      (toDHCfg (hR, .right) (left1 a (1 + b)) r) := by
  have hs := segLR_step a b [1] default r
  simpa [left1, append_assoc] using hs

lemma rule_L2 (a b : ℕ) (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) (left2 (1 + a) b) r) [tm]⊢*
      (toDHCfg (hR, .right) (left2 a (1 + b)) r) := by
  have hs := segLR_step a b [1, 1] default r
  simpa [left2, append_assoc] using hs

lemma zero_cons_default : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default :=
  all0_spec (a := [0]) (by decide)

lemma rule_L20 (b : ℕ) (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) (left2 0 b) r) [tm]⊢*
      (toDHCfg (hR, .right) (left1 0 b) r) := by
  unfold left2 left1
  refine stepStar_trans (steps_L_101 b ([1, 1] +> default) r) ?_
  have h_turn : (toDHCfg (hL, .left) ([1, 1] +> default) ([1, 1, 0] ^ b +> r)) [tm]⊢*
      (toDHCfg (hR, .right) ([1] +> default) ([1, 1, 0] ^ b +> r)) := by
    have hs := steps_spec tm 10 ⟨[0], [1, 1, 0], E, .left⟩
      (x' := ⟨[1, 1, 0, 0], [], A, .right⟩) (by decide) default ([1, 1, 0] ^ b +> r)
    simpa [toCfg, toDHCfg, append_cons, append_nil, zero_cons_default] using hs
  exact stepStar_trans h_turn (steps_R_A_110 b ([1] +> default) r)

lemma step_L1_turn_C (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) ([1] +> default) r) [tm]⊢*
      (([1] +> default) {{C}}> ([1, 1, 0] +> r)) := by
  have hs1 : (toDHCfg (hL, .left) ([1] +> default) r) [tm]⊢*
      (default <{{B}} ([1, 1, 0] +> r)) := by
    have hs := steps_spec tm 10 ⟨[0], [1, 0], E, .left⟩
      (x' := ⟨[1, 1, 0], [], B, .left⟩) (by decide) default r
    simpa [toCfg, toDHCfg, append_cons, append_nil, zero_cons_default] using hs
  have hs2 : (default <{{B}} ([1, 1, 0] +> r)) [tm]⊢*
      (([1] +> default) {{C}}> ([1, 1, 0] +> r)) := by
    have hs := steps_spec tm 10 ⟨[], [0], B, .left⟩
      (x' := ⟨[1], [], C, .right⟩) (by decide) default ([1, 1, 0] +> r)
    simpa [toCfg, toDHCfg, append_cons, append_nil, zero_cons_default] using hs
  exact stepStar_trans hs1 hs2

lemma merge_110 (b k : ℕ) (s : ListBlank (Fin 2)) :
    [1, 1, 0] +> ([1, 1, 0] ^ b +> ([1, 1, 0] ^ k +> s)) =
      ([1, 1, 0] ^ (1 + k + b)) +> s := by
  have hk : 1 + k + b = (b + 1) + k := by omega
  rw [hk, pow_add_list, pow_succ_list, append_assoc, append_assoc]

lemma rule_LZ (b k : ℕ) (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) (left1 0 b) ((word U) ^ k +> (word Z +> r))) [tm]⊢*
      (toDHCfg (hR, .right) (left1 (1 + k + b) 0) ([0] +> r)) := by
  unfold left1
  dsimp [word]
  refine stepStar_trans (steps_L_101 b ([1] +> default) ([1, 1, 0] ^ k +> ([0, 0] +> r))) ?_
  refine stepStar_trans (step_L1_turn_C ([1, 1, 0] ^ b +> ([1, 1, 0] ^ k +> ([0, 0] +> r)))) ?_
  rw [merge_110 b k ([0, 0] +> r)]
  refine stepStar_trans (steps_R_C_110 (1 + k + b) ([1] +> default) ([0, 0] +> r)) ?_
  have h_end := steps_spec tm 10 ⟨[], [0], C, .right⟩
    (x' := ⟨[1], [], A, .right⟩) (by decide)
    ([1, 1, 1] ^ (1 + k + b) +> ([1] +> default)) ([0] +> r)
  simpa [toCfg, toDHCfg, append_cons, append_nil] using h_end

lemma rule_LO (b k : ℕ) (r : ListBlank (Fin 2)) :
    (toDHCfg (hL, .left) (left1 0 b) ((word U) ^ k +> (word O +> r))) [tm]⊢*
      (toDHCfg (hR, .right) (left2 (1 + k + b) 0) r) := by
  unfold left1 left2
  dsimp [word]
  refine stepStar_trans (steps_L_101 b ([1] +> default) ([1, 1, 0] ^ k +> ([1, 0] +> r))) ?_
  refine stepStar_trans (step_L1_turn_C ([1, 1, 0] ^ b +> ([1, 1, 0] ^ k +> ([1, 0] +> r)))) ?_
  rw [merge_110 b k ([1, 0] +> r)]
  refine stepStar_trans (steps_R_C_110 (1 + k + b) ([1] +> default) ([1, 0] +> r)) ?_
  have h_end := steps_spec tm 10 ⟨[], [1, 0], C, .right⟩
    (x' := ⟨[1, 1], [], A, .right⟩) (by decide)
    ([1, 1, 1] ^ (1 + k + b) +> ([1] +> default)) r
  simp only [toCfg, toDHCfg, append_cons, append_nil] at h_end ⊢
  rw [one_comm_111_pow (1 + k + b) (1 >> default)] at h_end
  exact h_end

-- High-level `Long13` normalization and invariant closure

lemma Inc_spec {r r' : List Digit} (h_inc : Inc r r') :
    SideRLs tm h (tape r) (tape r') := by
  induction h_inc with
  | nil => exact rule_nil
  | Z r => exact rule_Z.sideRLs_concat (.nil (tape r))
  | O _ ih => exact rule_O.sideRLs_concat ih
  | U _ ih => exact rule_U.sideRLs_concat ih

lemma incs_total (m : ℕ) (r : List Digit) :
    ∃ r', SideRLs tm (h ^ m) (tape r) (tape r') ∧
      potential r' ≤ m + potential r ∧ (0 < m → O ∈ r') := by
  induction m with
  | zero =>
    exact ⟨r, .nil (tape r), by omega, by omega⟩
  | succ m ih =>
    obtain ⟨r', h_side, h_pot, _⟩ := ih
    obtain ⟨r'', h_inc, h_pot', h_mem⟩ := Inc_total r'
    refine ⟨r'', h_side.trans_succ (Inc_spec h_inc), by omega, fun _ => h_mem⟩

lemma U_pass (n k : ℕ) :
    SegRLs tm (h ^ n) (h ^ n) ((word U) ^ k) ((word U) ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm (h ^ n)
  | succ k ih =>
    rw [pow_succ_list (word U) k]
    exact (rule_U.wall_pow n).concat ih

lemma Z_even (n : ℕ) :
    SegRLs tm (h ^ (n * 2)) (h ^ n) (word Z) (word Z) := by
  induction n with
  | zero => exact .nil (word Z)
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq, pow_add_list, pow_succ_list h n]
    have h_step : SegRLs tm (h ^ 2) h (word Z) (word Z) := by
      simpa using rule_Z.trans rule_O
    exact h_step.trans ih

lemma Z_odd (n : ℕ) :
    SegRLs tm (h ^ (1 + n * 2)) (h ^ n) (word Z) (word O) := by
  have h_eq : 1 + n * 2 = n * 2 + 1 := by omega
  rw [h_eq, pow_add_list, ← List.append_nil (h ^ n)]
  exact (Z_even n).trans rule_Z

lemma shiftZ_even (k n : ℕ) :
    SegRLs tm (h ^ (2 + n * 2)) (h ^ (1 + k + n))
      ([0] ++ (word U) ^ k ++ [0]) (word Z ++ (word U) ^ k) :=
  (rule_shiftZ k).trans_add ((Z_even n).concat (U_pass n k))

lemma shiftZ_odd (k n : ℕ) :
    SegRLs tm (h ^ (3 + n * 2)) (h ^ (1 + k + n))
      ([0] ++ (word U) ^ k ++ [0]) (word O ++ (word U) ^ k) := by
  have h_eq : 3 + n * 2 = 2 + (1 + n * 2) := by omega
  rw [h_eq]
  exact (rule_shiftZ k).trans_add ((Z_odd n).concat (U_pass n k))

lemma shiftO (k n : ℕ) :
    SegRLs tm (h ^ (2 + n)) (h ^ (1 + k + n))
      ([0] ++ (word U) ^ k ++ word O) ((word U) ^ (1 + k)) :=
  (rule_shiftO k).trans_add (U_pass n (1 + k))

def Normalized (r : List Digit) (m : ℕ) : Prop :=
  ∃ r', SideRLs tm (h ^ m) ([0] +> tape r) (tape r') ∧ potential r' ≤ m + potential r

lemma normalize_empty (m : ℕ) : Normalized [] m := by
  obtain ⟨r', h_side, h_pot, _⟩ := incs_total m []
  refine ⟨r', ?_, h_pot⟩
  have h0 : ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
    all0_spec (a := [0]) (by decide)
  change SideRLs tm (h ^ m) ([0] +> default) (tape r')
  rwa [h0]

lemma normalize_Z (r : List Digit)
    (ih : ∀ m, potential r ≤ m → Normalized r m)
    (k m : ℕ) (h_bound : potential (prepend k (Z :: r)) ≤ m) :
    Normalized (prepend k (Z :: r)) m := by
  rcases k with _ | k
  · dsimp [prepend, potential] at h_bound
    have hm : m = (m / 2) * 2 + m % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
    · obtain ⟨r', h_side, h_pot⟩ := ih (m / 2) (by omega)
      refine ⟨Z :: r', ?_, ?_⟩
      · have h_eq : m = (m / 2) * 2 := by omega
        rw [h_eq]
        change SideRLs tm (h ^ ((m / 2) * 2)) (word Z +> ([0] +> tape r)) (word Z +> tape r')
        exact (Z_even (m / 2)).sideRLs_concat h_side
      · dsimp [prepend, potential]; omega
    · obtain ⟨r', h_side, h_pot⟩ := ih (m / 2) (by omega)
      refine ⟨O :: r', ?_, ?_⟩
      · have h_eq : m = 1 + (m / 2) * 2 := by omega
        rw [h_eq]
        change SideRLs tm (h ^ (1 + (m / 2) * 2)) (word Z +> ([0] +> tape r)) (word O +> tape r')
        exact (Z_odd (m / 2)).sideRLs_concat h_side
      · dsimp [prepend, potential]; omega
  · have hk : k + 1 = 1 + k := by omega
    rw [hk] at h_bound ⊢
    rw [potential_prepend] at h_bound
    have hm2 : 2 ≤ m := by omega
    set p := m - 2
    have hmp : m = 2 + p := by omega
    set q := p / 2
    rcases Nat.mod_two_eq_zero_or_one p with hp0 | hp1
    · obtain ⟨r', h_side, h_pot⟩ := ih (1 + (1 + k) + q) (by dsimp [potential] at h_bound; omega)
      refine ⟨Z :: prepend (1 + k) r', ?_, ?_⟩
      · have h_m_eq : m = 2 + q * 2 := by omega
        rw [h_m_eq, tape_prepend]
        change SideRLs tm (h ^ (2 + q * 2))
          ([0] +> ((word U) ^ (1 + k) +> (word Z +> tape r)))
          (word Z +> tape (prepend (1 + k) r'))
        rw [tape_prepend]
        have h_seg := (shiftZ_even (1 + k) q).sideRLs_concat h_side
        have h_lhs : ([0] ++ (word U) ^ (1 + k) ++ [0]) +> ([0] +> tape r) =
            [0] +> ((word U) ^ (1 + k) +> (word Z +> tape r)) := by
          simp only [word, List.append_assoc, append_assoc, append_cons, append_nil]
        have h_rhs : (word Z ++ (word U) ^ (1 + k)) +> tape r' =
            word Z +> ((word U) ^ (1 + k) +> tape r') := by
          rw [append_assoc]
        rwa [h_lhs, h_rhs] at h_seg
      · dsimp [potential] at h_bound ⊢
        rw [potential_prepend, potential_prepend]
        dsimp [potential]
        omega
    · obtain ⟨r', h_side, h_pot⟩ := ih (1 + (1 + k) + q) (by dsimp [potential] at h_bound; omega)
      refine ⟨O :: prepend (1 + k) r', ?_, ?_⟩
      · have h_m_eq : m = 3 + q * 2 := by omega
        rw [h_m_eq, tape_prepend]
        change SideRLs tm (h ^ (3 + q * 2))
          ([0] +> ((word U) ^ (1 + k) +> (word Z +> tape r)))
          (word O +> tape (prepend (1 + k) r'))
        rw [tape_prepend]
        have h_seg := (shiftZ_odd (1 + k) q).sideRLs_concat h_side
        have h_lhs : ([0] ++ (word U) ^ (1 + k) ++ [0]) +> ([0] +> tape r) =
            [0] +> ((word U) ^ (1 + k) +> (word Z +> tape r)) := by
          simp only [word, List.append_assoc, append_assoc, append_cons, append_nil]
        have h_rhs : (word O ++ (word U) ^ (1 + k)) +> tape r' =
            word O +> ((word U) ^ (1 + k) +> tape r') := by
          rw [append_assoc]
        rwa [h_lhs, h_rhs] at h_seg
      · dsimp [potential] at h_bound ⊢
        rw [potential_prepend, potential_prepend]
        dsimp [potential]
        omega

lemma normalize_O (r : List Digit) (k m : ℕ)
    (h_bound : potential (prepend k (O :: r)) ≤ m) :
    Normalized (prepend k (O :: r)) m := by
  rcases k with _ | k
  · dsimp [prepend, potential] at h_bound
    rcases m with _ | m
    · omega
    · obtain ⟨r', h_side, h_pot, _⟩ := incs_total m r
      refine ⟨U :: r', ?_, ?_⟩
      · have hm : m + 1 = 1 + m := by omega
        rw [hm, pow_add_list]
        have h1 : SideRLs tm h ([0] +> tape (O :: r)) (word U +> tape r) := by
          have hs := rule_shortO.sideRLs_concat (.nil (tape r))
          simpa [tape, append_assoc] using hs
        have h2 : SideRLs tm (h ^ m) (word U +> tape r) (tape (U :: r')) :=
          (rule_U.wall_pow m).sideRLs_concat h_side
        exact h1.trans h2
      · dsimp [prepend, potential]; omega
  · have hk : k + 1 = 1 + k := by omega
    rw [hk] at h_bound ⊢
    rw [potential_prepend] at h_bound
    have hm2 : 2 ≤ m := by omega
    set p := m - 2
    have hmp : m = 2 + p := by omega
    obtain ⟨r', h_side, h_pot, _⟩ := incs_total (1 + (1 + k) + p) r
    refine ⟨prepend (1 + (1 + k)) r', ?_, ?_⟩
    · rw [hmp, tape_prepend, tape_prepend]
      change SideRLs tm (h ^ (2 + p))
        ([0] +> ((word U) ^ (1 + k) +> (word O +> tape r)))
        ((word U) ^ (1 + (1 + k)) +> tape r')
      have h_seg := (shiftO (1 + k) p).sideRLs_concat h_side
      have h_lhs : ([0] ++ (word U) ^ (1 + k) ++ word O) +> tape r =
          [0] +> ((word U) ^ (1 + k) +> (word O +> tape r)) := by
        simp only [List.append_assoc, append_assoc]
      rwa [h_lhs] at h_seg
    · rw [potential_prepend, potential_prepend]
      dsimp [potential] at h_bound ⊢
      omega

lemma normalize (r : List Digit) :
    ∀ k m, potential (prepend k r) ≤ m → Normalized (prepend k r) m := by
  induction r with
  | nil =>
    intro k m h_bound
    have h_z : Normalized (prepend k [Z]) m := by
      refine normalize_Z [] (fun m' _ => normalize_empty m') k m ?_
      rcases k with _ | k
      · dsimp [prepend, potential] at h_bound ⊢; omega
      · have hk : k + 1 = 1 + k := by omega
        rw [hk, potential_prepend] at h_bound ⊢
        dsimp [potential] at h_bound ⊢
        omega
    obtain ⟨r', h_side, h_pot⟩ := h_z
    refine ⟨r', ?_, ?_⟩
    · rw [tape_prepend] at h_side ⊢
      have hz0 : tape [Z] = default := by
        change ([0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default
        exact all0_spec (a := [0, 0]) (by decide)
      rwa [hz0] at h_side
    · rcases k with _ | k
      · dsimp [prepend, potential] at h_pot ⊢; omega
      · have hk : k + 1 = 1 + k := by omega
        rw [hk, potential_prepend] at h_pot ⊢
        dsimp [potential] at h_pot ⊢
        omega
  | cons d r ih =>
    intro k m h_bound
    cases d with
    | U =>
      rw [prepend_U] at h_bound ⊢
      exact ih (1 + k) m h_bound
    | Z =>
      exact normalize_Z r (ih 0) k m h_bound
    | O =>
      exact normalize_O r k m h_bound

lemma normalize_positive (r : List Digit) (m : ℕ) (h_lt : potential r < m) :
    ∃ r', SideRLs tm (h ^ m) ([0] +> tape r) (tape r') ∧
      potential r' ≤ m + potential r ∧ O ∈ r' := by
  rcases m with _ | m
  · omega
  · obtain ⟨r', h_side, h_pot⟩ := normalize r 0 m (by dsimp [prepend]; omega)
    dsimp [prepend] at h_side h_pot
    obtain ⟨r'', h_inc, h_pot', h_mem⟩ := Inc_total r'
    refine ⟨r'', h_side.trans_succ (Inc_spec h_inc), by omega, h_mem⟩

lemma left1_calls (a : ℕ) :
    ∀ b r r', SideRLs tm (h ^ a) r r' →
      (toDHCfg (hL, .left) (left1 a b) r) [tm]⊢*
        (toDHCfg (hL, .left) (left1 0 (b + a)) r') := by
  induction a with
  | zero =>
    intro b r r' h_side
    cases h_side
    rw [Nat.add_zero]
    exact stepStar_refl tm _
  | succ a ih =>
    intro b r r' h_side
    rw [pow_succ_list h a] at h_side
    obtain ⟨s, h1, ha⟩ := h_side.split
    have h_add : b + (a + 1) = (1 + b) + a := by omega
    have ha1 : a + 1 = 1 + a := by omega
    rw [h_add, ha1]
    exact stepStar_trans (rule_L1 a b r)
      (stepStar_trans (stepPlus_to_stepStar (h1.elim_single (left1 a (1 + b))))
        (ih (1 + b) s r' ha))

lemma left2_calls (a : ℕ) :
    ∀ b r r', SideRLs tm (h ^ (1 + a)) r r' →
      (toDHCfg (hL, .left) (left2 a b) r) [tm]⊢*
        (toDHCfg (hL, .left) (left1 0 (b + a)) r') := by
  induction a with
  | zero =>
    intro b r r' h_side
    exact stepStar_trans (rule_L20 b r)
      (stepPlus_to_stepStar (h_side.elim_single (left1 0 b)))
  | succ a ih =>
    intro b r r' h_side
    have h_pow : h ^ (1 + (a + 1)) = h ++ h ^ (1 + a) := by
      have hk : 1 + (a + 1) = (1 + a) + 1 := by omega
      rw [hk, pow_succ_list]
    rw [h_pow] at h_side
    obtain ⟨s, h1, ha⟩ := h_side.split
    have h_add : b + (a + 1) = (1 + b) + a := by omega
    have ha1 : a + 1 = 1 + a := by omega
    rw [h_add, ha1]
    exact stepStar_trans (rule_L2 a b r)
      (stepStar_trans (stepPlus_to_stepStar (h1.elim_single (left2 a (1 + b))))
        (ih (1 + b) s r' ha))

lemma left1_send (a b : ℕ) (r r' : ListBlank (Fin 2))
    (h_side : SideRLs tm (h ^ (1 + a)) r r') :
    (toDHCfg (hR, .right) (left1 a b) r) [tm]⊢⁺
      (toDHCfg (hL, .left) (left1 0 (b + a)) r') := by
  have hk : 1 + a = a + 1 := by omega
  rw [hk, pow_succ_list] at h_side
  obtain ⟨s, h1, ha⟩ := h_side.split
  exact stepPlus_stepStar_trans (h1.elim_single (left1 a b)) (left1_calls a b s r' ha)

lemma left2_send (a b : ℕ) (r r' : ListBlank (Fin 2))
    (h_side : SideRLs tm (h ^ (2 + a)) r r') :
    (toDHCfg (hR, .right) (left2 a b) r) [tm]⊢⁺
      (toDHCfg (hL, .left) (left1 0 (b + a)) r') := by
  have hk : 2 + a = (1 + a) + 1 := by omega
  rw [hk, pow_succ_list] at h_side
  obtain ⟨s, h1, ha⟩ := h_side.split
  exact stepPlus_stepStar_trans (h1.elim_single (left2 a b)) (left2_calls a b s r' ha)

lemma first_digit (r : List Digit) (h_mem : O ∈ r) :
    ∃ k d t, r = prepend k (d :: t) ∧ (d = Z ∨ d = O) := by
  induction r with
  | nil => cases h_mem
  | cons d r ih =>
    cases d with
    | U =>
      cases h_mem with
      | tail _ h_mem' =>
        obtain ⟨k, d', t, rfl, hd⟩ := ih h_mem'
        refine ⟨1 + k, d', t, ?_, hd⟩
        unfold prepend
        have hk : 1 + k = k + 1 := by omega
        rw [hk, List.replicate_succ, List.cons_append]
    | Z =>
      exact ⟨0, Z, r, rfl, Or.inl rfl⟩
    | O =>
      exact ⟨0, O, r, rfl, Or.inr rfl⟩

lemma next_step (n : ℕ) (r : List Digit) (h_mem : O ∈ r) (h_pot : potential r ≤ n * 2) :
    ∃ n' r', ((stateCfg n r) [tm]⊢⁺ (stateCfg n' r')) ∧ O ∈ r' ∧ potential r' ≤ n' * 2 := by
  obtain ⟨k, d, t, rfl, hd⟩ := first_digit r h_mem
  have h_pb := potential_bound k (d :: t)
  rcases hd with rfl | rfl
  · dsimp [potential] at h_pb
    obtain ⟨r', h_side, h_pot', h_mem'⟩ := normalize_positive t (2 + k + n) (by omega)
    refine ⟨1 + k + n, r', ?_, h_mem', by omega⟩
    unfold stateCfg
    rw [tape_prepend]
    dsimp [tape]
    have h_lz := rule_LZ n k (tape t)
    have h_s1 := left1_send (1 + k + n) 0 ([0] +> tape t) (tape r') (by
      have hk : 1 + (1 + k + n) = 2 + k + n := by omega
      rwa [hk])
    rw [Nat.zero_add] at h_s1
    exact stepStar_stepPlus_trans h_lz h_s1
  · dsimp [potential] at h_pb
    obtain ⟨r', h_side, h_pot', h_mem'⟩ := incs_total (3 + k + n) t
    refine ⟨1 + k + n, r', ?_, h_mem' (by omega), by omega⟩
    unfold stateCfg
    rw [tape_prepend]
    dsimp [tape]
    have h_lo := rule_LO n k (tape t)
    have h_s2 := left2_send (1 + k + n) 0 (tape t) (tape r') (by
      have hk : 2 + (1 + k + n) = 3 + k + n := by omega
      rwa [hk])
    rw [Nat.zero_add] at h_s2
    exact stepStar_stepPlus_trans h_lo h_s2

lemma init_reaches_tm :
    (init []) [tm]⊢* (stateCfg 1 [U, O]) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold stateCfg toDHCfg left1
  dsimp [tape, word]
  bb_steps

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ n r, c = flipCfg (stateCfg n r) ∧ O ∈ r ∧ potential r ≤ n * 2)
    ⟨flipCfg (stateCfg 1 [U, O]), ?_, 1, [U, O], rfl, by decide, by decide⟩ ?_
  · exact stepStar_unflipTM init_reaches_tm
  · rintro _ ⟨n, r, rfl, h_mem, h_pot⟩
    obtain ⟨n', r', h_step, h_mem', h_pot'⟩ := next_step n r h_mem h_pot
    exact ⟨flipCfg (stateCfg n' r'), stepPlus_unflipTM h_step, n', r', rfl, h_mem', h_pot'⟩

end BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_1LCHHH
