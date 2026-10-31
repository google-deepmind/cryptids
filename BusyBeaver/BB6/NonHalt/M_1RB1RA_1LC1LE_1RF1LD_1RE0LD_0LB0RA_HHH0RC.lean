/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RA_1LC1LE_1RF1LD_1RE0LD_0LB0RA_---0RC` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RA_1LC1LE_1RF1LD_1RE0LD_0LB0RA_---0RC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RA_1LC1LE_1RF1LD_1RE0LD_0LB0RA_HHH0RC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RA_1LC1LE_1RF1LD_1RE0LD_0LB0RA_---0RC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[simp] lemma zMz (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma z00 : Turing.ListBlank.cons (0 : Fin 2) default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = Turing.ListBlank.cons a (l +> s) := rfl
@[simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

lemma zSm (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z01 (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa (tm : Machine (Fin 2) (Fin 6)) (c_1 : Cfg (Fin 2) (Fin 6)) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zPs {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 : Cfg (Fin 2) (Fin 6)} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z02 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSp {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z03 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂

macro "finish" : tactic =>
  `(tactic| exact ⟨0, rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

/-- Words on the tape (`BECv10.v:2858–2861`).
Note that on the left tape, Coq `<[1;0]` is `U = [0, 1]` and Coq `<[0;1]` is `V = [1, 0]`. -/
abbrev Z : zF := [0, 0]
abbrev U : zF := [0, 1]
abbrev V : zF := [1, 0]
abbrev O : zF := [1, 1]

@[simp] lemma zZd : Z +> (default : zB) = default := by simp [Z]

open BusyBeaver.Longitudinal (DH0 toDHCfg SideRLs SegRLs)
open BusyBeaver.Longitudinal.BoundedConfig (segRLs_c_spec)

abbrev Call := DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)
abbrev ch : Call := ((A, []), (D, []))
abbrev Side := SideRLs target_tm
abbrev Seg := SegRLs target_tm

@[simp] lemma z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] lemma z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

lemma zLp_add {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n :=
  BusyBeaver.Longitudinal.pow_add_list l m n

lemma zLp_shift {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ^ n ++ l := by
  rw [Nat.add_comm 1 n, BusyBeaver.Longitudinal.pow_succ_list']

lemma z07 (l : zF) (n : Nat) (s : zB) : (l ^ (1 + n)) +> s = l +> ((l ^ n) +> s) := by
  rw [zLp', append_assoc]

lemma z09 (l : zF) (n : Nat) (s : zB) : (l ^ n) +> (l +> s) = (l ^ (1 + n)) +> s := by
  rw [zLp_shift, append_assoc]

lemma rot_U_V (k : Nat) (r : zB) :
    ([1] : zF) +> ((U ^ k) +> r) = (V ^ k) +> ([1] +> r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 U k r, z07 V k ([1] +> r)]
    simp only [U, V, append_cons, append_nil] at ih ⊢
    rw [ih]

lemma rot_Z (k : Nat) (r : zB) :
    ([0] : zF) +> ((Z ^ k) +> r) = (Z ^ k) +> ([0] +> r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 Z k r, z07 Z k ([0] +> r)]
    simp only [Z, append_cons, append_nil] at ih ⊢
    rw [ih]

lemma rot_O (k : Nat) (r : zB) :
    ([1] : zF) +> ((O ^ k) +> r) = (O ^ k) +> ([1] +> r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k + 1 = 1 + k := by omega
    rw [hk, z07 O k r, z07 O k ([1] +> r)]
    simp only [O, append_cons, append_nil] at ih ⊢
    rw [ih]

lemma mod2 (n : Nat) : (∃ k, n = k * 2) ∨ (∃ k, n = 1 + k * 2) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact Or.inl ⟨k, by omega⟩
  · exact Or.inr ⟨k, by omega⟩

lemma zSc {ls1 ls2 : List Call} {w1 w2 : zF} {r1 r2 : zB}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1.sideRLs_concat h2

lemma zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 :=
  h1.trans h2

/-- Binary number representation on the right half-tape (`BECv10.v:2864`). -/
inductive Num : Nat → zB → Prop where
  | nil : Num 0 default
  | zero {n : Nat} {r : zB} : Num n r → Num (n * 2) (Z +> r)
  | one {n : Nat} {r : zB} : Num n r → Num (1 + n * 2) (O +> r)

lemma Num_eq {n m : Nat} {r s : zB} (h : Num n r) (hn : n = m) (hr : r = s) : Num m s := by
  subst hn; subst hr; exact h

lemma Num_even (n : Nat) {r : zB} (h : Num (n * 2) r) : ∃ s, r = Z +> s ∧ Num n s := by
  generalize hm : n * 2 = m at h
  cases h with
  | nil =>
    have hn : n = 0 := by omega
    subst hn
    exact ⟨default, by simp [Z], Num.nil⟩
  | @zero n0 s h0 =>
    have hn : n0 = n := by omega
    subst hn
    exact ⟨s, rfl, h0⟩
  | @one n0 s _ => omega

lemma Num_odd (n : Nat) {r : zB} (h : Num (1 + n * 2) r) : ∃ s, r = O +> s ∧ Num n s := by
  generalize hm : 1 + n * 2 = m at h
  cases h with
  | nil => omega
  | @zero n0 s _ => omega
  | @one n0 s h0 =>
    have hn : n0 = n := by omega
    subst hn
    exact ⟨s, rfl, h0⟩

lemma carry : Seg [ch] [ch] O Z :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_Z_O : Seg [ch] [] Z O :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_100_011 : Seg [ch] [] [1, 0, 0] [0, 1, 1] :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma increment {n : Nat} {r : zB} (h : Num n r) : ∃ s, Num (1 + n) s ∧ Side [ch] r s := by
  induction h with
  | nil =>
    refine ⟨O +> default, Num.one Num.nil, ?_⟩
    simpa only [zZd] using zSc seg_Z_O (SideRLs.nil default)
  | @zero n r hn _ =>
    exact ⟨O +> r, Num.one hn, zSc seg_Z_O (SideRLs.nil r)⟩
  | @one n r _ ih =>
    rcases ih with ⟨s, hs, hSide⟩
    exact ⟨Z +> s, Num_eq (Num.zero hs) (by omega) rfl, zSc carry hSide⟩

-- Tape-sweep helper lemmas for `es` / `es'`

lemma shiftL_E_U_step (l r : zB) :
    ((U +> l) <{{E}} r) [target_tm]⊢* (l <{{E}} (V +> r)) := by
  simp only [U, V, append_cons, append_nil]
  execute

lemma shiftL_E_U (q : Nat) (l r : zB) :
    (((U ^ q) +> l) <{{E}} r) [target_tm]⊢* (l <{{E}} ((V ^ q) +> r)) := by
  induction q generalizing r with
  | zero =>
    simp only [z05, append_nil]
    finish
  | succ q ih =>
    have hq : q + 1 = 1 + q := by omega
    rw [hq, z07 U q l]
    refine zSt (shiftL_E_U_step ((U ^ q) +> l) r) ?_
    simpa only [z09 V q r] using ih (V +> r)

lemma shiftR_F_V_step (l r : zB) :
    (l {{F}}> (V +> r)) [target_tm]⊢* ((V +> l) {{F}}> r) := by
  simp only [V, append_cons, append_nil]
  execute

lemma shiftR_F_V (q : Nat) (l r : zB) :
    (l {{F}}> ((V ^ q) +> r)) [target_tm]⊢* (((V ^ q) +> l) {{F}}> r) := by
  induction q generalizing l with
  | zero =>
    simp only [z05, append_nil]
    finish
  | succ q ih =>
    have hq : q + 1 = 1 + q := by omega
    rw [hq, z07 V q r]
    refine zSt (shiftR_F_V_step l ((V ^ q) +> r)) ?_
    simpa only [z09 V q l] using ih (V +> l)

lemma shiftL_B_V_step (l r : zB) :
    ((V +> l) <{{B}} r) [target_tm]⊢* (l <{{B}} (U +> r)) := by
  simp only [V, U, append_cons, append_nil]
  execute

lemma shiftL_B_V (d : Nat) (l r : zB) :
    (((V ^ d) +> l) <{{B}} r) [target_tm]⊢* (l <{{B}} ((U ^ d) +> r)) := by
  induction d generalizing r with
  | zero =>
    simp only [z05, append_nil]
    finish
  | succ d ih =>
    have hd : d + 1 = 1 + d := by omega
    rw [hd, z07 V d l]
    refine zSt (shiftL_B_V_step ((V ^ d) +> l) r) ?_
    simpa only [z09 U d r] using ih (U +> r)

lemma shiftR_A_U_step (l r : zB) :
    (l {{A}}> (U +> r)) [target_tm]⊢* ((V +> l) {{A}}> r) := by
  simp only [U, V, append_cons, append_nil]
  execute

lemma shiftR_A_U (d : Nat) (l r : zB) :
    (l {{A}}> ((U ^ d) +> r)) [target_tm]⊢* (((V ^ d) +> l) {{A}}> r) := by
  induction d generalizing l with
  | zero =>
    simp only [z05, append_nil]
    finish
  | succ d ih =>
    have hd : d + 1 = 1 + d := by omega
    rw [hd, z07 U d r]
    refine zSt (shiftR_A_U_step l ((U ^ d) +> r)) ?_
    simpa only [z09 V d l] using ih (V +> l)

lemma scanO_step (l r : zB) :
    (l {{A}}> (O +> r)) [target_tm]⊢* ((O +> l) {{A}}> r) := by
  simp only [O, append_cons, append_nil]
  execute

lemma scanO (j : Nat) (l r : zB) :
    (l {{A}}> ((O ^ j) +> r)) [target_tm]⊢* (((O ^ j) +> l) {{A}}> r) := by
  induction j generalizing l with
  | zero =>
    simp only [z05, append_nil]
    finish
  | succ j ih =>
    have hj : j + 1 = 1 + j := by omega
    rw [hj, z07 O j r]
    refine zSt (scanO_step l ((O ^ j) +> r)) ?_
    simpa only [z09 O j l] using ih (O +> l)

-- Two ordinary right calls, including the intervening left return (`BECv10.v:2899–2908`)

lemma pair_base (l s : zB) :
    ((U +> l) <{{D}} (Z +> s)) [target_tm]⊢* (l <{{E}} (V +> (O +> s))) := by
  simp only [U, Z, V, O, append_cons, append_nil]
  execute

lemma pair (n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (1 + n) s ∧ ∀ l q,
      (((U ^ (1 + q)) +> l) {{A}}> r) [target_tm]⊢⁺
        (l <{{E}} ((V ^ (1 + q)) +> (O +> s))) := by
  rcases increment h with ⟨r', hN', hSide⟩
  have hN'_eq : Num ((1 + n) * 2) r' := Num_eq hN' (by omega) rfl
  rcases Num_even (1 + n) hN'_eq with ⟨s, rfl, hs⟩
  refine ⟨s, hs, fun l q => ?_⟩
  have h1 : (((U ^ (1 + q)) +> l) {{A}}> r) [target_tm]⊢⁺
      (((U ^ (1 + q)) +> l) <{{D}} (Z +> s)) :=
    hSide.elim_single ((U ^ (1 + q)) +> l)
  refine z02 h1 ?_
  rw [z07 U q l]
  refine zSt (pair_base ((U ^ q) +> l) s) ?_
  simpa only [z09 V q (O +> s)] using shiftL_E_U q l (V +> (O +> s))

def S0 (l : zB) (a q : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((U ^ q) +> ((V ^ a) +> l)) {{A}}> r

def S1 (l : zB) (a q : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((U ^ q) +> (Z +> ((V ^ a) +> l))) {{A}}> r

lemma scanV_step (l r : zB) :
    (l {{A}}> (V +> ([1] +> r))) [target_tm]⊢* ((U +> l) {{A}}> ([1] +> r)) := by
  simp only [V, U, append_cons, append_nil]
  execute

lemma scanV (q : Nat) (l r : zB) :
    (l {{A}}> ((V ^ q) +> ([1] +> r))) [target_tm]⊢* (((U ^ q) +> l) {{A}}> ([1] +> r)) := by
  induction q generalizing l with
  | zero =>
    simp only [z05, append_nil]
    finish
  | succ q ih =>
    cases q with
    | zero =>
      simp only [Nat.zero_add, z06]
      exact scanV_step l r
    | succ q' =>
      have hq : q' + 1 + 1 = 1 + (q' + 1) := by omega
      rw [hq]
      have h1 : (l {{A}}> ((V ^ (1 + (q' + 1))) +> ([1] +> r))) [target_tm]⊢*
          ((U +> l) {{A}}> ((V ^ (q' + 1)) +> ([1] +> r))) := by
        rw [z07 V (q' + 1) ([1] +> r), zLp V q', append_assoc]
        simpa only [V, append_cons, append_nil] using scanV_step l ([0] +> ((V ^ q') +> ([1] +> r)))
      refine zSt h1 ?_
      simpa only [z09 U (q' + 1) l] using ih (U +> l)

lemma resume0_step (l r : zB) :
    ((V +> l) <{{E}} r) [target_tm]⊢* ((Z +> l) {{A}}> r) := by
  simp only [V, Z, append_cons, append_nil]
  execute

lemma resume0 (a q : Nat) (l r : zB) :
    (((V ^ (1 + a)) +> l) <{{E}} ((V ^ q) +> ([1] +> r))) [target_tm]⊢*
      (((U ^ q) +> (Z +> ((V ^ a) +> l))) {{A}}> ([1] +> r)) := by
  rw [z07 V a l]
  exact zSt (resume0_step ((V ^ a) +> l) ((V ^ q) +> ([1] +> r)))
    (scanV q (Z +> ((V ^ a) +> l)) r)

lemma resume1_step (l r : zB) :
    ((Z +> (V +> l)) <{{E}} r) [target_tm]⊢* ((U +> l) {{A}}> (V +> r)) := by
  simp only [Z, V, U, append_cons, append_nil]
  execute

lemma resume1 (a q : Nat) (l r : zB) :
    ((Z +> ((V ^ (1 + a)) +> l)) <{{E}} ((V ^ q) +> ([1] +> r))) [target_tm]⊢*
      (((U ^ (2 + q)) +> ((V ^ a) +> l)) {{A}}> ([1] +> r)) := by
  rw [z07 V a l]
  refine zSt (resume1_step ((V ^ a) +> l) ((V ^ q) +> ([1] +> r))) ?_
  have h2 := scanV (1 + q) (U +> ((V ^ a) +> l)) r
  rw [z07 V q ([1] +> r), z09 U (1 + q) ((V ^ a) +> l)] at h2
  have h2_eq : (1 : Nat) + (1 + q) = 2 + q := by omega
  rwa [h2_eq] at h2

lemma O_eq_1_1 (s : zB) : O +> s = [1] +> ([1] +> s) := rfl

lemma count0 (l : zB) (a q n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (3 + n * 2) s ∧ (S0 l (1 + a) (1 + q) r) [target_tm]⊢⁺ (S1 l a (1 + q) s) := by
  rcases pair n h with ⟨s, hs, hPair⟩
  refine ⟨O +> s, Num_eq (Num.one hs) (by omega) rfl, ?_⟩
  unfold S0 S1
  refine z02 (hPair ((V ^ (1 + a)) +> l) q) ?_
  rw [O_eq_1_1 s]
  exact resume0 a (1 + q) l ([1] +> s)

lemma count1 (l : zB) (a q n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (3 + n * 2) s ∧ (S1 l (1 + a) (1 + q) r) [target_tm]⊢⁺ (S0 l a (3 + q) s) := by
  rcases pair n h with ⟨s, hs, hPair⟩
  refine ⟨O +> s, Num_eq (Num.one hs) (by omega) rfl, ?_⟩
  unfold S1 S0
  refine z02 (hPair (Z +> ((V ^ (1 + a)) +> l)) q) ?_
  have hr := resume1 a (1 + q) l ([1] +> s)
  have hq : 2 + (1 + q) = 3 + q := by omega
  rw [hq] at hr
  rw [O_eq_1_1 s]
  exact hr

lemma counts (l : zB) (a a0 q n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (1 + n * 2 + a * 4) s ∧
      (S0 l (a * 2 + a0) (1 + q) r) [target_tm]⊢* (S0 l a0 (1 + q + a * 2) s) := by
  induction a generalizing q n r with
  | zero =>
    refine ⟨r, Num_eq h (by omega) rfl, ?_⟩
    have ha : 0 * 2 + a0 = a0 := by omega
    have hq : 1 + q + 0 * 2 = 1 + q := by omega
    rw [ha, hq]
    finish
  | succ a ih =>
    rcases count0 l (1 + (a * 2 + a0)) q n h with ⟨r1, hN1, h1⟩
    have hN1' : Num (1 + (1 + n) * 2) r1 := Num_eq hN1 (by omega) rfl
    rcases count1 l (a * 2 + a0) q (1 + n) hN1' with ⟨r2, hN2, h2⟩
    have hN2' : Num (1 + (2 + n) * 2) r2 := Num_eq hN2 (by omega) rfl
    rcases ih (2 + q) (2 + n) hN2' with ⟨s, hNs, hs⟩
    refine ⟨s, Num_eq hNs (by omega) rfl, ?_⟩
    have ha : (a + 1) * 2 + a0 = 1 + (1 + (a * 2 + a0)) := by omega
    have hq1 : 1 + (2 + q) = 3 + q := by omega
    have hq2 : 3 + q + a * 2 = 1 + q + (a + 1) * 2 := by omega
    rw [ha]
    rw [hq1] at hs
    rw [hq2] at hs
    exact zSt (zPs h1) (zSt (zPs h2) hs)

def K (b : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) := S0 default 0 b r

lemma overflow_start (r : zB) :
    (default <{{E}} r) [target_tm]⊢* ((V +> default) {{F}}> (V +> r)) := by
  simp only [V, append_cons, append_nil, z00]
  execute

lemma overflow_end (l s : zB) :
    (l {{F}}> (O +> s)) [target_tm]⊢* ((U +> l) {{A}}> s) := by
  simp only [O, U, append_cons, append_nil]
  execute

lemma overflow (b n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (1 + n) s ∧ (K (1 + b) r) [target_tm]⊢⁺ (S0 default (3 + b) 1 s) := by
  rcases pair n h with ⟨s, hs, hPair⟩
  refine ⟨s, hs, ?_⟩
  unfold K S0
  simp only [z05, z06, append_nil]
  refine z02 (hPair default b) ?_
  refine zSt (overflow_start ((V ^ (1 + b)) +> (O +> s))) ?_
  rw [← z07 V (1 + b) (O +> s)]
  have hSweep := shiftR_F_V (1 + (1 + b)) (V +> default) (O +> s)
  rw [z09 V (1 + (1 + b)) default] at hSweep
  have hb : 1 + (1 + (1 + b)) = 3 + b := by omega
  rw [hb] at hSweep
  exact zSt hSweep (overflow_end ((V ^ (3 + b)) +> default) s)

lemma S1_0_to_K (b : Nat) (s : zB) :
    S1 default 0 b s = K b s := by
  unfold S1 K S0
  simp only [z05, append_nil, zZd]

lemma counts_end (a q n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ b s, Num (1 + n * 2 + a * 2) s ∧ a + q ≤ b ∧ 1 ≤ b ∧
      (S0 default a (1 + q) r) [target_tm]⊢* (K b s) := by
  rcases mod2 a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases counts default k 0 q n h with ⟨s, hNs, hs⟩
    refine ⟨1 + q + k * 2, s, Num_eq hNs (by omega) rfl, by omega, by omega, ?_⟩
    unfold K
    simpa only [Nat.add_zero] using hs
  · have hk : 1 + k * 2 = k * 2 + 1 := by omega
    rw [hk]
    rcases counts default k 1 q n h with ⟨s, hNs, hs⟩
    have hNs' : Num (1 + (n + k * 2) * 2) s := Num_eq hNs (by omega) rfl
    rcases count0 default 0 (q + k * 2) (n + k * 2) hNs' with ⟨t, hNt, ht⟩
    refine ⟨1 + q + k * 2, t, Num_eq hNt (by omega) rfl, by omega, by omega, ?_⟩
    have hq : 1 + (q + k * 2) = 1 + q + k * 2 := by omega
    rw [hq, S1_0_to_K] at ht
    exact zSt hs (zPs ht)

inductive Bits : Nat → Nat → zF → Prop where
  | nil : Bits 0 0 []
  | zero {j n : Nat} {w : zF} : Bits j n w → Bits (1 + j) (n * 2) (Z ++ w)
  | one {j n : Nat} {w : zF} : Bits j n w → Bits (1 + j) (1 + n * 2) (O ++ w)

lemma Bits_eq {j j' n n' : Nat} {w w' : zF}
    (h : Bits j n w) (hj : j = j') (hn : n = n') (hw : w = w') : Bits j' n' w' := by
  subst hj; subst hn; subst hw; exact h

lemma finite_increment {j n : Nat} {w : zF} (h : Bits j n w) (hb : 1 + n < 2 ^ j) :
    ∃ w', Bits j (1 + n) w' ∧ Seg [ch] [] (1 :: w) (0 :: w') := by
  induction h with
  | nil => omega
  | @zero j n w h ih =>
    refine ⟨O ++ w, Bits.one h, ?_⟩
    change Seg [ch] [] ([1, 0, 0] ++ w) ([0, 1, 1] ++ w)
    exact seg_100_011.concat (SegRLs.nil w)
  | @one j n w h ih =>
    have hb' : 1 + n < 2 ^ j := by
      have hp : 2 ^ (1 + j) = 2 * 2 ^ j := by rw [Nat.add_comm 1 j, Nat.pow_succ]; omega
      omega
    rcases ih hb' with ⟨w', hBits', hSeg'⟩
    refine ⟨Z ++ w', Bits_eq (Bits.zero hBits') rfl (by omega) rfl, ?_⟩
    change Seg [ch] [] (O ++ (1 :: w)) (Z ++ (0 :: w'))
    exact carry.concat hSeg'

lemma wrap_base (l r : zB) :
    ((V +> (V +> l)) <{{D}} ([0] +> r)) [target_tm]⊢*
      (l <{{B}} (U +> (U +> ([1] +> r)))) := by
  simp only [V, U, append_cons, append_nil]
  execute

lemma wrap (d : Nat) (l r : zB) :
    (((V ^ (2 + d)) +> l) <{{D}} ([0] +> r)) [target_tm]⊢*
      (l <{{B}} ((U ^ (2 + d)) +> ([1] +> r))) := by
  have hd : 2 + d = 1 + (1 + d) := by omega
  rw [hd, z07 V (1 + d) l, z07 V d l]
  refine zSt (wrap_base ((V ^ d) +> l) r) ?_
  have hShift := shiftL_B_V d l (U +> (U +> ([1] +> r)))
  rwa [z09 U d (U +> ([1] +> r)), z09 U (1 + d) ([1] +> r)] at hShift

lemma internal_inc {j n : Nat} {w : zF} (h : Bits j n w) (hb : 1 + n < 2 ^ j) :
    ∃ w', Bits j (1 + n) w' ∧ ∀ l d r,
      (((V ^ (2 + d)) +> l) {{A}}> ([1] +> (w +> ([0] +> r)))) [target_tm]⊢⁺
        (l <{{B}} ((U ^ (2 + d)) +> ([1] +> (w' +> ([0] +> r))))) := by
  rcases finite_increment h hb with ⟨w', hBits', hSeg⟩
  refine ⟨w', hBits', fun l d r => ?_⟩
  have hSide : Side [ch] ((1 :: w) +> ([0] +> r)) ((0 :: w') +> ([0] +> r)) :=
    zSc hSeg (SideRLs.nil ([0] +> r))
  have h1 := hSide.elim_single ((V ^ (2 + d)) +> l)
  have h_in : ((1 :: w) +> ([0] +> r)) = [1] +> (w +> ([0] +> r)) := rfl
  have h_out : ((0 :: w') +> ([0] +> r)) = [0] +> (w' +> ([0] +> r)) := rfl
  simp only [toDHCfg, append_nil, h_in, h_out] at h1
  exact z02 h1 (wrap d l (w' +> ([0] +> r)))

lemma resumeB2_base (l r : zB) :
    ((U +> (U +> l)) <{{B}} r) [target_tm]⊢* ((V +> (O +> l)) {{A}}> r) := by
  simp only [U, V, O, append_cons, append_nil]
  execute

lemma resumeB2 (d : Nat) (l r : zB) :
    (((U ^ 2) +> l) <{{B}} ((U ^ d) +> r)) [target_tm]⊢*
      (((V ^ (1 + d)) +> (O +> l)) {{A}}> r) := by
  have h2 : (U ^ 2) +> l = U +> (U +> l) := by simp [zLp, append_assoc]
  rw [h2]
  refine zSt (resumeB2_base l ((U ^ d) +> r)) ?_
  simpa only [z09 V d (O +> l)] using shiftR_A_U d (V +> (O +> l)) r

lemma resumeBO_base (l r : zB) :
    ((O +> l) <{{B}} r) [target_tm]⊢* ((V +> l) {{A}}> r) := by
  simp only [O, V, append_cons, append_nil]
  execute

lemma resumeBO (d : Nat) (l r : zB) :
    ((O +> l) <{{B}} ((U ^ d) +> r)) [target_tm]⊢*
      (((V ^ (1 + d)) +> l) {{A}}> r) := by
  refine zSt (resumeBO_base l ((U ^ d) +> r)) ?_
  simpa only [z09 V d l] using shiftR_A_U d (V +> l) r

def Internal (l : zB) (c d : Nat) (w : zF) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((V ^ d) +> ((U ^ c) +> l)) {{A}}> ([1] +> (w +> ([0] +> r)))

lemma internal_pair {j n : Nat} {w : zF} (h : Bits j n w) (hb : 2 + n < 2 ^ j) :
    ∃ w', Bits j (2 + n) w' ∧ ∀ l c d r,
      (Internal l (2 + c) (2 + d) w r) [target_tm]⊢⁺ (Internal l c (4 + d) w' r) := by
  rcases internal_inc h (by omega) with ⟨w1, hN1, h1⟩
  rcases internal_inc hN1 (by omega) with ⟨w2, hN2, h2⟩
  refine ⟨w2, Bits_eq hN2 rfl (by omega) rfl, fun l c d r => ?_⟩
  unfold Internal
  have hc : (U ^ (2 + c)) +> l = (U ^ 2) +> ((U ^ c) +> l) := by
    rw [zLp_add U 2 c, append_assoc]
  rw [hc]
  refine z02 (h1 ((U ^ 2) +> ((U ^ c) +> l)) d r) ?_
  refine zSt (resumeB2 (2 + d) ((U ^ c) +> l) ([1] +> (w1 +> ([0] +> r)))) ?_
  have hd1 : 1 + (2 + d) = 2 + (1 + d) := by omega
  rw [hd1]
  refine zPs (z02 (h2 (O +> ((U ^ c) +> l)) (1 + d) r) ?_)
  have hd2 : 2 + (1 + d) = 3 + d := by omega
  have hd3 : 1 + (3 + d) = 4 + d := by omega
  rw [hd2]
  simpa only [hd3] using resumeBO (3 + d) ((U ^ c) +> l) ([1] +> (w2 +> ([0] +> r)))

lemma internal_pairs (k : Nat) {j n : Nat} {w : zF} (h : Bits j n w) (hb : n + k * 2 < 2 ^ j) :
    ∃ w', Bits j (n + k * 2) w' ∧ ∀ l c d r,
      (Internal l (k * 2 + c) (2 + d) w r) [target_tm]⊢* (Internal l c (2 + d + k * 2) w' r) := by
  induction k generalizing n w with
  | zero =>
    refine ⟨w, Bits_eq h rfl (by omega) rfl, fun l c d r => ?_⟩
    have hc : 0 * 2 + c = c := by omega
    have hd : 2 + d + 0 * 2 = 2 + d := by omega
    rw [hc, hd]
    finish
  | succ k ih =>
    rcases internal_pair h (by omega) with ⟨w1, hN1, h1⟩
    rcases ih hN1 (by omega) with ⟨w2, hN2, h2⟩
    refine ⟨w2, Bits_eq hN2 rfl (by omega) rfl, fun l c d r => ?_⟩
    have hc : (k + 1) * 2 + c = 2 + (k * 2 + c) := by omega
    have hd1 : 4 + d = 2 + (2 + d) := by omega
    have hd2 : 2 + (2 + d) + k * 2 = 2 + d + (k + 1) * 2 := by omega
    rw [hc]
    have step1 := h1 l (k * 2 + c) d r
    have step2 := h2 l c (2 + d) r
    rw [hd1] at step1
    rw [hd2] at step2
    exact zSt (zPs step1) step2

lemma Bits_zeros (j : Nat) : Bits j 0 (Z ^ j) := by
  induction j with
  | zero => exact Bits.nil
  | succ j ih =>
    rw [zLp]
    exact Bits_eq (Bits.zero ih) (by omega) (by omega) rfl

lemma Bits_ones (j : Nat) {w : zF} (h : Bits j (2 ^ j - 1) w) : w = O ^ j := by
  generalize hn : 2 ^ j - 1 = n at h
  induction h with
  | nil => rfl
  | @zero j0 n0 w0 _ _ =>
    have hp : 0 < 2 ^ j0 := Nat.two_pow_pos j0
    have hp2 : 2 ^ (1 + j0) = 2 * 2 ^ j0 := by rw [Nat.add_comm 1 j0, Nat.pow_succ]; omega
    omega
  | @one j0 n0 w0 h0 ih =>
    have hp : 0 < 2 ^ j0 := Nat.two_pow_pos j0
    have hp2 : 2 ^ (1 + j0) = 2 * 2 ^ j0 := by rw [Nat.add_comm 1 j0, Nat.pow_succ]; omega
    have hn0 : 2 ^ j0 - 1 = n0 := by omega
    rw [ih hn0, zLp']

-- Entry, internal transition, and exit lemmas (`BECv10.v:3081–3186`)

lemma side_O_pow_Z (k : Nat) (r : zB) :
    Side [ch] ((O ^ k) +> (Z +> r)) ((Z ^ k) +> (O +> r)) := by
  induction k with
  | zero =>
    simp only [z05, append_nil]
    exact zSc seg_Z_O (SideRLs.nil r)
  | succ k ih =>
    rw [zLp, append_assoc, zLp, append_assoc]
    exact zSc carry ih

lemma enter_mid1 (l r : zB) :
    ((U +> l) {{A}}> (Z +> r)) [target_tm]⊢* ((V +> (O +> l)) {{A}}> r) := by
  simp only [U, Z, V, O, append_cons, append_nil]
  execute

lemma enter_mid2 (l r : zB) :
    ((V +> (O +> l)) <{{D}} (Z +> (Z +> r))) [target_tm]⊢*
      ((V +> l) <{{B}} (U +> (O +> (V +> r)))) := by
  simp only [V, O, Z, U, append_cons, append_nil]
  execute

lemma enter (b j : Nat) (r : zB) :
    (K (1 + b) (O +> (O +> (Z +> ((O ^ (1 + j)) +> (Z +> r)))))) [target_tm]⊢⁺
      (default <{{B}} ((U ^ (5 + b)) +> (O +> (V +> ((Z ^ j) +> (O +> r)))))) := by
  have hSide1 : Side [ch]
      (O +> (O +> (Z +> ((O ^ (1 + j)) +> (Z +> r)))))
      (Z +> (Z +> (O +> ((O ^ (1 + j)) +> (Z +> r))))) :=
    zSc carry (zSc carry (zSc seg_Z_O (SideRLs.nil ((O ^ (1 + j)) +> (Z +> r)))))
  unfold K S0
  simp only [z05, append_nil]
  have h1 := hSide1.elim_single ((U ^ (1 + b)) +> default)
  simp only [toDHCfg, append_nil] at h1
  refine z02 h1 ?_
  rw [z07 U b default]
  refine zSt (pair_base ((U ^ b) +> default) (Z +> (O +> ((O ^ (1 + j)) +> (Z +> r))))) ?_
  have hShift1 := shiftL_E_U b default (V +> (O +> (Z +> (O +> ((O ^ (1 + j)) +> (Z +> r))))))
  rw [z09 V b] at hShift1
  refine zSt hShift1 ?_
  refine zSt (overflow_start ((V ^ (1 + b)) +> (O +> (Z +> (O +> ((O ^ (1 + j)) +> (Z +> r))))))) ?_
  rw [← z07 V (1 + b)]
  have hSweep := shiftR_F_V (1 + (1 + b)) (V +> default) (O +> (Z +> (O +> ((O ^ (1 + j)) +> (Z +> r)))))
  rw [z09 V (1 + (1 + b)) default] at hSweep
  have hb3 : 1 + (1 + (1 + b)) = 3 + b := by omega
  rw [hb3] at hSweep
  refine zSt hSweep ?_
  refine zSt (overflow_end ((V ^ (3 + b)) +> default) (Z +> (O +> ((O ^ (1 + j)) +> (Z +> r))))) ?_
  refine zSt (enter_mid1 ((V ^ (3 + b)) +> default) (O +> ((O ^ (1 + j)) +> (Z +> r)))) ?_
  rw [← z07 O (1 + j) (Z +> r)]
  have hSide2 := (side_O_pow_Z (1 + (1 + j)) r).elim_single (V +> (O +> ((V ^ (3 + b)) +> default)))
  simp only [toDHCfg, append_nil] at hSide2
  rw [z07 Z (1 + j) (O +> r), z07 Z j (O +> r)] at hSide2
  refine zSt (zPs hSide2) ?_
  refine zSt (enter_mid2 ((V ^ (3 + b)) +> default) ((Z ^ j) +> (O +> r))) ?_
  rw [← z07 V (3 + b) default]
  have hShiftB := shiftL_B_V (1 + (3 + b)) default (U +> (O +> (V +> ((Z ^ j) +> (O +> r)))))
  rw [z09 U (1 + (3 + b))] at hShiftB
  have hb5 : 1 + (1 + (3 + b)) = 5 + b := by omega
  rwa [hb5] at hShiftB

lemma sweep_B_U (d : Nat) (r : zB) :
    (default <{{B}} ((U ^ d) +> r)) [target_tm]⊢*
      (([1] +> ((U ^ d) +> default)) {{F}}> ([1] +> r)) := by
  have h1 : (default <{{B}} ((U ^ d) +> r)) [target_tm]⊢*
      (([1] +> default) {{F}}> ([1] +> ((U ^ d) +> r))) := by
    simp only [append_cons, append_nil, z00]
    execute
  refine zSt h1 ?_
  rw [rot_U_V d r, rot_U_V d default]
  exact shiftR_F_V d ([1] +> default) ([1] +> r)

lemma start_internal_tail (l r : zB) :
    (([1] +> l) {{F}}> ([1] +> (O +> (V +> (Z +> r))))) [target_tm]⊢*
      ((V +> (V +> l)) {{A}}> (O +> (V +> r))) := by
  simp only [O, V, Z, append_cons, append_nil]
  execute

lemma start_internal (b j : Nat) (r : zB) :
    (default <{{B}} ((U ^ (5 + b)) +> (O +> (V +> ((Z ^ (1 + j)) +> (O +> r)))))) [target_tm]⊢*
      (Internal default (5 + b) 2 (O ++ (Z ^ j)) (O +> r)) := by
  refine zSt (sweep_B_U (5 + b) (O +> (V +> ((Z ^ (1 + j)) +> (O +> r))))) ?_
  rw [z07 Z j (O +> r)]
  have hTail := start_internal_tail ((U ^ (5 + b)) +> default) ((Z ^ j) +> (O +> r))
  have hEq : ((V +> (V +> ((U ^ (5 + b)) +> default))) {{A}}> (O +> (V +> ((Z ^ j) +> (O +> r))))) =
      Internal default (5 + b) 2 (O ++ (Z ^ j)) (O +> r) := by
    unfold Internal
    have hV2 : (V ^ 2) +> ((U ^ (5 + b)) +> default) = V +> (V +> ((U ^ (5 + b)) +> default)) := by
      simp [zLp, append_assoc]
    have hR : O +> (V +> ((Z ^ j) +> (O +> r))) = [1] +> ((O ++ (Z ^ j)) +> ([0] +> (O +> r))) := by
      rw [append_assoc O (Z ^ j) ([0] +> (O +> r)), ← rot_Z j (O +> r)]
      rfl
    rw [hV2, hR]
  rwa [hEq] at hTail

lemma clear_one_step (l r : zB) :
    ((O +> l) <{{E}} r) [target_tm]⊢* ((U +> l) {{A}}> r) := by
  simp only [O, U, append_cons, append_nil]
  execute

lemma clear_one (n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (3 + n * 2) s ∧ ∀ l q,
      (((U ^ (1 + q)) +> (O +> l)) {{A}}> r) [target_tm]⊢⁺
        (((U ^ (2 + q)) +> l) {{A}}> s) := by
  rcases pair n h with ⟨s, hs, hPair⟩
  refine ⟨O +> s, Num_eq (Num.one hs) (by omega) rfl, fun l q => ?_⟩
  refine z02 (hPair (O +> l) q) ?_
  refine zSt (clear_one_step l ((V ^ (1 + q)) +> (O +> s))) ?_
  have hScan := scanV (1 + q) (U +> l) ([1] +> s)
  rw [z09 U (1 + q) l] at hScan
  have hq : 1 + (1 + q) = 2 + q := by omega
  rw [hq] at hScan
  rw [O_eq_1_1 s]
  exact hScan

lemma clear_ones (j n : Nat) {r : zB} (h : Num (1 + n * 2) r) :
    ∃ s, Num (1 + n * 2 + j * 2) s ∧ ∀ l q,
      (((U ^ (1 + q)) +> ((O ^ j) +> l)) {{A}}> r) [target_tm]⊢*
        (((U ^ (1 + q + j)) +> l) {{A}}> s) := by
  induction j generalizing n r with
  | zero =>
    refine ⟨r, Num_eq h (by omega) rfl, fun l q => ?_⟩
    simp only [z05, append_nil, Nat.add_zero]
    finish
  | succ j ih =>
    rcases clear_one n h with ⟨r1, hN1, h1⟩
    have hN1' : Num (1 + (1 + n) * 2) r1 := Num_eq hN1 (by omega) rfl
    rcases ih (1 + n) hN1' with ⟨s, hNs, hs⟩
    refine ⟨s, Num_eq hNs (by omega) rfl, fun l q => ?_⟩
    rw [zLp O j, append_assoc]
    refine zSt (zPs (h1 ((O ^ j) +> l) q)) ?_
    have step2 := hs l (1 + q)
    have hq1 : 1 + (1 + q) = 2 + q := by omega
    have hq2 : 2 + q + j = 1 + q + (j + 1) := by omega
    rw [hq1] at step2
    rw [hq2] at step2
    exact step2

def Safe (b : Nat) (r : zB) : Prop :=
  1 ≤ b ∧ ∃ n, Num (1 + n * 2) r ∧ n ≤ b * 2

def Returns (b : Nat) (r : zB) : Prop :=
  ∃ b' r', Safe b' r' ∧ (K b r) [target_tm]⊢⁺ (K b' r')

lemma branch1 (b m : Nat) (r : zB) (hN : Num (1 + m * 4) r) (hB : m ≤ 1 + b) :
    Returns (1 + b) r := by
  have hN' : Num (1 + (m * 2) * 2) r := Num_eq hN (by omega) rfl
  rcases overflow b (m * 2) hN' with ⟨s, hNs, hs⟩
  rcases counts_end (3 + b) 0 m hNs with ⟨b', t, hNt, hB1, hB2, ht⟩
  refine ⟨b', t, ⟨hB2, m + 3 + b, Num_eq hNt (by omega) rfl, by omega⟩, z02 hs ht⟩

lemma bridge2 (l : zB) (a : Nat) (r : zB) :
    (S0 l a 1 (Z +> (Z +> r))) [target_tm]⊢* (S0 l a 2 (O +> r)) := by
  unfold S0
  simp only [z06, zLp, z05, append_nil, append_assoc, Z, O, U, append_cons]
  execute

lemma bridge3 (l : zB) (a : Nat) (r : zB) :
    (S0 l a 1 (Z +> (O +> (Z +> r)))) [target_tm]⊢* (S0 l (2 + a) 1 (O +> r)) := by
  unfold S0
  have ha : (V ^ (2 + a)) +> l = V +> (V +> ((V ^ a) +> l)) := by
    have h2 : 2 + a = 1 + (1 + a) := by omega
    rw [h2, z07 V (1 + a) l, z07 V a l]
  rw [ha]
  simp only [z06, Z, O, U, V, append_cons, append_nil]
  execute

lemma branch2 (b m : Nat) (r : zB) (hN : Num (7 + m * 8) r) (hB : m ≤ 1 + b) :
    Returns (1 + b) r := by
  have hN' : Num (1 + (3 + m * 4) * 2) r := Num_eq hN (by omega) rfl
  rcases overflow b (3 + m * 4) hN' with ⟨s, hNs, hs⟩
  have hNs' : Num ((2 + m * 2) * 2) s := Num_eq hNs (by omega) rfl
  rcases Num_even (2 + m * 2) hNs' with ⟨s1, rfl, hN1⟩
  have hN1' : Num ((1 + m) * 2) s1 := Num_eq hN1 (by omega) rfl
  rcases Num_even (1 + m) hN1' with ⟨s2, rfl, hN2⟩
  rcases counts_end (3 + b) 1 (1 + m) (Num.one hN2) with ⟨b', t, hNt, hB1, hB2, ht⟩
  refine ⟨b', t, ⟨hB2, m + 4 + b, Num_eq hNt (by omega) rfl, by omega⟩, ?_⟩
  exact z02 hs (zSt (bridge2 default (3 + b) s2) ht)

lemma branch3 (b m : Nat) (r : zB) (hN : Num (3 + m * 16) r) (hB : m ≤ 1 + b) :
    Returns (1 + b) r := by
  have hN' : Num (1 + (1 + m * 8) * 2) r := Num_eq hN (by omega) rfl
  rcases overflow b (1 + m * 8) hN' with ⟨s, hNs, hs⟩
  have hNs' : Num ((1 + m * 4) * 2) s := Num_eq hNs (by omega) rfl
  rcases Num_even (1 + m * 4) hNs' with ⟨s1, rfl, hN1⟩
  have hN1' : Num (1 + (m * 2) * 2) s1 := Num_eq hN1 (by omega) rfl
  rcases Num_odd (m * 2) hN1' with ⟨s2, rfl, hN2⟩
  rcases Num_even m hN2 with ⟨s3, rfl, hN3⟩
  rcases counts_end (5 + b) 0 m (Num.one hN3) with ⟨b', t, hNt, hB1, hB2, ht⟩
  refine ⟨b', t, ⟨hB2, m + 5 + b, Num_eq hNt (by omega) rfl, by omega⟩, ?_⟩
  have hb : 2 + (3 + b) = 5 + b := by omega
  have hBr := bridge3 default (3 + b) s3
  rw [hb] at hBr
  exact z02 hs (zSt hBr ht)

lemma zeros_after_one (j : Nat) (r : zB) :
    ([1] : zF) +> ((O ^ j) +> ([0] +> r)) = (O ^ j) +> (V +> r) := by
  rw [rot_O]
  rfl

lemma exit_internal (j : Nat) (l r : zB) :
    (l {{A}}> ([1] +> ((O ^ j) +> ([0] +> (O +> r))))) [target_tm]⊢*
      ((U +> ((O ^ j) +> l)) {{A}}> (O +> r)) := by
  rw [zeros_after_one]
  refine zSt (scanO j l (V +> (O +> r))) ?_
  have hScan := scanV 1 ((O ^ j) +> l) ([1] +> r)
  simp only [z06] at hScan
  rwa [O_eq_1_1 r]

lemma start_zero_tail (l r : zB) :
    (([1] +> l) {{F}}> ([1] +> (O +> (V +> (O +> r))))) [target_tm]⊢*
      ((U +> (V +> (O +> l))) {{A}}> (O +> r)) := by
  simp only [O, V, U, append_cons, append_nil]
  execute

lemma start_zero (b : Nat) (r : zB) :
    (default <{{B}} ((U ^ (5 + b)) +> (O +> (V +> (O +> r))))) [target_tm]⊢*
      (S0 (O +> ((U ^ (5 + b)) +> default)) 1 1 (O +> r)) := by
  refine zSt (sweep_B_U (5 + b) (O +> (V +> (O +> r)))) ?_
  unfold S0
  simp only [z06]
  exact start_zero_tail ((U ^ (5 + b)) +> default) r

lemma cleanup (l r : zB) :
    ((Z +> (O +> (U +> l))) <{{E}} (V +> (O +> r))) [target_tm]⊢*
      (S0 l 2 2 (O +> r)) := by
  unfold S0
  simp only [zLp, z05, append_nil, append_assoc, Z, O, U, V, append_cons]
  execute

lemma fourth_zero (b m : Nat) {r : zB} (hN : Num m r) (hB : m + 4 ≤ (8 + b) * 2) :
    Returns (1 + b) (O +> (O +> (Z +> (O +> (Z +> r))))) := by
  rcases count0 (O +> ((U ^ (5 + b)) +> default)) 0 0 m (Num.one hN) with ⟨s, hNs, hs⟩
  have hNs' : Num (1 + (1 + m) * 2) s := Num_eq hNs (by omega) rfl
  rcases pair (1 + m) hNs' with ⟨t, hNt, ht⟩
  have hNt' : Num (1 + (2 + m) * 2) (O +> t) := Num_eq (Num.one hNt) (by omega) rfl
  rcases counts ((U ^ (4 + b)) +> default) 1 0 1 (2 + m) hNt' with ⟨s', hNs', hs'⟩
  refine ⟨8 + b, s', ⟨by omega, 4 + m, Num_eq hNs' (by omega) rfl, by omega⟩, ?_⟩
  have hEnter : (K (1 + b) (O +> (O +> (Z +> (O +> (Z +> r)))))) [target_tm]⊢⁺
      (default <{{B}} ((U ^ (5 + b)) +> (O +> (V +> (O +> r))))) := enter b 0 r
  refine z02 hEnter ?_
  refine zSt (start_zero b r) ?_
  refine zSt (zPs hs) ?_
  unfold S1
  simp only [z05, append_nil]
  refine zSt (zPs (ht (Z +> (O +> ((U ^ (5 + b)) +> default))) 0)) ?_
  have h54 : (U ^ (5 + b)) +> default = U +> ((U ^ (4 + b)) +> default) := by
    have hb5 : 5 + b = 1 + (4 + b) := by omega
    rw [hb5, z07 U (4 + b) default]
  rw [h54]
  refine zSt (cleanup ((U ^ (4 + b)) +> default) t) ?_
  refine zSt hs' ?_
  have hEq : S0 ((U ^ (4 + b)) +> default) 0 4 s' = K (8 + b) s' := by
    unfold K S0
    simp only [z05, append_nil]
    rw [← append_assoc, ← zLp_add U 4 (4 + b)]
    have hb8 : 4 + (4 + b) = 8 + b := by omega
    rw [hb8]
  rw [hEq]
  finish

lemma index_power (j : Nat) : j ≤ 2 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hp : 0 < 2 ^ j := Nat.two_pow_pos j
    rw [Nat.pow_succ]
    omega

lemma fourth_positive (b j m : Nat) {r : zB} (hN : Num m r)
    (hB : 4 * 2 ^ (1 + j) * (1 + m * 2) ≤ 2 + b) :
    Returns (1 + b) (O +> (O +> (Z +> ((O ^ (2 + j)) +> (Z +> r))))) := by
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  have hP1 : 2 ^ (1 + j) = 2 ^ j * 2 := by rw [Nat.add_comm 1 j, Nat.pow_succ]
  have hJ : j ≤ 2 ^ j := index_power j
  have hM1 : 2 ^ (1 + j) ≤ 2 ^ (1 + j) * (1 + m * 2) :=
    Nat.le_mul_of_pos_right (2 ^ (1 + j)) (by omega)
  have hM2 : 1 + m * 2 ≤ 2 ^ (1 + j) * (1 + m * 2) :=
    Nat.le_mul_of_pos_left (1 + m * 2) (by omega)
  have hB' : 4 * (2 ^ (1 + j) * (1 + m * 2)) ≤ 2 + b := by
    rwa [← Nat.mul_assoc]
  have hBudget : 2 ^ j * 2 ≤ 7 + b := by omega
  have hBits0 : Bits (1 + j) 1 (O ++ (Z ^ j)) :=
    Bits_eq (Bits.one (Bits_zeros j)) rfl (by omega) rfl
  rcases internal_pairs (2 ^ j - 1) hBits0 (by omega) with ⟨w, hNw, hw⟩
  have hNw' : Bits (1 + j) (2 ^ (1 + j) - 1) w := Bits_eq hNw rfl (by omega) rfl
  have hEw : w = O ^ (1 + j) := Bits_ones (1 + j) hNw'
  subst hEw
  rcases clear_ones (1 + j) m (Num.one hN) with ⟨s, hNs, hs⟩
  have hNs' : Num (1 + (m + 1 + j) * 2) s := Num_eq hNs (by omega) rfl
  rcases counts ((U ^ (7 + b - 2 ^ (1 + j))) +> default) (2 ^ j) 0 (1 + j) (m + 1 + j) hNs'
    with ⟨t, hNt, ht⟩
  refine ⟨9 + b + j, t, ⟨by omega, m + 1 + j + 2 ^ (1 + j),
    Num_eq hNt (by omega) rfl, by omega⟩, ?_⟩
  have hj2 : 2 + j = 1 + (1 + j) := by omega
  rw [hj2]
  refine z02 (enter b (1 + j) r) ?_
  refine zSt (start_internal b j r) ?_
  have hw_step := hw default (7 + b - 2 ^ (1 + j)) 0 (O +> r)
  have hc_eq : (2 ^ j - 1) * 2 + (7 + b - 2 ^ (1 + j)) = 5 + b := by omega
  have hd_eq : 2 + 0 + (2 ^ j - 1) * 2 = 2 ^ j * 2 := by omega
  rw [hc_eq, Nat.add_zero] at hw_step
  rw [hd_eq] at hw_step
  refine zSt hw_step ?_
  unfold Internal
  refine zSt (exit_internal (1 + j)
    ((V ^ (2 ^ j * 2)) +> ((U ^ (7 + b - 2 ^ (1 + j))) +> default)) r) ?_
  have hs_step := hs ((V ^ (2 ^ j * 2)) +> ((U ^ (7 + b - 2 ^ (1 + j))) +> default)) 0
  simp only [Nat.add_zero, z06] at hs_step
  refine zSt hs_step ?_
  have ht_eq1 : 2 ^ j * 2 + 0 = 2 ^ j * 2 := by omega
  unfold S0 at ht
  rw [ht_eq1] at ht
  refine zSt ht ?_
  have hEq : (((U ^ (1 + (1 + j) + 2 ^ j * 2)) +>
      ((V ^ 0) +> ((U ^ (7 + b - 2 ^ (1 + j))) +> default))) {{A}}> t) =
      K (9 + b + j) t := by
    unfold K S0
    simp only [z05, append_nil]
    rw [← append_assoc, ← zLp_add U (1 + (1 + j) + 2 ^ j * 2) (7 + b - 2 ^ (1 + j))]
    have hb9 : 1 + (1 + j) + 2 ^ j * 2 + (7 + b - 2 ^ (1 + j)) = 9 + b + j := by omega
    rw [hb9]
  rw [hEq]
  finish

lemma Num_run {n : Nat} {r : zB} (h : Num n r) :
    ∃ j m s, r = (O ^ j) +> (Z +> s) ∧ Num m s ∧ 1 + n = 2 ^ j * (1 + m * 2) := by
  induction h with
  | nil =>
    exact ⟨0, 0, default, by simp [z05, Z], Num.nil, by omega⟩
  | @zero n r hN _ =>
    exact ⟨0, n, r, by simp [z05], hN, by omega⟩
  | @one n r _ ih =>
    rcases ih with ⟨j, m, s, rfl, hNs, hEq⟩
    refine ⟨1 + j, m, s, by rw [z07 O j (Z +> s)], hNs, ?_⟩
    have hp : 2 ^ (1 + j) = 2 * 2 ^ j := by rw [Nat.add_comm 1 j, Nat.pow_succ]; omega
    calc
      1 + (1 + n * 2) = 2 * (1 + n) := by omega
      _ = 2 * (2 ^ j * (1 + m * 2)) := by rw [hEq]
      _ = (2 * 2 ^ j) * (1 + m * 2) := by ring
      _ = 2 ^ (1 + j) * (1 + m * 2) := by rw [← hp]

lemma closed {b : Nat} {r : zB} (h : Safe b r) : Returns b r := by
  rcases h with ⟨hB, n, hN, hVb⟩
  cases b with
  | zero => omega
  | succ b =>
    have hb1 : b + 1 = 1 + b := by omega
    rw [hb1] at hVb ⊢
    rcases mod2 n with ⟨m, rfl⟩ | ⟨k, rfl⟩
    · exact branch1 b m r (Num_eq hN (by omega) rfl) (by omega)
    · rcases mod2 k with ⟨u, rfl⟩ | ⟨m, rfl⟩
      · rcases mod2 u with ⟨m, rfl⟩ | ⟨v, rfl⟩
        · exact branch3 b m r (Num_eq hN (by omega) rfl) (by omega)
        · rcases Num_odd (1 + (1 + v * 2) * 2 * 2) hN with ⟨r1, rfl, hN1⟩
          rcases Num_odd ((1 + v * 2) * 2) hN1 with ⟨r2, rfl, hN2⟩
          rcases Num_even (1 + v * 2) hN2 with ⟨r3, rfl, hN3⟩
          rcases Num_odd v hN3 with ⟨r4, rfl, hN4⟩
          rcases Num_run hN4 with ⟨j, m, s, rfl, hNs, hF⟩
          cases j with
          | zero =>
            simp only [z05, append_nil]
            have hPow0 : 2 ^ 0 = 1 := rfl
            rw [hPow0, Nat.one_mul] at hF
            exact fourth_zero b m hNs (by omega)
          | succ j =>
            have hj1 : j + 1 = 1 + j := by omega
            rw [hj1] at hF
            have hj2 : O +> ((O ^ (j + 1)) +> (Z +> s)) = (O ^ (2 + j)) +> (Z +> s) := by
              rw [hj1, ← z07 O (1 + j) (Z +> s)]
              have h11 : 1 + (1 + j) = 2 + j := by omega
              rw [h11]
            rw [hj2]
            refine fourth_positive b j m hNs ?_
            have hEq : 4 * 2 ^ (1 + j) * (1 + m * 2) = 4 * (1 + v) := by
              rw [Nat.mul_assoc, ← hF]
            omega
      · exact branch2 b m r (Num_eq hN (by omega) rfl) (by omega)

lemma start_to_K1 : (init []) [target_tm]⊢* K 1 (O +> default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold K S0
  simp only [z05, z06, append_nil, U, O, append_cons]
  execute

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ b r, c = K b r ∧ Safe b r)
    ⟨K 1 (O +> default), start_to_K1, 1, O +> default, rfl, le_refl 1, 0, Num.one Num.nil, by omega⟩ ?_
  rintro _ ⟨b, r, rfl, hSafe⟩
  rcases closed hSafe with ⟨b', r', hSafe', hStep⟩
  exact ⟨K b' r', hStep, b', r', rfl, hSafe'⟩

end BusyBeaver.M_1RB1RA_1LC1LE_1RF1LD_1RE0LD_0LB0RA_HHH0RC
