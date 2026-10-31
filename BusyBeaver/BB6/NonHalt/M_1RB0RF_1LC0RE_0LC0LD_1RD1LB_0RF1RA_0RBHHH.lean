/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 1 => none

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
@[simp] lemma z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
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

abbrev ld : zF := [1, 1, 0]
abbrev d0 : zF := [0, 0, 0]
abbrev d1 : zF := [1, 0, 0]
abbrev w1ld : zF := [1, 1, 1, 0]
abbrev lh : zB := [1] +> default

@[simp] lemma zDd : d0 +> (default : zB) = default := by simp [d0]

lemma z1_eq : [1] +> (d1 +> (default : zB)) = ld +> default := by simp [d1, ld]
lemma z0_eq : [1] +> (d0 +> (default : zB)) = d1 +> default := by simp [d0, d1]

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

open BusyBeaver.Longitudinal (DH0 toDHCfg SideRLs SegRLs)
open BusyBeaver.Longitudinal.BoundedConfig (segRLs_c_spec)

abbrev Call := DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)
abbrev ch : Call := ((B, []), (C, []))
abbrev ch' : Call := ((D, [1]), (C, []))

def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  toDHCfg (c.1, .right) l r

def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  toDHCfg ((C, []), .left) l r

abbrev Side := SideRLs target_tm
abbrev Seg := SegRLs target_tm

@[simp] lemma z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] lemma z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

lemma z08 {ls1 ls2 : List Call} {r1 r2 r3 : zB}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3 :=
  h1.trans h2

lemma zSc {ls1 ls2 : List Call} {w1 w2 : zF} {r1 r2 : zB}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1.sideRLs_concat h2

lemma zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 :=
  h1.trans h2

lemma seg_ch_d0 : Seg [ch] [] d0 d1 :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch_d1 : Seg [ch] [ch] d1 d0 :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch_ld : Seg [ch] [ch] ld ld :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch'_ld_atom : Seg [ch'] [ch, ch', ch] ld ld :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch_w1ld_atom : Seg [ch] [ch, ch', ch] w1ld ld :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch'_d1 : Seg [ch'] [] d1 (ld ++ [1]) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch'_d0_atom : Seg [ch'] [ch', ch] d0 ld :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch_1d1 : Seg [ch] [] ([1] ++ d1) (ld ++ [1]) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_ch_1d0 : Seg [ch] [] ([1] ++ d0) (d0 ++ [1]) :=
  segRLs_c_spec target_tm (T := 200) (by decide)

lemma seg_wall_ld (k : Nat) : Seg ([ch] ^ k) ([ch] ^ k) ld ld :=
  seg_ch_ld.wall_pow k

lemma seg_ch2_d0 : Seg [ch, ch] [ch] d0 d0 := zSg seg_ch_d0 seg_ch_d1
lemma seg_ch2_d1 : Seg [ch, ch] [ch] d1 d1 := zSg seg_ch_d1 seg_ch_d0

lemma seg_d0_even (k : Nat) : Seg ([ch] ^ (k * 2)) ([ch] ^ k) d0 d0 :=
  SegRLs.addmul (h := [ch]) (a := 2) (x := k) (b := 0) (c := 0) (.nil d0) seg_ch2_d0

lemma seg_d1_even (k : Nat) : Seg ([ch] ^ (k * 2)) ([ch] ^ k) d1 d1 :=
  SegRLs.addmul (h := [ch]) (a := 2) (x := k) (b := 0) (c := 0) (.nil d1) seg_ch2_d1

lemma seg_d0_odd (k : Nat) : Seg ([ch] ^ (1 + k * 2)) ([ch] ^ k) d0 d1 := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch_d0 (seg_d1_even k)

lemma seg_hx_ld (k : Nat) : Seg ([ch'] ++ [ch] ^ k) ([ch] ++ ([ch'] ++ [ch] ^ (1 + k))) ld ld := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch'_ld_atom (seg_wall_ld k)

lemma seg_h1_ld (k : Nat) : Seg ([ch] ^ (1 + k)) ([ch] ++ ([ch'] ++ [ch] ^ (1 + k))) w1ld ld := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch_w1ld_atom (seg_wall_ld k)

lemma seg_hx_d0 (k : Nat) : Seg ([ch'] ++ [ch] ^ k) ([ch'] ++ [ch] ^ (1 + k)) d0 ld := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch'_d0_atom (seg_wall_ld k)

inductive RD where
  | LD
  | D0
  | D1
deriving DecidableEq

inductive H where
  | hx
  | h1
deriving DecidableEq

open RD H

def toRC : List RD -> zB
  | [] => default
  | LD :: ls => ld +> toRC ls
  | D0 :: ls => d0 +> toRC ls
  | D1 :: ls => d1 +> toRC ls

def toH' : H -> zF
  | hx => []
  | h1 => [1]

def toH : H -> List Call
  | hx => [ch']
  | h1 => []

inductive Inc : List RD -> List RD -> Prop where
  | nil : Inc [] [D1]
  | d0 (r : List RD) : Inc (D0 :: r) (D1 :: r)
  | d1 {r r' : List RD} : Inc r r' -> Inc (D1 :: r) (D0 :: r')
  | ld {r r' : List RD} : Inc r r' -> Inc (LD :: r) (LD :: r')

inductive RIncs : H -> Nat -> List RD -> List RD -> Prop where
  | hx_ld {k : Nat} {r r1 r' : List RD} :
      Inc r r1 -> RIncs hx (1 + k) r1 r' -> RIncs hx k (LD :: r) (LD :: r')
  | hx_d1 {k : Nat} {r r' : List RD} :
      RIncs h1 k r r' -> RIncs hx k (D1 :: r) (LD :: r')
  | hx_d0 {k : Nat} {r r' : List RD} :
      RIncs hx (1 + k) r r' -> RIncs hx k (D0 :: r) (LD :: r')
  | h1_ld {k : Nat} {r r1 r' : List RD} :
      Inc r r1 -> RIncs hx (1 + k) r1 r' -> RIncs h1 (1 + k) (LD :: r) (LD :: r')
  | h1_d1 {k : Nat} {r r' : List RD} :
      RIncs h1 k r r' -> RIncs h1 (1 + k) (D1 :: r) (LD :: r')
  | h1_d0_0 {k : Nat} {r r' : List RD} :
      RIncs h1 k r r' -> RIncs h1 (1 + k * 2) (D0 :: r) (D0 :: r')
  | h1_d0_1 {k : Nat} {r r' : List RD} :
      RIncs h1 k r r' -> RIncs h1 (2 + k * 2) (D0 :: r) (D1 :: r')
  | h1_rh_0 :
      RIncs h1 0 [] [D1]
  | h1_rh_1 {k : Nat} {r' : List RD} :
      RIncs h1 k [] r' -> RIncs h1 (1 + k * 2) [] (D0 :: r')
  | h1_rh_2 {k : Nat} {r' : List RD} :
      RIncs h1 k [] r' -> RIncs h1 (2 + k * 2) [] (D1 :: r')
  | h1_z1 :
      RIncs h1 0 [D1] [LD]
  | h1_z0 :
      RIncs h1 0 [D0] [D1]

lemma Inc_spec {r r' : List RD} (h : Inc r r') :
    Side [ch] (toRC r) (toRC r') := by
  induction h with
  | nil =>
    simpa only [toRC, zDd] using zSc seg_ch_d0 (SideRLs.nil default)
  | d0 r =>
    exact zSc seg_ch_d0 (SideRLs.nil (toRC r))
  | d1 _ ih =>
    exact zSc seg_ch_d1 ih
  | ld _ ih =>
    exact zSc seg_ch_ld ih

lemma RIncs_spec {tp : H} {k : Nat} {r r' : List RD} (h : RIncs tp k r r') :
    Side (toH tp ++ [ch] ^ k) (toH' tp +> toRC r) (toRC r') := by
  induction h with
  | @hx_ld k r r1 r' h_inc _ ih =>
    simp only [toH, toH', toRC, append_nil] at ih ⊢
    exact zSc (seg_hx_ld k) (z08 (Inc_spec h_inc) ih)
  | @hx_d1 k r r' _ ih =>
    simp only [toH, toH', toRC, append_nil, List.nil_append] at ih ⊢
    have h1 := zSc seg_ch'_d1 (SideRLs.nil (toRC r))
    rw [append_assoc] at h1
    have h2 := zSc (seg_wall_ld k) ih
    exact z08 h1 h2
  | @hx_d0 k r r' _ ih =>
    simp only [toH, toH', toRC, append_nil] at ih ⊢
    exact zSc (seg_hx_d0 k) ih
  | @h1_ld k r r1 r' h_inc _ ih =>
    simp only [toH, toH', toRC, append_nil, List.nil_append] at ih ⊢
    have hw : [1] +> (ld +> toRC r) = w1ld +> toRC r := by rfl
    rw [hw]
    exact zSc (seg_h1_ld k) (z08 (Inc_spec h_inc) ih)
  | @h1_d1 k r r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    rw [zLp', <- append_assoc [1] d1 (toRC r)]
    have h1 := zSc seg_ch_1d1 (SideRLs.nil (toRC r))
    rw [append_assoc] at h1
    have h2 := zSc (seg_wall_ld k) ih
    exact z08 h1 h2
  | @h1_d0_0 k r r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    rw [zLp', <- append_assoc [1] d0 (toRC r)]
    have h1 := zSc seg_ch_1d0 (SideRLs.nil (toRC r))
    rw [append_assoc] at h1
    have h2 := zSc (seg_d0_even k) ih
    exact z08 h1 h2
  | @h1_d0_1 k r r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    have hk : 2 + k * 2 = 1 + (1 + k * 2) := by omega
    rw [hk, zLp', <- append_assoc [1] d0 (toRC r)]
    have h1 := zSc seg_ch_1d0 (SideRLs.nil (toRC r))
    rw [append_assoc] at h1
    have h2 := zSc (seg_d0_odd k) ih
    exact z08 h1 h2
  | h1_rh_0 =>
    simp only [toH, toH', toRC, z05, List.append_nil, <- z0_eq, zDd]
    exact SideRLs.nil ([1] +> default)
  | @h1_rh_1 k r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    have h_in : [1] +> (default : zB) = ([1] ++ d0) +> default := by
      rw [append_assoc, zDd]
    rw [zLp', h_in]
    have h1 := zSc seg_ch_1d0 (SideRLs.nil default)
    rw [append_assoc] at h1
    have h2 := zSc (seg_d0_even k) ih
    exact z08 h1 h2
  | @h1_rh_2 k r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    have hk : 2 + k * 2 = 1 + (1 + k * 2) := by omega
    have h_in : [1] +> (default : zB) = ([1] ++ d0) +> default := by
      rw [append_assoc, zDd]
    rw [hk, zLp', h_in]
    have h1 := zSc seg_ch_1d0 (SideRLs.nil default)
    rw [append_assoc] at h1
    have h2 := zSc (seg_d0_odd k) ih
    exact z08 h1 h2
  | h1_z1 =>
    simp only [toH, toH', toRC, z05, List.append_nil, z1_eq]
    exact SideRLs.nil (ld +> default)
  | h1_z0 =>
    simp only [toH, toH', toRC, z05, List.append_nil, z0_eq]
    exact SideRLs.nil (d1 +> default)

lemma Inc_total (r : List RD) : ∃ r', Inc r r' := by
  induction r with
  | nil => exact ⟨[D1], Inc.nil⟩
  | cons d r ih =>
    rcases ih with ⟨r', hI⟩
    cases d with
    | LD => exact ⟨LD :: r', Inc.ld hI⟩
    | D0 => exact ⟨D1 :: r, Inc.d0 r⟩
    | D1 => exact ⟨D0 :: r', Inc.d1 hI⟩

lemma Inc_fun {r r1 r2 : List RD} (h1 : Inc r r1) (h2 : Inc r r2) : r1 = r2 := by
  induction h1 generalizing r2 with
  | nil => cases h2; rfl
  | d0 r => cases h2; rfl
  | d1 _ ih => cases h2 with | d1 h2' => rw [ih h2']
  | ld _ ih => cases h2 with | ld h2' => rw [ih h2']

lemma RIncs_eqk {tp : H} {k k' : Nat} {r r' : List RD}
    (h : RIncs tp k r r') (hk : k = k') : RIncs tp k' r r' := by
  subst hk; exact h

lemma RIncs_Inc {tp : H} {k : Nat} {r r' r'' : List RD}
    (h : RIncs tp k r r') (hJ : Inc r' r'') : RIncs tp (1 + k) r r'' := by
  induction h generalizing r'' with
  | hx_ld h_inc h_ri ih =>
    cases hJ with
    | ld hJ' => exact RIncs.hx_ld h_inc (ih hJ')
  | hx_d1 h_ri ih =>
    cases hJ with
    | ld hJ' => exact RIncs.hx_d1 (ih hJ')
  | hx_d0 h_ri ih =>
    cases hJ with
    | ld hJ' => exact RIncs.hx_d0 (ih hJ')
  | h1_ld h_inc h_ri ih =>
    cases hJ with
    | ld hJ' => exact RIncs.h1_ld h_inc (ih hJ')
  | h1_d1 h_ri ih =>
    cases hJ with
    | ld hJ' => exact RIncs.h1_d1 (ih hJ')
  | @h1_d0_0 k r r' h_ri ih =>
    cases hJ with
    | d0 _ =>
      exact RIncs_eqk (RIncs.h1_d0_1 h_ri) (by omega)
  | @h1_d0_1 k r r' h_ri ih =>
    cases hJ with
    | d1 hJ' =>
      exact RIncs_eqk (RIncs.h1_d0_0 (ih hJ')) (by omega)
  | h1_rh_0 =>
    cases hJ with
    | d1 hJ' =>
      cases hJ' with
      | nil => exact RIncs.h1_rh_1 RIncs.h1_rh_0
  | @h1_rh_1 k r' h_ri ih =>
    cases hJ with
    | d0 _ =>
      exact RIncs_eqk (RIncs.h1_rh_2 h_ri) (by omega)
  | @h1_rh_2 k r' h_ri ih =>
    cases hJ with
    | d1 hJ' =>
      exact RIncs_eqk (RIncs.h1_rh_1 (ih hJ')) (by omega)
  | h1_z1 =>
    cases hJ with
    | ld hJ' =>
      cases hJ' with
      | nil => exact RIncs.h1_d1 RIncs.h1_rh_0
  | h1_z0 =>
    cases hJ with
    | d1 hJ' =>
      cases hJ' with
      | nil => exact RIncs.h1_d0_0 RIncs.h1_rh_0

lemma mod2 (n : Nat) : (∃ b, n = b * 2) ∨ (∃ b, n = 1 + b * 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; exact ⟨n / 2, by omega⟩
  · right; exact ⟨n / 2, by omega⟩

lemma RIncs_nxt_1 (k : Nat) : ∃ r, RIncs h1 k [] r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact ⟨[D1], RIncs.h1_rh_0⟩
    | succ m =>
      rcases mod2 m with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · rcases ih b (by omega) with ⟨r, hI⟩
        refine ⟨D0 :: r, ?_⟩
        exact RIncs_eqk (RIncs.h1_rh_1 hI) (by omega)
      · rcases ih b (by omega) with ⟨r, hI⟩
        refine ⟨D1 :: r, ?_⟩
        exact RIncs_eqk (RIncs.h1_rh_2 hI) (by omega)

lemma End_1 {tp : H} {m : Nat} {e w : List RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    ∀ q, m ≤ q -> ∃ w', RIncs h1 q w w' := by
  induction h with
  | hx_ld _ _ _ => cases htp
  | hx_d1 _ _ => cases htp
  | hx_d0 _ _ => cases htp
  | h1_ld _ _ _ => cases he
  | h1_d1 _ _ => cases he
  | h1_d0_0 _ _ => cases he
  | h1_d0_1 _ _ => cases he
  | h1_rh_0 =>
    intro q _
    cases q with
    | zero => exact ⟨[LD], RIncs.h1_z1⟩
    | succ q =>
      rcases RIncs_nxt_1 q with ⟨w', hI⟩
      exact ⟨LD :: w', RIncs_eqk (RIncs.h1_d1 hI) (by omega)⟩
  | @h1_rh_1 k r' h_ri ih =>
    intro q hq
    have ih' := ih rfl rfl
    rcases mod2 q with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · cases b with
      | zero => omega
      | succ b =>
        rcases ih' b (by omega) with ⟨w', hI2⟩
        exact ⟨D1 :: w', RIncs_eqk (RIncs.h1_d0_1 hI2) (by omega)⟩
    · rcases ih' b (by omega) with ⟨w', hI2⟩
      exact ⟨D0 :: w', RIncs.h1_d0_0 hI2⟩
  | @h1_rh_2 k r' h_ri ih =>
    intro q hq
    have ih' := ih rfl rfl
    cases q with
    | zero => omega
    | succ q =>
      rcases ih' q (by omega) with ⟨w', hI2⟩
      exact ⟨LD :: w', RIncs_eqk (RIncs.h1_d1 hI2) (by omega)⟩
  | h1_z1 => cases he
  | h1_z0 => cases he

lemma End_x {tp : H} {m : Nat} {e w : List RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    ∀ q, m ≤ 2 * q + 2 -> ∃ w', RIncs hx q w w' := by
  induction h with
  | hx_ld _ _ _ => cases htp
  | hx_d1 _ _ => cases htp
  | hx_d0 _ _ => cases htp
  | h1_ld _ _ _ => cases he
  | h1_d1 _ _ => cases he
  | h1_d0_0 _ _ => cases he
  | h1_d0_1 _ _ => cases he
  | h1_rh_0 =>
    intro q _
    rcases RIncs_nxt_1 q with ⟨w', hI⟩
    exact ⟨LD :: w', RIncs.hx_d1 hI⟩
  | @h1_rh_1 k r' h_ri ih =>
    intro q hq
    rcases ih rfl rfl (1 + q) (by omega) with ⟨w', hI2⟩
    exact ⟨LD :: w', RIncs.hx_d0 hI2⟩
  | @h1_rh_2 k r' h_ri _ =>
    intro q hq
    rcases End_1 h_ri rfl rfl q (by omega) with ⟨w', hI2⟩
    exact ⟨LD :: w', RIncs.hx_d1 hI2⟩
  | h1_z1 => cases he
  | h1_z0 => cases he

lemma inv_hx_ld {k : Nat} {r rK : List RD} (h : RIncs hx k (LD :: r) rK) :
    ∃ r1 rK', Inc r r1 ∧ RIncs hx (1 + k) r1 rK' ∧ rK = LD :: rK' := by
  cases h with
  | hx_ld h_inc h_ri => exact ⟨_, _, h_inc, h_ri, rfl⟩

lemma inv_hx_d1 {k : Nat} {r rK : List RD} (h : RIncs hx k (D1 :: r) rK) :
    ∃ rK', RIncs h1 k r rK' ∧ rK = LD :: rK' := by
  cases h with
  | hx_d1 h_ri => exact ⟨_, h_ri, rfl⟩

lemma inv_hx_d0 {k : Nat} {r rK : List RD} (h : RIncs hx k (D0 :: r) rK) :
    ∃ rK', RIncs hx (1 + k) r rK' ∧ rK = LD :: rK' := by
  cases h with
  | hx_d0 h_ri => exact ⟨_, h_ri, rfl⟩

lemma inv_h1_ld {k : Nat} {r rK : List RD} (h : RIncs h1 (1 + k) (LD :: r) rK) :
    ∃ r1 rK', Inc r r1 ∧ RIncs hx (1 + k) r1 rK' ∧ rK = LD :: rK' := by
  generalize hk : 1 + k = K at h
  cases h with
  | @h1_ld k0 _ r1 rK' h_inc h_ri =>
    have hk0 : k0 = k := by omega
    subst hk0
    exact ⟨r1, rK', h_inc, h_ri, rfl⟩

lemma inv_h1_d1 {k : Nat} {r rK : List RD} (h : RIncs h1 (1 + k) (D1 :: r) rK) :
    ∃ rK', RIncs h1 k r rK' ∧ rK = LD :: rK' := by
  generalize hk : 1 + k = K at h
  cases h with
  | @h1_d1 k0 _ rK' h_ri =>
    have hk0 : k0 = k := by omega
    subst hk0
    exact ⟨rK', h_ri, rfl⟩
  | h1_z1 => omega

lemma inv_h1_d0 {K : Nat} {r rK : List RD} (h : RIncs h1 K (D0 :: r) rK) :
    (∃ A rK', K = 1 + A * 2 ∧ RIncs h1 A r rK' ∧ rK = D0 :: rK') ∨
    (∃ A rK', K = 2 + A * 2 ∧ RIncs h1 A r rK' ∧ rK = D1 :: rK') ∨
    (K = 0 ∧ r = [] ∧ rK = [D1]) := by
  generalize hd : D0 :: r = r0 at h
  cases h with
  | h1_ld _ _ => cases hd
  | h1_d1 _ => cases hd
  | @h1_d0_0 A r_in rK' h_ri =>
    injection hd with _ hr; subst hr
    left; exact ⟨A, rK', rfl, h_ri, rfl⟩
  | @h1_d0_1 A r_in rK' h_ri =>
    injection hd with _ hr; subst hr
    right; left; exact ⟨A, rK', rfl, h_ri, rfl⟩
  | h1_rh_0 => cases hd
  | h1_rh_1 _ => cases hd
  | h1_rh_2 _ => cases hd
  | h1_z1 => cases hd
  | h1_z0 =>
    injection hd with _ hr; subst hr
    right; right; exact ⟨rfl, rfl, rfl⟩

lemma inv_z1 {K : Nat} {rK : List RD} (h : RIncs h1 K [D1] rK) :
    (K = 0 ∧ rK = [LD]) ∨
    (∃ K0 rK', K = 1 + K0 ∧ RIncs h1 K0 [] rK' ∧ rK = LD :: rK') := by
  generalize hd : ([D1] : List RD) = r0 at h
  cases h with
  | h1_ld _ _ => cases hd
  | @h1_d1 K0 r_in rK' h_ri =>
    injection hd with _ hr; subst hr
    right; exact ⟨K0, rK', rfl, h_ri, rfl⟩
  | h1_d0_0 _ => cases hd
  | h1_d0_1 _ => cases hd
  | h1_rh_0 => cases hd
  | h1_rh_1 _ => cases hd
  | h1_rh_2 _ => cases hd
  | h1_z1 => left; exact ⟨rfl, rfl⟩
  | h1_z0 => cases hd

def Inv (tp : H) (k j : Nat) (tq : H) (q : Nat) : Prop :=
  match tp, tq with
  | hx, hx => k ≤ q ∧ j ≤ q
  | h1, hx => k + 1 ≤ q ∧ j ≤ q
  | h1, h1 => (j = 0 ∧ 2 * k + 1 ≤ q) ∨ (1 ≤ j ∧ k + j ≤ q ∧ 1 ≤ q)
  | hx, h1 => False

lemma key {tp : H} {k : Nat} {r r1 : List RD} (D : RIncs tp k r r1) :
    ∀ j rK tq q, RIncs tp (k + j) r rK -> Inv tp k j tq q -> ∃ r2, RIncs tq q rK r2 := by
  induction D with
  | @hx_ld k r r1 r' Hi D ih =>
    intro j rK tq q E HI
    rcases inv_hx_ld E with ⟨r1', rK', Hi', E', rfl⟩
    rw [Inc_fun Hi' Hi] at E'
    cases tq with
    | h1 => cases HI
    | hx =>
      rcases Inc_total rK' with ⟨rK'', J⟩
      have E'' : RIncs hx ((1 + k) + (1 + j)) r1 rK'' :=
        RIncs_eqk (RIncs_Inc E' J) (by omega)
      rcases ih (1 + j) rK'' hx (1 + q) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
      exact ⟨LD :: r2, RIncs.hx_ld J I2⟩
  | @hx_d1 k r r' D ih =>
    intro j rK tq q E HI
    rcases inv_hx_d1 E with ⟨rK', E', rfl⟩
    cases tq with
    | h1 => cases HI
    | hx =>
      rcases Inc_total rK' with ⟨rK'', J⟩
      have E'' : RIncs h1 (k + (1 + j)) r rK'' :=
        RIncs_eqk (RIncs_Inc E' J) (by omega)
      rcases ih (1 + j) rK'' hx (1 + q) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
      exact ⟨LD :: r2, RIncs.hx_ld J I2⟩
  | @hx_d0 k r r' D ih =>
    intro j rK tq q E HI
    rcases inv_hx_d0 E with ⟨rK', E', rfl⟩
    cases tq with
    | h1 => cases HI
    | hx =>
      rcases Inc_total rK' with ⟨rK'', J⟩
      have E'' : RIncs hx ((1 + k) + (1 + j)) r rK'' :=
        RIncs_eqk (RIncs_Inc E' J) (by omega)
      rcases ih (1 + j) rK'' hx (1 + q) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
      exact ⟨LD :: r2, RIncs.hx_ld J I2⟩
  | @h1_ld k r r1 r' Hi D ih =>
    intro j rK tq q E HI
    have E0 : RIncs h1 (1 + (k + j)) (LD :: r) rK := RIncs_eqk E (by omega)
    rcases inv_h1_ld E0 with ⟨r1', rK', Hi', E', rfl⟩
    rw [Inc_fun Hi' Hi] at E'
    rcases Inc_total rK' with ⟨rK'', J⟩
    have E'' : RIncs hx ((1 + k) + (1 + j)) r1 rK'' :=
      RIncs_eqk (RIncs_Inc E' J) (by omega)
    cases tq with
    | hx =>
      rcases ih (1 + j) rK'' hx (1 + q) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
      exact ⟨LD :: r2, RIncs.hx_ld J I2⟩
    | h1 =>
      cases q with
      | zero => dsimp [Inv] at HI; omega
      | succ q0 =>
        rcases ih (1 + j) rK'' hx (1 + q0) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
        exact ⟨LD :: r2, RIncs_eqk (RIncs.h1_ld J I2) (by omega)⟩
  | @h1_d1 k r r' D ih =>
    intro j rK tq q E HI
    have E0 : RIncs h1 (1 + (k + j)) (D1 :: r) rK := RIncs_eqk E (by omega)
    rcases inv_h1_d1 E0 with ⟨rK', E', rfl⟩
    rcases Inc_total rK' with ⟨rK'', J⟩
    have E'' : RIncs h1 (k + (1 + j)) r rK'' :=
      RIncs_eqk (RIncs_Inc E' J) (by omega)
    cases tq with
    | hx =>
      rcases ih (1 + j) rK'' hx (1 + q) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
      exact ⟨LD :: r2, RIncs.hx_ld J I2⟩
    | h1 =>
      cases q with
      | zero => dsimp [Inv] at HI; omega
      | succ q0 =>
        rcases ih (1 + j) rK'' hx (1 + q0) E'' (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
        exact ⟨LD :: r2, RIncs_eqk (RIncs.h1_ld J I2) (by omega)⟩
  | @h1_d0_0 a r r' D ih =>
    intro j rK tq q E HI
    rcases inv_h1_d0 E with ⟨A, rK', HK, E', rfl⟩ | ⟨A, rK', HK, E', rfl⟩ | ⟨HK, _, _⟩
    · have E2 : RIncs h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hx =>
        rcases ih (A - a) rK' hx (1 + q) E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
        exact ⟨LD :: r2, RIncs.hx_d0 I2⟩
      | h1 =>
        rcases mod2 q with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · cases b with
          | zero => dsimp [Inv] at HI; omega
          | succ b =>
            rcases ih (A - a) rK' h1 b E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
            exact ⟨D1 :: r2, RIncs_eqk (RIncs.h1_d0_1 I2) (by omega)⟩
        · rcases ih (A - a) rK' h1 b E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
          exact ⟨D0 :: r2, RIncs.h1_d0_0 I2⟩
    · have E2 : RIncs h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hx =>
        rcases ih (A - a) rK' h1 q E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
        exact ⟨LD :: r2, RIncs.hx_d1 I2⟩
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          rcases ih (A - a) rK' h1 q0 E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
          exact ⟨LD :: r2, RIncs_eqk (RIncs.h1_d1 I2) (by omega)⟩
    · omega
  | @h1_d0_1 a r r' D ih =>
    intro j rK tq q E HI
    rcases inv_h1_d0 E with ⟨A, rK', HK, E', rfl⟩ | ⟨A, rK', HK, E', rfl⟩ | ⟨HK, _, _⟩
    · have E2 : RIncs h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hx =>
        rcases ih (A - a) rK' hx (1 + q) E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
        exact ⟨LD :: r2, RIncs.hx_d0 I2⟩
      | h1 =>
        rcases mod2 q with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · cases b with
          | zero => dsimp [Inv] at HI; omega
          | succ b =>
            rcases ih (A - a) rK' h1 b E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
            exact ⟨D1 :: r2, RIncs_eqk (RIncs.h1_d0_1 I2) (by omega)⟩
        · rcases ih (A - a) rK' h1 b E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
          exact ⟨D0 :: r2, RIncs.h1_d0_0 I2⟩
    · have E2 : RIncs h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hx =>
        rcases ih (A - a) rK' h1 q E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
        exact ⟨LD :: r2, RIncs.hx_d1 I2⟩
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          rcases ih (A - a) rK' h1 q0 E2 (by dsimp [Inv] at HI ⊢; omega) with ⟨r2, I2⟩
          exact ⟨LD :: r2, RIncs_eqk (RIncs.h1_d1 I2) (by omega)⟩
    · omega
  | h1_rh_0 =>
    intro j rK tq q E HI
    cases tq with
    | hx => exact End_x E rfl rfl q (by dsimp [Inv] at HI; omega)
    | h1 => exact End_1 E rfl rfl q (by dsimp [Inv] at HI; omega)
  | h1_rh_1 _ _ =>
    intro j rK tq q E HI
    cases tq with
    | hx => exact End_x E rfl rfl q (by dsimp [Inv] at HI; omega)
    | h1 => exact End_1 E rfl rfl q (by dsimp [Inv] at HI; omega)
  | h1_rh_2 _ _ =>
    intro j rK tq q E HI
    cases tq with
    | hx => exact End_x E rfl rfl q (by dsimp [Inv] at HI; omega)
    | h1 => exact End_1 E rfl rfl q (by dsimp [Inv] at HI; omega)
  | h1_z1 =>
    intro j rK tq q E HI
    rcases inv_z1 E with ⟨HK, rfl⟩ | ⟨K0, rK', HK, E', rfl⟩
    · cases tq with
      | hx =>
        rcases RIncs_nxt_1 (1 + q) with ⟨w, I⟩
        exact ⟨LD :: LD :: w, RIncs.hx_ld Inc.nil (RIncs.hx_d1 I)⟩
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          rcases RIncs_nxt_1 (1 + q0) with ⟨w, I⟩
          exact ⟨LD :: LD :: w, RIncs_eqk (RIncs.h1_ld Inc.nil (RIncs.hx_d1 I)) (by omega)⟩
    · rcases Inc_total rK' with ⟨rK'', J⟩
      have E'' := RIncs_Inc E' J
      cases tq with
      | hx =>
        rcases End_x E'' rfl rfl (1 + q) (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
        exact ⟨LD :: w, RIncs.hx_ld J I⟩
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          rcases End_x E'' rfl rfl (1 + q0) (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
          exact ⟨LD :: w, RIncs_eqk (RIncs.h1_ld J I) (by omega)⟩
  | h1_z0 =>
    intro j rK tq q E HI
    rcases inv_h1_d0 E with ⟨A, rK', HK, E', rfl⟩ | ⟨A, rK', HK, E', rfl⟩ | ⟨HK, _, rfl⟩
    · cases tq with
      | hx =>
        rcases End_x E' rfl rfl (1 + q) (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
        exact ⟨LD :: w, RIncs.hx_d0 I⟩
      | h1 =>
        rcases mod2 q with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · cases b with
          | zero => dsimp [Inv] at HI; omega
          | succ b =>
            rcases End_1 E' rfl rfl b (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
            exact ⟨D1 :: w, RIncs_eqk (RIncs.h1_d0_1 I) (by omega)⟩
        · rcases End_1 E' rfl rfl b (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
          exact ⟨D0 :: w, RIncs.h1_d0_0 I⟩
    · cases tq with
      | hx =>
        rcases End_1 E' rfl rfl q (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
        exact ⟨LD :: w, RIncs.hx_d1 I⟩
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          rcases End_1 E' rfl rfl q0 (by dsimp [Inv] at HI; omega) with ⟨w, I⟩
          exact ⟨LD :: w, RIncs_eqk (RIncs.h1_d1 I) (by omega)⟩
    · cases tq with
      | hx =>
        rcases RIncs_nxt_1 q with ⟨w, I⟩
        exact ⟨LD :: w, RIncs.hx_d1 I⟩
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          rcases RIncs_nxt_1 q0 with ⟨w, I⟩
          exact ⟨LD :: w, RIncs_eqk (RIncs.h1_d1 I) (by omega)⟩

lemma domain {r r' : List RD} (h : RIncs hx 0 r r') : ∃ r'', RIncs hx 0 r' r'' :=
  key h 0 r' hx 0 h (by dsimp [Inv]; omega)

def S' (r : List RD) : Cfg (Fin 2) (Fin 6) :=
  zCR lh ch' (toRC r)

lemma turn_lh (r : List RD) : (zCL lh (toRC r)) [target_tm]⊢⁺ S' r := by
  unfold zCL S' zCR lh toDHCfg
  simp only [append_cons, append_nil]
  execute

lemma BigStep {r r' : List RD} (h : RIncs hx 0 r r') :
    (S' r) [target_tm]⊢⁺ (S' r') := by
  have hS := RIncs_spec h
  simp only [toH, toH', z05, List.append_nil, append_nil] at hS
  exact zPt (hS.elim_single lh) (turn_lh r')

lemma start_to_S' : (init []) [target_tm]⊢⁺ S' [LD, D1] := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold S' zCR lh toDHCfg
  dsimp [toRC, ld, d1]
  execute

lemma init_r : ∃ r', RIncs hx 0 [LD, D1] r' := by
  refine ⟨[LD, LD, LD, D1, D1], ?_⟩
  refine RIncs.hx_ld (Inc.d1 Inc.nil) ?_
  refine RIncs.hx_d0 ?_
  refine RIncs.hx_d1 ?_
  exact RIncs.h1_rh_2 RIncs.h1_rh_0

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun c => ∃ r r', c = S' r ∧ RIncs hx 0 r r')
    ⟨S' [LD, D1], zPs start_to_S', [LD, D1], ?_⟩ ?_
  · rcases init_r with ⟨r', hr'⟩
    exact ⟨r', rfl, hr'⟩
  · rintro _ ⟨r, r', rfl, hR⟩
    rcases domain hR with ⟨r'', hR'⟩
    exact ⟨S' r', BigStep hR, r', r'', rfl, hR'⟩

end BusyBeaver.M_1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RBHHH
