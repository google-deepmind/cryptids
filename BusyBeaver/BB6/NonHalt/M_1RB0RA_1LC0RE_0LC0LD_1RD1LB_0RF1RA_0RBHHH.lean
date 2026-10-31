/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
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

private def A : Fin 6 := 0
private def B : Fin 6 := 1
private def C : Fin 6 := 2
private def D : Fin 6 := 3
private def E : Fin 6 := 4
private def F : Fin 6 := 5

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[simp] private lemma zMz (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 0 = some config := rfl
@[simp] private lemma zMo (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 1 = step M config := rfl
@[simp] private lemma zMs (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] private lemma z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] private lemma zDh : (default : zB).head = 0 := rfl
@[simp] private lemma zDt : (default : zB).tail = default := rfl
@[simp] private lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] private lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] private lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

private lemma zSm (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
private lemma z01 (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
private lemma zMa (tm : Machine (Fin 2) (Fin 6)) (c_1 : Cfg (Fin 2) (Fin 6)) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
private lemma zMt (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
private lemma zPs {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 : Cfg (Fin 2) (Fin 6)} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
private lemma zPt {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c_1 c_2 c_3 n m hn hm⟩
private lemma z02 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
private lemma z03 {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂

local macro "finish" : tactic =>
  `(tactic| exact ⟨0, rfl⟩)
local macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
local macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | gstep)))

private abbrev ld : zF := [1, 1, 0]
private abbrev d0 : zF := [0, 0, 0]
private abbrev d1 : zF := [1, 0, 0]
private abbrev w1ld : zF := [1, 1, 1, 0]
private abbrev w1d0 : zF := [1, 0, 0, 0]
private abbrev w1d1 : zF := [1, 1, 0, 0]
private abbrev lh : zB := [1] +> default

@[simp] private lemma zDd : d0 +> (default : zB) = default := by simp [d0]

private lemma z1_eq : [1] +> (d1 +> (default : zB)) = ld +> default := by simp [d1, ld]
private lemma z0_eq : [1] +> (d0 +> (default : zB)) = d1 +> default := by simp [d0, d1]

private inductive Call where
  | ch
  | ch'

private def zCs : Call -> Fin 6
  | .ch => B
  | .ch' => D

private def zCw : Call -> zF
  | .ch => []
  | .ch' => [1]

private def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((zCw c +> l) {{zCs c}}> r)

private def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l <{{C}} r)

private def z04 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l, (zCR l c r1) [target_tm]⊢⁺ (zCL l r2)

private inductive Side : List Call -> zB -> zB -> Prop where
  | nil (r : zB) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : zB} :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3

private def Seg (ls_in ls_out : List Call) (w1 w2 : zF) : Prop :=
  ∀ r1 r2, Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)

@[simp] private lemma z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] private lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] private lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] private lemma z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

private lemma z07 {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, zLp, zLp, ih, List.append_assoc]

private lemma z08 {ls1 ls2 : List Call} {r1 r2 r3 : zB}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)

private lemma z09 {ls1 ls2 : List Call} {r1 r3 : zB}
    (h : Side (ls1 ++ ls2) r1 r3) : ∃ r2, Side ls1 r1 r2 ∧ Side ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1, Side.nil r1, h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc, hrest⟩
    rcases ih hrest with ⟨r2, h1, h2⟩
    exact ⟨r2, Side.cons hc h1, h2⟩

private lemma z0a (w : zF) : Seg [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)

private lemma zSc {ls1 ls2 : List Call} {w1 w2 : zF} {r1 r2 : zB}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2

private lemma zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases z09 h with ⟨r2, ha, hb⟩
  exact z08 (h1 r1 r2 ha) (h2 r2 r3 hb)

private lemma zS4 {c : Call} {w1 w2 : zF}
    (h1 : ∀ l r, (zCR l c (w1 +> r)) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)

private lemma zS2 {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r, (zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r, (zCL (mid +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc (mid +> l)) (h2 l r2))

private lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r, (zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r, (zCL (mid1 +> l) r) [target_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r, (zCL (mid2 +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c1, c2] w1 w2 := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1, hrest⟩
  rcases hrest with _ | ⟨hc2, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1)
    (zPt (hc1 (mid1 +> l))
      (zPt (h2 l _)
        (zPt (hc2 (mid2 +> l)) (h3 l r3))))

private lemma seg_ch_d0 : Seg [.ch] [] d0 d1 :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1; simp only [append_cons, append_nil]; execute)

private lemma seg_ch_d1 : Seg [.ch] [.ch] d1 d0 :=
  zS2 (mid := [0, 0, 0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons, append_nil]; execute)

private lemma seg_ch_ld : Seg [.ch] [.ch] ld ld :=
  zS2 (mid := [1, 1, 0])
    (fun l r => by unfold zCR zCw zCs ld; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL ld; simp only [append_cons, append_nil]; execute)

private lemma seg_ch'_ld_atom : Seg [.ch'] [.ch, .ch'] ld ld :=
  zS5 (mid1 := [1, 0, 1, 0]) (mid2 := [1, 1, 0])
    (fun l r => by unfold zCR zCw zCs ld; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL ld; simp only [append_cons, append_nil]; execute)

private lemma seg_ch_w1ld_atom : Seg [.ch] [.ch, .ch'] w1ld ld :=
  zS5 (mid1 := [1, 0, 1, 0]) (mid2 := [1, 1, 0])
    (fun l r => by unfold zCR zCw zCs w1ld; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL ld; simp only [append_cons, append_nil]; execute)

private lemma seg_ch'_d1 : Seg [.ch'] [] d1 (ld ++ [1]) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 ld; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

private lemma seg_ch'_d0_atom : Seg [.ch'] [.ch', .ch] d0 ld :=
  zS5 (mid1 := [1, 1, 1]) (mid2 := [1, 1, 0])
    (fun l r => by unfold zCR zCw zCs d0; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons, append_nil]; execute)
    (fun l r => by unfold zCL ld; simp only [append_cons, append_nil]; execute)

private lemma seg_ch_1d1 : Seg [.ch] [] ([1] ++ d1) (ld ++ [1]) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 ld; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

private lemma seg_ch_1d0 : Seg [.ch] [] ([1] ++ d0) (d0 ++ [1]) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

private lemma seg_wall_ld (k : Nat) : Seg ([.ch] ^ k) ([.ch] ^ k) ld ld := by
  induction k with
  | zero => exact z0a ld
  | succ k ih =>
    rw [zLp]
    exact zSg seg_ch_ld ih

private lemma zSa {w2 : zF} (hw : Seg [.ch, .ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0a w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq, z07, zLp]
    exact zSg hw ih

private lemma seg_ch2_d0 : Seg [.ch, .ch] [.ch] d0 d0 := zSg seg_ch_d0 seg_ch_d1
private lemma seg_ch2_d1 : Seg [.ch, .ch] [.ch] d1 d1 := zSg seg_ch_d1 seg_ch_d0

private lemma seg_d0_even (k : Nat) : Seg ([.ch] ^ (k * 2)) ([.ch] ^ k) d0 d0 :=
  zSa seg_ch2_d0 k

private lemma seg_d1_even (k : Nat) : Seg ([.ch] ^ (k * 2)) ([.ch] ^ k) d1 d1 :=
  zSa seg_ch2_d1 k

private lemma seg_d0_odd (k : Nat) : Seg ([.ch] ^ (1 + k * 2)) ([.ch] ^ k) d0 d1 := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch_d0 (seg_d1_even k)

private lemma seg_hx_ld (k : Nat) : Seg ([.ch'] ++ [.ch] ^ k) ([.ch] ++ ([.ch'] ++ [.ch] ^ k)) ld ld := by
  simpa only [List.cons_append, List.nil_append] using zSg seg_ch'_ld_atom (seg_wall_ld k)

private lemma seg_h1_ld (k : Nat) : Seg ([.ch] ^ (1 + k)) ([.ch] ++ ([.ch'] ++ [.ch] ^ k)) w1ld ld := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch_w1ld_atom (seg_wall_ld k)

private lemma seg_hx_d0 (k : Nat) : Seg ([.ch'] ++ [.ch] ^ k) ([.ch'] ++ [.ch] ^ (1 + k)) d0 ld := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg seg_ch'_d0_atom (seg_wall_ld k)

private inductive RD where
  | LD
  | D0
  | D1
  | W1LD
  | W1D0
  | W1D1
deriving DecidableEq

private inductive H where
  | hi
  | hx
  | h1
deriving DecidableEq


private def toRC : List RD -> zB
  | [] => default
  | RD.LD :: ls => ld +> toRC ls
  | RD.D0 :: ls => d0 +> toRC ls
  | RD.D1 :: ls => d1 +> toRC ls
  | RD.W1LD :: ls => w1ld +> toRC ls
  | RD.W1D0 :: ls => w1d0 +> toRC ls
  | RD.W1D1 :: ls => w1d1 +> toRC ls

private def toH' : H -> zF
  | H.hi => []
  | H.hx => []
  | H.h1 => [1]

private def toH : H -> List Call
  | H.hi => [.ch]
  | H.hx => [.ch']
  | H.h1 => []

private inductive RIncs : H -> Nat -> List RD -> List RD -> Prop where
  | hi_nil : RIncs H.hi 0 [] [RD.D1]
  | hi_d0 (r : List RD) : RIncs H.hi 0 (RD.D0 :: r) (RD.D1 :: r)
  | hi_d1 {r r' : List RD} : RIncs H.hi 0 r r' -> RIncs H.hi 0 (RD.D1 :: r) (RD.D0 :: r')
  | hi_ld {r r' : List RD} : RIncs H.hi 0 r r' -> RIncs H.hi 0 (RD.LD :: r) (RD.LD :: r')
  | hi_w1d0 {r r' : List RD} : RIncs H.h1 0 r r' -> RIncs H.hi 0 (RD.W1D0 :: r) (RD.D0 :: r')
  | hi_w1d1 {r r' : List RD} : RIncs H.h1 0 r r' -> RIncs H.hi 0 (RD.W1D1 :: r) (RD.LD :: r')
  | hi_w1ld {r r1 r' : List RD} :
      RIncs H.hi 0 r r1 -> RIncs H.hx 0 r1 r' -> RIncs H.hi 0 (RD.W1LD :: r) (RD.LD :: r')
  | hx_ld {k : Nat} {r r1 r' : List RD} :
      RIncs H.hi 0 r r1 -> RIncs H.hx k r1 r' -> RIncs H.hx k (RD.LD :: r) (RD.LD :: r')
  | hx_d1 {k : Nat} {r r' : List RD} :
      RIncs H.h1 k r r' -> RIncs H.hx k (RD.D1 :: r) (RD.LD :: r')
  | hx_d0 {k : Nat} {r r' : List RD} :
      RIncs H.hx (1 + k) r r' -> RIncs H.hx k (RD.D0 :: r) (RD.LD :: r')
  | h1_ld {k : Nat} {r r1 r' : List RD} :
      RIncs H.hi 0 r r1 -> RIncs H.hx k r1 r' -> RIncs H.h1 (1 + k) (RD.LD :: r) (RD.LD :: r')
  | h1_d1 {k : Nat} {r r' : List RD} :
      RIncs H.h1 k r r' -> RIncs H.h1 (1 + k) (RD.D1 :: r) (RD.LD :: r')
  | h1_d0_0 {k : Nat} {r r' : List RD} :
      RIncs H.h1 k r r' -> RIncs H.h1 (1 + k * 2) (RD.D0 :: r) (RD.D0 :: r')
  | h1_d0_1 {k : Nat} {r r' : List RD} :
      RIncs H.h1 k r r' -> RIncs H.h1 (2 + k * 2) (RD.D0 :: r) (RD.D1 :: r')
  | h1_rh_0 :
      RIncs H.h1 0 [] [RD.D1]
  | h1_rh_1 {k : Nat} {r' : List RD} :
      RIncs H.h1 k [] r' -> RIncs H.h1 (1 + k * 2) [] (RD.D0 :: r')
  | h1_rh_2 {k : Nat} {r' : List RD} :
      RIncs H.h1 k [] r' -> RIncs H.h1 (2 + k * 2) [] (RD.D1 :: r')
  | h1_z1 :
      RIncs H.h1 0 [RD.D1] [RD.LD]
  | h1_z0 :
      RIncs H.h1 0 [RD.D0] [RD.D1]
  | h1_z_ld {r r1 r2 : List RD} :
      RIncs H.hi 0 r r1 -> RIncs H.hx 0 r1 r2 -> RIncs H.h1 0 (RD.LD :: r) (RD.W1LD :: r)
  | h1_z_d1 {r r1 : List RD} :
      r ≠ [] -> RIncs H.h1 0 r r1 -> RIncs H.h1 0 (RD.D1 :: r) (RD.W1D1 :: r)
  | h1_z_d0 {r r1 : List RD} :
      r ≠ [] -> RIncs H.h1 0 r r1 -> RIncs H.h1 0 (RD.D0 :: r) (RD.W1D0 :: r)

private lemma side_nil_eq {r1 r2 : zB} (h : Side [] r1 r2) : r1 = r2 := by
  cases h; rfl

private lemma RIncs_spec {tp : H} {k : Nat} {r r' : List RD} (h : RIncs tp k r r') :
    Side (toH tp ++ [.ch] ^ k) (toH' tp +> toRC r) (toRC r') := by
  induction h with
  | hi_nil =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil]
    simpa only [zDd] using zSc seg_ch_d0 (Side.nil default)
  | hi_d0 r =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil]
    exact zSc seg_ch_d0 (Side.nil (toRC r))
  | hi_d1 _ ih =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil] at ih ⊢
    exact zSc seg_ch_d1 ih
  | hi_ld _ ih =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil] at ih ⊢
    exact zSc seg_ch_ld ih
  | hi_w1d0 _ ih =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil] at ih ⊢
    have heq := side_nil_eq ih
    have hw : w1d0 = [1] ++ d0 := rfl
    rw [hw, <- heq, <- append_assoc d0 [1] (toRC _)]
    exact zSc seg_ch_1d0 (Side.nil _)
  | hi_w1d1 _ ih =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil] at ih ⊢
    have heq := side_nil_eq ih
    have hw : w1d1 = [1] ++ d1 := rfl
    rw [hw, <- heq, <- append_assoc ld [1] (toRC _)]
    exact zSc seg_ch_1d1 (Side.nil _)
  | hi_w1ld _ _ ih1 ih2 =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil] at ih1 ih2 ⊢
    exact zSc seg_ch_w1ld_atom (z08 ih1 ih2)
  | @hx_ld k r r1 r' _ _ ih1 ih2 =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil] at ih1 ih2 ⊢
    exact zSc (seg_hx_ld k) (z08 ih1 ih2)
  | @hx_d1 k r r' _ ih =>
    simp only [toH, toH', toRC, append_nil, List.nil_append] at ih ⊢
    have H.h1 := zSc seg_ch'_d1 (Side.nil (toRC r))
    rw [append_assoc] at H.h1
    have h2 := zSc (seg_wall_ld k) ih
    exact z08 H.h1 h2
  | @hx_d0 k r r' _ ih =>
    simp only [toH, toH', toRC, append_nil] at ih ⊢
    exact zSc (seg_hx_d0 k) ih
  | @h1_ld k r r1 r' _ _ ih1 ih2 =>
    simp only [toH, toH', toRC, z05, List.append_nil, append_nil, List.nil_append] at ih1 ih2 ⊢
    have hw : [1] +> (ld +> toRC r) = w1ld +> toRC r := rfl
    rw [hw]
    exact zSc (seg_h1_ld k) (z08 ih1 ih2)
  | @h1_d1 k r r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    rw [zLp', <- append_assoc [1] d1 (toRC r)]
    have H.h1 := zSc seg_ch_1d1 (Side.nil (toRC r))
    rw [append_assoc] at H.h1
    have h2 := zSc (seg_wall_ld k) ih
    exact z08 H.h1 h2
  | @h1_d0_0 k r r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    rw [zLp', <- append_assoc [1] d0 (toRC r)]
    have H.h1 := zSc seg_ch_1d0 (Side.nil (toRC r))
    rw [append_assoc] at H.h1
    have h2 := zSc (seg_d0_even k) ih
    exact z08 H.h1 h2
  | @h1_d0_1 k r r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    have hk : 2 + k * 2 = 1 + (1 + k * 2) := by omega
    rw [hk, zLp', <- append_assoc [1] d0 (toRC r)]
    have H.h1 := zSc seg_ch_1d0 (Side.nil (toRC r))
    rw [append_assoc] at H.h1
    have h2 := zSc (seg_d0_odd k) ih
    exact z08 H.h1 h2
  | h1_rh_0 =>
    simp only [toH, toH', toRC, z05, List.append_nil, <- z0_eq, zDd]
    exact Side.nil ([1] +> default)
  | @h1_rh_1 k r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    have h_in : [1] +> (default : zB) = ([1] ++ d0) +> default := by
      rw [append_assoc, zDd]
    rw [zLp', h_in]
    have H.h1 := zSc seg_ch_1d0 (Side.nil default)
    rw [append_assoc] at H.h1
    have h2 := zSc (seg_d0_even k) ih
    exact z08 H.h1 h2
  | @h1_rh_2 k r' _ ih =>
    simp only [toH, toH', toRC, List.nil_append] at ih ⊢
    have hk : 2 + k * 2 = 1 + (1 + k * 2) := by omega
    have h_in : [1] +> (default : zB) = ([1] ++ d0) +> default := by
      rw [append_assoc, zDd]
    rw [hk, zLp', h_in]
    have H.h1 := zSc seg_ch_1d0 (Side.nil default)
    rw [append_assoc] at H.h1
    have h2 := zSc (seg_d0_odd k) ih
    exact z08 H.h1 h2
  | h1_z1 =>
    simp only [toH, toH', toRC, z05, List.append_nil, z1_eq]
    exact Side.nil (ld +> default)
  | h1_z0 =>
    simp only [toH, toH', toRC, z05, List.append_nil, z0_eq]
    exact Side.nil (d1 +> default)
  | h1_z_ld _ _ _ _ =>
    simp only [toH, toH', toRC, z05, List.append_nil]
    exact Side.nil _
  | h1_z_d1 _ _ _ =>
    simp only [toH, toH', toRC, z05, List.append_nil]
    exact Side.nil _
  | h1_z_d0 _ _ _ =>
    simp only [toH, toH', toRC, z05, List.append_nil]
    exact Side.nil _

private lemma RIncs_eqk {tp : H} {k k' : Nat} {r r' : List RD}
    (h : RIncs tp k r r') (hk : k = k') : RIncs tp k' r r' := by
  subst hk; exact h

private lemma RIncs_fun {tp : H} {k : Nat} {r r1 r2 : List RD}
    (h1 : RIncs tp k r r1) (h2 : RIncs tp k r r2) : r1 = r2 := by
  induction h1 generalizing r2 with
  | hi_nil => cases h2; rfl
  | hi_d0 _ => cases h2; rfl
  | hi_d1 _ ih => cases h2 with | hi_d1 h2' => rw [ih h2']
  | hi_ld _ ih => cases h2 with | hi_ld h2' => rw [ih h2']
  | hi_w1d0 _ ih => cases h2 with | hi_w1d0 h2' => rw [ih h2']
  | hi_w1d1 _ ih => cases h2 with | hi_w1d1 h2' => rw [ih h2']
  | hi_w1ld _ _ ih1 ih2 =>
    cases h2 with | hi_w1ld h2a h2b => rw [← ih1 h2a] at h2b; rw [ih2 h2b]
  | hx_ld _ _ ih1 ih2 =>
    cases h2 with | hx_ld h2a h2b => rw [← ih1 h2a] at h2b; rw [ih2 h2b]
  | hx_d1 _ ih => cases h2 with | hx_d1 h2' => rw [ih h2']
  | hx_d0 _ ih => cases h2 with | hx_d0 h2' => rw [ih h2']
  | @h1_ld k0 r r1_a r'_a h1a h1b ih1 ih2 =>
    generalize hk : 1 + k0 = K at h2
    cases h2 with
    | @h1_ld k2 _ _ _ h2a h2b =>
      have hk' : k2 = k0 := by omega
      subst hk'; rw [← ih1 h2a] at h2b; rw [ih2 h2b]
    | h1_z_ld _ _ => omega
  | @h1_d1 k0 r r'_a h1a ih =>
    generalize hk : 1 + k0 = K at h2
    cases h2 with
    | @h1_d1 k2 _ _ h2a =>
      have hk' : k2 = k0 := by omega
      subst hk'; rw [ih h2a]
    | h1_z1 => omega
    | h1_z_d1 _ _ => omega
  | @h1_d0_0 k0 r r'_a h1a ih =>
    generalize hk : 1 + k0 * 2 = K at h2
    cases h2 with
    | @h1_d0_0 k2 _ _ h2a =>
      have hk' : k2 = k0 := by omega
      subst hk'; rw [ih h2a]
    | @h1_d0_1 k2 _ _ _ => omega
    | h1_z0 => omega
    | h1_z_d0 _ _ => omega
  | @h1_d0_1 k0 r r'_a h1a ih =>
    generalize hk : 2 + k0 * 2 = K at h2
    cases h2 with
    | @h1_d0_0 k2 _ _ _ => omega
    | @h1_d0_1 k2 _ _ h2a =>
      have hk' : k2 = k0 := by omega
      subst hk'; rw [ih h2a]
    | h1_z0 => omega
    | h1_z_d0 _ _ => omega
  | h1_rh_0 =>
    generalize hk : (0 : Nat) = K at h2
    cases h2 with
    | h1_rh_0 => rfl
    | h1_rh_1 _ => omega
    | h1_rh_2 _ => omega
  | @h1_rh_1 k0 r'_a h1a ih =>
    generalize hk : 1 + k0 * 2 = K at h2
    cases h2 with
    | h1_rh_0 => omega
    | @h1_rh_1 k2 _ h2a =>
      have hk' : k2 = k0 := by omega
      subst hk'; rw [ih h2a]
    | @h1_rh_2 k2 _ _ => omega
  | @h1_rh_2 k0 r'_a h1a ih =>
    generalize hk : 2 + k0 * 2 = K at h2
    cases h2 with
    | h1_rh_0 => omega
    | @h1_rh_1 k2 _ _ => omega
    | @h1_rh_2 k2 _ h2a =>
      have hk' : k2 = k0 := by omega
      subst hk'; rw [ih h2a]
  | h1_z1 =>
    generalize hk : (0 : Nat) = K at h2
    cases h2 with
    | h1_d1 _ => omega
    | h1_z1 => rfl
    | h1_z_d1 hne _ => exact False.elim (hne rfl)
  | h1_z0 =>
    generalize hk : (0 : Nat) = K at h2
    cases h2 with
    | h1_d0_0 _ => omega
    | h1_d0_1 _ => omega
    | h1_z0 => rfl
    | h1_z_d0 hne _ => exact False.elim (hne rfl)
  | h1_z_ld _ _ _ _ =>
    generalize hk : (0 : Nat) = K at h2
    cases h2 with
    | h1_ld _ _ => omega
    | h1_z_ld _ _ => rfl
  | h1_z_d1 hne _ _ =>
    generalize hk : (0 : Nat) = K at h2
    cases h2 with
    | h1_d1 _ => omega
    | h1_z1 => exact False.elim (hne rfl)
    | h1_z_d1 _ _ => rfl
  | h1_z_d0 hne _ _ =>
    generalize hk : (0 : Nat) = K at h2
    cases h2 with
    | h1_d0_0 _ => omega
    | h1_d0_1 _ => omega
    | h1_z0 => exact False.elim (hne rfl)
    | h1_z_d0 _ _ => rfl

private lemma RIncs_step {tp : H} {k : Nat} {r r' : List RD}
    (h : RIncs tp k r r') (htp : tp ≠ H.hi) :
    ∃ r'', RIncs H.hi 0 r' r'' ∧ RIncs tp (1 + k) r r'' := by
  induction h with
  | hi_nil => exact absurd rfl htp
  | hi_d0 _ => exact absurd rfl htp
  | hi_d1 _ _ => exact absurd rfl htp
  | hi_ld _ _ => exact absurd rfl htp
  | hi_w1d0 _ _ => exact absurd rfl htp
  | hi_w1d1 _ _ => exact absurd rfl htp
  | hi_w1ld _ _ _ _ => exact absurd rfl htp
  | hx_ld h_inc _ _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.LD :: r'', RIncs.hi_ld hJ, RIncs.hx_ld h_inc h_ri'⟩
  | hx_d1 _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.LD :: r'', RIncs.hi_ld hJ, RIncs.hx_d1 h_ri'⟩
  | hx_d0 _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.LD :: r'', RIncs.hi_ld hJ, RIncs.hx_d0 h_ri'⟩
  | h1_ld h_inc _ _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.LD :: r'', RIncs.hi_ld hJ, RIncs.h1_ld h_inc h_ri'⟩
  | h1_d1 _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.LD :: r'', RIncs.hi_ld hJ, RIncs.h1_d1 h_ri'⟩
  | @h1_d0_0 k r r' h_ri _ =>
    exact ⟨RD.D1 :: r', RIncs.hi_d0 r', RIncs_eqk (RIncs.h1_d0_1 h_ri) (by omega)⟩
  | @h1_d0_1 k r r' _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.D0 :: r'', RIncs.hi_d1 hJ, RIncs_eqk (RIncs.h1_d0_0 h_ri') (by omega)⟩
  | h1_rh_0 =>
    exact ⟨[RD.D0, RD.D1], RIncs.hi_d1 RIncs.hi_nil, RIncs.h1_rh_1 RIncs.h1_rh_0⟩
  | @h1_rh_1 k r' h_ri _ =>
    exact ⟨RD.D1 :: r', RIncs.hi_d0 r', RIncs_eqk (RIncs.h1_rh_2 h_ri) (by omega)⟩
  | @h1_rh_2 k r' _ ih =>
    rcases ih (by decide) with ⟨r'', hJ, h_ri'⟩
    exact ⟨RD.D0 :: r'', RIncs.hi_d1 hJ, RIncs_eqk (RIncs.h1_rh_1 h_ri') (by omega)⟩
  | h1_z1 =>
    exact ⟨[RD.LD, RD.D1], RIncs.hi_ld RIncs.hi_nil, RIncs.h1_d1 RIncs.h1_rh_0⟩
  | h1_z0 =>
    exact ⟨[RD.D0, RD.D1], RIncs.hi_d1 RIncs.hi_nil, RIncs.h1_d0_0 RIncs.h1_rh_0⟩
  | h1_z_ld h_inc h_ri _ _ =>
    exact ⟨RD.LD :: _, RIncs.hi_w1ld h_inc h_ri, RIncs.h1_ld h_inc h_ri⟩
  | h1_z_d1 _ h_ri _ =>
    exact ⟨RD.LD :: _, RIncs.hi_w1d1 h_ri, RIncs.h1_d1 h_ri⟩
  | h1_z_d0 _ h_ri _ =>
    exact ⟨RD.D0 :: _, RIncs.hi_w1d0 h_ri, RIncs.h1_d0_0 h_ri⟩

private lemma mod2 (n : Nat) : (∃ b, n = b * 2) ∨ (∃ b, n = 1 + b * 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; exact ⟨n / 2, by omega⟩
  · right; exact ⟨n / 2, by omega⟩

private inductive Good : H -> Nat -> List RD -> Prop where
  | hx_ld {k : Nat} {r r1 : List RD} :
      RIncs H.hi 0 r r1 -> Good H.hx (1 + k) r1 -> Good H.hx k (RD.LD :: r)
  | hx_d1 {k : Nat} {r : List RD} :
      Good H.h1 (1 + k) r -> Good H.hx k (RD.D1 :: r)
  | hx_d0 {k : Nat} {r : List RD} :
      Good H.hx (1 + k) r -> Good H.hx k (RD.D0 :: r)
  | h1_ld {k : Nat} {r r1 : List RD} :
      RIncs H.hi 0 r r1 -> Good H.hx (1 + k) r1 -> Good H.h1 (1 + k) (RD.LD :: r)
  | h1_d1 {k : Nat} {r : List RD} :
      Good H.h1 (1 + k) r -> Good H.h1 (1 + k) (RD.D1 :: r)
  | h1_d0_0 {a : Nat} {r : List RD} :
      Good H.h1 a r -> Good H.h1 (1 + a * 2) (RD.D0 :: r)
  | h1_d0_1 {a : Nat} {r : List RD} :
      Good H.h1 a r -> Good H.h1 (2 + a * 2) (RD.D0 :: r)
  | h1_z1 :
      Good H.h1 0 [RD.D1]
  | h1_nil {k : Nat} :
      Good H.h1 k []

private lemma RIncs_nxt_1 (k : Nat) : ∃ r, RIncs H.h1 k [] r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact ⟨[RD.D1], RIncs.h1_rh_0⟩
    | succ m =>
      rcases mod2 m with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · rcases ih b (by omega) with ⟨r, hI⟩
        exact ⟨RD.D0 :: r, RIncs_eqk (RIncs.h1_rh_1 hI) (by omega)⟩
      · rcases ih b (by omega) with ⟨r, hI⟩
        exact ⟨RD.D1 :: r, RIncs_eqk (RIncs.h1_rh_2 hI) (by omega)⟩

private lemma rK_nonnil {k : Nat} {r rK : List RD} (h : RIncs H.h1 k r rK) : rK ≠ [] := by
  cases h <;> simp

private lemma inv_hx_ld {k : Nat} {r rK : List RD} (h : RIncs H.hx k (RD.LD :: r) rK) :
    ∃ r1 rK', RIncs H.hi 0 r r1 ∧ RIncs H.hx k r1 rK' ∧ rK = RD.LD :: rK' := by
  cases h with
  | hx_ld h_inc h_ri => exact ⟨_, _, h_inc, h_ri, rfl⟩

private lemma inv_hx_d1 {k : Nat} {r rK : List RD} (h : RIncs H.hx k (RD.D1 :: r) rK) :
    ∃ rK', RIncs H.h1 k r rK' ∧ rK = RD.LD :: rK' := by
  cases h with
  | hx_d1 h_ri => exact ⟨_, h_ri, rfl⟩

private lemma inv_hx_d0 {k : Nat} {r rK : List RD} (h : RIncs H.hx k (RD.D0 :: r) rK) :
    ∃ rK', RIncs H.hx (1 + k) r rK' ∧ rK = RD.LD :: rK' := by
  cases h with
  | hx_d0 h_ri => exact ⟨_, h_ri, rfl⟩

private lemma inv_h1_ld {k : Nat} {r rK : List RD} (h : RIncs H.h1 (1 + k) (RD.LD :: r) rK) :
    ∃ r1 rK', RIncs H.hi 0 r r1 ∧ RIncs H.hx k r1 rK' ∧ rK = RD.LD :: rK' := by
  generalize hk : 1 + k = K at h
  cases h with
  | @h1_ld k0 _ r1 rK' h_inc h_ri =>
    have hk0 : k0 = k := by omega
    subst hk0
    exact ⟨r1, rK', h_inc, h_ri, rfl⟩
  | h1_z_ld _ _ => omega

private lemma inv_h1_d1 {k : Nat} {r rK : List RD} (h : RIncs H.h1 (1 + k) (RD.D1 :: r) rK) :
    ∃ rK', RIncs H.h1 k r rK' ∧ rK = RD.LD :: rK' := by
  generalize hk : 1 + k = K at h
  cases h with
  | @h1_d1 k0 _ rK' h_ri =>
    have hk0 : k0 = k := by omega
    subst hk0
    exact ⟨rK', h_ri, rfl⟩
  | h1_z1 => omega
  | h1_z_d1 _ _ => omega

private lemma inv_h1_d0 {K : Nat} {r rK : List RD} (h : RIncs H.h1 K (RD.D0 :: r) rK) (hK : 1 ≤ K) :
    (∃ A rK', K = 1 + A * 2 ∧ RIncs H.h1 A r rK' ∧ rK = RD.D0 :: rK') ∨
    (∃ A rK', K = 2 + A * 2 ∧ RIncs H.h1 A r rK' ∧ rK = RD.D1 :: rK') := by
  generalize hd : RD.D0 :: r = r0 at h
  cases h with
  | h1_ld _ _ => cases hd
  | h1_d1 _ => cases hd
  | @h1_d0_0 A r_in rK' h_ri =>
    injection hd with _ hr; subst hr
    left; exact ⟨A, rK', rfl, h_ri, rfl⟩
  | @h1_d0_1 A r_in rK' h_ri =>
    injection hd with _ hr; subst hr
    right; exact ⟨A, rK', rfl, h_ri, rfl⟩
  | h1_rh_0 => cases hd
  | h1_rh_1 _ => cases hd
  | h1_rh_2 _ => cases hd
  | h1_z1 => cases hd
  | h1_z0 => omega
  | h1_z_ld _ _ => cases hd
  | h1_z_d1 _ _ => cases hd
  | h1_z_d0 _ _ => omega

private lemma inv_z1 {K : Nat} {rK : List RD} (h : RIncs H.h1 K [RD.D1] rK) :
    (K = 0 ∧ rK = [RD.LD]) ∨
    (∃ K0 rK', K = 1 + K0 ∧ RIncs H.h1 K0 [] rK' ∧ rK = RD.LD :: rK') := by
  generalize hd : ([RD.D1] : List RD) = r0 at h
  cases h with
  | h1_ld _ _ => cases hd
  | @h1_d1 K0 _ rK' h_ri =>
    injection hd with _ hr; subst hr
    right; exact ⟨K0, rK', rfl, h_ri, rfl⟩
  | h1_d0_0 _ => cases hd
  | h1_d0_1 _ => cases hd
  | h1_rh_0 => cases hd
  | h1_rh_1 _ => cases hd
  | h1_rh_2 _ => cases hd
  | h1_z1 => left; exact ⟨rfl, rfl⟩
  | h1_z0 => cases hd
  | h1_z_ld _ _ => cases hd
  | h1_z_d1 hne _ => injection hd with _ hr; subst hr; exact False.elim (hne rfl)
  | h1_z_d0 _ _ => cases hd

private lemma End_step {tp : H} {m : Nat} {e w : List RD} (h : RIncs tp m e w)
    (htp : tp = H.h1) (he : e = []) :
    ∀ tq q, (tq = H.hx ∨ tq = H.h1) -> ∃ w', RIncs tq q w w' := by
  induction h with
  | hi_nil => cases htp
  | hi_d0 _ => cases htp
  | hi_d1 _ _ => cases htp
  | hi_ld _ _ => cases htp
  | hi_w1d0 _ _ => cases htp
  | hi_w1d1 _ _ => cases htp
  | hi_w1ld _ _ _ _ => cases htp
  | hx_ld _ _ _ _ => cases htp
  | hx_d1 _ _ => cases htp
  | hx_d0 _ _ => cases htp
  | h1_ld _ _ _ _ => cases he
  | h1_d1 _ _ => cases he
  | h1_d0_0 _ _ => cases he
  | h1_d0_1 _ _ => cases he
  | h1_rh_0 =>
    intro tq q htq
    rcases htq with rfl | rfl
    · rcases RIncs_nxt_1 q with ⟨w', hI⟩
      exact ⟨RD.LD :: w', RIncs.hx_d1 hI⟩
    · cases q with
      | zero => exact ⟨[RD.LD], RIncs.h1_z1⟩
      | succ q0 =>
        rcases RIncs_nxt_1 q0 with ⟨w', hI⟩
        exact ⟨RD.LD :: w', RIncs_eqk (RIncs.h1_d1 hI) (by omega)⟩
  | @h1_rh_1 k r' h_ri ih =>
    intro tq q htq
    have ih' := ih rfl rfl
    rcases htq with rfl | rfl
    · rcases ih' H.hx (1 + q) (Or.inl rfl) with ⟨w', hI2⟩
      exact ⟨RD.LD :: w', RIncs.hx_d0 hI2⟩
    · cases q with
      | zero =>
        rcases ih' H.h1 0 (Or.inr rfl) with ⟨w', hI2⟩
        exact ⟨RD.W1D0 :: r', RIncs.h1_z_d0 (rK_nonnil h_ri) hI2⟩
      | succ m0 =>
        rcases mod2 m0 with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · rcases ih' H.h1 b (Or.inr rfl) with ⟨w', hI2⟩
          exact ⟨RD.D0 :: w', RIncs_eqk (RIncs.h1_d0_0 hI2) (by omega)⟩
        · rcases ih' H.h1 b (Or.inr rfl) with ⟨w', hI2⟩
          exact ⟨RD.D1 :: w', RIncs_eqk (RIncs.h1_d0_1 hI2) (by omega)⟩
  | @h1_rh_2 k r' h_ri ih =>
    intro tq q htq
    have ih' := ih rfl rfl
    rcases htq with rfl | rfl
    · rcases ih' H.h1 q (Or.inr rfl) with ⟨w', hI2⟩
      exact ⟨RD.LD :: w', RIncs.hx_d1 hI2⟩
    · cases q with
      | zero =>
        rcases ih' H.h1 0 (Or.inr rfl) with ⟨w', hI2⟩
        exact ⟨RD.W1D1 :: r', RIncs.h1_z_d1 (rK_nonnil h_ri) hI2⟩
      | succ q0 =>
        rcases ih' H.h1 q0 (Or.inr rfl) with ⟨w', hI2⟩
        exact ⟨RD.LD :: w', RIncs_eqk (RIncs.h1_d1 hI2) (by omega)⟩
  | h1_z1 => cases he
  | h1_z0 => cases he
  | h1_z_ld _ _ _ _ => cases he
  | h1_z_d1 _ _ _ => cases he
  | h1_z_d0 _ _ _ => cases he

private lemma Good_eqk {tp : H} {k k' : Nat} {r : List RD}
    (h : Good tp k r) (hk : k = k') : Good tp k' r := by
  subst hk; exact h

private lemma Good_step {tp : H} {k : Nat} {r : List RD} (hG : Good tp k r) :
    ∀ j rK tq q, RIncs tp (k + j) r rK ->
    (tq = H.hx ∨ (tq = H.h1 ∧ tp = H.h1)) -> ∃ r2, RIncs tq q rK r2 := by
  induction hG with
  | @hx_ld k r r1 Hi _ ih =>
    intro j rK tq q E htq
    have h_hx : tq = H.hx := by rcases htq with rfl | ⟨_, h⟩; rfl; cases h
    subst h_hx
    rcases inv_hx_ld E with ⟨r1', rK', Hi', E', rfl⟩
    rw [RIncs_fun Hi' Hi] at E'
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    rcases ih j rK'' H.hx q (RIncs_eqk E'' (by omega)) (Or.inl rfl) with ⟨r2, I2⟩
    exact ⟨RD.LD :: r2, RIncs.hx_ld J I2⟩
  | @hx_d1 k r _ ih =>
    intro j rK tq q E htq
    have h_hx : tq = H.hx := by rcases htq with rfl | ⟨_, h⟩; rfl; cases h
    subst h_hx
    rcases inv_hx_d1 E with ⟨rK', E', rfl⟩
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    rcases ih j rK'' H.hx q (RIncs_eqk E'' (by omega)) (Or.inl rfl) with ⟨r2, I2⟩
    exact ⟨RD.LD :: r2, RIncs.hx_ld J I2⟩
  | @hx_d0 k r _ ih =>
    intro j rK tq q E htq
    have h_hx : tq = H.hx := by rcases htq with rfl | ⟨_, h⟩; rfl; cases h
    subst h_hx
    rcases inv_hx_d0 E with ⟨rK', E', rfl⟩
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    rcases ih (1 + j) rK'' H.hx q (RIncs_eqk E'' (by omega)) (Or.inl rfl) with ⟨r2, I2⟩
    exact ⟨RD.LD :: r2, RIncs.hx_ld J I2⟩
  | @h1_ld k r r1 Hi _ ih =>
    intro j rK tq q E htq
    have E0 : RIncs H.h1 (1 + (k + j)) (RD.LD :: r) rK := RIncs_eqk E (by omega)
    rcases inv_h1_ld E0 with ⟨r1', rK', Hi', E', rfl⟩
    rw [RIncs_fun Hi' Hi] at E'
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    have E3 : RIncs H.hx ((1 + k) + j) r1 rK'' := RIncs_eqk E'' (by omega)
    rcases htq with rfl | ⟨rfl, _⟩
    · rcases ih j rK'' H.hx q E3 (Or.inl rfl) with ⟨r2, I2⟩
      exact ⟨RD.LD :: r2, RIncs.hx_ld J I2⟩
    · cases q with
      | zero =>
        rcases ih j rK'' H.hx 0 E3 (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.W1LD :: rK', RIncs.h1_z_ld J I2⟩
      | succ q0 =>
        rcases ih j rK'' H.hx q0 E3 (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs_eqk (RIncs.h1_ld J I2) (by omega)⟩
  | @h1_d1 k r _ ih =>
    intro j rK tq q E htq
    have E0 : RIncs H.h1 (1 + (k + j)) (RD.D1 :: r) rK := RIncs_eqk E (by omega)
    rcases inv_h1_d1 E0 with ⟨rK', E', rfl⟩
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    have E3 : RIncs H.h1 ((1 + k) + j) r rK'' := RIncs_eqk E'' (by omega)
    rcases htq with rfl | ⟨rfl, _⟩
    · rcases ih j rK'' H.hx q E3 (Or.inl rfl) with ⟨r2, I2⟩
      exact ⟨RD.LD :: r2, RIncs.hx_ld J I2⟩
    · cases q with
      | zero =>
        rcases ih j rK'' H.hx 0 E3 (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.W1LD :: rK', RIncs.h1_z_ld J I2⟩
      | succ q0 =>
        rcases ih j rK'' H.hx q0 E3 (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs_eqk (RIncs.h1_ld J I2) (by omega)⟩
  | @h1_d0_0 a r _ ih =>
    intro j rK tq q E htq
    rcases inv_h1_d0 E (by omega) with ⟨A, rK', hKA, E', rfl⟩ | ⟨A, rK', hKA, E', rfl⟩
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      rcases htq with rfl | ⟨rfl, _⟩
      · rcases ih (A - a) rK' H.hx (1 + q) hE' (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs.hx_d0 I2⟩
      · cases q with
        | zero =>
          rcases ih (A - a) rK' H.h1 0 hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
          exact ⟨RD.W1D0 :: rK', RIncs.h1_z_d0 (rK_nonnil E') I2⟩
        | succ m0 =>
          rcases mod2 m0 with ⟨b, rfl⟩ | ⟨b, rfl⟩
          · rcases ih (A - a) rK' H.h1 b hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
            exact ⟨RD.D0 :: r2, RIncs_eqk (RIncs.h1_d0_0 I2) (by omega)⟩
          · rcases ih (A - a) rK' H.h1 b hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
            exact ⟨RD.D1 :: r2, RIncs_eqk (RIncs.h1_d0_1 I2) (by omega)⟩
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      rcases htq with rfl | ⟨rfl, _⟩
      · rcases ih (A - a) rK' H.h1 q hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs.hx_d1 I2⟩
      · cases q with
        | zero =>
          rcases ih (A - a) rK' H.h1 0 hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
          exact ⟨RD.W1D1 :: rK', RIncs.h1_z_d1 (rK_nonnil E') I2⟩
        | succ q0 =>
          rcases ih (A - a) rK' H.h1 q0 hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
          exact ⟨RD.LD :: r2, RIncs_eqk (RIncs.h1_d1 I2) (by omega)⟩
  | @h1_d0_1 a r _ ih =>
    intro j rK tq q E htq
    rcases inv_h1_d0 E (by omega) with ⟨A, rK', hKA, E', rfl⟩ | ⟨A, rK', hKA, E', rfl⟩
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      rcases htq with rfl | ⟨rfl, _⟩
      · rcases ih (A - a) rK' H.hx (1 + q) hE' (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs.hx_d0 I2⟩
      · cases q with
        | zero =>
          rcases ih (A - a) rK' H.h1 0 hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
          exact ⟨RD.W1D0 :: rK', RIncs.h1_z_d0 (rK_nonnil E') I2⟩
        | succ m0 =>
          rcases mod2 m0 with ⟨b, rfl⟩ | ⟨b, rfl⟩
          · rcases ih (A - a) rK' H.h1 b hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
            exact ⟨RD.D0 :: r2, RIncs_eqk (RIncs.h1_d0_0 I2) (by omega)⟩
          · rcases ih (A - a) rK' H.h1 b hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
            exact ⟨RD.D1 :: r2, RIncs_eqk (RIncs.h1_d0_1 I2) (by omega)⟩
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      rcases htq with rfl | ⟨rfl, _⟩
      · rcases ih (A - a) rK' H.h1 q hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs.hx_d1 I2⟩
      · cases q with
        | zero =>
          rcases ih (A - a) rK' H.h1 0 hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
          exact ⟨RD.W1D1 :: rK', RIncs.h1_z_d1 (rK_nonnil E') I2⟩
        | succ q0 =>
          rcases ih (A - a) rK' H.h1 q0 hE' (Or.inr ⟨rfl, rfl⟩) with ⟨r2, I2⟩
          exact ⟨RD.LD :: r2, RIncs_eqk (RIncs.h1_d1 I2) (by omega)⟩
  | h1_z1 =>
    intro j rK tq q E htq
    rcases inv_z1 E with ⟨_, rfl⟩ | ⟨K0, rK', _, E', rfl⟩
    · rcases htq with rfl | ⟨rfl, _⟩
      · rcases RIncs_nxt_1 q with ⟨w, hI⟩
        exact ⟨RD.LD :: RD.LD :: w, RIncs.hx_ld RIncs.hi_nil (RIncs.hx_d1 hI)⟩
      · cases q with
        | zero =>
          exact ⟨[RD.W1LD], RIncs.h1_z_ld RIncs.hi_nil (RIncs.hx_d1 RIncs.h1_rh_0)⟩
        | succ q0 =>
          rcases RIncs_nxt_1 q0 with ⟨w, hI⟩
          exact ⟨RD.LD :: RD.LD :: w, RIncs_eqk (RIncs.h1_ld RIncs.hi_nil (RIncs.hx_d1 hI)) (by omega)⟩
    · rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
      rcases htq with rfl | ⟨rfl, _⟩
      · rcases End_step E'' rfl rfl H.hx q (Or.inl rfl) with ⟨r2, I2⟩
        exact ⟨RD.LD :: r2, RIncs.hx_ld J I2⟩
      · cases q with
        | zero =>
          rcases End_step E'' rfl rfl H.hx 0 (Or.inl rfl) with ⟨r2, I2⟩
          exact ⟨RD.W1LD :: rK', RIncs.h1_z_ld J I2⟩
        | succ q0 =>
          rcases End_step E'' rfl rfl H.hx q0 (Or.inl rfl) with ⟨r2, I2⟩
          exact ⟨RD.LD :: r2, RIncs_eqk (RIncs.h1_ld J I2) (by omega)⟩
  | h1_nil =>
    intro j rK tq q E htq
    rcases htq with rfl | ⟨rfl, _⟩
    · exact End_step E rfl rfl H.hx q (Or.inl rfl)
    · exact End_step E rfl rfl H.h1 q (Or.inr rfl)

private lemma End_good_1 {tp : H} {m : Nat} {e w : List RD} (h : RIncs tp m e w)
    (htp : tp = H.h1) (he : e = []) :
    ∀ q, m ≤ q -> Good H.h1 q w := by
  induction h with
  | hi_nil => cases htp
  | hi_d0 _ => cases htp
  | hi_d1 _ => cases htp
  | hi_ld _ => cases htp
  | hi_w1d0 _ => cases htp
  | hi_w1d1 _ => cases htp
  | hi_w1ld _ _ => cases htp
  | hx_ld _ _ _ _ => cases htp
  | hx_d1 _ _ => cases htp
  | hx_d0 _ _ => cases htp
  | h1_ld _ _ _ _ => cases he
  | h1_d1 _ _ => cases he
  | h1_d0_0 _ _ => cases he
  | h1_d0_1 _ _ => cases he
  | h1_rh_0 =>
    intro q _
    cases q with
    | zero => exact Good.h1_z1
    | succ q0 => exact Good_eqk (Good.h1_d1 (@Good.h1_nil (1 + q0))) (by omega)
  | @h1_rh_1 b r' _ ih =>
    intro q hq
    have ih' := ih rfl rfl
    rcases mod2 q with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · cases c with
      | zero => omega
      | succ c => exact Good_eqk (Good.h1_d0_1 (ih' c (by omega))) (by omega)
    · exact Good.h1_d0_0 (ih' c (by omega))
  | @h1_rh_2 b r' _ ih =>
    intro q hq
    have ih' := ih rfl rfl
    cases q with
    | zero => omega
    | succ q0 => exact Good_eqk (Good.h1_d1 (ih' (1 + q0) (by omega))) (by omega)
  | h1_z1 => cases he
  | h1_z0 => cases he
  | h1_z_ld _ _ _ _ => cases he
  | h1_z_d1 _ _ _ => cases he
  | h1_z_d0 _ _ _ => cases he

private lemma End_good_x {tp : H} {m : Nat} {e w : List RD} (h : RIncs tp m e w)
    (htp : tp = H.h1) (he : e = []) :
    ∀ q, m ≤ 2 * q + 2 -> Good H.hx q w := by
  induction h with
  | hi_nil => cases htp
  | hi_d0 _ => cases htp
  | hi_d1 _ => cases htp
  | hi_ld _ => cases htp
  | hi_w1d0 _ => cases htp
  | hi_w1d1 _ => cases htp
  | hi_w1ld _ _ => cases htp
  | hx_ld _ _ _ _ => cases htp
  | hx_d1 _ _ => cases htp
  | hx_d0 _ _ => cases htp
  | h1_ld _ _ _ _ => cases he
  | h1_d1 _ _ => cases he
  | h1_d0_0 _ _ => cases he
  | h1_d0_1 _ _ => cases he
  | h1_rh_0 =>
    intro q _
    exact Good.hx_d1 Good.h1_nil
  | @h1_rh_1 b r' _ ih =>
    intro q hq
    exact Good.hx_d0 (ih rfl rfl (1 + q) (by omega))
  | @h1_rh_2 b r' h_ri _ =>
    intro q hq
    exact Good.hx_d1 (End_good_1 h_ri rfl rfl (1 + q) (by omega))
  | h1_z1 => cases he
  | h1_z0 => cases he
  | h1_z_ld _ _ _ _ => cases he
  | h1_z_d1 _ _ _ => cases he
  | h1_z_d0 _ _ _ => cases he

private def Inv (tp : H) (k j : Nat) (tq : H) (q : Nat) : Prop :=
  match tp, tq with
  | H.hx, H.hx => k ≤ q ∧ j ≤ q
  | H.h1, H.hx => k ≤ q ∧ j ≤ q
  | H.h1, H.h1 => (j = 0 ∧ 2 * k + 1 ≤ q) ∨ (1 ≤ j ∧ k + j ≤ q ∧ 1 ≤ q)
  | _, _   => False

private lemma Good_pres {tp : H} {k : Nat} {r : List RD} (hG : Good tp k r) :
    ∀ j rK tq q, RIncs tp (k + j) r rK ->
    Inv tp k j tq q -> Good tq q rK := by
  induction hG with
  | @hx_ld k r r1 Hi _ ih =>
    intro j rK tq q E HI
    cases tq with
    | hi => cases HI
    | h1 => cases HI
    | hx =>
      rcases inv_hx_ld E with ⟨r1', rK', Hi', E', rfl⟩
      rw [RIncs_fun Hi' Hi] at E'
      rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
      exact Good.hx_ld J (ih j rK'' H.hx (1 + q) (RIncs_eqk E'' (by omega)) (by dsimp [Inv] at HI ⊢; omega))
  | @hx_d1 k r _ ih =>
    intro j rK tq q E HI
    cases tq with
    | hi => cases HI
    | h1 => cases HI
    | hx =>
      rcases inv_hx_d1 E with ⟨rK', E', rfl⟩
      rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
      exact Good.hx_ld J (ih j rK'' H.hx (1 + q) (RIncs_eqk E'' (by omega)) (by dsimp [Inv] at HI ⊢; omega))
  | @hx_d0 k r _ ih =>
    intro j rK tq q E HI
    cases tq with
    | hi => cases HI
    | h1 => cases HI
    | hx =>
      rcases inv_hx_d0 E with ⟨rK', E', rfl⟩
      rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
      exact Good.hx_ld J (ih (1 + j) rK'' H.hx (1 + q) (RIncs_eqk E'' (by omega)) (by dsimp [Inv] at HI ⊢; omega))
  | @h1_ld k r r1 Hi _ ih =>
    intro j rK tq q E HI
    have E0 : RIncs H.h1 (1 + (k + j)) (RD.LD :: r) rK := RIncs_eqk E (by omega)
    rcases inv_h1_ld E0 with ⟨r1', rK', Hi', E', rfl⟩
    rw [RIncs_fun Hi' Hi] at E'
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    have E3 : RIncs H.hx ((1 + k) + j) r1 rK'' := RIncs_eqk E'' (by omega)
    cases tq with
    | hi => cases HI
    | hx => exact Good.hx_ld J (ih j rK'' H.hx (1 + q) E3 (by dsimp [Inv] at HI ⊢; omega))
    | h1 =>
      cases q with
      | zero => dsimp [Inv] at HI; omega
      | succ q0 =>
        exact Good_eqk (Good.h1_ld J (ih j rK'' H.hx (1 + q0) E3 (by dsimp [Inv] at HI ⊢; omega))) (by omega)
  | @h1_d1 k r _ ih =>
    intro j rK tq q E HI
    have E0 : RIncs H.h1 (1 + (k + j)) (RD.D1 :: r) rK := RIncs_eqk E (by omega)
    rcases inv_h1_d1 E0 with ⟨rK', E', rfl⟩
    rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
    have E3 : RIncs H.h1 ((1 + k) + j) r rK'' := RIncs_eqk E'' (by omega)
    cases tq with
    | hi => cases HI
    | hx => exact Good.hx_ld J (ih j rK'' H.hx (1 + q) E3 (by dsimp [Inv] at HI ⊢; omega))
    | h1 =>
      cases q with
      | zero => dsimp [Inv] at HI; omega
      | succ q0 =>
        exact Good_eqk (Good.h1_ld J (ih j rK'' H.hx (1 + q0) E3 (by dsimp [Inv] at HI ⊢; omega))) (by omega)
  | @h1_d0_0 a r _ ih =>
    intro j rK tq q E HI
    rcases inv_h1_d0 E (by omega) with ⟨A, rK', hKA, E', rfl⟩ | ⟨A, rK', hKA, E', rfl⟩
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hi => cases HI
      | hx => exact Good.hx_d0 (ih (A - a) rK' H.hx (1 + q) hE' (by dsimp [Inv] at HI ⊢; omega))
      | h1 =>
        rcases mod2 q with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · cases b with
          | zero => dsimp [Inv] at HI; omega
          | succ b0 =>
            exact Good_eqk (Good.h1_d0_1 (ih (A - a) rK' H.h1 b0 hE' (by dsimp [Inv] at HI ⊢; omega))) (by omega)
        · exact Good.h1_d0_0 (ih (A - a) rK' H.h1 b hE' (by dsimp [Inv] at HI ⊢; omega))
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hi => cases HI
      | hx => exact Good.hx_d1 (ih (A - a) rK' H.h1 (1 + q) hE' (by dsimp [Inv] at HI ⊢; omega))
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          exact Good_eqk (Good.h1_d1 (ih (A - a) rK' H.h1 (1 + q0) hE' (by dsimp [Inv] at HI ⊢; omega))) (by omega)
  | @h1_d0_1 a r _ ih =>
    intro j rK tq q E HI
    rcases inv_h1_d0 E (by omega) with ⟨A, rK', hKA, E', rfl⟩ | ⟨A, rK', hKA, E', rfl⟩
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hi => cases HI
      | hx => exact Good.hx_d0 (ih (A - a) rK' H.hx (1 + q) hE' (by dsimp [Inv] at HI ⊢; omega))
      | h1 =>
        rcases mod2 q with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · cases b with
          | zero => dsimp [Inv] at HI; omega
          | succ b0 =>
            exact Good_eqk (Good.h1_d0_1 (ih (A - a) rK' H.h1 b0 hE' (by dsimp [Inv] at HI ⊢; omega))) (by omega)
        · exact Good.h1_d0_0 (ih (A - a) rK' H.h1 b hE' (by dsimp [Inv] at HI ⊢; omega))
    · have hE' : RIncs H.h1 (a + (A - a)) r rK' := RIncs_eqk E' (by omega)
      cases tq with
      | hi => cases HI
      | hx => exact Good.hx_d1 (ih (A - a) rK' H.h1 (1 + q) hE' (by dsimp [Inv] at HI ⊢; omega))
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          exact Good_eqk (Good.h1_d1 (ih (A - a) rK' H.h1 (1 + q0) hE' (by dsimp [Inv] at HI ⊢; omega))) (by omega)
  | h1_z1 =>
    intro j rK tq q E HI
    rcases inv_z1 E with ⟨_, rfl⟩ | ⟨K0, rK', _, E', rfl⟩
    · cases tq with
      | hi => cases HI
      | hx => exact Good.hx_ld RIncs.hi_nil (Good.hx_d1 Good.h1_nil)
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 => exact Good_eqk (Good.h1_ld RIncs.hi_nil (Good.hx_d1 (@Good.h1_nil (1 + (1 + q0))))) (by omega)
    · rcases RIncs_step E' (by decide) with ⟨rK'', J, E''⟩
      cases tq with
      | hi => cases HI
      | hx =>
        exact Good.hx_ld J (End_good_x E'' rfl rfl (1 + q) (by dsimp [Inv] at HI; omega))
      | h1 =>
        cases q with
        | zero => dsimp [Inv] at HI; omega
        | succ q0 =>
          exact Good_eqk (Good.h1_ld J (End_good_x E'' rfl rfl (1 + q0) (by dsimp [Inv] at HI; omega))) (by omega)
  | @h1_nil k =>
    intro j rK tq q E HI
    cases tq with
    | hi => cases HI
    | hx => exact End_good_x E rfl rfl q (by dsimp [Inv] at HI; omega)
    | h1 => exact End_good_1 E rfl rfl q (by dsimp [Inv] at HI; omega)

private lemma domain {r r1 : List RD} (hG : Good H.hx 0 r) (hE : RIncs H.hx 0 r r1) :
    ∃ r2, RIncs H.hx 0 r1 r2 ∧ Good H.hx 0 r1 := by
  have hE0 : RIncs H.hx (0 + 0) r r1 := hE
  rcases Good_step hG 0 r1 H.hx 0 hE0 (Or.inl rfl) with ⟨r2, hR2⟩
  exact ⟨r2, hR2, Good_pres hG 0 r1 H.hx 0 hE0 (by simp [Inv])⟩

private lemma turn_lh (r : zB) : (zCL lh r) [target_tm]⊢⁺ (zCR lh .ch' r) := by
  unfold zCL zCR zCw zCs lh
  simp only [append_cons, append_nil]
  execute

private lemma big_step {r r' : List RD} (h : RIncs H.hx 0 r r') :
    (zCR lh .ch' (toRC r)) [target_tm]⊢⁺ (zCR lh .ch' (toRC r')) := by
  have hs := RIncs_spec h
  simp only [toH, toH', z05, List.append_nil, append_nil] at hs
  rcases hs with _ | ⟨hc, hnil⟩
  cases hnil
  exact zPt (hc lh) (turn_lh (toRC r'))

private lemma start_step : (init []) [target_tm]⊢⁺ (zCR lh .ch' (toRC [RD.D1])) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold zCR lh zCw zCs
  dsimp [toRC, d1]
  execute

private lemma arb_steps (N : Nat) :
    ∃ m r r1, N ≤ m ∧ ((init []) [target_tm]⊢^{m} (zCR lh .ch' (toRC r))) ∧
      RIncs H.hx 0 r r1 ∧ Good H.hx 0 r := by
  induction N with
  | zero =>
    obtain ⟨m, _, hm⟩ := start_step
    exact ⟨m, [RD.D1], [RD.LD, RD.D1], Nat.zero_le _, hm,
      RIncs.hx_d1 RIncs.h1_rh_0, Good.hx_d1 Good.h1_nil⟩
  | succ N ih =>
    obtain ⟨m, r, r1, _, hm, hE, hG⟩ := ih
    obtain ⟨r2, hE2, hG2⟩ := domain hG hE
    obtain ⟨k, _, hk⟩ := big_step hE
    exact ⟨m + k, r1, r2, by omega, zMt target_tm _ _ _ m k hm hk, hE2, hG2⟩

private lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨n, hn⟩
  rcases arb_steps (n + 1) with ⟨m, _, _, hnm, hm, _, _⟩
  have h_eq : (n + 1) + (m - (n + 1)) = m := Nat.add_sub_of_le hnm
  rw [← h_eq] at hm
  have h_some := zIm hm
  rw [zMs, hn] at h_some
  exact h_some

end BusyBeaver.M_1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RBHHH
