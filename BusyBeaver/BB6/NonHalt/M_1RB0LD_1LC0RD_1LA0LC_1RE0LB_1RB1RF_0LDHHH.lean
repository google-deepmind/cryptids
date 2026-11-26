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


/-!
# Busy Beaver Machine `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-! ### Reusable Step-Counted & Reachability Helpers -/

private abbrev lb0 : ListBlank (Fin 2) := default

private theorem reachesIn_zero (c : Cfg (Fin 2) (Fin 6)) : ReachesIn target_tm 0 c c :=
  ReachesIn.zero target_tm c

private theorem reachesStar_refl (c : Cfg (Fin 2) (Fin 6)) : ReachesStar target_tm c c :=
  ⟨0, rfl⟩

private theorem reachesPlus_trans_star {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : ReachesPlus target_tm c₁ c₂) (h₂ : ReachesStar target_tm c₂ c₃) :
    ReachesPlus target_tm c₁ c₃ := by
  obtain ⟨m, hm, h1⟩ := h₁
  obtain ⟨n, h2⟩ := h₂
  exact ⟨m + n, Nat.add_pos_left hm n, multiStep_trans h1 h2⟩

private theorem headLeft_cons_eq (q : Fin 6) (a : Fin 2) (l r : ListBlank (Fin 2)) :
    ((a >> l) <{{q}} r) = (l {{q}}> (a >> r)) := by
  simp

private theorem rtrans {n : ℕ} (m : ℕ) {nm : ℕ} {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : ReachesIn target_tm n c₁ c₂)
    (h₂ : ReachesIn target_tm m c₂ c₃)
    (hnm : n + m = nm := by omega) :
    ReachesIn target_tm nm c₁ c₃ :=
  hnm ▸ h₁.trans h₂

private theorem rstep_rr {n : ℕ} {q q' : Fin 6} {a w : Fin 2}
    {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (hM : target_tm q a = some (some q', Stmt.write w Dir.right))
    (h : ReachesIn target_tm n ((w >> l) {{q'}}> r) c₃) :
    ReachesIn target_tm (n + 1) (l {{q}}> (a >> r)) c₃ :=
  ReachesIn.step_left (step_headRight_right hM l r) h

private theorem rstep_rl {n : ℕ} {q q' : Fin 6} {a w s2 : Fin 2}
    {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (hM : target_tm q a = some (some q', Stmt.write w Dir.left))
    (h : ReachesIn target_tm n (l {{q'}}> (s2 >> w >> r)) c₃) :
    ReachesIn target_tm (n + 1) ((s2 >> l) {{q}}> (a >> r)) c₃ := by
  have hs := step_headRight_left hM (s2 >> l) r
  rw [Cfg.headLeft_cons] at hs
  exact ReachesIn.step_left hs h

private theorem rstep_lr {n : ℕ} {q q' : Fin 6} {a w : Fin 2}
    {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (hM : target_tm q a = some (some q', Stmt.write w Dir.right))
    (h : ReachesIn target_tm n ((w >> l) {{q'}}> r) c₃) :
    ReachesIn target_tm (n + 1) ((a >> l) <{{q}} r) c₃ :=
  ReachesIn.step_left (step_headLeft_right hM l r) h

private theorem rstep_ll {n : ℕ} {q q' : Fin 6} {a w : Fin 2}
    {l r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (hM : target_tm q a = some (some q', Stmt.write w Dir.left))
    (h : ReachesIn target_tm n (l <{{q'}} (w >> r)) c₃) :
    ReachesIn target_tm (n + 1) ((a >> l) <{{q}} r) c₃ :=
  ReachesIn.step_left (step_headLeft_left hM l r) h

local macro "stepK" : tactic =>
  `(tactic| (
    try dsimp only [ListBlank.append]
    repeat (first
      | refine rstep_rr rfl ?_
      | refine rstep_rl rfl ?_
      | refine rstep_lr rfl ?_
      | refine rstep_ll rfl ?_)
    first
      | exact reachesIn_zero _
      | (rw [headLeft_cons_eq]; exact reachesIn_zero _)
      | (rw [← headLeft_cons_eq]; exact reachesIn_zero _)))

private theorem lb_zero_cons_default :
    ((0 : Fin 2) >> (default : ListBlank (Fin 2))) = default := by
  apply ListBlank.ext
  intro i
  cases i <;> rfl

/-! ### Triplet Repetition Algebra & Base Sweep Lemmas -/

def rep110 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, lb => lb
  | n + 1, lb => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> rep110 n lb

def rep001 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, lb => lb
  | n + 1, lb => (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 n lb

private theorem rep110_add : ∀ (a b : ℕ) (lb : ListBlank (Fin 2)),
    rep110 (a + b) lb = rep110 a (rep110 b lb)
  | 0, _, _ => by simp only [Nat.zero_add, rep110]
  | a + 1, b, lb => by
    rw [Nat.succ_add]
    dsimp only [rep110]
    rw [rep110_add a b lb]

private theorem rep001_add : ∀ (a b : ℕ) (lb : ListBlank (Fin 2)),
    rep001 (a + b) lb = rep001 a (rep001 b lb)
  | 0, _, _ => by simp only [Nat.zero_add, rep001]
  | a + 1, b, lb => by
    rw [Nat.succ_add]
    dsimp only [rep001]
    rw [rep001_add a b lb]

private theorem rep110_shift : ∀ (n : ℕ) (lb : ListBlank (Fin 2)),
    rep110 n ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> lb) =
      (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> rep110 n lb
  | 0, _ => rfl
  | n + 1, lb => by
    dsimp only [rep110]
    rw [rep110_shift n lb]

private theorem rep001_shift : ∀ (n : ℕ) (lb : ListBlank (Fin 2)),
    rep001 n ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb) =
      (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 n lb
  | 0, _ => rfl
  | n + 1, lb => by
    dsimp only [rep001]
    rw [rep001_shift n lb]

private theorem reach_splitR_lb : ∀ (q : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (3 * q)
      (l {{(1 : Fin 6)}}> ((1 : Fin 2) >> rep001 q r))
      (rep110 q l {{(1 : Fin 6)}}> ((1 : Fin 2) >> r))
  | 0, _, _ => reachesIn_zero _
  | q + 1, l, r => by
    dsimp only [rep001]
    have h1 : ReachesIn target_tm 3
        (l {{(1 : Fin 6)}}> ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 q
          r))
        (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}> ((1 : Fin 2) >> rep001
          q r)) := by
      stepK
    have h2 := reach_splitR_lb q ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) r
    rw [rep110_shift q l] at h2
    exact rtrans (3 * q) h1 h2

private theorem reach_splitL_lb : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesIn target_tm (6 * k)
      (rep110 (2 * k) l {{(1 : Fin 6)}}> ((0 : Fin 2) >> r))
      (l {{(1 : Fin 6)}}> ((0 : Fin 2) >> rep001 (2 * k) r))
  | 0, _, _ => reachesIn_zero _
  | k + 1, l, r => by
    have hk : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [hk, rep110_add 2 (2 * k), rep001_add 2 (2 * k)]
    dsimp only [rep110]
    have h1 : ReachesIn target_tm 6
        (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          rep110 (2 * k) l) {{(1 : Fin 6)}}> ((0 : Fin 2) >> r))
        (rep110 (2 * k) l {{(1 : Fin 6)}}>
          ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
            (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) := by
      stepK
    have h2 := reach_splitL_lb k l
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)
    rw [rep001_shift (2 * k), rep001_shift (2 * k)] at h2
    exact rtrans (6 * k) h1 h2

private theorem reach_R1_lb (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2
      (l {{(1 : Fin 6)}}> ((1 : Fin 2) >> (1 : Fin 2) >> r))
      (l {{(1 : Fin 6)}}> ((0 : Fin 2) >> (0 : Fin 2) >> r)) := by stepK

private theorem reach_R2_lb (b3 : Fin 2) (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 3
      (l {{(1 : Fin 6)}}> ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> b3 >> r))
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}> (b3 >> r)) := by
  rcases b3 with ⟨_ | _ | n, hn⟩
  · stepK
  · stepK
  · omega

private theorem reach_R3_lb (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 5
      (l {{(1 : Fin 6)}}> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (((0 : Fin 2) >> l) {{(1 : Fin 6)}}> ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) := by
        stepK

private theorem reach_L1_lb (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 2
      (((0 : Fin 2) >> l) {{(2 : Fin 6)}}> ((0 : Fin 2) >> r))
      (((1 : Fin 2) >> l) {{(1 : Fin 6)}}> ((1 : Fin 2) >> r)) := by stepK

private theorem reach_L2_lb (cb : Fin 2) (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 3
      (((1 : Fin 2) >> (1 : Fin 2) >> cb >> l) {{(2 : Fin 6)}}> ((0 : Fin 2) >> r))
      (l {{(1 : Fin 6)}}> (cb >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  rcases cb with ⟨_ | _ | n, hn⟩
  · stepK
  · stepK
  · omega

private theorem reach_L3_lb (l r : ListBlank (Fin 2)) :
    ReachesIn target_tm 4
      (((1 : Fin 2) >> (0 : Fin 2) >> l) {{(2 : Fin 6)}}> ((0 : Fin 2) >> r))
      (((1 : Fin 2) >> (1 : Fin 2) >> l) {{(1 : Fin 6)}}> ((1 : Fin 2) >> r)) := by stepK

/-! ### Quadratic Era Lemmas (`era_drain`, `era_osc`, `era_osc10`) -/

private theorem era_drain_one (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (rep110 (2 * (k + 1)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))
      (rep110 (2 * (k + 2)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  have hs1 := reach_splitL_lb (k + 1) ((1 : Fin 2) >> (1 : Fin 2) >> lb0)
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)
  have ht1 : ReachesIn target_tm 5
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * (k + 1)) ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 :
          Fin 2) >> r)))
      (((1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * k + 3) ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
          2) >> r))) := by
    have ha : 2 * k + 3 = 1 + 2 * (k + 1) := by omega
    rw [ha, rep001_add 1 (2 * (k + 1))]
    dsimp only [rep001, lb0]
    conv_lhs => rw [← lb_zero_cons_default, ← lb_zero_cons_default]
    stepK
  have hs2 := reach_splitR_lb (2 * k + 3) ((1 : Fin 2) >> lb0)
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)
  have ht2 := reach_R1_lb (rep110 (2 * k + 3) ((1 : Fin 2) >> lb0))
    ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)
  have hl3_eq : rep110 (2 * k + 3) ((1 : Fin 2) >> lb0) =
      rep110 (2 * (k + 1)) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0) := by
    have ha : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
    rw [ha, rep110_add (2 * (k + 1)) 1]
    rfl
  have hs3 := reach_splitL_lb (k + 1)
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0)
    ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)
  rw [← hl3_eq] at hs3
  have ht3 : ReachesIn target_tm 7
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * (k + 1)) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 :
          Fin 2) >> r)))
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * k + 3) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
          2) >> r))) := by
    have ha : 2 * k + 3 = 1 + 2 * (k + 1) := by omega
    rw [ha, rep001_add 1 (2 * (k + 1))]
    dsimp only [rep001, lb0]
    conv_lhs => rw [← lb_zero_cons_default]
    stepK
  have hs4 := reach_splitR_lb (2 * k + 3) ((1 : Fin 2) >> (1 : Fin 2) >> lb0)
    ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)
  have ht4 := reach_R2_lb 0 (rep110 (2 * k + 3) ((1 : Fin 2) >> (1 : Fin 2) >> lb0))
    ((1 : Fin 2) >> r)
  have hl4_eq : ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      rep110 (2 * k + 3) ((1 : Fin 2) >> (1 : Fin 2) >> lb0)) =
      rep110 (2 * (k + 2)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) := by
    have ha : 2 * (k + 2) = 1 + (2 * k + 3) := by omega
    rw [ha, rep110_add 1 (2 * k + 3)]
    rfl
  rw [hl4_eq] at ht4
  exact (((((((hs1.trans ht1).trans hs2).trans ht2).trans hs3).trans ht3).trans hs4).trans
    ht4).to_plus (by omega)

private theorem era_drain_iter : ∀ (c_m1 k : ℕ) (r : ListBlank (Fin 2)),
    ReachesPlus target_tm
      (rep110 (2 * (k + 1)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> rep001 (c_m1 + 1) r))
      (rep110 (2 * (k + 1 + (c_m1 + 1))) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> r))
  | 0, k, r => by
    dsimp only [rep001]
    have hk : k + 1 + 1 = k + 2 := by omega
    rw [hk]
    exact era_drain_one k r
  | c_m1 + 1, k, r => by
    have hc : c_m1 + 1 + 1 = 1 + (c_m1 + 1) := by omega
    conv_lhs => rw [hc, rep001_add 1 (c_m1 + 1)]
    dsimp only [rep001]
    have h1 := era_drain_one k (rep001 (c_m1 + 1) r)
    have h2 := era_drain_iter c_m1 (k + 1) r
    have hk2 : 2 * (k + 1 + 1 + (c_m1 + 1)) = 2 * (k + 1 + (c_m1 + 1 + 1)) := by omega
    rw [hk2] at h2
    exact stepPlus_trans h1 h2

private theorem era_osc_one (j : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * j) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2)
          >> r)))
      (((0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (j + 1)) ((0 : Fin 2) >> r))) := by
  let L0 := (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l
  have hs1 := reach_splitR_lb (2 * j) L0 ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2)
    >> r)
  have ht1 := reach_R2_lb 0 (rep110 (2 * j) L0) ((1 : Fin 2) >> r)
  rw [← rep110_shift (2 * j) L0] at ht1
  have hs2 := reach_splitL_lb j ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L0) ((1 : Fin 2) >> r)
  have ht2 : ReachesIn target_tm 5
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * j) ((1 : Fin 2) >> r)))
      (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * j + 1) ((1 : Fin 2) >> r))) := by
    have ha : 2 * j + 1 = 1 + 2 * j := by omega
    rw [ha, rep001_add 1 (2 * j)]
    dsimp only [rep001, L0]
    stepK
  let L1 := (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l
  have hs3 := reach_splitR_lb (2 * j + 1) L1 ((1 : Fin 2) >> r)
  have ht3 := reach_R1_lb (rep110 (2 * j + 1) L1) r
  have hl3_eq : rep110 (2 * j + 1) L1 =
      rep110 (2 * j) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L1) := by
    rw [rep110_add (2 * j) 1]
    rfl
  have hs4 := reach_splitL_lb j ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L1) ((0 : Fin 2) >> r)
  rw [← hl3_eq] at hs4
  have ht4 : ReachesIn target_tm 6
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L1) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * j) ((0 : Fin 2) >> r)))
      (((0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (j + 1)) ((0 : Fin 2) >> r))) := by
    have ha : 2 * (j + 1) = 2 + 2 * j := by omega
    rw [ha, rep001_add 2 (2 * j)]
    dsimp only [rep001, L1]
    stepK
  exact (((((((hs1.trans ht1).trans hs2).trans ht2).trans hs3).trans ht3).trans hs4).trans
    ht4).to_plus (by omega)

private theorem era_osc_iter : ∀ (n_m1 j : ℕ) (l r : ListBlank (Fin 2)),
    ReachesPlus target_tm
      (((0 : Fin 2) >> rep110 (n_m1 + 1) l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * j) ((0 : Fin 2) >> rep001 (n_m1 + 1) r)))
      (((0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (j + (n_m1 + 1))) ((0 : Fin 2) >> r)))
  | 0, j, l, r => by
    dsimp only [rep110, rep001]
    exact era_osc_one j l r
  | n_m1 + 1, j, l, r => by
    have hn : n_m1 + 1 + 1 = 1 + (n_m1 + 1) := by omega
    conv_lhs => rw [hn, rep110_add 1 (n_m1 + 1), rep001_add 1 (n_m1 + 1)]
    dsimp only [rep110, rep001]
    have h1 := era_osc_one j (rep110 (n_m1 + 1) l) (rep001 (n_m1 + 1) r)
    have h2 := era_osc_iter n_m1 (j + 1) l r
    have hj : 2 * (j + 1 + (n_m1 + 1)) = 2 * (j + (n_m1 + 1 + 1)) := by omega
    rw [hj] at h2
    exact stepPlus_trans h1 h2

private theorem era_osc10_one (j : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin
        6)}}>
        ((1 : Fin 2) >> rep001 (2 * j) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2)
          >> r)))
      (((1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (j + 1)) ((0 : Fin 2) >> r))) := by
  let L0 := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l
  have hs1 := reach_splitR_lb (2 * j) L0 ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2)
    >> r)
  have ht1 := reach_R2_lb 0 (rep110 (2 * j) L0) ((1 : Fin 2) >> r)
  rw [← rep110_shift (2 * j) L0] at ht1
  have hs2 := reach_splitL_lb j ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L0) ((1 : Fin 2) >> r)
  have ht2 : ReachesIn target_tm 7
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * j) ((1 : Fin 2) >> r)))
      (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin
        6)}}>
        ((1 : Fin 2) >> rep001 (2 * j + 1) ((1 : Fin 2) >> r))) := by
    have ha : 2 * j + 1 = 1 + 2 * j := by omega
    rw [ha, rep001_add 1 (2 * j)]
    dsimp only [rep001, L0]
    stepK
  let L1 := (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l
  have hs3 := reach_splitR_lb (2 * j + 1) L1 ((1 : Fin 2) >> r)
  have ht3 := reach_R1_lb (rep110 (2 * j + 1) L1) r
  have hl3_eq : rep110 (2 * j + 1) L1 =
      rep110 (2 * j) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L1) := by
    rw [rep110_add (2 * j) 1]
    rfl
  have hs4 := reach_splitL_lb j ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L1) ((0 : Fin 2) >> r)
  rw [← hl3_eq] at hs4
  have ht4 : ReachesIn target_tm 6
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L1) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * j) ((0 : Fin 2) >> r)))
      (((1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (j + 1)) ((0 : Fin 2) >> r))) := by
    have ha : 2 * (j + 1) = 2 + 2 * j := by omega
    rw [ha, rep001_add 2 (2 * j)]
    dsimp only [rep001, L1]
    stepK
  exact (((((((hs1.trans ht1).trans hs2).trans ht2).trans hs3).trans ht3).trans hs4).trans
    ht4).to_plus (by omega)

private theorem era_osc10_iter : ∀ (n_m1 j : ℕ) (l r : ListBlank (Fin 2)),
    ReachesPlus target_tm
      (((1 : Fin 2) >> (0 : Fin 2) >> rep110 (n_m1 + 1) l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * j) ((0 : Fin 2) >> rep001 (n_m1 + 1) r)))
      (((1 : Fin 2) >> (0 : Fin 2) >> l) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (j + (n_m1 + 1))) ((0 : Fin 2) >> r)))
  | 0, j, l, r => by
    dsimp only [rep110, rep001]
    exact era_osc10_one j l r
  | n_m1 + 1, j, l, r => by
    have hn : n_m1 + 1 + 1 = 1 + (n_m1 + 1) := by omega
    conv_lhs => rw [hn, rep110_add 1 (n_m1 + 1), rep001_add 1 (n_m1 + 1)]
    dsimp only [rep110, rep001]
    have h1 := era_osc10_one j (rep110 (n_m1 + 1) l) (rep001 (n_m1 + 1) r)
    have h2 := era_osc10_iter n_m1 (j + 1) l r
    have hj : 2 * (j + 1 + (n_m1 + 1)) = 2 * (j + (n_m1 + 1 + 1)) := by omega
    rw [hj] at h2
    exact stepPlus_trans h1 h2

/-! ### Exponential `4^m` Super-Era Cascade Lemmas (`super4x`) -/

def pow4 : ℕ → ℕ
  | 0 => 1
  | m + 1 => 4 * pow4 m

def sum4 : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + 4 * sum4 m

private theorem pow4_eq_pow : ∀ (m : ℕ), pow4 m = 4 ^ m
  | 0 => rfl
  | m + 1 => by
    dsimp only [pow4]
    rw [pow4_eq_pow m, Nat.pow_succ, Nat.mul_comm]

private theorem sum4_spec : ∀ (m : ℕ), 3 * sum4 m + 1 = pow4 m
  | 0 => rfl
  | m + 1 => by
    dsimp only [sum4, pow4]
    have := sum4_spec m
    omega

private theorem sum4_eq_div (m : ℕ) : sum4 m = (4 ^ m - 1) / 3 := by
  have h1 := sum4_spec m
  rw [pow4_eq_pow] at h1
  omega

private theorem sum4_add : ∀ (m d : ℕ), sum4 (m + d) = pow4 d * sum4 m + sum4 d
  | _, 0 => by simp [pow4, sum4]
  | m, d + 1 => by
    rw [← Nat.add_assoc]
    dsimp only [sum4, pow4]
    have ih := sum4_add m d
    rw [ih]
    ring

private theorem pow4_add : ∀ (m d : ℕ), pow4 (m + d) = pow4 d * pow4 m
  | _, 0 => by simp [pow4]
  | m, d + 1 => by
    rw [← Nat.add_assoc]
    dsimp only [pow4]
    rw [pow4_add m d]
    ring

private theorem pow4_pos : ∀ k : ℕ, 1 ≤ pow4 k
  | 0 => Nat.le_refl 1
  | k + 1 => by dsimp only [pow4]; have := pow4_pos k; omega

private theorem sum4_odd (m : ℕ) (hm : 1 ≤ m) : sum4 m % 2 = 1 := by
  cases m with
  | zero => omega
  | succ k => dsimp only [sum4]; omega

private theorem sum4_lower : ∀ (m : ℕ), 10 ≤ m → 15000 * m + 150000 ≤ sum4 m
  | 0, h => by omega
  | m + 1, h => by
    by_cases hm : m = 9
    · subst hm; decide
    · have h10 : 10 ≤ m := by omega
      have ih := sum4_lower m h10
      dsimp only [sum4]
      omega

private theorem super4x_pre1 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 92
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >> rep001 3 r))
      (lb0 {{(1 : Fin 6)}}> ((1 : Fin 2) >> rep001 4 ((0 : Fin 2) >> r))) := by
  have h : ReachesIn target_tm 92
      (((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default) {{(1 :
        Fin 6)}}>
        ((0 : Fin 2) >> rep001 3 r))
      (((0 : Fin 2) >> default) {{(1 : Fin 6)}}> ((1 : Fin 2) >> rep001 4 ((0 : Fin 2) >> r))) := by
    dsimp only [rep001]
    stepK
  simpa only [lb0, lb_zero_cons_default] using h

private theorem super4x_pre2 (r : ListBlank (Fin 2)) :
    ReachesIn target_tm 86
      (lb0 {{(1 : Fin 6)}}> ((1 : Fin 2) >> rep001 4 ((0 : Fin 2) >> rep001 2 r)))
      (rep110 6 ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 86
      (((0 : Fin 2) >> (0 : Fin 2) >> default) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 4 ((0 : Fin 2) >> rep001 2 r)))
      (rep110 6 ((1 : Fin 2) >> (1 : Fin 2) >> default) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by
    dsimp only [rep001, rep110]
    stepK
  simpa only [lb0, lb_zero_cons_default] using h

private theorem super4x_partA (a d : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 (2 * (a + 3)) ((0 : Fin 2) >> rep001 (2 * (2 * (a + 3)) + 1 + d) r)))
      (rep110 (2 * (2 * a + 5)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a + 12 + d) r)) := by
  set r0 := (0 : Fin 2) >> rep001 (2 * (2 * (a + 3)) + 1 + d) r
  have ha_split : 2 * (a + 3) = 3 + (2 + (2 * a + 1)) := by omega
  conv_lhs => rw [ha_split, rep001_add 3 (2 + (2 * a + 1)), rep001_add 2 (2 * a + 1)]
  have hp1 := (super4x_pre1 (rep001 2 (rep001 (2 * a + 1) r0))).to_plus (by omega)
  have hp2 := (super4x_pre2 (rep001 (2 * a + 1) r0)).to_plus (by omega)
  have hdr := era_drain_iter (2 * a) 2 r0
  have hdr_in : 2 * (2 + 1) = 6 := by omega
  have hdr_out : 2 * (2 + 1 + (2 * a + 1)) = 2 * (2 * a + 4) := by omega
  rw [hdr_in, hdr_out] at hdr
  have hs19 := (reach_splitL_lb (2 * a + 4) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) ((1 : Fin 2) >>
    r0)).to_star
  have ht19 : ReachesIn target_tm 5
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * (2 * a + 4)) ((1 : Fin 2) >> r0)))
      (((1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (4 * a + 9) ((1 : Fin 2) >> r0))) := by
    have h19a : 4 * a + 9 = 1 + 2 * (2 * a + 4) := by omega
    rw [h19a, rep001_add 1 (2 * (2 * a + 4))]
    dsimp only [rep001, lb0]
    conv_lhs => rw [← lb_zero_cons_default, ← lb_zero_cons_default]
    stepK
  have hs20 := (reach_splitR_lb (4 * a + 9) ((1 : Fin 2) >> lb0) ((1 : Fin 2) >> r0)).to_star
  have ht20 := (reach_R1_lb (rep110 (4 * a + 9) ((1 : Fin 2) >> lb0)) r0).to_star
  have hl21 : rep110 (4 * a + 9) ((1 : Fin 2) >> lb0) =
      rep110 (2 * (2 * a + 4)) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0)
        := by
    have h21a : 4 * a + 9 = 2 * (2 * a + 4) + 1 := by omega
    rw [h21a, rep110_add (2 * (2 * a + 4)) 1]
    rfl
  have hs21 := (reach_splitL_lb (2 * a + 4)
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0) ((0 : Fin 2) >> r0)).to_star
  rw [← hl21] at hs21
  have ht21 : ReachesIn target_tm 7
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * (2 * a + 4)) ((0 : Fin 2) >> r0)))
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (4 * a + 9) ((0 : Fin 2) >> r0))) := by
    have h21a : 4 * a + 9 = 1 + 2 * (2 * a + 4) := by omega
    rw [h21a, rep001_add 1 (2 * (2 * a + 4))]
    dsimp only [rep001, lb0]
    conv_lhs => rw [← lb_zero_cons_default]
    stepK
  have hr0_eq : (0 : Fin 2) >> r0 =
      (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a +
        12 + d) r := by
    dsimp only [r0]
    have hb : 2 * (2 * (a + 3)) + 1 + d = 1 + (4 * a + 12 + d) := by omega
    rw [hb, rep001_add 1 (4 * a + 12 + d)]
    rfl
  have hs22 : ReachesStar target_tm
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (4 * a + 9) ((0 : Fin 2) >> r0)))
      (rep110 (4 * a + 9) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          rep001 (4 * a + 12 + d) r)) := by
    rw [hr0_eq]
    exact (reach_splitR_lb (4 * a + 9) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) _).to_star
  have ht22 := (reach_R2_lb 0 (rep110 (4 * a + 9) ((1 : Fin 2) >> (1 : Fin 2) >> lb0))
    ((0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a + 12 + d) r)).to_star
  have hl22 : ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      rep110 (4 * a + 9) ((1 : Fin 2) >> (1 : Fin 2) >> lb0)) =
      rep110 (2 * (2 * a + 5)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) := by
    have h22a : 2 * (2 * a + 5) = 1 + (4 * a + 9) := by omega
    rw [h22a, rep110_add 1 (4 * a + 9)]
    rfl
  rw [hl22] at ht22
  have hpre := stepPlus_trans (stepPlus_trans hp1 hp2) hdr
  have htail := stepStar_trans hs19 (stepStar_trans ht19.to_star (stepStar_trans hs20
    (stepStar_trans ht20 (stepStar_trans hs21 (stepStar_trans ht21.to_star (stepStar_trans hs22
      ht22))))))
  exact reachesPlus_trans_star hpre htail

private theorem super4x_partB (a d : ℕ) (r : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (rep110 (2 * (2 * a + 5)) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a + 12 + d) r))
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 (4 * (2 * (a + 3))) ((0 : Fin 2) >> rep001 d r))) := by
  set r22 := (0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a + 12 + d) r
  have hs23 := (reach_splitL_lb (2 * a + 5) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) r22).to_star
  have ht23 : ReachesIn target_tm 5
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (2 * (2 * a + 5)) r22))
      (((1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (4 * a + 11) r22)) := by
    have h23a : 4 * a + 11 = 1 + 2 * (2 * a + 5) := by omega
    rw [h23a, rep001_add 1 (2 * (2 * a + 5))]
    dsimp only [rep001, lb0]
    conv_lhs => rw [← lb_zero_cons_default, ← lb_zero_cons_default]
    stepK
  have hr24_eq : r22 =
      (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a +
        11 + d) r := by
    dsimp only [r22]
    have hb : 4 * a + 12 + d = 1 + (4 * a + 11 + d) := by omega
    rw [hb, rep001_add 1 (4 * a + 11 + d)]
    rfl
  have hs24 : ReachesStar target_tm
      (((1 : Fin 2) >> lb0) {{(1 : Fin 6)}}> ((1 : Fin 2) >> rep001 (4 * a + 11) r22))
      (rep110 (4 * a + 11) ((1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          rep001 (4 * a + 11 + d) r)) := by
    rw [hr24_eq]
    exact (reach_splitR_lb (4 * a + 11) ((1 : Fin 2) >> lb0) _).to_star
  have ht24 := (reach_R3_lb (rep110 (4 * a + 11) ((1 : Fin 2) >> lb0))
    ((0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a + 11 + d) r)).to_star
  have hr24_out : ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 (4 * a + 11
    + d) r) =
      (0 : Fin 2) >> rep001 ((4 * a + 10 + 1) + (1 + d)) r := by
    have hb : (4 * a + 10 + 1) + (1 + d) = 1 + (4 * a + 11 + d) := by omega
    rw [hb, rep001_add 1 (4 * a + 11 + d)]
    rfl
  rw [hr24_out, rep001_add (4 * a + 10 + 1) (1 + d)] at ht24
  have hosc := (era_osc_iter (4 * a + 10) 0 ((1 : Fin 2) >> lb0) (rep001 (1 + d) r)).to_star
  simp only [Nat.mul_zero, Nat.zero_add] at hosc
  dsimp only [rep001] at hosc
  have hr26_eq : (0 : Fin 2) >> rep001 (1 + d) r =
      (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 d r := by
    rw [rep001_add 1 d]
    rfl
  have hs26 : ReachesStar target_tm
      (((0 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (2 * (4 * a + 11)) ((0 : Fin 2) >> rep001 (1 + d) r)))
      (rep110 (2 * (4 * a + 11)) ((0 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep001 d r))
          := by
    rw [hr26_eq]
    exact (reach_splitR_lb (2 * (4 * a + 11)) ((0 : Fin 2) >> (1 : Fin 2) >> lb0) _).to_star
  have ht26 := (reach_R2_lb 0 (rep110 (2 * (4 * a + 11)) ((0 : Fin 2) >> (1 : Fin 2) >> lb0))
    ((1 : Fin 2) >> rep001 d r)).to_star
  have hl26 : ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      rep110 (2 * (4 * a + 11)) ((0 : Fin 2) >> (1 : Fin 2) >> lb0)) =
      rep110 (2 * (4 * a + 11))
        ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0) := by
    rw [← rep110_shift (2 * (4 * a + 11))]
  rw [hl26] at ht26
  have hs27 := (reach_splitL_lb (4 * a + 11)
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0)
    ((1 : Fin 2) >> rep001 d r)).to_star
  have ht27 : ReachesIn target_tm 5
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin
        6)}}>
        ((0 : Fin 2) >> rep001 (2 * (4 * a + 11)) ((1 : Fin 2) >> rep001 d r)))
      (((1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin 6)}}>
        ((1 : Fin 2) >> rep001 (8 * a + 23) ((1 : Fin 2) >> rep001 d r))) := by
    have h27a : 8 * a + 23 = 1 + 2 * (4 * a + 11) := by omega
    rw [h27a, rep001_add 1 (2 * (4 * a + 11))]
    dsimp only [rep001]
    stepK
  have hs28 := (reach_splitR_lb (8 * a + 23) ((1 : Fin 2) >> (1 : Fin 2) >> lb0)
    ((1 : Fin 2) >> rep001 d r)).to_star
  have ht28 := (reach_R1_lb (rep110 (8 * a + 23) ((1 : Fin 2) >> (1 : Fin 2) >> lb0)) (rep001 d
    r)).to_star
  have hl29 : rep110 (8 * a + 23) ((1 : Fin 2) >> (1 : Fin 2) >> lb0) =
      rep110 (2 * (4 * a + 11))
        ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> lb0) := by
    have h29a : 8 * a + 23 = 2 * (4 * a + 11) + 1 := by omega
    rw [h29a, rep110_add (2 * (4 * a + 11)) 1]
    rfl
  have hs29 := (reach_splitL_lb (4 * a + 11)
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> lb0)
    ((0 : Fin 2) >> rep001 d r)).to_star
  rw [← hl29] at hs29
  have ht29 : ReachesIn target_tm 6
      (((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> lb0) {{(1 : Fin
        6)}}>
        ((0 : Fin 2) >> rep001 (2 * (4 * a + 11)) ((0 : Fin 2) >> rep001 d r)))
      (lb0 {{(1 : Fin 6)}}>
        ((0 : Fin 2) >> rep001 (4 * (2 * (a + 3))) ((0 : Fin 2) >> rep001 d r))) := by
    have h29a : 4 * (2 * (a + 3)) = 2 + 2 * (4 * a + 11) := by omega
    rw [h29a, rep001_add 2 (2 * (4 * a + 11))]
    dsimp only [rep001, lb0]
    conv_lhs => rw [← lb_zero_cons_default]
    exact rstep_rl rfl (rstep_rl rfl (rstep_rl rfl (rstep_rl rfl (rstep_rl rfl (rstep_rl rfl
      (reachesIn_zero _))))))
  exact stepStar_trans hs23 (stepStar_trans ht23.to_star (stepStar_trans hs24 (stepStar_trans ht24
    (stepStar_trans hosc (stepStar_trans hs26 (stepStar_trans ht26 (stepStar_trans hs27
      (stepStar_trans ht27.to_star (stepStar_trans hs28 (stepStar_trans ht28
        (stepStar_trans hs29 ht29.to_star)))))))))))

private theorem super4x_one (a d : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 (2 * (a + 3)) ((0 : Fin 2) >> rep001 (2 * (2 * (a + 3)) + 1 + d) r)))
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 (4 * (2 * (a + 3))) ((0 : Fin 2) >> rep001 d r))) :=
  reachesPlus_trans_star (super4x_partA a d r) (super4x_partB a d r)

private theorem super4x_iter : ∀ (m a d : ℕ) (r : ListBlank (Fin 2)),
    let A := 2 * (a + 3)
    ReachesStar target_tm
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 A ((0 : Fin 2) >> rep001 (2 * A * sum4 m + m + d) r)))
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 (A * pow4 m) ((0 : Fin 2) >> rep001 d r)))
  | 0, a, d, r => by
    dsimp only [sum4, pow4]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
    exact reachesStar_refl _
  | m + 1, a, d, r => by
    intro A
    have hdr_eq : 2 * A * sum4 (m + 1) + (m + 1) + d =
        2 * A + 1 + (2 * (2 * (4 * a + 9 + 3)) * sum4 m + m + d) := by
      dsimp only [sum4, A]; ring
    rw [hdr_eq]
    have h1 := (super4x_one a (2 * (2 * (4 * a + 9 + 3)) * sum4 m + m + d) r).to_star
    have ha_next : 4 * A = 2 * (4 * a + 9 + 3) := by dsimp only [A]; omega
    rw [show 2 * (a + 3) = A from rfl, ha_next] at h1
    have h2 := super4x_iter m (4 * a + 9) d r
    dsimp only at h2
    have hout_eq : 2 * (4 * a + 9 + 3) * pow4 m = A * pow4 (m + 1) := by
      dsimp only [pow4, A]; ring
    rw [hout_eq] at h2
    exact stepStar_trans h1 h2

private theorem super4x_iter_plus (m a d : ℕ) (hm : 0 < m) (r : ListBlank (Fin 2)) :
    let A := 2 * (a + 3)
    ReachesPlus target_tm
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 A ((0 : Fin 2) >> rep001 (2 * A * sum4 m + m + d) r)))
      (lb0 {{(1 : Fin 6)}}> ((0 : Fin 2) >>
        rep001 (A * pow4 m) ((0 : Fin 2) >> rep001 d r))) := by
  cases m with
  | zero => omega
  | succ k =>
    intro A
    have hdr_eq : 2 * A * sum4 (k + 1) + (k + 1) + d =
        2 * A + 1 + (2 * (2 * (4 * a + 9 + 3)) * sum4 k + k + d) := by
      dsimp only [sum4, A]; ring
    rw [hdr_eq]
    have h1 := super4x_one a (2 * (2 * (4 * a + 9 + 3)) * sum4 k + k + d) r
    have ha_next : 4 * A = 2 * (4 * a + 9 + 3) := by dsimp only [A]; omega
    rw [show 2 * (a + 3) = A from rfl, ha_next] at h1
    have h2 := super4x_iter k (4 * a + 9) d r
    dsimp only at h2
    have hout_eq : 2 * (4 * a + 9 + 3) * pow4 k = A * pow4 (k + 1) := by
      dsimp only [pow4, A]; ring
    rw [hout_eq] at h2
    exact reachesPlus_trans_star h1 h2

/-! ### Part 1: Fast Concrete Macro Executor (`init [] ⊢* C(N₀)`) -/

inductive LChunk : Type where
  | b0 : LChunk
  | b1 : LChunk
  | t110 (m : ℕ) : LChunk
  deriving DecidableEq

inductive RChunk : Type where
  | b0 : RChunk
  | b1 : RChunk
  | t001 (m : ℕ) : RChunk
  deriving DecidableEq

structure State : Type where
  hd : Fin 2
  l : List LChunk
  r : List RChunk
  deriving DecidableEq

def exL : List LChunk → ListBlank (Fin 2)
  | [] => default
  | .b0 :: tl => (0 : Fin 2) >> exL tl
  | .b1 :: tl => (1 : Fin 2) >> exL tl
  | .t110 m :: tl => rep110 (m + 1) (exL tl)

def exR : List RChunk → ListBlank (Fin 2)
  | [] => default
  | .b0 :: tl => (0 : Fin 2) >> exR tl
  | .b1 :: tl => (1 : Fin 2) >> exR tl
  | .t001 m :: tl => rep001 (m + 1) (exR tl)

def encode (s : State) : Cfg (Fin 2) (Fin 6) :=
  exL s.l {{(1 : Fin 6)}}> (s.hd >> exR s.r)

def pushL110 (m : ℕ) : List LChunk → List LChunk
  | .t110 k :: tl => .t110 (m + 1 + k) :: tl
  | l => .t110 m :: l

def pushLNat110 : ℕ → List LChunk → List LChunk
  | 0, l => l
  | m + 1, l => pushL110 m l

def pushL0 : List LChunk → List LChunk
  | [] => []
  | l => .b0 :: l

def pushL1 : List LChunk → List LChunk
  | .b1 :: .b0 :: tl => pushL110 0 tl
  | l => .b1 :: l

def pushR001 (m : ℕ) : List RChunk → List RChunk
  | .t001 k :: tl => .t001 (m + 1 + k) :: tl
  | r => .t001 m :: r

def pushRNat001 : ℕ → List RChunk → List RChunk
  | 0, r => r
  | m + 1, r => pushR001 m r

def pushR0 : List RChunk → List RChunk
  | [] => []
  | .b0 :: .b1 :: tl => pushR001 0 tl
  | r => .b0 :: r

def pushR1 (r : List RChunk) : List RChunk :=
  .b1 :: r

def popL : List LChunk → Fin 2 × List LChunk
  | [] => (0, [])
  | .b0 :: tl => (0, tl)
  | .b1 :: tl => (1, tl)
  | .t110 0 :: tl => (1, .b1 :: .b0 :: tl)
  | .t110 (m + 1) :: tl => (1, .b1 :: .b0 :: .t110 m :: tl)

def popR : List RChunk → Fin 2 × List RChunk
  | [] => (0, [])
  | .b0 :: tl => (0, tl)
  | .b1 :: tl => (1, tl)
  | .t001 0 :: tl => (0, .b0 :: .b1 :: tl)
  | .t001 (m + 1) :: tl => (0, .b0 :: .b1 :: .t001 m :: tl)

def splitRChunk : List LChunk → List RChunk → List LChunk × List RChunk
  | l, .t001 m :: r => splitRChunk (pushL110 m l) r
  | l, r => (l, r)

def splitLChunk : List LChunk → List RChunk → List LChunk × List RChunk
  | .t110 (m1 + 1) :: l, r =>
    let p := m1 / 2
    let r1 := pushR001 (2 * p + 1) r
    if m1 % 2 = 0 then splitLChunk l r1
    else (.t110 0 :: l, r1)
  | l, r => (l, r)

def stripOnesL : List LChunk → List RChunk → List LChunk × List RChunk
  | [], r => ([], r)
  | .b0 :: tl, r => (tl, r)
  | .b1 :: tl, r => stripOnesL tl (pushR0 r)
  | .t110 0 :: tl, r => (tl, pushR0 (pushR0 r))
  | .t110 (m + 1) :: tl, r => (.t110 m :: tl, pushR0 (pushR0 r))

def okSuper4x (A B m : ℕ) : Bool :=
  0 < m && (2 * A * ((4 ^ m - 1) / 3) + m < B)

def bsearchM (A B : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 ≥ hi then lo
    else
      let mid := (lo + hi) / 2
      if okSuper4x A B mid then bsearchM A B fuel mid hi
      else bsearchM A B fuel lo mid

def findMaxM (A B : ℕ) : ℕ :=
  if okSuper4x A B 1 then bsearchM A B 9 1 512 else 0

def trySuper4x (hd : Fin 2) (l : List LChunk) (r : List RChunk) : Option State :=
  if hd = 0 then
    match l, r with
    | [], .t001 a_m1 :: .b0 :: .t001 b_m1 :: rtail =>
      if 5 ≤ a_m1 && a_m1 % 2 = 1 then
        let A := a_m1 + 1
        let B := b_m1 + 1
        let m := findMaxM A B
        if 0 < m then
          let p4 := 4 ^ m
          let s4 := (p4 - 1) / 3
          let dr := 2 * A * s4 + m
          if dr + 1 ≤ B then
            some ⟨0, [], .t001 (A * p4 - 1) :: .b0 :: .t001 (B - (dr + 1)) :: rtail⟩
          else none
        else none
      else none
    | _, _ => none
  else none

def tryEraDrain (hd : Fin 2) (l : List LChunk) (r : List RChunk) : Option State :=
  if hd = 0 then
    match l, r with
    | [.t110 (m1 + 1), .b1, .b1], .b1 :: .t001 c_m1 :: rtail =>
      if m1 % 2 = 0 then
        some ⟨0, [.t110 (m1 + 1 + 2 * (c_m1 + 1)), .b1, .b1], pushR1 rtail⟩
      else none
    | _, _ => none
  else none

def tryEraOscR (r : List RChunk) : Option (ℕ × ℕ × List RChunk) :=
  match r with
  | .b0 :: .t001 c_m1 :: rtail => some (0, c_m1, rtail)
  | .t001 (m1 + 1) :: .b0 :: .t001 c_m1 :: rtail =>
    if m1 % 2 = 0 then some (m1 / 2 + 1, c_m1, rtail) else none
  | _ => none

def tryEraOsc (hd : Fin 2) (l : List LChunk) (r : List RChunk) : Option State :=
  if hd = 1 then
    match l with
    | .b0 :: .t110 a_m1 :: ltail =>
      match tryEraOscR r with
      | some (j, c_m1, rtail) =>
        let n_m1 := min a_m1 c_m1
        let l_new := pushL0 (pushLNat110 (a_m1 - n_m1) ltail)
        let r_new := pushR001 (2 * j + 2 * n_m1 + 1) (pushR0 (pushRNat001 (c_m1 - n_m1) rtail))
        some ⟨1, l_new, r_new⟩
      | none => none
    | .b1 :: .b0 :: .t110 a_m1 :: ltail =>
      match tryEraOscR r with
      | some (j, c_m1, rtail) =>
        let n_m1 := min a_m1 c_m1
        let l_new := pushL1 (pushL0 (pushLNat110 (a_m1 - n_m1) ltail))
        let r_new := pushR001 (2 * j + 2 * n_m1 + 1) (pushR0 (pushRNat001 (c_m1 - n_m1) rtail))
        some ⟨1, l_new, r_new⟩
      | none => none
    | _ => none
  else none

def stepBase (hd : Fin 2) (l : List LChunk) (r : List RChunk) : Option State :=
  if hd = 1 then
    let (l1, r_in) := splitRChunk l r
    let (b1, r1) := popR r_in
    if b1 = 1 then some ⟨0, l1, pushR0 r1⟩
    else
      let (b2, r2) := popR r1
      if b2 = 0 then
        let (b3, r3) := popR r2
        some ⟨b3, pushL110 0 l1, r3⟩
      else
        let (b3, r3) := popR r2
        if b3 = 0 then some ⟨1, pushL0 l1, pushR0 (pushR0 r3)⟩
        else none
  else
    let (l1, r1) := splitLChunk l r
    let (l_after, r_rem) := stripOnesL l1 (pushR1 r1)
    let (e, e_rem) := popL l_after
    if e = 0 then some ⟨1, pushL1 e_rem, r_rem⟩
    else
      let (ab, a_rem) := popL e_rem
      if ab = 1 then
        let (cb, c_rem) := popL a_rem
        some ⟨cb, c_rem, pushR001 0 r_rem⟩
      else some ⟨1, pushL1 (pushL1 a_rem), r_rem⟩

def stepFast (s : State) : Option State :=
  match trySuper4x s.hd s.l s.r with
  | some s' => some s'
  | none =>
    match tryEraDrain s.hd s.l s.r with
    | some s' => some s'
    | none =>
      match tryEraOsc s.hd s.l s.r with
      | some s' => some s'
      | none => stepBase s.hd s.l s.r

def iterPow2 : ℕ → State → Option State
  | 0, s => stepFast s
  | k + 1, s => (iterPow2 k s).bind (iterPow2 k)

private theorem exL_pushL110 (m : ℕ) (l : List LChunk) :
    exL (pushL110 m l) = rep110 (m + 1) (exL l) := by
  cases l with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | b0 => rfl
    | b1 => rfl
    | t110 k =>
      dsimp only [pushL110, exL]
      have ha : m + 1 + k + 1 = (m + 1) + (k + 1) := by omega
      rw [ha, rep110_add]

private theorem exL_pushLNat110 (n : ℕ) (l : List LChunk) :
    exL (pushLNat110 n l) = rep110 n (exL l) := by
  cases n with
  | zero => rfl
  | succ m => exact exL_pushL110 m l

private theorem exL_pushL0 (l : List LChunk) :
    exL (pushL0 l) = (0 : Fin 2) >> exL l := by
  cases l with
  | nil => exact lb_zero_cons_default.symm
  | cons _ _ => rfl

private theorem exL_pushL1 (l : List LChunk) :
    exL (pushL1 l) = (1 : Fin 2) >> exL l := by
  cases l with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | b0 => rfl
    | t110 _ => rfl
    | b1 =>
      cases tl with
      | nil => rfl
      | cons hd2 tl2 =>
        cases hd2 with
        | b1 => rfl
        | t110 _ => rfl
        | b0 => dsimp only [pushL1]; rw [exL_pushL110]; rfl

private theorem exR_pushR001 (m : ℕ) (r : List RChunk) :
    exR (pushR001 m r) = rep001 (m + 1) (exR r) := by
  cases r with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | b0 => rfl
    | b1 => rfl
    | t001 k =>
      dsimp only [pushR001, exR]
      have ha : m + 1 + k + 1 = (m + 1) + (k + 1) := by omega
      rw [ha, rep001_add]

private theorem exR_pushRNat001 (n : ℕ) (r : List RChunk) :
    exR (pushRNat001 n r) = rep001 n (exR r) := by
  cases n with
  | zero => rfl
  | succ m => exact exR_pushR001 m r

private theorem exR_pushR0 (r : List RChunk) :
    exR (pushR0 r) = (0 : Fin 2) >> exR r := by
  cases r with
  | nil => exact lb_zero_cons_default.symm
  | cons hd tl =>
    cases hd with
    | b1 => rfl
    | t001 _ => rfl
    | b0 =>
      cases tl with
      | nil => rfl
      | cons hd2 tl2 =>
        cases hd2 with
        | b0 => rfl
        | t001 _ => rfl
        | b1 => dsimp only [pushR0]; rw [exR_pushR001]; rfl

private theorem popL_ok (l : List LChunk) :
    exL l = (popL l).1 >> exL (popL l).2 := by
  cases l with
  | nil => exact lb_zero_cons_default.symm
  | cons hd tl =>
    cases hd with
    | b0 => rfl
    | b1 => rfl
    | t110 m => cases m <;> rfl

private theorem popR_ok (r : List RChunk) :
    exR r = (popR r).1 >> exR (popR r).2 := by
  cases r with
  | nil => exact lb_zero_cons_default.symm
  | cons hd tl =>
    cases hd with
    | b0 => rfl
    | b1 => rfl
    | t001 m => cases m <;> rfl

private theorem splitRChunk_ok : ∀ (l : List LChunk) (r : List RChunk),
    ReachesStar target_tm
      (exL l {{(1 : Fin 6)}}> ((1 : Fin 2) >> exR r))
      (exL (splitRChunk l r).1 {{(1 : Fin 6)}}> ((1 : Fin 2) >> exR (splitRChunk l r).2))
  | _, [] => reachesStar_refl _
  | _, .b0 :: _ => reachesStar_refl _
  | _, .b1 :: _ => reachesStar_refl _
  | l, .t001 m :: r => by
    dsimp only [splitRChunk, exR]
    have h1 := (reach_splitR_lb (m + 1) (exL l) (exR r)).to_star
    rw [← exL_pushL110 m l] at h1
    exact stepStar_trans h1 (splitRChunk_ok (pushL110 m l) r)

private theorem splitLChunk_ok : ∀ (l : List LChunk) (r : List RChunk),
    ReachesStar target_tm
      (exL l {{(1 : Fin 6)}}> ((0 : Fin 2) >> exR r))
      (exL (splitLChunk l r).1 {{(1 : Fin 6)}}> ((0 : Fin 2) >> exR (splitLChunk l r).2))
  | [], _ => reachesStar_refl _
  | .b0 :: _, _ => reachesStar_refl _
  | .b1 :: _, _ => reachesStar_refl _
  | .t110 0 :: _, _ => reachesStar_refl _
  | .t110 (m1 + 1) :: l, r => by
    dsimp only [splitLChunk]
    by_cases hm : m1 % 2 = 0
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hm))]
      dsimp only [exL]
      have hm_eq : m1 + 1 + 1 = 2 * (m1 / 2 + 1) := by omega
      rw [hm_eq]
      have h1 := (reach_splitL_lb (m1 / 2 + 1) (exL l) (exR r)).to_star
      have hr_eq : rep001 (2 * (m1 / 2 + 1)) (exR r) = exR (pushR001 (2 * (m1 / 2) + 1) r) := by
        rw [exR_pushR001]
        have ha : 2 * (m1 / 2) + 1 + 1 = 2 * (m1 / 2 + 1) := by omega
        rw [ha]
      rw [hr_eq] at h1
      exact stepStar_trans h1 (splitLChunk_ok l (pushR001 (2 * (m1 / 2) + 1) r))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hm))]
      dsimp only [exL]
      have hm_eq : m1 + 1 + 1 = 2 * (m1 / 2 + 1) + 1 := by omega
      rw [hm_eq, rep110_add (2 * (m1 / 2 + 1)) 1]
      have h1 := (reach_splitL_lb (m1 / 2 + 1) (rep110 1 (exL l)) (exR r)).to_star
      have hr_eq : rep001 (2 * (m1 / 2 + 1)) (exR r) = exR (pushR001 (2 * (m1 / 2) + 1) r) := by
        rw [exR_pushR001]
        have ha : 2 * (m1 / 2) + 1 + 1 = 2 * (m1 / 2 + 1) := by omega
        rw [ha]
      rw [hr_eq] at h1
      exact h1

private theorem stripOnesC_ok : ∀ (l : List LChunk) (r : List RChunk),
    ReachesStar target_tm
      (exL l <{{(2 : Fin 6)}} exR r)
      (exL (stripOnesL l r).1 {{(2 : Fin 6)}}> ((0 : Fin 2) >> exR (stripOnesL l r).2))
  | [], r => by
    dsimp only [stripOnesL, exL]
    conv_lhs => rw [← lb_zero_cons_default]
    rw [headLeft_cons_eq]
  | .b0 :: tl, r => by
    dsimp only [stripOnesL, exL]
    rw [headLeft_cons_eq]
  | .b1 :: tl, r => by
    dsimp only [stripOnesL, exL]
    have h1 : ReachesIn target_tm 1
        (((1 : Fin 2) >> exL tl) <{{(2 : Fin 6)}} exR r)
        (exL tl <{{(2 : Fin 6)}} exR (pushR0 r)) := by
      rw [exR_pushR0]
      exact rstep_ll rfl (reachesIn_zero _)
    exact stepStar_trans h1.to_star (stripOnesC_ok tl (pushR0 r))
  | .t110 0 :: tl, r => by
    dsimp only [stripOnesL, exL, rep110]
    rw [exR_pushR0, exR_pushR0]
    exact ReachesIn.to_star (n := 2) (rstep_ll rfl (rstep_ll rfl
      (by rw [headLeft_cons_eq]; exact reachesIn_zero _)))
  | .t110 (m + 1) :: tl, r => by
    dsimp only [stripOnesL, exL]
    have hm : m + 1 + 1 = 1 + (m + 1) := by omega
    conv_lhs => rw [hm, rep110_add 1 (m + 1)]
    dsimp only [rep110]
    rw [exR_pushR0, exR_pushR0]
    exact ReachesIn.to_star (n := 2) (rstep_ll rfl (rstep_ll rfl
      (by rw [headLeft_cons_eq]; exact reachesIn_zero _)))

private theorem trySuper4x_some (hd : Fin 2) (l : List LChunk) (r : List RChunk)
    (s' : State) (H : trySuper4x hd l r = some s') :
    ReachesPlus target_tm (encode ⟨hd, l, r⟩) (encode s') := by
  unfold trySuper4x at H
  by_cases hhd : hd = 0
  · subst hhd
    rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    split at H
    · next a_m1 b_m1 rtail =>
      by_cases hcond : (5 ≤ a_m1 && a_m1 % 2 = 1) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hcond))] at H
        dsimp only at H
        have ha5 : 5 ≤ a_m1 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond; exact hcond.1
        have haodd : a_m1 % 2 = 1 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond; exact hcond.2
        set A := a_m1 + 1
        set B := b_m1 + 1
        set m := findMaxM A B
        by_cases hm : 0 < m
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hm))] at H
          set p4 := 4 ^ m
          set s4 := (p4 - 1) / 3
          set dr := 2 * A * s4 + m
          by_cases hB : dr + 1 ≤ B
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true hB))] at H
            injection H with hs'
            subst hs'
            dsimp only [encode, exL, exR]
            set a := (a_m1 - 5) / 2
            have hA : a_m1 + 1 = 2 * (a + 3) := by omega
            have hp4_eq : p4 = pow4 m := (pow4_eq_pow m).symm
            have hs4_eq : s4 = sum4 m := (sum4_eq_div m).symm
            have hp4_pos : 0 < p4 := by rw [hp4_eq]; exact pow4_pos m
            have hAp4 : A * p4 - 1 + 1 = 2 * (a + 3) * pow4 m := by
              have h1 : 1 ≤ A * p4 := Nat.mul_pos (by omega) hp4_pos
              rw [Nat.sub_add_cancel h1, hp4_eq]; dsimp only [A]; rw [hA]
            have hB_eq : b_m1 + 1 = 2 * (2 * (a + 3)) * sum4 m + m + (B - (dr + 1) + 1) := by
              have h1 : 2 * (2 * (a + 3)) * sum4 m + m = dr := by
                dsimp only [dr, A]; rw [hA, hs4_eq]
              rw [h1]
              dsimp only [B] at hB ⊢
              omega
            rw [hA, hB_eq, hAp4]
            exact super4x_iter_plus m a (B - (dr + 1) + 1) hm (exR rtail)
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hB))] at H; nomatch H
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hm))] at H; nomatch H
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hcond))] at H; nomatch H
    · nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H; nomatch H

private theorem tryEraDrain_some (hd : Fin 2) (l : List LChunk) (r : List RChunk)
    (s' : State) (H : tryEraDrain hd l r = some s') :
    ReachesPlus target_tm (encode ⟨hd, l, r⟩) (encode s') := by
  unfold tryEraDrain at H
  by_cases hhd : hd = 0
  · subst hhd
    rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    split at H
    · next m1 c_m1 rtail =>
      by_cases hm : m1 % 2 = 0
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hm))] at H
        injection H with hs'; subst hs'
        dsimp only [encode, exL, exR, pushR1]
        have hm_eq : m1 + 1 + 1 = 2 * (m1 / 2 + 1) := by omega
        have hout_eq : m1 + 1 + 2 * (c_m1 + 1) + 1 = 2 * (m1 / 2 + 1 + (c_m1 + 1)) := by omega
        rw [hm_eq, hout_eq]
        exact era_drain_iter c_m1 (m1 / 2) (exR rtail)
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hm))] at H; nomatch H
    · nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H; nomatch H

private theorem tryEraOscR_ok (r : List RChunk) (j c_m1 : ℕ) (rtail : List RChunk)
    (H : tryEraOscR r = some (j, c_m1, rtail)) :
    exR r = rep001 (2 * j) ((0 : Fin 2) >> rep001 (c_m1 + 1) (exR rtail)) := by
  unfold tryEraOscR at H
  split at H
  · next cm rt =>
    injection H with h1; obtain ⟨rfl, h2⟩ := Prod.mk.inj h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl
  · next m1 cm rt =>
    by_cases hm : m1 % 2 = 0
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hm))] at H
      injection H with h1; obtain ⟨rfl, h2⟩ := Prod.mk.inj h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      dsimp only [exR]
      have hm_eq : m1 + 1 + 1 = 2 * (m1 / 2 + 1) := by omega
      rw [hm_eq]
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hm))] at H; nomatch H
  · nomatch H

private theorem tryEraOsc_some (hd : Fin 2) (l : List LChunk) (r : List RChunk)
    (s' : State) (H : tryEraOsc hd l r = some s') :
    ReachesPlus target_tm (encode ⟨hd, l, r⟩) (encode s') := by
  unfold tryEraOsc at H
  by_cases hhd : hd = 1
  · subst hhd
    rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    split at H
    · next a_m1 ltail =>
      rcases Er : tryEraOscR r with _ | ⟨j, c_m1, rtail⟩
      · rw [Er] at H; nomatch H
      · rw [Er] at H
        injection H with hs'; subst hs'
        set n_m1 := min a_m1 c_m1
        dsimp only [encode]
        rw [tryEraOscR_ok r j c_m1 rtail Er, exL_pushL0, exL_pushLNat110,
          exR_pushR001, exR_pushR0, exR_pushRNat001]
        dsimp only [exL]
        have ha : a_m1 + 1 = (n_m1 + 1) + (a_m1 - n_m1) := by omega
        have hc : c_m1 + 1 = (n_m1 + 1) + (c_m1 - n_m1) := by omega
        have hj : 2 * j + 2 * n_m1 + 1 + 1 = 2 * (j + (n_m1 + 1)) := by omega
        rw [ha, hc, hj, rep110_add (n_m1 + 1) (a_m1 - n_m1), rep001_add (n_m1 + 1) (c_m1 - n_m1)]
        exact era_osc_iter n_m1 j (rep110 (a_m1 - n_m1) (exL ltail)) (rep001 (c_m1 - n_m1) (exR
          rtail))
    · next a_m1 ltail =>
      rcases Er : tryEraOscR r with _ | ⟨j, c_m1, rtail⟩
      · rw [Er] at H; nomatch H
      · rw [Er] at H
        injection H with hs'; subst hs'
        set n_m1 := min a_m1 c_m1
        dsimp only [encode]
        rw [tryEraOscR_ok r j c_m1 rtail Er, exL_pushL1, exL_pushL0, exL_pushLNat110,
          exR_pushR001, exR_pushR0, exR_pushRNat001]
        dsimp only [exL]
        have ha : a_m1 + 1 = (n_m1 + 1) + (a_m1 - n_m1) := by omega
        have hc : c_m1 + 1 = (n_m1 + 1) + (c_m1 - n_m1) := by omega
        have hj : 2 * j + 2 * n_m1 + 1 + 1 = 2 * (j + (n_m1 + 1)) := by omega
        rw [ha, hc, hj, rep110_add (n_m1 + 1) (a_m1 - n_m1), rep001_add (n_m1 + 1) (c_m1 - n_m1)]
        exact era_osc10_iter n_m1 j (rep110 (a_m1 - n_m1) (exL ltail)) (rep001 (c_m1 - n_m1) (exR
          rtail))
    · nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H; nomatch H

private theorem fin2_eq_zero_of_ne_one {b : Fin 2} (h : b ≠ 1) : b = 0 := by omega
private theorem fin2_eq_one_of_ne_zero {b : Fin 2} (h : b ≠ 0) : b = 1 := by omega

private theorem stepBase_some (hd : Fin 2) (l : List LChunk) (r : List RChunk)
    (s' : State) (H : stepBase hd l r = some s') :
    ReachesPlus target_tm (encode ⟨hd, l, r⟩) (encode s') := by
  unfold stepBase at H
  by_cases hhd : hd = 1
  · subst hhd
    rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    have hsw := splitRChunk_ok l r
    rcases ER : splitRChunk l r with ⟨l1, r_in⟩
    rw [ER] at hsw H; dsimp only at hsw H
    have hp1 := popR_ok r_in
    rcases EP1 : popR r_in with ⟨b1, r1⟩
    rw [EP1] at hp1 H; dsimp only at hp1 H
    by_cases hb1 : b1 = 1
    · subst hb1; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H; injection H with hs'; subst
        hs'
      dsimp only [encode]; rw [hp1] at hsw; rw [exR_pushR0]
      exact stepStar_stepPlus_stepPlus hsw ((reach_R1_lb (exL l1) (exR r1)).to_plus (by omega))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb1))] at H
      have hb1_0 := fin2_eq_zero_of_ne_one hb1; subst hb1_0
      have hp2 := popR_ok r1
      rcases EP2 : popR r1 with ⟨b2, r2⟩
      rw [EP2] at hp2 H; dsimp only at hp2 H
      by_cases hb2 : b2 = 0
      · subst hb2; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
        have hp3 := popR_ok r2
        rcases EP3 : popR r2 with ⟨b3, r3⟩
        rw [EP3] at hp3 H; dsimp only at hp3 H
        injection H with hs'; subst hs'
        dsimp only [encode]; rw [hp1, hp2, hp3] at hsw; rw [exL_pushL110]; dsimp only [rep110]
        exact stepStar_stepPlus_stepPlus hsw ((reach_R2_lb b3 (exL l1) (exR r3)).to_plus (by omega))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at H
        have hb2_1 := fin2_eq_one_of_ne_zero hb2; subst hb2_1
        have hp3 := popR_ok r2
        rcases EP3 : popR r2 with ⟨b3, r3⟩
        rw [EP3] at hp3 H; dsimp only at hp3 H
        by_cases hb3 : b3 = 0
        · subst hb3; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H; injection H with hs';
            subst hs'
          dsimp only [encode]; rw [hp1, hp2, hp3] at hsw; rw [exL_pushL0, exR_pushR0, exR_pushR0]
          exact stepStar_stepPlus_stepPlus hsw ((reach_R3_lb (exL l1) (exR r3)).to_plus (by omega))
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb3))] at H; nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H
    have hhd_0 := fin2_eq_zero_of_ne_one hhd; subst hhd_0
    have hsw := splitLChunk_ok l r
    rcases EL : splitLChunk l r with ⟨l1, r1⟩
    rw [EL] at hsw H; dsimp only at hsw H
    have hb0 : ReachesIn target_tm 1
        (exL l1 {{(1 : Fin 6)}}> ((0 : Fin 2) >> exR r1))
        (exL l1 <{{(2 : Fin 6)}} exR (pushR1 r1)) :=
      ReachesIn.step_left (step_headRight_left rfl (exL l1) (exR r1)) (reachesIn_zero _)
    have hones := stripOnesC_ok l1 (pushR1 r1)
    rcases EO : stripOnesL l1 (pushR1 r1) with ⟨l_after, r_rem⟩
    rw [EO] at hones H; dsimp only at hones H
    have hpre := stepStar_trans (stepStar_trans hsw hb0.to_star) hones
    have hpe := popL_ok l_after
    rcases EPE : popL l_after with ⟨e, e_rem⟩
    rw [EPE] at hpe H; dsimp only at hpe H
    by_cases he : e = 0
    · subst he; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H; injection H with hs'; subst
        hs'
      dsimp only [encode]; rw [hpe] at hpre; rw [exL_pushL1]
      exact stepStar_stepPlus_stepPlus hpre ((reach_L1_lb (exL e_rem) (exR r_rem)).to_plus (by
        omega))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false he))] at H
      have he_1 := fin2_eq_one_of_ne_zero he; subst he_1
      have hpa := popL_ok e_rem
      rcases EPA : popL e_rem with ⟨ab, a_rem⟩
      rw [EPA] at hpa H; dsimp only at hpa H
      by_cases hab : ab = 1
      · subst hab; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
        have hpc := popL_ok a_rem
        rcases EPC : popL a_rem with ⟨cb, c_rem⟩
        rw [EPC] at hpc H; dsimp only at hpc H
        injection H with hs'; subst hs'
        dsimp only [encode]; rw [hpe, hpa, hpc] at hpre; rw [exR_pushR001]; dsimp only [rep001]
        exact stepStar_stepPlus_stepPlus hpre ((reach_L2_lb cb (exL c_rem) (exR r_rem)).to_plus
          (by omega))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hab))] at H
        injection H with hs'; subst hs'
        have hab_0 := fin2_eq_zero_of_ne_one hab; subst hab_0
        dsimp only [encode]; rw [hpe, hpa] at hpre; rw [exL_pushL1, exL_pushL1]
        exact stepStar_stepPlus_stepPlus hpre ((reach_L3_lb (exL a_rem) (exR r_rem)).to_plus (by
          omega))

private theorem stepFast_sound (s s' : State) (H : stepFast s = some s') :
    ReachesPlus target_tm (encode s) (encode s') := by
  rcases s with ⟨hd, l, r⟩
  unfold stepFast at H
  dsimp only at H
  rcases E0 : trySuper4x hd l r with _ | s0
  · rw [E0] at H; dsimp only at H
    rcases E1 : tryEraDrain hd l r with _ | s1
    · rw [E1] at H; dsimp only at H
      rcases E2 : tryEraOsc hd l r with _ | s2
      · rw [E2] at H; dsimp only at H
        exact stepBase_some hd l r s' H
      · rw [E2] at H; injection H with hs; subst hs
        exact tryEraOsc_some hd l r s2 E2
    · rw [E1] at H; injection H with hs; subst hs
      exact tryEraDrain_some hd l r s1 E1
  · rw [E0] at H; injection H with hs; subst hs
    exact trySuper4x_some hd l r s0 E0

private theorem iterPow2_sound : ∀ (k : ℕ) (s s' : State),
    iterPow2 k s = some s' → ReachesPlus target_tm (encode s) (encode s')
  | 0, s, s', H => stepFast_sound s s' H
  | k + 1, s, s', H => by
    dsimp only [iterPow2] at H
    rcases E1 : iterPow2 k s with _ | sm
    · rw [E1] at H; nomatch H
    · rw [E1] at H
      exact stepPlus_trans (iterPow2_sound k s sm E1) (iterPow2_sound k sm s' H)

def startState : State := ⟨0, [.b1], []⟩

def N0 : ℕ :=
  168916542770708232164041355802806696743472136660680390606743144800220774608018174794

def attractorState (N : ℕ) : State := ⟨0, [.t110 (N - 1), .b1], []⟩

def runFast17205 (s : State) : Option State :=
  (((((iterPow2 14 s).bind (iterPow2 9)).bind (iterPow2 8)).bind
    (iterPow2 5)).bind (iterPow2 4)).bind (fun x => (iterPow2 2 x).bind (iterPow2 0))

private theorem init_reaches_start :
    ReachesStar target_tm (init []) (encode startState) := by
  refine ⟨1, ?_⟩
  change step target_tm (init []) = some (encode startState)
  rfl

private theorem start_reaches_N0_eq :
    runFast17205 startState = some (attractorState N0) := rfl

private theorem start_reaches_N0 :
    ReachesPlus target_tm (encode startState) (encode (attractorState N0)) := by
  have H := start_reaches_N0_eq
  unfold runFast17205 at H
  rcases E1 : iterPow2 14 startState with _ | s1; · rw [E1] at H; nomatch H
  rw [E1] at H; dsimp only [Option.bind] at H
  rcases E2 : iterPow2 9 s1 with _ | s2; · rw [E2] at H; nomatch H
  rw [E2] at H; dsimp only [Option.bind] at H
  rcases E3 : iterPow2 8 s2 with _ | s3; · rw [E3] at H; nomatch H
  rw [E3] at H; dsimp only [Option.bind] at H
  rcases E4 : iterPow2 5 s3 with _ | s4; · rw [E4] at H; nomatch H
  rw [E4] at H; dsimp only [Option.bind] at H
  rcases E5 : iterPow2 4 s4 with _ | s5; · rw [E5] at H; nomatch H
  rw [E5] at H; dsimp only [Option.bind] at H
  rcases E6 : iterPow2 2 s5 with _ | s6; · rw [E6] at H; nomatch H
  rw [E6] at H; dsimp only [Option.bind] at H
  exact stepPlus_trans (iterPow2_sound 14 _ _ E1)
    (stepPlus_trans (iterPow2_sound 9 _ _ E2)
      (stepPlus_trans (iterPow2_sound 8 _ _ E3)
        (stepPlus_trans (iterPow2_sound 5 _ _ E4)
          (stepPlus_trans (iterPow2_sound 4 _ _ E5)
            (stepPlus_trans (iterPow2_sound 2 _ _ E6)
              (iterPow2_sound 0 _ _ H))))))

private theorem init_reaches_N0 :
    ReachesStar target_tm (init []) (encode (attractorState N0)) :=
  stepStar_trans init_reaches_start start_reaches_N0.to_star

/-! ### Part 2: Closed-Form Symbolic Interpreter for the Period-642 Exponential Attractor -/

def Inv (m N : ℕ) : Prop :=
  10 ≤ m ∧ m % 2 = 0 ∧ N % 2 = 0 ∧
  600 * sum4 m + 200 + 2000 * m ≤ 9 * N ∧
  9 * N + 2000 * m ≤ 615 * sum4 m + 205

private theorem inv_init_N0 : Inv 136 N0 := by
  refine ⟨by omega, by omega, by decide, ?_, ?_⟩ <;>
  · rw [sum4_eq_div]; decide

private theorem inv_step {m N : ℕ} (h : Inv m N) :
    Inv (m + 4) (256 * N + 54 - 180 * m) := by
  rcases h with ⟨hm10, hme, hNe, hlo, hhi⟩
  have hs4 : sum4 (m + 4) = 256 * sum4 m + 85 := by
    dsimp only [sum4]; omega
  have hge : 180 * m ≤ 256 * N := by omega
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [hs4]; omega
  · rw [hs4]; omega

structure LinForm : Type where
  aN : ℤ
  aQ : ℤ
  am : ℤ
  ac : ℤ
  deriving DecidableEq

def lfConst (c : ℤ) : LinForm := ⟨0, 0, 0, c⟩
def lfAdd (x y : LinForm) : LinForm := ⟨x.aN + y.aN, x.aQ + y.aQ, x.am + y.am, x.ac + y.ac⟩
def lfSub (x y : LinForm) : LinForm := ⟨x.aN - y.aN, x.aQ - y.aQ, x.am - y.am, x.ac - y.ac⟩
def lfScale2 (x : LinForm) : LinForm := ⟨2 * x.aN, 2 * x.aQ, 2 * x.am, 2 * x.ac⟩

def evalLF (m N : ℕ) (f : LinForm) : ℤ :=
  f.aN * (N : ℤ) + f.aQ * (sum4 m : ℤ) + f.am * (m : ℤ) + f.ac

def evalLFNat (m N : ℕ) (f : LinForm) : ℕ :=
  (evalLF m N f).toNat

def isNonnegLF (f : LinForm) : Bool :=
  let (cQ, cm, cc) :=
    if 0 ≤ f.aN then
      (600 * f.aN + 9 * f.aQ, 2000 * f.aN + 9 * f.am, 200 * f.aN + 9 * f.ac)
    else
      (615 * f.aN + 9 * f.aQ, -2000 * f.aN + 9 * f.am, 205 * f.aN + 9 * f.ac)
  if cQ < 0 then false
  else if cQ == 0 then decide (0 ≤ cm ∧ 0 ≤ cm * 10 + cc)
  else
    let mc := cQ * 15000 + cm
    let kc := cQ * 150000 + cc
    decide (0 ≤ mc ∧ 0 ≤ mc * 10 + kc)

def isPosLF (f : LinForm) : Bool := isNonnegLF (lfSub f (lfConst 1))

def isEvenLF (f : LinForm) : Bool := (f.aQ + f.ac) % 2 == 0

private theorem evalLF_const (m N : ℕ) (c : ℤ) : evalLF m N (lfConst c) = c := by
  simp [evalLF, lfConst]

private theorem evalLF_add (m N : ℕ) (x y : LinForm) :
    evalLF m N (lfAdd x y) = evalLF m N x + evalLF m N y := by
  dsimp only [evalLF, lfAdd]; ring

private theorem evalLF_sub (m N : ℕ) (x y : LinForm) :
    evalLF m N (lfSub x y) = evalLF m N x - evalLF m N y := by
  dsimp only [evalLF, lfSub]; ring

private theorem evalLF_scale2 (m N : ℕ) (x : LinForm) :
    evalLF m N (lfScale2 x) = 2 * evalLF m N x := by
  dsimp only [evalLF, lfScale2]; ring

private theorem isNonnegLF_sound {m N : ℕ} (hinv : Inv m N) (f : LinForm)
    (hok : isNonnegLF f = true) : 0 ≤ evalLF m N f := by
  rcases hinv with ⟨hm10, _, _, hlo, hhi⟩
  have hQ_low : (15000 * (m : ℤ) + 150000) ≤ (sum4 m : ℤ) := by
    have := sum4_lower m hm10; omega
  have hmZ : (10 : ℤ) ≤ (m : ℤ) := by omega
  have hloZ : 600 * (sum4 m : ℤ) + 200 + 2000 * (m : ℤ) ≤ 9 * (N : ℤ) := by omega
  have hhiZ : 9 * (N : ℤ) + 2000 * (m : ℤ) ≤ 615 * (sum4 m : ℤ) + 205 := by omega
  unfold isNonnegLF at hok
  have hfinish : ∀ cQ cm cc : ℤ,
      cQ * (sum4 m : ℤ) + cm * (m : ℤ) + cc ≤ 9 * evalLF m N f →
      (if cQ < 0 then false
       else if (cQ == 0) = true then decide (0 ≤ cm ∧ 0 ≤ cm * 10 + cc)
       else decide (0 ≤ cQ * 15000 + cm ∧ 0 ≤ (cQ * 15000 + cm) * 10 + (cQ * 150000 + cc))) = true →
      0 ≤ evalLF m N f := by
    intro cQ cm cc hbound hchk
    by_cases hneg : cQ < 0
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hneg))] at hchk; nomatch hchk
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hneg))] at hchk
      by_cases hzero : cQ = 0
      · subst hzero
        simp only [beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at hchk
        have : 0 ≤ cm * (m : ℤ) + cc := by nlinarith
        linarith
      · have hne : (cQ == 0) = false := beq_false_of_ne hzero
        rw [hne] at hchk
        simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hchk
        have hcQ_pos : 0 < cQ := by omega
        have : 0 ≤ cQ * (sum4 m : ℤ) + cm * (m : ℤ) + cc := by nlinarith
        linarith
  by_cases ha : 0 ≤ f.aN
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true ha))] at hok
    dsimp only at hok
    refine hfinish (600 * f.aN + 9 * f.aQ) (2000 * f.aN + 9 * f.am) (200 * f.aN + 9 * f.ac) ?_ hok
    have hmul : f.aN * (600 * (sum4 m : ℤ) + 200 + 2000 * (m : ℤ)) ≤ f.aN * (9 * (N : ℤ)) :=
      mul_le_mul_of_nonneg_left hloZ ha
    dsimp only [evalLF]; linarith
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false ha))] at hok
    dsimp only at hok
    refine hfinish (615 * f.aN + 9 * f.aQ) (-2000 * f.aN + 9 * f.am) (205 * f.aN + 9 * f.ac) ?_ hok
    have hle : f.aN ≤ 0 := by omega
    have hmul : f.aN * (615 * (sum4 m : ℤ) + 205 - 2000 * (m : ℤ)) ≤ f.aN * (9 * (N : ℤ)) :=
      mul_le_mul_of_nonpos_left (by linarith) hle
    dsimp only [evalLF]; linarith

private theorem isPosLF_sound {m N : ℕ} (hinv : Inv m N) (f : LinForm)
    (hok : isPosLF f = true) : 1 ≤ evalLF m N f := by
  have h := isNonnegLF_sound hinv (lfSub f (lfConst 1)) hok
  rw [evalLF_sub, evalLF_const] at h
  omega

private theorem isEvenLF_sound {m N : ℕ} (hinv : Inv m N) (f : LinForm)
    (hok : isEvenLF f = true) : evalLF m N f % 2 = 0 := by
  rcases hinv with ⟨hm10, hme, hNe, _, _⟩
  have hQo : sum4 m % 2 = 1 := sum4_odd m (by omega)
  unfold isEvenLF at hok
  simp only [beq_iff_eq] at hok
  dsimp only [evalLF]
  obtain ⟨kN, hkN⟩ : ∃ k : ℤ, (N : ℤ) = 2 * k := ⟨(N / 2 : ℕ), by omega⟩
  obtain ⟨km, hkm⟩ : ∃ k : ℤ, (m : ℤ) = 2 * k := ⟨(m / 2 : ℕ), by omega⟩
  obtain ⟨kQ, hkQ⟩ : ∃ k : ℤ, (sum4 m : ℤ) = 2 * k + 1 := ⟨(sum4 m / 2 : ℕ), by omega⟩
  rw [hkN, hkm, hkQ]
  have hrewrite : f.aN * (2 * kN) + f.aQ * (2 * kQ + 1) + f.am * (2 * km) + f.ac =
      2 * (f.aN * kN + f.aQ * kQ + f.am * km) + (f.aQ + f.ac) := by ring
  rw [hrewrite]; omega

private theorem isOddLF_sound {m N : ℕ} (hinv : Inv m N) (f : LinForm)
    (hne : isEvenLF f ≠ true) : evalLF m N f % 2 = 1 := by
  rcases hinv with ⟨hm10, hme, hNe, _, _⟩
  have hQo : sum4 m % 2 = 1 := sum4_odd m (by omega)
  unfold isEvenLF at hne
  simp only [ne_eq, beq_iff_eq] at hne
  dsimp only [evalLF]
  obtain ⟨kN, hkN⟩ : ∃ k : ℤ, (N : ℤ) = 2 * k := ⟨(N / 2 : ℕ), by omega⟩
  obtain ⟨km, hkm⟩ : ∃ k : ℤ, (m : ℤ) = 2 * k := ⟨(m / 2 : ℕ), by omega⟩
  obtain ⟨kQ, hkQ⟩ : ∃ k : ℤ, (sum4 m : ℤ) = 2 * k + 1 := ⟨(sum4 m / 2 : ℕ), by omega⟩
  rw [hkN, hkm, hkQ]
  have hrewrite : f.aN * (2 * kN) + f.aQ * (2 * kQ + 1) + f.am * (2 * km) + f.ac =
      2 * (f.aN * kN + f.aQ * kQ + f.am * km) + (f.aQ + f.ac) := by ring
  rw [hrewrite]; omega

inductive SLChunk : Type where
  | b0 : SLChunk
  | b1 : SLChunk
  | t110 (f : LinForm) : SLChunk
  deriving DecidableEq

inductive SRChunk : Type where
  | b0 : SRChunk
  | b1 : SRChunk
  | t001 (f : LinForm) : SRChunk
  deriving DecidableEq

structure SymState : Type where
  hd : Fin 2
  l : List SLChunk
  r : List SRChunk
  deriving DecidableEq

def exSL (m N : ℕ) : List SLChunk → ListBlank (Fin 2)
  | [] => default
  | .b0 :: tl => (0 : Fin 2) >> exSL m N tl
  | .b1 :: tl => (1 : Fin 2) >> exSL m N tl
  | .t110 f :: tl => rep110 (evalLFNat m N f) (exSL m N tl)

def exSR (m N : ℕ) : List SRChunk → ListBlank (Fin 2)
  | [] => default
  | .b0 :: tl => (0 : Fin 2) >> exSR m N tl
  | .b1 :: tl => (1 : Fin 2) >> exSR m N tl
  | .t001 f :: tl => rep001 (evalLFNat m N f) (exSR m N tl)

def evalSym (m N : ℕ) (s : SymState) : Cfg (Fin 2) (Fin 6) :=
  exSL m N s.l {{(1 : Fin 6)}}> (s.hd >> exSR m N s.r)

def validL (m N : ℕ) : List SLChunk → Prop
  | [] => True
  | .b0 :: tl => validL m N tl
  | .b1 :: tl => validL m N tl
  | .t110 f :: tl => 1 ≤ evalLF m N f ∧ validL m N tl

def validR (m N : ℕ) : List SRChunk → Prop
  | [] => True
  | .b0 :: tl => validR m N tl
  | .b1 :: tl => validR m N tl
  | .t001 f :: tl => 1 ≤ evalLF m N f ∧ validR m N tl

def validSym (m N : ℕ) (s : SymState) : Prop :=
  validL m N s.l ∧ validR m N s.r

def symPushL110 (f : LinForm) : List SLChunk → List SLChunk
  | .t110 g :: tl => .t110 (lfAdd f g) :: tl
  | l => .t110 f :: l

def symPushL0 : List SLChunk → List SLChunk
  | [] => []
  | l => .b0 :: l

def symPushL1 : List SLChunk → List SLChunk
  | .b1 :: .b0 :: tl => symPushL110 (lfConst 1) tl
  | l => .b1 :: l

def symPushR001 (f : LinForm) : List SRChunk → List SRChunk
  | .t001 g :: tl => .t001 (lfAdd f g) :: tl
  | r => .t001 f :: r

def symPushR0 : List SRChunk → List SRChunk
  | [] => []
  | .b0 :: .b1 :: tl => symPushR001 (lfConst 1) tl
  | r => .b0 :: r

def symPushR1 (r : List SRChunk) : List SRChunk := .b1 :: r

def symPopL : List SLChunk → Option (Fin 2 × List SLChunk)
  | [] => some (0, [])
  | .b0 :: tl => some (0, tl)
  | .b1 :: tl => some (1, tl)
  | .t110 f :: tl =>
    if f == lfConst 1 then some (1, .b1 :: .b0 :: tl)
    else if isPosLF (lfSub f (lfConst 1)) then
      some (1, .b1 :: .b0 :: .t110 (lfSub f (lfConst 1)) :: tl)
    else none

def symPopR : List SRChunk → Option (Fin 2 × List SRChunk)
  | [] => some (0, [])
  | .b0 :: tl => some (0, tl)
  | .b1 :: tl => some (1, tl)
  | .t001 f :: tl =>
    if f == lfConst 1 then some (0, .b0 :: .b1 :: tl)
    else if isPosLF (lfSub f (lfConst 1)) then
      some (0, .b0 :: .b1 :: .t001 (lfSub f (lfConst 1)) :: tl)
    else none

def symSplitR : List SLChunk → List SRChunk → List SLChunk × List SRChunk
  | l, .t001 f :: r => symSplitR (symPushL110 f l) r
  | l, r => (l, r)

def symSplitL : List SLChunk → List SRChunk → Option (List SLChunk × List SRChunk)
  | .t110 f :: tl, r =>
    if f == lfConst 1 then some (.t110 f :: tl, r)
    else if isEvenLF f then
      if isNonnegLF (lfSub f (lfConst 2)) then
        symSplitL tl (symPushR001 f r)
      else none
    else
      if isNonnegLF (lfSub f (lfConst 3)) then
        some (.t110 (lfConst 1) :: tl, symPushR001 (lfSub f (lfConst 1)) r)
      else none
  | l, r => some (l, r)

def symStripOnesL : List SLChunk → List SRChunk → Option (List SLChunk × List SRChunk)
  | [], r => some ([], r)
  | .b0 :: tl, r => some (tl, r)
  | .b1 :: tl, r => symStripOnesL tl (symPushR0 r)
  | .t110 f :: tl, r =>
    if f == lfConst 1 then some (tl, symPushR0 (symPushR0 r))
    else if isPosLF (lfSub f (lfConst 1)) then
      some (.t110 (lfSub f (lfConst 1)) :: tl, symPushR0 (symPushR0 r))
    else none

def s4xNeed (d : ℕ) : LinForm :=
  ⟨0, 20 * (pow4 d : ℤ), 1, 20 * (sum4 d : ℤ) + (d : ℤ)⟩

def s4xNewA (d : ℕ) : LinForm :=
  ⟨0, 30 * (pow4 d : ℤ), 0, 10 * (pow4 d : ℤ)⟩

def symTrySuper4x (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) : Option SymState :=
  if hd = 0 then
    match l, r with
    | [], .t001 a :: .b0 :: .t001 B :: rtail =>
      if a == lfConst 10 then
        let pick :=
          if isPosLF (lfSub B (s4xNeed 3)) then some 3
          else if isPosLF (lfSub B (s4xNeed 2)) then some 2
          else if isPosLF (lfSub B (s4xNeed 1)) then some 1
          else if isPosLF (lfSub B (s4xNeed 0)) then some 0
          else none
        match pick with
        | some d => some ⟨0, [], .t001 (s4xNewA d) :: .b0 :: .t001 (lfSub B (s4xNeed d)) :: rtail⟩
        | none => none
      else none
    | _, _ => none
  else none

def symTryEraDrain (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) : Option SymState :=
  if hd = 0 then
    match l, r with
    | [.t110 a, .b1, .b1], .b1 :: .t001 c :: rtail =>
      if isEvenLF a && isNonnegLF (lfSub a (lfConst 2)) && isPosLF c then
        some ⟨0, [.t110 (lfAdd a (lfScale2 c)), .b1, .b1], symPushR1 rtail⟩
      else none
    | _, _ => none
  else none

def symTryEraOscR (r : List SRChunk) : Option (LinForm × LinForm × List SRChunk) :=
  match r with
  | .b0 :: .t001 c :: rtail => some (lfConst 0, c, rtail)
  | .t001 j2 :: .b0 :: .t001 c :: rtail =>
    if isEvenLF j2 && isNonnegLF (lfSub j2 (lfConst 2)) then some (j2, c, rtail) else none
  | _ => none

def symTryEraOsc (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) : Option SymState :=
  if hd = 1 then
    let extracted : Option (Bool × LinForm × List SLChunk) :=
      match l with
      | .b0 :: .t110 a :: ltail => some (false, a, ltail)
      | .b1 :: .b0 :: .t110 a :: ltail => some (true, a, ltail)
      | _ => none
    match extracted with
    | some (is10, a, ltail) =>
      match symTryEraOscR r with
      | some (j2, c, rtail) =>
        let cmp : Option (LinForm × List SLChunk × List SRChunk) :=
          if a == c then some (a, ltail, rtail)
          else if isPosLF (lfSub c a) then some (a, ltail, symPushR001 (lfSub c a) rtail)
          else if isPosLF (lfSub a c) then some (c, symPushL110 (lfSub a c) ltail, rtail)
          else none
        match cmp with
        | some (n, lbase, rbase) =>
          let l1 := symPushL0 lbase
          let l_new := if is10 then symPushL1 l1 else l1
          let r_new := symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase)
          some ⟨1, l_new, r_new⟩
        | none => none
      | none => none
    | none => none
  else none

def symStepBase (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) : Option SymState :=
  if hd = 1 then
    let (l1, r_in) := symSplitR l r
    match symPopR r_in with
    | none => none
    | some (b1, r1) =>
      if b1 = 1 then some ⟨0, l1, symPushR0 r1⟩
      else
        match symPopR r1 with
        | none => none
        | some (b2, r2) =>
          if b2 = 0 then
            match symPopR r2 with
            | none => none
            | some (b3, r3) => some ⟨b3, symPushL110 (lfConst 1) l1, r3⟩
          else
            match symPopR r2 with
            | none => none
            | some (b3, r3) =>
              if b3 = 0 then some ⟨1, symPushL0 l1, symPushR0 (symPushR0 r3)⟩
              else none
  else
    match symSplitL l r with
    | none => none
    | some (l1, r1) =>
      match symStripOnesL l1 (symPushR1 r1) with
      | none => none
      | some (l_after, r_rem) =>
        match symPopL l_after with
        | none => none
        | some (e, e_rem) =>
          if e = 0 then some ⟨1, symPushL1 e_rem, r_rem⟩
          else
            match symPopL e_rem with
            | none => none
            | some (ab, a_rem) =>
              if ab = 1 then
                match symPopL a_rem with
                | none => none
                | some (cb, c_rem) => some ⟨cb, c_rem, symPushR001 (lfConst 1) r_rem⟩
              else some ⟨1, symPushL1 (symPushL1 a_rem), r_rem⟩

def symStep (s : SymState) : Option SymState :=
  match symTrySuper4x s.hd s.l s.r with
  | some s' => some s'
  | none =>
    match symTryEraDrain s.hd s.l s.r with
    | some s' => some s'
    | none =>
      match symTryEraOsc s.hd s.l s.r with
      | some s' => some s'
      | none => symStepBase s.hd s.l s.r

def symIterPow2 : ℕ → SymState → Option SymState
  | 0, s => symStep s
  | k + 1, s => (symIterPow2 k s).bind (symIterPow2 k)

/-! ### Soundness of the Symbolic Interpreter -/

private theorem exSL_pushL110 {m N : ℕ} (f : LinForm) (l : List SLChunk)
    (hf : 1 ≤ evalLF m N f) (hl : validL m N l) :
    validL m N (symPushL110 f l) ∧
      exSL m N (symPushL110 f l) = rep110 (evalLFNat m N f) (exSL m N l) := by
  cases l with
  | nil => exact ⟨⟨hf, trivial⟩, rfl⟩
  | cons hd tl =>
    cases hd with
    | b0 => exact ⟨⟨hf, hl⟩, rfl⟩
    | b1 => exact ⟨⟨hf, hl⟩, rfl⟩
    | t110 g =>
      rcases hl with ⟨hg, htl⟩
      dsimp only [symPushL110, validL, exSL]
      refine ⟨⟨by rw [evalLF_add]; omega, htl⟩, ?_⟩
      have hadd : evalLFNat m N (lfAdd f g) = evalLFNat m N f + evalLFNat m N g := by
        dsimp only [evalLFNat]; rw [evalLF_add]; omega
      rw [hadd, rep110_add]

private theorem exSL_pushL0 {m N : ℕ} (l : List SLChunk) (hl : validL m N l) :
    validL m N (symPushL0 l) ∧ exSL m N (symPushL0 l) = (0 : Fin 2) >> exSL m N l := by
  cases l with
  | nil => exact ⟨trivial, lb_zero_cons_default.symm⟩
  | cons _ _ => exact ⟨hl, rfl⟩

private theorem exSL_pushL1 {m N : ℕ} (l : List SLChunk) (hl : validL m N l) :
    validL m N (symPushL1 l) ∧ exSL m N (symPushL1 l) = (1 : Fin 2) >> exSL m N l := by
  cases l with
  | nil => exact ⟨trivial, rfl⟩
  | cons hd tl =>
    cases hd with
    | b0 => exact ⟨hl, rfl⟩
    | t110 _ => exact ⟨hl, rfl⟩
    | b1 =>
      cases tl with
      | nil => exact ⟨hl, rfl⟩
      | cons hd2 tl2 =>
        cases hd2 with
        | b1 => exact ⟨hl, rfl⟩
        | t110 _ => exact ⟨hl, rfl⟩
        | b0 =>
          dsimp only [symPushL1]
          have h1 : 1 ≤ evalLF m N (lfConst 1) := by rw [evalLF_const]
          obtain ⟨hv, hex⟩ := exSL_pushL110 (lfConst 1) tl2 h1 hl
          refine ⟨hv, ?_⟩
          rw [hex]
          have hc1 : evalLFNat m N (lfConst 1) = 1 := by simp [evalLFNat, evalLF_const]
          rw [hc1]; rfl

private theorem exSR_pushR001 {m N : ℕ} (f : LinForm) (r : List SRChunk)
    (hf : 1 ≤ evalLF m N f) (hr : validR m N r) :
    validR m N (symPushR001 f r) ∧
      exSR m N (symPushR001 f r) = rep001 (evalLFNat m N f) (exSR m N r) := by
  cases r with
  | nil => exact ⟨⟨hf, trivial⟩, rfl⟩
  | cons hd tl =>
    cases hd with
    | b0 => exact ⟨⟨hf, hr⟩, rfl⟩
    | b1 => exact ⟨⟨hf, hr⟩, rfl⟩
    | t001 g =>
      rcases hr with ⟨hg, htl⟩
      dsimp only [symPushR001, validR, exSR]
      refine ⟨⟨by rw [evalLF_add]; omega, htl⟩, ?_⟩
      have hadd : evalLFNat m N (lfAdd f g) = evalLFNat m N f + evalLFNat m N g := by
        dsimp only [evalLFNat]; rw [evalLF_add]; omega
      rw [hadd, rep001_add]

private theorem exSR_pushR0 {m N : ℕ} (r : List SRChunk) (hr : validR m N r) :
    validR m N (symPushR0 r) ∧ exSR m N (symPushR0 r) = (0 : Fin 2) >> exSR m N r := by
  cases r with
  | nil => exact ⟨trivial, lb_zero_cons_default.symm⟩
  | cons hd tl =>
    cases hd with
    | b1 => exact ⟨hr, rfl⟩
    | t001 _ => exact ⟨hr, rfl⟩
    | b0 =>
      cases tl with
      | nil => exact ⟨hr, rfl⟩
      | cons hd2 tl2 =>
        cases hd2 with
        | b0 => exact ⟨hr, rfl⟩
        | t001 _ => exact ⟨hr, rfl⟩
        | b1 =>
          dsimp only [symPushR0]
          have h1 : 1 ≤ evalLF m N (lfConst 1) := by rw [evalLF_const]
          obtain ⟨hv, hex⟩ := exSR_pushR001 (lfConst 1) tl2 h1 hr
          refine ⟨hv, ?_⟩
          rw [hex]
          have hc1 : evalLFNat m N (lfConst 1) = 1 := by simp [evalLFNat, evalLF_const]
          rw [hc1]; rfl

private theorem symPopL_ok {m N : ℕ} (hinv : Inv m N) (l l' : List SLChunk) (b : Fin 2)
    (hl : validL m N l) (H : symPopL l = some (b, l')) :
    validL m N l' ∧ exSL m N l = b >> exSL m N l' := by
  cases l with
  | nil =>
    dsimp only [symPopL] at H; injection H with h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨trivial, lb_zero_cons_default.symm⟩
  | cons hd tl =>
    cases hd with
    | b0 =>
      dsimp only [symPopL] at H; injection H with h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      exact ⟨hl, rfl⟩
    | b1 =>
      dsimp only [symPopL] at H; injection H with h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      exact ⟨hl, rfl⟩
    | t110 f =>
      rcases hl with ⟨hf, htl⟩
      dsimp only [symPopL] at H
      by_cases h1 : (f == lfConst 1) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true h1))] at H; injection H with hp; obtain ⟨rfl,
          rfl⟩ := Prod.mk.inj hp
        have hf1 : f = lfConst 1 := beq_iff_eq.mp h1
        subst hf1
        refine ⟨htl, ?_⟩
        dsimp only [exSL]; rw [show evalLFNat m N (lfConst 1) = 1 by simp [evalLFNat,
          evalLF_const]]; rfl
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false h1))] at H
        by_cases h2 : isPosLF (lfSub f (lfConst 1)) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true h2))] at H; injection H with hp; obtain ⟨rfl,
            rfl⟩ := Prod.mk.inj hp
          have hsub := isPosLF_sound hinv _ h2
          refine ⟨⟨hsub, htl⟩, ?_⟩
          dsimp only [exSL]
          have heq : evalLFNat m N f = 1 + evalLFNat m N (lfSub f (lfConst 1)) := by
            dsimp only [evalLFNat]; rw [evalLF_sub, evalLF_const] at hsub ⊢; omega
          rw [heq, rep110_add 1]; rfl
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false h2))] at H; nomatch H

private theorem symPopR_ok {m N : ℕ} (hinv : Inv m N) (r r' : List SRChunk) (b : Fin 2)
    (hr : validR m N r) (H : symPopR r = some (b, r')) :
    validR m N r' ∧ exSR m N r = b >> exSR m N r' := by
  cases r with
  | nil =>
    dsimp only [symPopR] at H; injection H with h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨trivial, lb_zero_cons_default.symm⟩
  | cons hd tl =>
    cases hd with
    | b0 =>
      dsimp only [symPopR] at H; injection H with h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      exact ⟨hr, rfl⟩
    | b1 =>
      dsimp only [symPopR] at H; injection H with h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      exact ⟨hr, rfl⟩
    | t001 f =>
      rcases hr with ⟨hf, htl⟩
      dsimp only [symPopR] at H
      by_cases h1 : (f == lfConst 1) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true h1))] at H; injection H with hp; obtain ⟨rfl,
          rfl⟩ := Prod.mk.inj hp
        have hf1 : f = lfConst 1 := beq_iff_eq.mp h1
        subst hf1
        refine ⟨htl, ?_⟩
        dsimp only [exSR]; rw [show evalLFNat m N (lfConst 1) = 1 by simp [evalLFNat,
          evalLF_const]]; rfl
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false h1))] at H
        by_cases h2 : isPosLF (lfSub f (lfConst 1)) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true h2))] at H; injection H with hp; obtain ⟨rfl,
            rfl⟩ := Prod.mk.inj hp
          have hsub := isPosLF_sound hinv _ h2
          refine ⟨⟨hsub, htl⟩, ?_⟩
          dsimp only [exSR]
          have heq : evalLFNat m N f = 1 + evalLFNat m N (lfSub f (lfConst 1)) := by
            dsimp only [evalLFNat]; rw [evalLF_sub, evalLF_const] at hsub ⊢; omega
          rw [heq, rep001_add 1]; rfl
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false h2))] at H; nomatch H

private theorem symSplitR_ok {m N : ℕ} : ∀ (l : List SLChunk) (r : List SRChunk),
    validL m N l → validR m N r →
    validL m N (symSplitR l r).1 ∧ validR m N (symSplitR l r).2 ∧
    ReachesStar target_tm
      (exSL m N l {{(1 : Fin 6)}}> ((1 : Fin 2) >> exSR m N r))
      (exSL m N (symSplitR l r).1 {{(1 : Fin 6)}}> ((1 : Fin 2) >> exSR m N (symSplitR l r).2))
  | _, [], hl, hr => ⟨hl, hr, reachesStar_refl _⟩
  | _, .b0 :: _, hl, hr => ⟨hl, hr, reachesStar_refl _⟩
  | _, .b1 :: _, hl, hr => ⟨hl, hr, reachesStar_refl _⟩
  | l, .t001 f :: r, hl, ⟨hf, hr⟩ => by
    dsimp only [symSplitR, exSR]
    obtain ⟨hl', hex⟩ := exSL_pushL110 f l hf hl
    have h1 := (reach_splitR_lb (evalLFNat m N f) (exSL m N l) (exSR m N r)).to_star
    rw [← hex] at h1
    obtain ⟨hvL, hvR, h2⟩ := symSplitR_ok (symPushL110 f l) r hl' hr
    exact ⟨hvL, hvR, stepStar_trans h1 h2⟩

private theorem symSplitL_ok {m N : ℕ} (hinv : Inv m N) :
    ∀ (l : List SLChunk) (r : List SRChunk) (l' : List SLChunk) (r' : List SRChunk),
    validL m N l → validR m N r → symSplitL l r = some (l', r') →
    validL m N l' ∧ validR m N r' ∧
    ReachesStar target_tm
      (exSL m N l {{(1 : Fin 6)}}> ((0 : Fin 2) >> exSR m N r))
      (exSL m N l' {{(1 : Fin 6)}}> ((0 : Fin 2) >> exSR m N r'))
  | [], r, l', r', hl, hr, H => by
    dsimp only [symSplitL] at H; injection H with hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact ⟨hl, hr, reachesStar_refl _⟩
  | .b0 :: tl, r, l', r', hl, hr, H => by
    dsimp only [symSplitL] at H; injection H with hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact ⟨hl, hr, reachesStar_refl _⟩
  | .b1 :: tl, r, l', r', hl, hr, H => by
    dsimp only [symSplitL] at H; injection H with hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact ⟨hl, hr, reachesStar_refl _⟩
  | .t110 f :: tl, r, l', r', ⟨hf, htl⟩, hr, H => by
    dsimp only [symSplitL] at H
    by_cases h1 : (f == lfConst 1) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true h1))] at H; injection H with hp; obtain ⟨rfl, rfl⟩
        := Prod.mk.inj hp
      exact ⟨⟨hf, htl⟩, hr, reachesStar_refl _⟩
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false h1))] at H
      by_cases hev : isEvenLF f = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hev))] at H
        by_cases h2 : isNonnegLF (lfSub f (lfConst 2)) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true h2))] at H
          have hfev := isEvenLF_sound hinv f hev
          have hge2 := isNonnegLF_sound hinv _ h2
          rw [evalLF_sub, evalLF_const] at hge2
          have hfn : evalLFNat m N f = 2 * (evalLFNat m N f / 2) := by dsimp only [evalLFNat]; omega
          obtain ⟨hr1, hex1⟩ := exSR_pushR001 f r hf hr
          have hstep : ReachesStar target_tm
              (exSL m N (.t110 f :: tl) {{(1 : Fin 6)}}> ((0 : Fin 2) >> exSR m N r))
              (exSL m N tl {{(1 : Fin 6)}}> ((0 : Fin 2) >> exSR m N (symPushR001 f r))) := by
            dsimp only [exSL]; rw [hex1, hfn]
            exact (reach_splitL_lb (evalLFNat m N f / 2) (exSL m N tl) (exSR m N r)).to_star
          obtain ⟨hvL, hvR, hrest⟩ := symSplitL_ok hinv tl (symPushR001 f r) l' r' htl hr1 H
          exact ⟨hvL, hvR, stepStar_trans hstep hrest⟩
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false h2))] at H; nomatch H
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hev))] at H
        by_cases h3 : isNonnegLF (lfSub f (lfConst 3)) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true h3))] at H; injection H with hp; obtain ⟨rfl,
            rfl⟩ := Prod.mk.inj hp
          have hge3 := isNonnegLF_sound hinv _ h3
          rw [evalLF_sub, evalLF_const] at hge3
          have hfodd : evalLF m N f % 2 = 1 := isOddLF_sound hinv f hev
          have hsub_pos : 1 ≤ evalLF m N (lfSub f (lfConst 1)) := by
            rw [evalLF_sub, evalLF_const]; omega
          obtain ⟨hr1, hex1⟩ := exSR_pushR001 (lfSub f (lfConst 1)) r hsub_pos hr
          have hc1 : 1 ≤ evalLF m N (lfConst 1) := by rw [evalLF_const]
          refine ⟨⟨hc1, htl⟩, hr1, ?_⟩
          dsimp only [exSL]; rw [hex1]
          set half := evalLFNat m N (lfSub f (lfConst 1)) / 2
          have hsub_even : evalLFNat m N (lfSub f (lfConst 1)) = 2 * half := by
            dsimp only [half, evalLFNat]; rw [evalLF_sub, evalLF_const]; omega
          have hfn : evalLFNat m N f = 2 * half + 1 := by
            dsimp only [half, evalLFNat]; rw [evalLF_sub, evalLF_const]; omega
          have hc1_nat : evalLFNat m N (lfConst 1) = 1 := by simp [evalLFNat, evalLF_const]
          rw [hfn, rep110_add (2 * half) 1, hc1_nat, hsub_even]
          exact (reach_splitL_lb half (rep110 1 (exSL m N tl)) (exSR m N r)).to_star
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false h3))] at H; nomatch H

private theorem symStripOnesL_ok {m N : ℕ} (hinv : Inv m N) :
    ∀ (l : List SLChunk) (r : List SRChunk) (l' : List SLChunk) (r' : List SRChunk),
    validL m N l → validR m N r → symStripOnesL l r = some (l', r') →
    validL m N l' ∧ validR m N r' ∧
    ReachesStar target_tm
      (exSL m N l <{{(2 : Fin 6)}} exSR m N r)
      (exSL m N l' {{(2 : Fin 6)}}> ((0 : Fin 2) >> exSR m N r'))
  | [], r, l', r', _, hr, H => by
    dsimp only [symStripOnesL] at H; injection H with hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    refine ⟨trivial, hr, ?_⟩
    dsimp only [exSL]; conv_lhs => rw [← lb_zero_cons_default]
    rw [headLeft_cons_eq]
  | .b0 :: tl, r, l', r', hl, hr, H => by
    dsimp only [symStripOnesL] at H; injection H with hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    refine ⟨hl, hr, ?_⟩
    dsimp only [exSL]; rw [headLeft_cons_eq]
  | .b1 :: tl, r, l', r', hl, hr, H => by
    dsimp only [symStripOnesL] at H
    obtain ⟨hr1, hex1⟩ := exSR_pushR0 r hr
    obtain ⟨hvL, hvR, h2⟩ := symStripOnesL_ok hinv tl (symPushR0 r) l' r' hl hr1 H
    refine ⟨hvL, hvR, ?_⟩
    dsimp only [exSL]
    have h1 : ReachesIn target_tm 1
        (((1 : Fin 2) >> exSL m N tl) <{{(2 : Fin 6)}} exSR m N r)
        (exSL m N tl <{{(2 : Fin 6)}} exSR m N (symPushR0 r)) := by
      rw [hex1]; exact rstep_ll rfl (reachesIn_zero _)
    exact stepStar_trans h1.to_star h2
  | .t110 f :: tl, r, l', r', ⟨hf, htl⟩, hr, H => by
    dsimp only [symStripOnesL] at H
    obtain ⟨hr1, hex1⟩ := exSR_pushR0 r hr
    obtain ⟨hr2, hex2⟩ := exSR_pushR0 (symPushR0 r) hr1
    by_cases h1 : (f == lfConst 1) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true h1))] at H; injection H with hp; obtain ⟨rfl, rfl⟩
        := Prod.mk.inj hp
      have hf1 : f = lfConst 1 := beq_iff_eq.mp h1; subst hf1
      refine ⟨htl, hr2, ?_⟩
      dsimp only [exSL]; rw [show evalLFNat m N (lfConst 1) = 1 by simp [evalLFNat, evalLF_const],
        hex2, hex1]
      dsimp only [rep110]
      exact ReachesIn.to_star (n := 2) (rstep_ll rfl (rstep_ll rfl
        (by rw [headLeft_cons_eq]; exact reachesIn_zero _)))
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false h1))] at H
      by_cases h2 : isPosLF (lfSub f (lfConst 1)) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true h2))] at H; injection H with hp; obtain ⟨rfl,
          rfl⟩ := Prod.mk.inj hp
        have hsub := isPosLF_sound hinv _ h2
        refine ⟨⟨hsub, htl⟩, hr2, ?_⟩
        dsimp only [exSL]
        have heq : evalLFNat m N f = 1 + evalLFNat m N (lfSub f (lfConst 1)) := by
          dsimp only [evalLFNat]; rw [evalLF_sub, evalLF_const] at hsub ⊢; omega
        rw [heq, rep110_add 1, hex2, hex1]
        dsimp only [rep110]
        exact ReachesIn.to_star (n := 2) (rstep_ll rfl (rstep_ll rfl
          (by rw [headLeft_cons_eq]; exact reachesIn_zero _)))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false h2))] at H; nomatch H

private theorem symTrySuper4x_sound {m N : ℕ} (hinv : Inv m N)
    (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) (s' : SymState)
    (hv : validSym m N ⟨hd, l, r⟩) (H : symTrySuper4x hd l r = some s') :
    validSym m N s' ∧ ReachesPlus target_tm (evalSym m N ⟨hd, l, r⟩) (evalSym m N s') := by
  unfold symTrySuper4x at H
  by_cases hhd : hd = 0
  · subst hhd; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    split at H
    · next a B rtail =>
      by_cases ha : (a == lfConst 10) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true ha))] at H
        have ha10 : a = lfConst 10 := beq_iff_eq.mp ha; subst ha10
        dsimp only at H
        have hrun : ∀ d : ℕ, isPosLF (lfSub B (s4xNeed d)) = true →
            s' = ⟨0, [], .t001 (s4xNewA d) :: .b0 :: .t001 (lfSub B (s4xNeed d)) :: rtail⟩ →
            validSym m N s' ∧
              ReachesPlus target_tm
                (evalSym m N ⟨0, [], .t001 (lfConst 10) :: .b0 :: .t001 B :: rtail⟩)
                (evalSym m N s') := by
          intro d hpos hs'
          subst hs'
          have hBsub := isPosLF_sound hinv _ hpos
          rcases hv with ⟨_, _, _, hrtail⟩
          have hnewA_pos : 1 ≤ evalLF m N (s4xNewA d) := by
            dsimp only [evalLF, s4xNewA]
            have hp : (1 : ℤ) ≤ (pow4 d : ℤ) := by exact_mod_cast pow4_pos d
            have hq : (0 : ℤ) ≤ 30 * (pow4 d : ℤ) * (sum4 m : ℤ) := by positivity
            linarith
          refine ⟨⟨trivial, hnewA_pos, hBsub, hrtail⟩, ?_⟩
          dsimp only [evalSym, exSL, exSR]
          have h10 : evalLFNat m N (lfConst 10) = 2 * (2 + 3) := by simp [evalLFNat, evalLF_const]
          have hneed_eq : evalLF m N (s4xNeed d) = (2 * (2 * (2 + 3)) * sum4 (m + d) + (m + d) :
            ℕ) := by
            dsimp only [evalLF, s4xNeed]
            rw [sum4_add m d]
            push_cast; ring
          have hnewA_eq : evalLFNat m N (s4xNewA d) = (2 * (2 + 3)) * pow4 (m + d) := by
            dsimp only [evalLFNat, evalLF, s4xNewA]
            rw [pow4_add m d, ← sum4_spec m]
            have : 30 * (pow4 d : ℤ) * (sum4 m : ℤ) + 10 * (pow4 d : ℤ) =
                ((10 * (pow4 d * (3 * sum4 m + 1)) : ℕ) : ℤ) := by push_cast; ring
            rw [show (0 : ℤ) * (N : ℤ) + 30 * (pow4 d : ℤ) * (sum4 m : ℤ) + 0 * (m : ℤ) + 10 *
              (pow4 d : ℤ) =
                ((10 * (pow4 d * (3 * sum4 m + 1)) : ℕ) : ℤ) by linarith]
            rw [Int.toNat_natCast]
          have hB_eq : evalLFNat m N B =
              2 * (2 * (2 + 3)) * sum4 (m + d) + (m + d) + evalLFNat m N (lfSub B (s4xNeed d)) := by
            dsimp only [evalLFNat]
            rw [evalLF_sub, hneed_eq] at hBsub ⊢
            omega
          rw [h10, hB_eq, hnewA_eq]
          have hmd : 0 < m + d := by rcases hinv with ⟨hm10, _⟩; omega
          exact super4x_iter_plus (m + d) 2 (evalLFNat m N (lfSub B (s4xNeed d))) hmd (exSR m N
            rtail)
        by_cases h3 : isPosLF (lfSub B (s4xNeed 3)) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true h3))] at H; injection H with hs'; exact hrun 3
            h3 hs'.symm
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false h3))] at H
          by_cases h2 : isPosLF (lfSub B (s4xNeed 2)) = true
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true h2))] at H; injection H with hs'; exact hrun
              2 h2 hs'.symm
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false h2))] at H
            by_cases h1 : isPosLF (lfSub B (s4xNeed 1)) = true
            · rw [(ite_eq_left_of_eq_true _ _ (eq_true h1))] at H; injection H with hs'; exact
                hrun 1 h1 hs'.symm
            · rw [(ite_eq_right_of_eq_false _ _ (eq_false h1))] at H
              by_cases h0 : isPosLF (lfSub B (s4xNeed 0)) = true
              · rw [(ite_eq_left_of_eq_true _ _ (eq_true h0))] at H; injection H with hs'; exact
                  hrun 0 h0 hs'.symm
              · rw [(ite_eq_right_of_eq_false _ _ (eq_false h0))] at H; nomatch H
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false ha))] at H; nomatch H
    · nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H; nomatch H

private theorem symTryEraDrain_sound {m N : ℕ} (hinv : Inv m N)
    (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) (s' : SymState)
    (hv : validSym m N ⟨hd, l, r⟩) (H : symTryEraDrain hd l r = some s') :
    validSym m N s' ∧ ReachesPlus target_tm (evalSym m N ⟨hd, l, r⟩) (evalSym m N s') := by
  unfold symTryEraDrain at H
  by_cases hhd : hd = 0
  · subst hhd; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    split at H
    · next a c rtail =>
      by_cases hcond : (isEvenLF a && isNonnegLF (lfSub a (lfConst 2)) && isPosLF c) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hcond))] at H; injection H with hs'; subst hs'
        simp only [Bool.and_eq_true] at hcond
        have haev := isEvenLF_sound hinv a hcond.1.1
        have hage2 := isNonnegLF_sound hinv _ hcond.1.2
        rw [evalLF_sub, evalLF_const] at hage2
        have hcpos := isPosLF_sound hinv c hcond.2
        rcases hv with ⟨_, _, hrtail⟩
        have hnew_pos : 1 ≤ evalLF m N (lfAdd a (lfScale2 c)) := by
          rw [evalLF_add, evalLF_scale2]; omega
        refine ⟨⟨⟨hnew_pos, trivial⟩, hrtail⟩, ?_⟩
        dsimp only [evalSym, exSL, exSR, symPushR1]
        set k := evalLFNat m N a / 2 - 1
        set cm1 := evalLFNat m N c - 1
        have ha_eq : evalLFNat m N a = 2 * (k + 1) := by dsimp only [k, evalLFNat]; omega
        have hc_eq : evalLFNat m N c = cm1 + 1 := by dsimp only [cm1, evalLFNat]; omega
        have hout_eq : evalLFNat m N (lfAdd a (lfScale2 c)) = 2 * (k + 1 + (cm1 + 1)) := by
          dsimp only [k, cm1, evalLFNat]; rw [evalLF_add, evalLF_scale2]; omega
        rw [ha_eq, hc_eq, hout_eq]
        exact era_drain_iter cm1 k (exSR m N rtail)
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hcond))] at H; nomatch H
    · nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H; nomatch H

private theorem symTryEraOscR_ok {m N : ℕ} (hinv : Inv m N) (r : List SRChunk)
    (j2 c : LinForm) (rtail : List SRChunk)
    (hr : validR m N r) (H : symTryEraOscR r = some (j2, c, rtail)) :
    0 ≤ evalLF m N j2 ∧ evalLF m N j2 % 2 = 0 ∧ 1 ≤ evalLF m N c ∧ validR m N rtail ∧
      exSR m N r = rep001 (evalLFNat m N j2) ((0 : Fin 2) >> rep001 (evalLFNat m N c) (exSR m N
        rtail)) := by
  unfold symTryEraOscR at H
  split at H
  · next c0 rt =>
    injection H with h1; obtain ⟨rfl, h2⟩ := Prod.mk.inj h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rcases hr with ⟨hc, hrt⟩
    refine ⟨by rw [evalLF_const], by rw [evalLF_const]; omega, hc, hrt, ?_⟩
    rw [show evalLFNat m N (lfConst 0) = 0 by simp [evalLFNat, evalLF_const]]; rfl
  · next j0 c0 rt =>
    by_cases hcond : (isEvenLF j0 && isNonnegLF (lfSub j0 (lfConst 2))) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hcond))] at H
      injection H with h1; obtain ⟨rfl, h2⟩ := Prod.mk.inj h1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp only [Bool.and_eq_true] at hcond
      have hjev := isEvenLF_sound hinv j0 hcond.1
      have hjge2 := isNonnegLF_sound hinv _ hcond.2
      rw [evalLF_sub, evalLF_const] at hjge2
      rcases hr with ⟨_, hc, hrt⟩
      exact ⟨by omega, hjev, hc, hrt, rfl⟩
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hcond))] at H; nomatch H
  · nomatch H

private theorem symTryEraOsc_sound {m N : ℕ} (hinv : Inv m N)
    (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) (s' : SymState)
    (hv : validSym m N ⟨hd, l, r⟩) (H : symTryEraOsc hd l r = some s') :
    validSym m N s' ∧ ReachesPlus target_tm (evalSym m N ⟨hd, l, r⟩) (evalSym m N s') := by
  unfold symTryEraOsc at H
  by_cases hhd : hd = 1
  · subst hhd; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    have hcore : ∀ (is10 : Bool) (a : LinForm) (ltail : List SLChunk),
        1 ≤ evalLF m N a → validL m N ltail →
        exSL m N l = (if is10 then (1 : Fin 2) >> (0 : Fin 2) >> rep110 (evalLFNat m N a) (exSL m
          N ltail)
                      else (0 : Fin 2) >> rep110 (evalLFNat m N a) (exSL m N ltail)) →
        (match symTryEraOscR r with
         | some (j2, c, rtail) =>
           match (if a == c then some (a, ltail, rtail)
                  else if isPosLF (lfSub c a) then some (a, ltail, symPushR001 (lfSub c a) rtail)
                  else if isPosLF (lfSub a c) then some (c, symPushL110 (lfSub a c) ltail, rtail)
                  else none) with
           | some (n, lbase, rbase) =>
             let l1 := symPushL0 lbase
             let l_new := if is10 then symPushL1 l1 else l1
             let r_new := symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase)
             some ⟨1, l_new, r_new⟩
           | none => none
         | none => none) = some s' →
        validSym m N s' ∧ ReachesPlus target_tm (evalSym m N ⟨1, l, r⟩) (evalSym m N s') := by
      intro is10 a ltail ha hltail hexL Hbody
      rcases Er : symTryEraOscR r with _ | ⟨j2, c, rtail⟩
      · rw [Er] at Hbody; nomatch Hbody
      · rw [Er] at Hbody; dsimp only at Hbody
        obtain ⟨hj0, hjev, hc, hrtail, hexR⟩ := symTryEraOscR_ok hinv r j2 c rtail hv.2 Er
        have hfinish : ∀ (n : LinForm) (lbase : List SLChunk) (rbase : List SRChunk),
            1 ≤ evalLF m N n →
            validL m N lbase → validR m N rbase →
            rep110 (evalLFNat m N a) (exSL m N ltail) = rep110 (evalLFNat m N n) (exSL m N lbase) →
            rep001 (evalLFNat m N c) (exSR m N rtail) = rep001 (evalLFNat m N n) (exSR m N rbase) →
            s' = ⟨1, if is10 then symPushL1 (symPushL0 lbase) else symPushL0 lbase,
                    symPushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase)⟩ →
            validSym m N s' ∧ ReachesPlus target_tm (evalSym m N ⟨1, l, r⟩) (evalSym m N s') := by
          intro n lbase rbase hn hlbase hrbase hLsplit hRsplit hs'
          subst hs'
          obtain ⟨hvl0, hexl0⟩ := exSL_pushL0 lbase hlbase
          obtain ⟨hvr0, hexr0⟩ := exSR_pushR0 rbase hrbase
          have hj2n_pos : 1 ≤ evalLF m N (lfAdd j2 (lfScale2 n)) := by
            rw [evalLF_add, evalLF_scale2]; omega
          obtain ⟨hvr1, hexr1⟩ := exSR_pushR001 (lfAdd j2 (lfScale2 n)) (symPushR0 rbase) hj2n_pos
            hvr0
          set nm1 := evalLFNat m N n - 1
          set j := evalLFNat m N j2 / 2
          have hn_eq : evalLFNat m N n = nm1 + 1 := by dsimp only [nm1, evalLFNat]; omega
          have hj_eq : evalLFNat m N j2 = 2 * j := by dsimp only [j, evalLFNat]; omega
          have hjout_eq : evalLFNat m N (lfAdd j2 (lfScale2 n)) = 2 * (j + (nm1 + 1)) := by
            dsimp only [j, nm1, evalLFNat]; rw [evalLF_add, evalLF_scale2]; omega
          cases is10
          · simp only [Bool.false_eq_true, ite_false]
            refine ⟨⟨hvl0, hvr1⟩, ?_⟩
            dsimp only [evalSym]; rw [hexL, hexR, hLsplit, hRsplit, hexl0, hexr1, hexr0, hn_eq,
              hj_eq, hjout_eq]
            exact era_osc_iter nm1 j (exSL m N lbase) (exSR m N rbase)
          · simp only [ite_true]
            obtain ⟨hvl1, hexl1⟩ := exSL_pushL1 (symPushL0 lbase) hvl0
            refine ⟨⟨hvl1, hvr1⟩, ?_⟩
            dsimp only [evalSym]; rw [hexL, hexR, hLsplit, hRsplit, hexl1, hexl0, hexr1, hexr0,
              hn_eq, hj_eq, hjout_eq]
            exact era_osc10_iter nm1 j (exSL m N lbase) (exSR m N rbase)
        by_cases heq : (a == c) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true heq))] at Hbody; injection Hbody with hs'
          have hac : a = c := beq_iff_eq.mp heq; subst hac
          exact hfinish a ltail rtail ha hltail hrtail rfl rfl hs'.symm
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false heq))] at Hbody
          by_cases hca : isPosLF (lfSub c a) = true
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true hca))] at Hbody; injection Hbody with hs'
            have hsub := isPosLF_sound hinv _ hca
            obtain ⟨hvr, hexr⟩ := exSR_pushR001 (lfSub c a) rtail hsub hrtail
            have hce : evalLFNat m N c = evalLFNat m N a + evalLFNat m N (lfSub c a) := by
              dsimp only [evalLFNat]; rw [evalLF_sub] at hsub ⊢; omega
            refine hfinish a ltail (symPushR001 (lfSub c a) rtail) ha hltail hvr rfl ?_ hs'.symm
            rw [hexr, hce, rep001_add]
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hca))] at Hbody
            by_cases hac2 : isPosLF (lfSub a c) = true
            · rw [(ite_eq_left_of_eq_true _ _ (eq_true hac2))] at Hbody; injection Hbody with hs'
              have hsub := isPosLF_sound hinv _ hac2
              obtain ⟨hvl, hexl⟩ := exSL_pushL110 (lfSub a c) ltail hsub hltail
              have hae : evalLFNat m N a = evalLFNat m N c + evalLFNat m N (lfSub a c) := by
                dsimp only [evalLFNat]; rw [evalLF_sub] at hsub ⊢; omega
              refine hfinish c (symPushL110 (lfSub a c) ltail) rtail hc hvl hrtail ?_ rfl hs'.symm
              rw [hexl, hae, rep110_add]
            · rw [(ite_eq_right_of_eq_false _ _ (eq_false hac2))] at Hbody; nomatch Hbody
    cases l with
    | nil => dsimp only at H; nomatch H
    | cons c0 tl0 =>
      cases c0 with
      | t110 _ => dsimp only at H; nomatch H
      | b0 =>
        cases tl0 with
        | nil => dsimp only at H; nomatch H
        | cons c1 tl1 =>
          cases c1 with
          | b0 => dsimp only at H; nomatch H
          | b1 => dsimp only at H; nomatch H
          | t110 a =>
            dsimp only at H
            exact hcore false a tl1 hv.1.1 hv.1.2 rfl H
      | b1 =>
        cases tl0 with
        | nil => dsimp only at H; nomatch H
        | cons c1 tl1 =>
          cases c1 with
          | b1 => dsimp only at H; nomatch H
          | t110 _ => dsimp only at H; nomatch H
          | b0 =>
            cases tl1 with
            | nil => dsimp only at H; nomatch H
            | cons c2 tl2 =>
              cases c2 with
              | b0 => dsimp only at H; nomatch H
              | b1 => dsimp only at H; nomatch H
              | t110 a =>
                dsimp only at H
                exact hcore true a tl2 hv.1.1 hv.1.2 rfl H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H; nomatch H

private theorem symStepBase_sound {m N : ℕ} (hinv : Inv m N)
    (hd : Fin 2) (l : List SLChunk) (r : List SRChunk) (s' : SymState)
    (hv : validSym m N ⟨hd, l, r⟩) (H : symStepBase hd l r = some s') :
    validSym m N s' ∧ ReachesPlus target_tm (evalSym m N ⟨hd, l, r⟩) (evalSym m N s') := by
  unfold symStepBase at H
  by_cases hhd : hd = 1
  · subst hhd; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
    obtain ⟨hvL1, hvR1, hsw⟩ := symSplitR_ok l r hv.1 hv.2
    rcases ER : symSplitR l r with ⟨l1, r_in⟩
    rw [ER] at hvL1 hvR1 hsw H; dsimp only at hvL1 hvR1 hsw H
    rcases EP1 : symPopR r_in with _ | ⟨b1, r1⟩
    · rw [EP1] at H; nomatch H
    · rw [EP1] at H; dsimp only at H
      obtain ⟨hvr1, hp1⟩ := symPopR_ok hinv r_in r1 b1 hvR1 EP1
      by_cases hb1 : b1 = 1
      · subst hb1; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H; injection H with hs';
          subst hs'
        obtain ⟨hvr0, hexr0⟩ := exSR_pushR0 r1 hvr1
        refine ⟨⟨hvL1, hvr0⟩, ?_⟩
        dsimp only [evalSym]; rw [hp1] at hsw; rw [hexr0]
        exact stepStar_stepPlus_stepPlus hsw ((reach_R1_lb (exSL m N l1) (exSR m N r1)).to_plus
          (by omega))
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb1))] at H
        have hb1_0 := fin2_eq_zero_of_ne_one hb1; subst hb1_0
        rcases EP2 : symPopR r1 with _ | ⟨b2, r2⟩
        · rw [EP2] at H; nomatch H
        · rw [EP2] at H; dsimp only at H
          obtain ⟨hvr2, hp2⟩ := symPopR_ok hinv r1 r2 b2 hvr1 EP2
          by_cases hb2 : b2 = 0
          · subst hb2; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
            rcases EP3 : symPopR r2 with _ | ⟨b3, r3⟩
            · rw [EP3] at H; nomatch H
            · rw [EP3] at H; dsimp only at H; injection H with hs'; subst hs'
              obtain ⟨hvr3, hp3⟩ := symPopR_ok hinv r2 r3 b3 hvr2 EP3
              have hc1 : 1 ≤ evalLF m N (lfConst 1) := by rw [evalLF_const]
              obtain ⟨hvl2, hexl2⟩ := exSL_pushL110 (lfConst 1) l1 hc1 hvL1
              refine ⟨⟨hvl2, hvr3⟩, ?_⟩
              dsimp only [evalSym]; rw [hp1, hp2, hp3] at hsw
              rw [hexl2, show evalLFNat m N (lfConst 1) = 1 by simp [evalLFNat, evalLF_const]]
              dsimp only [rep110]
              exact stepStar_stepPlus_stepPlus hsw ((reach_R2_lb b3 (exSL m N l1) (exSR m N
                r3)).to_plus (by omega))
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb2))] at H
            have hb2_1 := fin2_eq_one_of_ne_zero hb2; subst hb2_1
            rcases EP3 : symPopR r2 with _ | ⟨b3, r3⟩
            · rw [EP3] at H; nomatch H
            · rw [EP3] at H; dsimp only at H
              obtain ⟨hvr3, hp3⟩ := symPopR_ok hinv r2 r3 b3 hvr2 EP3
              by_cases hb3 : b3 = 0
              · subst hb3; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H; injection H with
                  hs'; subst hs'
                obtain ⟨hvl2, hexl2⟩ := exSL_pushL0 l1 hvL1
                obtain ⟨hvr4, hexr4⟩ := exSR_pushR0 r3 hvr3
                obtain ⟨hvr5, hexr5⟩ := exSR_pushR0 (symPushR0 r3) hvr4
                refine ⟨⟨hvl2, hvr5⟩, ?_⟩
                dsimp only [evalSym]; rw [hp1, hp2, hp3] at hsw; rw [hexl2, hexr5, hexr4]
                exact stepStar_stepPlus_stepPlus hsw ((reach_R3_lb (exSL m N l1) (exSR m N
                  r3)).to_plus (by omega))
              · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb3))] at H; nomatch H
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hhd))] at H
    have hhd_0 := fin2_eq_zero_of_ne_one hhd; subst hhd_0
    rcases EL : symSplitL l r with _ | ⟨l1, r1⟩
    · rw [EL] at H; nomatch H
    · rw [EL] at H; dsimp only at H
      obtain ⟨hvL1, hvR1, hsw⟩ := symSplitL_ok hinv l r l1 r1 hv.1 hv.2 EL
      have hb0 : ReachesIn target_tm 1
          (exSL m N l1 {{(1 : Fin 6)}}> ((0 : Fin 2) >> exSR m N r1))
          (exSL m N l1 <{{(2 : Fin 6)}} exSR m N (symPushR1 r1)) :=
        ReachesIn.step_left (step_headRight_left rfl (exSL m N l1) (exSR m N r1)) (reachesIn_zero _)
      rcases EO : symStripOnesL l1 (symPushR1 r1) with _ | ⟨l_after, r_rem⟩
      · rw [EO] at H; nomatch H
      · rw [EO] at H; dsimp only at H
        obtain ⟨hvLa, hvRr, hones⟩ := symStripOnesL_ok hinv l1 (symPushR1 r1) l_after r_rem hvL1
          hvR1 EO
        have hpre := stepStar_trans (stepStar_trans hsw hb0.to_star) hones
        rcases EPE : symPopL l_after with _ | ⟨e, e_rem⟩
        · rw [EPE] at H; nomatch H
        · rw [EPE] at H; dsimp only at H
          obtain ⟨hve, hpe⟩ := symPopL_ok hinv l_after e_rem e hvLa EPE
          by_cases he : e = 0
          · subst he; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H; injection H with hs';
              subst hs'
            obtain ⟨hvl1, hexl1⟩ := exSL_pushL1 e_rem hve
            refine ⟨⟨hvl1, hvRr⟩, ?_⟩
            dsimp only [evalSym]; rw [hpe] at hpre; rw [hexl1]
            exact stepStar_stepPlus_stepPlus hpre ((reach_L1_lb (exSL m N e_rem) (exSR m N
              r_rem)).to_plus (by omega))
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false he))] at H
            have he_1 := fin2_eq_one_of_ne_zero he; subst he_1
            rcases EPA : symPopL e_rem with _ | ⟨ab, a_rem⟩
            · rw [EPA] at H; nomatch H
            · rw [EPA] at H; dsimp only at H
              obtain ⟨hva, hpa⟩ := symPopL_ok hinv e_rem a_rem ab hve EPA
              by_cases hab : ab = 1
              · subst hab; rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))] at H
                rcases EPC : symPopL a_rem with _ | ⟨cb, c_rem⟩
                · rw [EPC] at H; nomatch H
                · rw [EPC] at H; dsimp only at H; injection H with hs'; subst hs'
                  obtain ⟨hvc, hpc⟩ := symPopL_ok hinv a_rem c_rem cb hva EPC
                  have hc1 : 1 ≤ evalLF m N (lfConst 1) := by rw [evalLF_const]
                  obtain ⟨hvr1, hexr1⟩ := exSR_pushR001 (lfConst 1) r_rem hc1 hvRr
                  refine ⟨⟨hvc, hvr1⟩, ?_⟩
                  dsimp only [evalSym]; rw [hpe, hpa, hpc] at hpre
                  rw [hexr1, show evalLFNat m N (lfConst 1) = 1 by simp [evalLFNat, evalLF_const]]
                  dsimp only [rep001]
                  exact stepStar_stepPlus_stepPlus hpre ((reach_L2_lb cb (exSL m N c_rem) (exSR m
                    N r_rem)).to_plus (by omega))
              · rw [(ite_eq_right_of_eq_false _ _ (eq_false hab))] at H; injection H with hs';
                  subst hs'
                have hab_0 := fin2_eq_zero_of_ne_one hab; subst hab_0
                obtain ⟨hvl1, hexl1⟩ := exSL_pushL1 a_rem hva
                obtain ⟨hvl2, hexl2⟩ := exSL_pushL1 (symPushL1 a_rem) hvl1
                refine ⟨⟨hvl2, hvRr⟩, ?_⟩
                dsimp only [evalSym]; rw [hpe, hpa] at hpre; rw [hexl2, hexl1]
                exact stepStar_stepPlus_stepPlus hpre ((reach_L3_lb (exSL m N a_rem) (exSR m N
                  r_rem)).to_plus (by omega))

private theorem symStep_sound {m N : ℕ} (hinv : Inv m N) (s s' : SymState)
    (hv : validSym m N s) (H : symStep s = some s') :
    validSym m N s' ∧ ReachesPlus target_tm (evalSym m N s) (evalSym m N s') := by
  rcases s with ⟨hd, l, r⟩
  unfold symStep at H; dsimp only at H
  rcases E0 : symTrySuper4x hd l r with _ | s0
  · rw [E0] at H; dsimp only at H
    rcases E1 : symTryEraDrain hd l r with _ | s1
    · rw [E1] at H; dsimp only at H
      rcases E2 : symTryEraOsc hd l r with _ | s2
      · rw [E2] at H; dsimp only at H
        exact symStepBase_sound hinv hd l r s' hv H
      · rw [E2] at H; injection H with hs; subst hs
        exact symTryEraOsc_sound hinv hd l r s2 hv E2
    · rw [E1] at H; injection H with hs; subst hs
      exact symTryEraDrain_sound hinv hd l r s1 hv E1
  · rw [E0] at H; injection H with hs; subst hs
    exact symTrySuper4x_sound hinv hd l r s0 hv E0

private theorem symIterPow2_sound {m N : ℕ} (hinv : Inv m N) :
    ∀ (k : ℕ) (s s' : SymState),
    validSym m N s → symIterPow2 k s = some s' →
    validSym m N s' ∧ ReachesPlus target_tm (evalSym m N s) (evalSym m N s')
  | 0, s, s', hv, H => symStep_sound hinv s s' hv H
  | k + 1, s, s', hv, H => by
    dsimp only [symIterPow2] at H
    rcases E1 : symIterPow2 k s with _ | sm
    · rw [E1] at H; nomatch H
    · rw [E1] at H
      obtain ⟨hvm, h1⟩ := symIterPow2_sound hinv k s sm hv E1
      obtain ⟨hv', h2⟩ := symIterPow2_sound hinv k sm s' hvm H
      exact ⟨hv', stepPlus_trans h1 h2⟩

def symStart : SymState := ⟨0, [.t110 ⟨1, 0, 0, 0⟩, .b1], []⟩
def symEnd : SymState := ⟨0, [.t110 ⟨256, 0, -180, 54⟩, .b1], []⟩

def symRun642 (s : SymState) : Option SymState :=
  ((symIterPow2 9 s).bind (symIterPow2 7)).bind (symIterPow2 1)

private theorem symRun642_eq : symRun642 symStart = some symEnd := rfl

private theorem cycle_642 {m N : ℕ} (hinv : Inv m N) :
    ReachesPlus target_tm
      (encode (attractorState N))
      (encode (attractorState (256 * N + 54 - 180 * m))) := by
  have hNpos : 1 ≤ N := by
    rcases hinv with ⟨hm10, _, _, hlo, _⟩
    have := sum4_lower m hm10; omega
  have hN'pos : 1 ≤ 256 * N + 54 - 180 * m := by
    rcases hinv with ⟨hm10, _, _, hlo, _⟩
    have := sum4_lower m hm10; omega
  have hv0 : validSym m N symStart := by
    refine ⟨⟨?_, trivial⟩, trivial⟩
    dsimp only [evalLF]; omega
  have H := symRun642_eq
  unfold symRun642 at H
  rcases E1 : symIterPow2 9 symStart with _ | s1; · rw [E1] at H; nomatch H
  rw [E1] at H; dsimp only [Option.bind] at H
  rcases E2 : symIterPow2 7 s1 with _ | s2; · rw [E2] at H; nomatch H
  rw [E2] at H; dsimp only [Option.bind] at H
  obtain ⟨hv1, h1⟩ := symIterPow2_sound hinv 9 symStart s1 hv0 E1
  obtain ⟨hv2, h2⟩ := symIterPow2_sound hinv 7 s1 s2 hv1 E2
  obtain ⟨_, h3⟩ := symIterPow2_sound hinv 1 s2 symEnd hv2 H
  have hall := stepPlus_trans h1 (stepPlus_trans h2 h3)
  have hstart_eq : evalSym m N symStart = encode (attractorState N) := by
    dsimp only [evalSym, symStart, encode, attractorState, exSL, exL, exSR, exR]
    have hN : evalLFNat m N ⟨1, 0, 0, 0⟩ = N - 1 + 1 := by
      dsimp only [evalLFNat, evalLF]; omega
    rw [hN]
  have hend_eq : evalSym m N symEnd = encode (attractorState (256 * N + 54 - 180 * m)) := by
    dsimp only [evalSym, symEnd, encode, attractorState, exSL, exL, exSR, exR]
    have hN' : evalLFNat m N ⟨256, 0, -180, 54⟩ = 256 * N + 54 - 180 * m - 1 + 1 := by
      dsimp only [evalLFNat, evalLF]; omega
    rw [hN']
  rw [hstart_eq, hend_eq] at hall
  exact hall

def InAttractor (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m N, Inv m N ∧ cfg = encode (attractorState N)

private theorem attractor_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : InAttractor cfg) :
    ∃ cfg', ReachesPlus target_tm cfg cfg' ∧ InAttractor cfg' := by
  rcases h with ⟨m, N, hinv, rfl⟩
  exact ⟨encode (attractorState (256 * N + 54 - 180 * m)),
    cycle_642 hinv,
    ⟨m + 4, 256 * N + 54 - 180 * m, inv_step hinv, rfl⟩⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  IsNotHalt.of_reachesPlus_invariant
    init_reaches_N0
    ⟨136, N0, inv_init_N0, rfl⟩
    attractor_closed


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH
