/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat

/-!
# Busy Beaver Machine `1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

@[expose] public section

/-- Transition function for `1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-! ### Reusable Step-Counted & Reachability Helpers -/

abbrev sA : Fin 6 := 2
abbrev sB : Fin 6 := 0
abbrev sF : Fin 6 := 5

private theorem reachesIn_zero (c : Cfg (Fin 2) (Fin 6)) : ReachesIn target_tm 0 c c :=
  ReachesIn.zero target_tm c

private theorem reachesStar_refl (c : Cfg (Fin 2) (Fin 6)) : ReachesStar target_tm c c :=
  ⟨0, rfl⟩

private theorem reachesStar_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : ReachesStar target_tm c₁ c₂) (h₂ : ReachesStar target_tm c₂ c₃) :
    ReachesStar target_tm c₁ c₃ := by
  obtain ⟨m, h1⟩ := h₁
  obtain ⟨n, h2⟩ := h₂
  exact ⟨m + n, multiStep_trans h1 h2⟩

private theorem reachesPlus_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : ReachesPlus target_tm c₁ c₂) (h₂ : ReachesPlus target_tm c₂ c₃) :
    ReachesPlus target_tm c₁ c₃ := by
  obtain ⟨m, hm, h1⟩ := h₁
  obtain ⟨n, _, h2⟩ := h₂
  exact ⟨m + n, Nat.add_pos_left hm n, multiStep_trans h1 h2⟩

private theorem reachesPlus_trans_star {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : ReachesPlus target_tm c₁ c₂) (h₂ : ReachesStar target_tm c₂ c₃) :
    ReachesPlus target_tm c₁ c₃ := by
  obtain ⟨m, hm, h1⟩ := h₁
  obtain ⟨n, h2⟩ := h₂
  exact ⟨m + n, Nat.add_pos_left hm n, multiStep_trans h1 h2⟩

private theorem headLeft_cons_eq (q : Fin 6) (a : Fin 2) (l r : ListBlank (Fin 2)) :
    ((a >> l) <{{q}} r) = (l {{q}}> (a >> r)) := by
  simp

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

private theorem lb_zero_cons_default :
    ((0 : Fin 2) >> (default : ListBlank (Fin 2))) = default := by
  apply ListBlank.ext
  intro i
  cases i <;> rfl

private theorem rstep_rl_def {n : ℕ} {q q' : Fin 6} {a w : Fin 2}
    {r : ListBlank (Fin 2)} {c₃ : Cfg (Fin 2) (Fin 6)}
    (hM : target_tm q a = some (some q', Stmt.write w Dir.left))
    (h : ReachesIn target_tm n ((default : ListBlank (Fin 2)) {{q'}}> ((0 : Fin 2) >> w >> r)) c₃) :
    ReachesIn target_tm (n + 1) ((default : ListBlank (Fin 2)) {{q}}> (a >> r)) c₃ := by
  rw [← lb_zero_cons_default]
  exact rstep_rl hM h

local macro "stepK" : tactic =>
  `(tactic| (
    repeat (first
      | refine rstep_rr rfl ?_
      | refine rstep_rl rfl ?_
      | refine rstep_rl_def rfl ?_
      | refine rstep_lr rfl ?_
      | refine rstep_ll rfl ?_)
    first
      | exact reachesIn_zero _
      | (rw [lb_zero_cons_default]; exact reachesIn_zero _)
      | (rw [headLeft_cons_eq]; exact reachesIn_zero _)
      | (rw [headLeft_cons_eq, lb_zero_cons_default]; exact reachesIn_zero _)
      | (rw [← headLeft_cons_eq]; exact reachesIn_zero _)
      | (simp only [headLeft_cons_eq, lb_zero_cons_default]; exact reachesIn_zero _)))

/-! ### 7-Token Run Algebra -/

inductive Tok where
  | b0 | b1 | p2 | q | u | m | s
  deriving DecidableEq

def tokStep (t : Tok) (lb : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  match t with
  | .b0 => (0 : Fin 2) >> lb
  | .b1 => (1 : Fin 2) >> lb
  | .p2 => (0 : Fin 2) >> (1 : Fin 2) >> lb
  | .q  => (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2)
    >> lb
  | .u  => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> lb
  | .m  => (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> lb
  | .s  => (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
           (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
           (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> lb

def repTok (t : Tok) : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, lb => lb
  | n + 1, lb => tokStep t (repTok t n lb)

private theorem repTok_add (t : Tok) : ∀ (a b : ℕ) (lb : ListBlank (Fin 2)),
    repTok t (a + b) lb = repTok t a (repTok t b lb)
  | 0, _, _ => by simp only [Nat.zero_add, repTok]
  | a + 1, b, lb => by
    rw [Nat.succ_add]
    dsimp only [repTok]
    rw [repTok_add t a b lb]

private theorem repTok_shift (t : Tok) : ∀ (n : ℕ) (lb : ListBlank (Fin 2)),
    repTok t n (tokStep t lb) = tokStep t (repTok t n lb)
  | 0, _ => rfl
  | n + 1, lb => by
    dsimp only [repTok]
    rw [repTok_shift t n lb]

private theorem repTok_b0_default : ∀ (n : ℕ),
    repTok .b0 n (default : ListBlank (Fin 2)) = default
  | 0 => rfl
  | n + 1 => by
    dsimp only [repTok, tokStep]
    rw [repTok_b0_default n, lb_zero_cons_default]

def rep000P2 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, lb => lb
  | n + 1,
    lb => (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep000P2 n lb

private theorem rep000P2_shift : ∀ (n : ℕ) (lb : ListBlank (Fin 2)),
    rep000P2 n ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> lb) =
      (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> rep000P2 n lb
  | 0, _ => rfl
  | n + 1, lb => by
    dsimp only [rep000P2]
    rw [rep000P2_shift n lb]

private abbrev s8Prefix (l : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
  (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l

/-! ### Base Macro & Bridge Reachability Lemmas -/

private theorem reach_A0 (b : Fin 2) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sA}}> ((0 : Fin 2) >> b >> r))
      (((1 : Fin 2) >> l) {{sB}}> (b >> r)) := by
  have h : ReachesIn target_tm 1
      (l {{sA}}> ((0 : Fin 2) >> b >> r))
      (((1 : Fin 2) >> l) {{sB}}> (b >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_A1_10 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (((0 : Fin 2) >> l) {{sB}}> ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 3
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (((0 : Fin 2) >> l) {{sB}}> ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_A1_11 (b : Fin 2) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> b >> r))
      ((tokStep .u l) {{sA}}> (b >> r)) := by
  have h : ReachesIn target_tm 3
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> b >> r))
      ((tokStep .u l) {{sA}}> (b >> r)) := by dsimp only [tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_B0_0 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 2
      (l {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_B0_1 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sB}}> ((0 : Fin 2) >> (1 : Fin 2) >> r))
      (l {{sB}}> ((1 : Fin 2) >> (0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 2
      (l {{sB}}> ((0 : Fin 2) >> (1 : Fin 2) >> r))
      (l {{sB}}> ((1 : Fin 2) >> (0 : Fin 2) >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_B1_1 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (((1 : Fin 2) >> l) {{sB}}> ((1 : Fin 2) >> r))
      (((0 : Fin 2) >> l) {{sA}}> ((0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 2
      (((1 : Fin 2) >> l) {{sB}}> ((1 : Fin 2) >> r))
      (((0 : Fin 2) >> l) {{sA}}> ((0 : Fin 2) >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_B1_00 (b : Fin 2) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (((0 : Fin 2) >> (0 : Fin 2) >> b >> l) {{sB}}> ((1 : Fin 2) >> r))
      (l {{sA}}> (b >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 3
      (((0 : Fin 2) >> (0 : Fin 2) >> b >> l) {{sB}}> ((1 : Fin 2) >> r))
      (l {{sA}}> (b >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_B1_01 (b : Fin 2) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (((0 : Fin 2) >> (1 : Fin 2) >> b >> l) {{sB}}> ((1 : Fin 2) >> r))
      (l {{sB}}> (b >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 3
      (((0 : Fin 2) >> (1 : Fin 2) >> b >> l) {{sB}}> ((1 : Fin 2) >> r))
      (l {{sB}}> (b >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) := by stepK
  exact h.to_plus (by omega)

private theorem reach_peelP_one (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sB}}> ((0 : Fin 2) >> repTok .p2 3 r))
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 14
      (l {{sB}}> ((0 : Fin 2) >> repTok .p2 3 r))
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> r)) := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_peelP_star : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesStar target_tm
      (l {{sB}}> ((0 : Fin 2) >> repTok .p2 (3 * k) r))
      ((repTok .q k l) {{sB}}> ((0 : Fin 2) >> r))
  | 0, _, _ => reachesStar_refl _
  | k + 1, l, r => by
    have hk : 3 * (k + 1) = 3 + 3 * k := by omega
    rw [hk, repTok_add .p2 3 (3 * k)]
    have h1 := reach_peelP_one l (repTok .p2 (3 * k) r)
    have h2 := reach_peelP_star k (tokStep .q l) r
    rw [repTok_shift .q k l] at h2
    exact (reachesPlus_trans_star h1 h2).to_star

private theorem reach_peelP_pos (k : ℕ) (hk : 1 ≤ k) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sB}}> ((0 : Fin 2) >> repTok .p2 (3 * k) r))
      ((repTok .q k l) {{sB}}> ((0 : Fin 2) >> r)) := by
  cases k with
  | zero => omega
  | succ m =>
    have hm : 3 * (m + 1) = 3 + 3 * m := by omega
    rw [hm, repTok_add .p2 3 (3 * m)]
    have h1 := reach_peelP_one l (repTok .p2 (3 * m) r)
    have h2 := reach_peelP_star m (tokStep .q l) r
    rw [repTok_shift .q m l] at h2
    exact reachesPlus_trans_star h1 h2

private theorem reach_peelQ_one (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .q l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 3 r)) := by
  have h : ReachesIn target_tm 22
      ((tokStep .q l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 3 r)) := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_peelQ_star : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesStar target_tm
      ((repTok .q k l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 (3 * k) r))
  | 0, _, _ => reachesStar_refl _
  | k + 1, l, r => by
    dsimp only [repTok]
    have h1 := reach_peelQ_one (repTok .q k l) r
    have h2 := reach_peelQ_star k l (repTok .p2 3 r)
    rw [← repTok_add .p2 (3 * k) 3 r, show 3 * k + 3 = 3 * (k + 1) by omega] at h2
    exact (reachesPlus_trans_star h1 h2).to_star

private theorem reach_peelQ_pos (k : ℕ) (hk : 1 ≤ k) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((repTok .q k l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 (3 * k) r)) := by
  cases k with
  | zero => omega
  | succ m =>
    dsimp only [repTok]
    have h1 := reach_peelQ_one (repTok .q m l) r
    have h2 := reach_peelQ_star m l (repTok .p2 3 r)
    rw [← repTok_add .p2 (3 * m) 3 r, show 3 * m + 3 = 3 * (m + 1) by omega] at h2
    exact reachesPlus_trans_star h1 h2

private theorem reach_wall00 (r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((default : ListBlank (Fin 2)) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r))
      (((1 : Fin 2) >> (default : ListBlank (Fin 2))) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 :
        Fin 2) >> r)) := by
  have h : ReachesIn target_tm 12
      ((default : ListBlank (Fin 2)) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r))
      (((1 : Fin 2) >> (default : ListBlank (Fin 2))) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 :
        Fin 2) >> r)) := by
    stepK
  exact h.to_plus (by omega)

private theorem reach_R_P1_000 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 :
        Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))
      ((tokStep .s l) {{sB}}> ((0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 67
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 :
        Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))
      ((tokStep .s l) {{sB}}> ((0 : Fin 2) >> r)) := by
    dsimp only [tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_R_01010 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (l {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 :
        Fin 2) >> r))
      ((tokStep .m l) {{sB}}> ((0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 9
      (l {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 :
        Fin 2) >> r))
      ((tokStep .m l) {{sB}}> ((0 : Fin 2) >> r)) := by
    dsimp only [tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_R_M_010000 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .m l) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 :
        Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 4 ((1 : Fin 2) >> r)))
        := by
  have h : ReachesIn target_tm 47
      ((tokStep .m l) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 :
        Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 4 ((1 : Fin 2) >> r)))
        := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_R_P2_000 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 :
        Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 ((0 : Fin 2) >> (0 :
        Fin 2) >> (0 : Fin 2) >> repTok .p2 3 r))) := by
  have h : ReachesIn target_tm 44
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 :
        Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 ((0 : Fin 2) >> (0 :
        Fin 2) >> (0 : Fin 2) >> repTok .p2 3 r))) := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_L_wall1 (r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      (((1 : Fin 2) >> (default : ListBlank (Fin 2))) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 :
        Fin 2) >> r))
      ((default : ListBlank (Fin 2)) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 :
        Fin 2) >> (1 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 6
      (((1 : Fin 2) >> (default : ListBlank (Fin 2))) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 :
        Fin 2) >> r))
      ((default : ListBlank (Fin 2)) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 :
        Fin 2) >> (1 : Fin 2) >> r)) := by
    stepK
  exact h.to_plus (by omega)

private theorem reach_L_S8 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((s8Prefix l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> repTok .p2 2 r)) := by
  have h : ReachesIn target_tm 18
      ((s8Prefix l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> repTok .p2 2 r)) := by
    dsimp only [s8Prefix, repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_L_S (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .s l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      ((tokStep .q (tokStep .m l)) {{sB}}> ((0 : Fin 2) >> repTok .p2 2 r)) :=
  reach_L_S8 (tokStep .m l) r

private theorem reach_L_MS (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .m (tokStep .s l)) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      ((tokStep .s (tokStep .m l)) {{sB}}> ((0 : Fin 2) >> repTok .p2 1 r)) := by
  have h : ReachesIn target_tm 96
      ((tokStep .m (tokStep .s l)) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      ((tokStep .s (tokStep .m l)) {{sB}}> ((0 : Fin 2) >> repTok .p2 1 r)) := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_R_Q11 (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r))
      ((s8Prefix l) {{sB}}> ((0 : Fin 2) >> r)) := by
  have h : ReachesIn target_tm 10
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r))
      ((s8Prefix l) {{sB}}> ((0 : Fin 2) >> r)) := by
    dsimp only [s8Prefix, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_R_000S8 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((repTok .q k (s8Prefix l)) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin
        2) >> r))
      ((tokStep .m (repTok .q (k + 1) l)) {{sB}}> ((0 : Fin 2) >> r)) := by
  have h1 := reach_B0_0 (repTok .q k (s8Prefix l)) ((0 : Fin 2) >> (0 : Fin 2) >> r)
  have h2 := reach_peelQ_star k (s8Prefix l) ((0 : Fin 2) >> r)
  have h3 := reach_L_S8 l (repTok .p2 (3 * k) ((0 : Fin 2) >> r))
  rw [← repTok_add .p2 2 (3 * k) ((0 : Fin 2) >> r),
      show 2 + 3 * k = 3 * k + 2 by omega,
      repTok_add .p2 (3 * k) 2 ((0 : Fin 2) >> r)] at h3
  have h4 := reach_peelP_star k (tokStep .q l) (repTok .p2 2 ((0 : Fin 2) >> r))
  rw [repTok_shift .q k l] at h4
  have h5 := reach_R_01010 (repTok .q (k + 1) l) r
  exact reachesPlus_trans
    (reachesPlus_trans_star h1 h2)
    (reachesPlus_trans (reachesPlus_trans_star h3 h4) h5)

private theorem reach_R_000S (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((repTok .q k (tokStep .s l)) {{sB}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin
        2) >> r))
      ((tokStep .m (repTok .q (k + 1) (tokStep .m l))) {{sB}}> ((0 : Fin 2) >> r)) :=
  reach_R_000S8 k (tokStep .m l) r

private theorem reach_R_11Pm000 (m : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .q l) {{sB}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> repTok .p2 (3 * m) ((0
        : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)))
      ((tokStep .m (repTok .q (m + 1) l)) {{sB}}> ((0 : Fin 2) >> r)) := by
  have h1 := reach_R_Q11 l (repTok .p2 (3 * m) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r))
  have h2 := reach_peelP_star m (s8Prefix l) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)
  have h3 := reach_R_000S8 m l r
  exact reachesPlus_trans (reachesPlus_trans_star h1 h2) h3

private theorem reach_L_M_enter (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .m l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sF}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 r)) := by
  have h : ReachesIn target_tm 15
      ((tokStep .m l) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sF}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 r)) := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_L_M_loop (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .m l) {{sF}}> ((0 : Fin 2) >> r))
      (l {{sF}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 :
        Fin 2) >> r)) := by
  have h : ReachesIn target_tm 11
      ((tokStep .m l) {{sF}}> ((0 : Fin 2) >> r))
      (l {{sF}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 :
        Fin 2) >> r)) := by
    dsimp only [tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_L_M_loop_iter : ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
    ReachesStar target_tm
      ((repTok .m k l) {{sF}}> ((0 : Fin 2) >> r))
      (l {{sF}}> ((0 : Fin 2) >> rep000P2 k r))
  | 0, _, _ => reachesStar_refl _
  | k + 1, l, r => by
    dsimp only [repTok]
    have h1 := reach_L_M_loop (repTok .m k l) r
    have h2 :=
      reach_L_M_loop_iter k l ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 :
      Fin 2) >> r)
    rw [rep000P2_shift k r] at h2
    exact (reachesPlus_trans_star h1 h2).to_star

private theorem reach_L_M_exit (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((tokStep .q l) {{sF}}> ((0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 r)) := by
  have h : ReachesIn target_tm 18
      ((tokStep .q l) {{sF}}> ((0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 r)) := by
    dsimp only [repTok, tokStep]; stepK
  exact h.to_plus (by omega)

private theorem reach_L_MkQ (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((repTok .m (k + 1) (tokStep .q l)) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r))
      (l {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        repTok .p2 2 (rep000P2 k ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 r))))
          := by
  dsimp only [repTok]
  have h1 := reach_L_M_enter (repTok .m k (tokStep .q l)) r
  have h2 :=
    reach_L_M_loop_iter k (tokStep .q l) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> repTok .p2
    2 r)
  have h3 :=
    reach_L_M_exit l (rep000P2 k ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> repTok .p2 2 r))
  exact reachesPlus_trans (reachesPlus_trans_star h1 h2) h3

/-! ### Purely Nonnegative Symbolic Interpreter & Unconditional Soundness -/

structure SN where
  ca : ℕ
  cb : ℕ
  c0 : ℕ
  deriving DecidableEq

def SN.isZero (x : SN) : Bool := x.ca == 0 && x.cb == 0 && x.c0 == 0
def SN.add (x y : SN) : SN := ⟨x.ca + y.ca, x.cb + y.cb, x.c0 + y.c0⟩
def SN.mul3 (x : SN) : SN := ⟨x.ca * 3, x.cb * 3, x.c0 * 3⟩
def SN.eval (a0 b0 : ℕ) (x : SN) : ℕ := x.ca * a0 + x.cb * b0 + x.c0

structure SRun where
  t : Tok
  k : SN
  deriving DecidableEq

abbrev SSide := List SRun

structure SState where
  isB : Bool
  h : Bool
  L : SSide
  R : SSide
  deriving DecidableEq

def boolToFin2 : Bool → Fin 2
  | false => 0
  | true => 1

def exSide (a0 b0 : ℕ) : SSide → ListBlank (Fin 2)
  | [] => default
  | ⟨t, k⟩ :: rest => repTok t (k.eval a0 b0) (exSide a0 b0 rest)

def evalSym (a0 b0 : ℕ) (st : SState) : Cfg (Fin 2) (Fin 6) :=
  let q := if st.isB then sB else sA
  (exSide a0 b0 st.L) {{q}}> (boolToFin2 st.h >> exSide a0 b0 st.R)

def sdec (k : SN) (t : Tok) (rest : SSide) : SSide :=
  if k.ca == 0 && k.cb == 0 && k.c0 == 1 then rest
  else ⟨t, ⟨k.ca, k.cb, k.c0 - 1⟩⟩ :: rest

private theorem exSide_sdec (a0 b0 : ℕ) (t : Tok) (k : SN) (rest : SSide) (hk : 1 ≤ k.c0) :
    exSide a0 b0 (⟨t, k⟩ :: rest) = tokStep t (exSide a0 b0 (sdec k t rest)) := by
  unfold sdec
  by_cases h1 : (k.ca == 0 && k.cb == 0 && k.c0 == 1) = true
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true h1))]
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with ⟨⟨hca, hcb⟩, hc0⟩
    simp only [exSide, SN.eval, hca, hcb, hc0, Nat.zero_mul, Nat.zero_add, repTok]
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false h1))]
    simp only [exSide, SN.eval]
    have heq : k.ca * a0 + k.cb * b0 + k.c0 = (k.ca * a0 + k.cb * b0 + (k.c0 - 1)) + 1 := by omega
    rw [heq]; rfl

def spushRaw (t : Tok) (k : SN) (s : SSide) : SSide :=
  if k.isZero then s
  else match s with
  | [] => match t with
    | .b0 => []
    | _ => [⟨t, k⟩]
  | ⟨t0, k0⟩ :: rest =>
    if t == t0 then ⟨t, k.add k0⟩ :: rest
    else ⟨t, k⟩ :: ⟨t0, k0⟩ :: rest

private theorem exSide_spushRaw (a0 b0 : ℕ) (t : Tok) (k : SN) (s : SSide) :
    exSide a0 b0 (spushRaw t k s) = repTok t (k.eval a0 b0) (exSide a0 b0 s) := by
  unfold spushRaw
  by_cases hz : k.isZero = true
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz))]
    simp only [SN.isZero, Bool.and_eq_true, beq_iff_eq] at hz
    rcases hz with ⟨⟨hca, hcb⟩, hc0⟩
    simp only [SN.eval, hca, hcb, hc0, Nat.zero_mul, Nat.add_zero, repTok]
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz))]
    cases s with
    | nil =>
      cases t <;> simp only [exSide, repTok_b0_default]
    | cons hd rest =>
      rcases hd with ⟨t0, k0⟩
      dsimp only
      by_cases ht : (t == t0) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true ht))]
        have hteq : t = t0 := beq_iff_eq.mp ht
        subst hteq
        have hadd : (k.add k0).eval a0 b0 = k.eval a0 b0 + k0.eval a0 b0 := by
          simp only [SN.add, SN.eval, Nat.add_mul]; omega
        dsimp only [exSide]
        rw [hadd, repTok_add]
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false ht))]
        rfl

def spush (t : Tok) (k : SN) (s : SSide) : SSide :=
  if k.isZero then s
  else match t, s with
  | .b0, ⟨.b1, k0⟩ :: rest =>
    if k.ca == 0 && k.cb == 0 && decide (1 ≤ k.c0) && decide (1 ≤ k0.c0) then
      let s1 := spushRaw .p2 ⟨0, 0, 1⟩ (sdec k0 .b1 rest)
      if k.c0 == 1 then s1 else ⟨.b0, ⟨0, 0, k.c0 - 1⟩⟩ :: s1
    else ⟨.b0, k⟩ :: ⟨.b1, k0⟩ :: rest
  | _, _ => spushRaw t k s

private theorem exSide_spush (a0 b0 : ℕ) (t : Tok) (k : SN) (s : SSide) :
    exSide a0 b0 (spush t k s) = repTok t (k.eval a0 b0) (exSide a0 b0 s) := by
  unfold spush
  by_cases hz : k.isZero = true
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hz))]
    simp only [SN.isZero, Bool.and_eq_true, beq_iff_eq] at hz
    rcases hz with ⟨⟨hca, hcb⟩, hc0⟩
    simp only [SN.eval, hca, hcb, hc0, Nat.zero_mul, Nat.add_zero, repTok]
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hz))]
    cases t with
    | b0 =>
      cases s with
      | nil => exact exSide_spushRaw a0 b0 .b0 k []
      | cons hd rest =>
        rcases hd with ⟨t0, k0⟩
        cases t0 with
        | b1 =>
          dsimp only
          by_cases hcond : (k.ca == 0 && k.cb == 0 && decide (1 ≤ k.c0) && decide (1 ≤ k0.c0)) =
            true
          · rw [(ite_eq_left_of_eq_true _ _ (eq_true hcond))]
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            rcases hcond with ⟨⟨⟨hca, hcb⟩, hk1⟩, hk01⟩
            have hdec := exSide_sdec a0 b0 .b1 k0 rest hk01
            have hp2 := exSide_spushRaw a0 b0 .p2 ⟨0, 0, 1⟩ (sdec k0 .b1 rest)
            have heval : k.eval a0 b0 = (k.c0 - 1) + 1 := by
              simp only [SN.eval, hca, hcb, Nat.zero_mul, Nat.zero_add]; omega
            by_cases hc1 : (k.c0 == 1) = true
            · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc1))]
              have hc1' : k.c0 = 1 := beq_iff_eq.mp hc1
              rw [hp2, heval, hc1', hdec]
              simp only [SN.eval, Nat.zero_mul, Nat.zero_add, Nat.sub_self, repTok, tokStep]
            · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc1))]
              rw [heval, repTok_add .b0 (k.c0 - 1) 1, hdec]
              simp only [exSide, hp2, SN.eval, Nat.zero_mul, Nat.zero_add, repTok, tokStep]
          · rw [(ite_eq_right_of_eq_false _ _ (eq_false hcond))]; rfl
        | _ => exact exSide_spushRaw a0 b0 .b0 k _
    | _ => exact exSide_spushRaw a0 b0 _ k s

def spushc (t : Tok) (c : ℕ) (s : SSide) : SSide := spush t ⟨0, 0, c⟩ s

private theorem exSide_spushc (a0 b0 : ℕ) (t : Tok) (c : ℕ) (s : SSide) :
    exSide a0 b0 (spushc t c s) = repTok t c (exSide a0 b0 s) := by
  rw [spushc, exSide_spush]
  simp only [SN.eval, Nat.zero_mul, Nat.zero_add]

def spop0 : SSide → Option SSide
  | [] => some []
  | ⟨.b0, k⟩ :: rest => if 1 ≤ k.c0 then some (sdec k .b0 rest) else none
  | ⟨.p2, k⟩ :: rest => if 1 ≤ k.c0 then some (spushc .b1 1 (sdec k .p2 rest)) else none
  | _ => none

def spop1 : SSide → Option SSide
  | ⟨.b1, k⟩ :: rest => if 1 ≤ k.c0 then some (sdec k .b1 rest) else none
  | ⟨.q,
    k⟩ :: rest => if 1 ≤ k.c0 then some (spushc .b0 2 (spushc .b1 2 (spushc .b0 1 (sdec k .q
    rest)))) else none
  | ⟨.u,
    k⟩ :: rest => if 1 ≤ k.c0 then some (spushc .b1 1 (spushc .b0 1 (sdec k .u rest))) else none
  | ⟨.m,
    k⟩ :: rest => if 1 ≤ k.c0 then some (spushc .b0 1 (spushc .b1 2 (spushc .b0 1 (sdec k .m
    rest)))) else none
  | ⟨.s,
    k⟩ :: rest => if 1 ≤ k.c0 then some (spushc .b0 4 (spushc .b1 2 (spushc .b0 1 (spushc .m 1
    (sdec k .s rest))))) else none
  | _ => none

def spopBit : SSide → Option (Bool × SSide)
  | [] => some (false, [])
  | ⟨.b0, k⟩ :: rest => if 1 ≤ k.c0 then some (false, sdec k .b0 rest) else none
  | ⟨.p2, k⟩ :: rest => if 1 ≤ k.c0 then some (false, spushc .b1 1 (sdec k .p2 rest)) else none
  | ⟨.b1, k⟩ :: rest => if 1 ≤ k.c0 then some (true, sdec k .b1 rest) else none
  | ⟨.q, k⟩ :: rest => if 1 ≤ k.c0 then some (true,
    spushc .b0 2 (spushc .b1 2 (spushc .b0 1 (sdec k .q rest)))) else none
  | ⟨.u, k⟩ :: rest => if 1 ≤ k.c0 then some (true,
    spushc .b1 1 (spushc .b0 1 (sdec k .u rest))) else none
  | ⟨.m, k⟩ :: rest => if 1 ≤ k.c0 then some (true,
    spushc .b0 1 (spushc .b1 2 (spushc .b0 1 (sdec k .m rest)))) else none
  | ⟨.s, k⟩ :: rest => if 1 ≤ k.c0 then some (true,
    spushc .b0 4 (spushc .b1 2 (spushc .b0 1 (spushc .m 1 (sdec k .s rest))))) else none

private theorem spop0_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop0 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> exSide a0 b0 s' := by
  cases s with
  | nil =>
    injection H with hs'; subst hs'
    exact lb_zero_cons_default.symm
  | cons hd rest =>
    rcases hd with ⟨t, k⟩
    cases t with
    | b0 =>
      dsimp only [spop0] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      exact exSide_sdec a0 b0 .b0 k rest hk
    | p2 =>
      dsimp only [spop0] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      rw [exSide_sdec a0 b0 .p2 k rest hk, exSide_spushc]; rfl
    | _ => nomatch H

private theorem spop1_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop1 s = some s') :
    exSide a0 b0 s = (1 : Fin 2) >> exSide a0 b0 s' := by
  cases s with
  | nil => nomatch H
  | cons hd rest =>
    rcases hd with ⟨t, k⟩
    cases t with
    | b1 =>
      dsimp only [spop1] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      exact exSide_sdec a0 b0 .b1 k rest hk
    | q =>
      dsimp only [spop1] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      rw [exSide_sdec a0 b0 .q k rest hk, exSide_spushc, exSide_spushc, exSide_spushc]; rfl
    | u =>
      dsimp only [spop1] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      rw [exSide_sdec a0 b0 .u k rest hk, exSide_spushc, exSide_spushc]; rfl
    | m =>
      dsimp only [spop1] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      rw [exSide_sdec a0 b0 .m k rest hk, exSide_spushc, exSide_spushc, exSide_spushc]; rfl
    | s =>
      dsimp only [spop1] at H
      split_ifs at H with hk
      injection H with hs'; subst hs'
      rw [exSide_sdec a0 b0 .s k rest hk, exSide_spushc, exSide_spushc, exSide_spushc,
        exSide_spushc]
      rfl
    | _ => nomatch H

private theorem spopBit_sound (a0 b0 : ℕ) {s s' : SSide} {b : Bool} (H : spopBit s = some (b, s')) :
    exSide a0 b0 s = boolToFin2 b >> exSide a0 b0 s' := by
  cases s with
  | nil =>
    injection H with hp; injection hp with hb hs'; subst hb; subst hs'
    exact lb_zero_cons_default.symm
  | cons hd rest =>
    rcases hd with ⟨t, k⟩
    cases t <;> simp only [spopBit] at H <;> split_ifs at H with hk
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      exact exSide_sdec a0 b0 .b0 k rest hk
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      exact exSide_sdec a0 b0 .b1 k rest hk
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      rw [exSide_sdec a0 b0 .p2 k rest hk, exSide_spushc]; rfl
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      rw [exSide_sdec a0 b0 .q k rest hk, exSide_spushc, exSide_spushc, exSide_spushc]; rfl
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      rw [exSide_sdec a0 b0 .u k rest hk, exSide_spushc, exSide_spushc]; rfl
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      rw [exSide_sdec a0 b0 .m k rest hk, exSide_spushc, exSide_spushc, exSide_spushc]; rfl
    · injection H with hp; injection hp with hb hs'; subst hb; subst hs'
      rw [exSide_sdec a0 b0 .s k rest hk, exSide_spushc, exSide_spushc, exSide_spushc,
        exSide_spushc]
      rfl

/-! ### Fast Short-Circuiting Bit-Pattern Poppers -/

def spop00 (s : SSide) : Option SSide :=
  (spop0 s).bind spop0

def spop10 (s : SSide) : Option SSide :=
  (spop1 s).bind spop0

def spop11 (s : SSide) : Option SSide :=
  (spop1 s).bind spop1

def spop000 (s : SSide) : Option SSide :=
  ((spop0 s).bind spop0).bind spop0

def spop01010 (s : SSide) : Option SSide :=
  ((((spop0 s).bind spop1).bind spop0).bind spop1).bind spop0

def spop10110 (s : SSide) : Option SSide :=
  ((((spop1 s).bind spop0).bind spop1).bind spop1).bind spop0

def spop100110 (s : SSide) : Option SSide :=
  (((((spop1 s).bind spop0).bind spop0).bind spop1).bind spop1).bind spop0

def spop010000 (s : SSide) : Option SSide :=
  (((((spop0 s).bind spop1).bind spop0).bind spop0).bind spop0).bind spop0

def spop0100001 (s : SSide) : Option SSide :=
  (spop010000 s).bind spop1

def spop010100001 (s : SSide) : Option SSide :=
  ((((((((spop0 s).bind spop1).bind spop0).bind spop1).bind spop0).bind spop0).bind spop0).bind
    spop0).bind spop1

private theorem bind_some_elim {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : x.bind f = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => nomatch h
  | some a => exact ⟨a, rfl, h⟩

private theorem spop00_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop00 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s1, h1, h2⟩ := bind_some_elim H
  rw [spop0_sound a0 b0 h1, spop0_sound a0 b0 h2]

private theorem spop10_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop10 s = some s') :
    exSide a0 b0 s = (1 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s1, h1, h2⟩ := bind_some_elim H
  rw [spop1_sound a0 b0 h1, spop0_sound a0 b0 h2]

private theorem spop11_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop11 s = some s') :
    exSide a0 b0 s = (1 : Fin 2) >> (1 : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s1, h1, h2⟩ := bind_some_elim H
  rw [spop1_sound a0 b0 h1, spop1_sound a0 b0 h2]

private theorem spop000_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop000 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s2, h12, h3⟩ := bind_some_elim H
  obtain ⟨s1, h1, h2⟩ := bind_some_elim h12
  rw [spop0_sound a0 b0 h1, spop0_sound a0 b0 h2, spop0_sound a0 b0 h3]

private theorem spop01010_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop01010 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      exSide a0 b0 s' := by
  obtain ⟨s4, h14, h5⟩ := bind_some_elim H
  obtain ⟨s3, h13, h4⟩ := bind_some_elim h14
  obtain ⟨s2, h12, h3⟩ := bind_some_elim h13
  obtain ⟨s1, h1, h2⟩ := bind_some_elim h12
  rw [spop0_sound a0 b0 h1, spop1_sound a0 b0 h2, spop0_sound a0 b0 h3, spop1_sound a0 b0 h4,
    spop0_sound a0 b0 h5]

private theorem spop10110_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop10110 s = some s') :
    exSide a0 b0 s = tokStep .m (exSide a0 b0 s') := by
  obtain ⟨s4, h14, h5⟩ := bind_some_elim H
  obtain ⟨s3, h13, h4⟩ := bind_some_elim h14
  obtain ⟨s2, h12, h3⟩ := bind_some_elim h13
  obtain ⟨s1, h1, h2⟩ := bind_some_elim h12
  rw [spop1_sound a0 b0 h1, spop0_sound a0 b0 h2, spop1_sound a0 b0 h3, spop1_sound a0 b0 h4,
    spop0_sound a0 b0 h5]
  rfl

private theorem spop100110_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop100110 s = some s') :
    exSide a0 b0 s = tokStep .q (exSide a0 b0 s') := by
  obtain ⟨s5, h15, h6⟩ := bind_some_elim H
  obtain ⟨s4, h14, h5⟩ := bind_some_elim h15
  obtain ⟨s3, h13, h4⟩ := bind_some_elim h14
  obtain ⟨s2, h12, h3⟩ := bind_some_elim h13
  obtain ⟨s1, h1, h2⟩ := bind_some_elim h12
  rw [spop1_sound a0 b0 h1, spop0_sound a0 b0 h2, spop0_sound a0 b0 h3,
      spop1_sound a0 b0 h4, spop1_sound a0 b0 h5, spop0_sound a0 b0 h6]
  rfl

private theorem spop010000_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop010000 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0
      : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s5, h15, h6⟩ := bind_some_elim H
  obtain ⟨s4, h14, h5⟩ := bind_some_elim h15
  obtain ⟨s3, h13, h4⟩ := bind_some_elim h14
  obtain ⟨s2, h12, h3⟩ := bind_some_elim h13
  obtain ⟨s1, h1, h2⟩ := bind_some_elim h12
  rw [spop0_sound a0 b0 h1, spop1_sound a0 b0 h2, spop0_sound a0 b0 h3,
      spop0_sound a0 b0 h4, spop0_sound a0 b0 h5, spop0_sound a0 b0 h6]

private theorem spop0100001_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop0100001 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0
      : Fin 2) >> (1 : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s6, h16, h7⟩ := bind_some_elim H
  rw [spop010000_sound a0 b0 h16, spop1_sound a0 b0 h7]

private theorem spop010100001_sound (a0 b0 : ℕ) {s s' : SSide} (H : spop010100001 s = some s') :
    exSide a0 b0 s = (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0
      : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> exSide a0 b0 s' := by
  obtain ⟨s8, h18, h9⟩ := bind_some_elim H
  obtain ⟨s7, h17, h8⟩ := bind_some_elim h18
  obtain ⟨s6, h16, h7⟩ := bind_some_elim h17
  obtain ⟨s5, h15, h6⟩ := bind_some_elim h16
  obtain ⟨s4, h14, h5⟩ := bind_some_elim h15
  obtain ⟨s3, h13, h4⟩ := bind_some_elim h14
  obtain ⟨s2, h12, h3⟩ := bind_some_elim h13
  obtain ⟨s1, h1, h2⟩ := bind_some_elim h12
  rw [spop0_sound a0 b0 h1, spop1_sound a0 b0 h2, spop0_sound a0 b0 h3,
      spop1_sound a0 b0 h4, spop0_sound a0 b0 h5, spop0_sound a0 b0 h6,
      spop0_sound a0 b0 h7, spop0_sound a0 b0 h8, spop1_sound a0 b0 h9]

/-! ### Peel & Super-Sweep Functions + Soundness -/

def speelP : SSide → Option (SN × SSide)
  | ⟨.p2, k⟩ :: rest =>
    if k.ca % 3 == 0 && k.cb % 3 == 0 then
      let q : SN := ⟨k.ca / 3, k.cb / 3, k.c0 / 3⟩
      let rem := k.c0 % 3
      some (q, if rem == 0 then rest else spushc .p2 rem rest)
    else none
  | s => some (⟨0, 0, 0⟩, s)

private theorem speelP_sound (a0 b0 : ℕ) {s s' : SSide} {q : SN} (H : speelP s = some (q, s')) :
    exSide a0 b0 s = repTok .p2 (3 * q.eval a0 b0) (exSide a0 b0 s') := by
  cases s with
  | nil =>
    injection H with hp; injection hp with hq hs'; subst hq; subst hs'
    simp only [SN.eval, Nat.zero_mul, Nat.add_zero, Nat.mul_zero, repTok]
  | cons hd rest =>
    rcases hd with ⟨t, k⟩
    cases t
    all_goals try (
      injection H with hp; injection hp with hq hs'; subst hq; subst hs'
      simp only [SN.eval, Nat.zero_mul, Nat.add_zero, Nat.mul_zero, repTok])
    simp only [speelP] at H
    by_cases hmod : (k.ca % 3 == 0 && k.cb % 3 == 0) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hmod))] at H
      injection H with hp; injection hp with hq hs'; subst hq; subst hs'
      simp only [Bool.and_eq_true, beq_iff_eq] at hmod
      rcases hmod with ⟨hma, hmb⟩
      simp only [exSide, SN.eval]
      have hdiv : k.ca * a0 + k.cb * b0 + k.c0 =
          3 * (k.ca / 3 * a0 + k.cb / 3 * b0 + k.c0 / 3) + k.c0 % 3 := by
        have h1 : k.ca = 3 * (k.ca / 3) := by omega
        have h2 : k.cb = 3 * (k.cb / 3) := by omega
        have h3 : k.c0 = 3 * (k.c0 / 3) + k.c0 % 3 := by omega
        calc k.ca * a0 + k.cb * b0 + k.c0
            = (3 * (k.ca / 3)) * a0 + (3 * (k.cb / 3)) * b0 + (3 * (k.c0 / 3) + k.c0 % 3) := by
              rw [← h1, ← h2, ← h3]
          _ = 3 * (k.ca / 3 * a0 + k.cb / 3 * b0 + k.c0 / 3) + k.c0 % 3 := by ring
      by_cases hr : (k.c0 % 3 == 0) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hr))]
        have hr0 : k.c0 % 3 = 0 := beq_iff_eq.mp hr
        rw [hdiv, hr0, Nat.add_zero]
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hr)), exSide_spushc, hdiv, repTok_add]
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hmod))] at H; nomatch H

def speelQAux : ℕ → SN → SSide → SN × SSide
  | 0, acc, s => (acc, s)
  | f + 1, acc, s =>
    match s with
    | ⟨.q, k⟩ :: rest => speelQAux f (acc.add k) rest
    | _ =>
      match spop100110 s with
      | some s1 => speelQAux f (acc.add ⟨0, 0, 1⟩) s1
      | none => (acc, s)

def speelQ (s : SSide) : SN × SSide := speelQAux 6 ⟨0, 0, 0⟩ s

private theorem speelQAux_sound (a0 b0 : ℕ) :
    ∀ (f : ℕ) (acc : SN) (s : SSide),
    repTok .q (acc.eval a0 b0) (exSide a0 b0 s) =
      repTok .q ((speelQAux f acc s).1.eval a0 b0) (exSide a0 b0 (speelQAux f acc s).2)
  | 0, _, _ => rfl
  | f + 1, acc, s => by
    cases s with
    | nil => rfl
    | cons hd rest =>
      rcases hd with ⟨t, k⟩
      cases t with
      | q =>
        dsimp only [speelQAux]
        rw [← speelQAux_sound a0 b0 f (acc.add k) rest]
        have hadd : (acc.add k).eval a0 b0 = acc.eval a0 b0 + k.eval a0 b0 := by
          simp only [SN.add, SN.eval, Nat.add_mul]; omega
        rw [hadd, repTok_add]; rfl
      | _ =>
        dsimp only [speelQAux]
        rcases E : spop100110 (⟨_, k⟩ :: rest) with _ | s1
        · rfl
        · dsimp only
          rw [← speelQAux_sound a0 b0 f (acc.add ⟨0, 0, 1⟩) s1]
          have hp := spop100110_sound a0 b0 E
          rw [hp]
          have hadd : (acc.add ⟨0, 0, 1⟩).eval a0 b0 = acc.eval a0 b0 + 1 := by
            simp only [SN.add, SN.eval, Nat.add_zero]; omega
          rw [hadd, repTok_add]; rfl

private theorem speelQ_sound (a0 b0 : ℕ) (s : SSide) :
    exSide a0 b0 s = repTok .q ((speelQ s).1.eval a0 b0) (exSide a0 b0 (speelQ s).2) := by
  have h := speelQAux_sound a0 b0 6 ⟨0, 0, 0⟩ s
  simp only [SN.eval, Nat.zero_mul, Nat.add_zero, repTok] at h
  exact h

def peelMAux : ℕ → ℕ → SSide → ℕ × SSide
  | 0, acc, s => (acc, s)
  | f + 1, acc, s =>
    match s with
    | ⟨.m, k⟩ :: rest =>
      if k.ca == 0 && k.cb == 0 then peelMAux f (acc + k.c0) rest
      else (acc, ⟨.m, k⟩ :: rest)
    | _ =>
      match spop10110 s with
      | some s1 => peelMAux f (acc + 1) s1
      | none => (acc, s)

private theorem peelMAux_sound (a0 b0 : ℕ) :
    ∀ (f acc : ℕ) (s : SSide),
    repTok .m acc (exSide a0 b0 s) =
      repTok .m (peelMAux f acc s).1 (exSide a0 b0 (peelMAux f acc s).2)
  | 0, _, _ => rfl
  | f + 1, acc, s => by
    cases s with
    | nil => rfl
    | cons hd rest =>
      rcases hd with ⟨t, k⟩
      cases t with
      | m =>
        dsimp only [peelMAux]
        by_cases hc : (k.ca == 0 && k.cb == 0) = true
        · rw [(ite_eq_left_of_eq_true _ _ (eq_true hc))]
          rw [← peelMAux_sound a0 b0 f (acc + k.c0) rest]
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hca, hcb⟩
          simp only [exSide, SN.eval, hca, hcb, Nat.zero_mul, Nat.zero_add, repTok_add]
        · rw [(ite_eq_right_of_eq_false _ _ (eq_false hc))]
      | _ =>
        dsimp only [peelMAux]
        rcases E : spop10110 (⟨_, k⟩ :: rest) with _ | s1
        · rfl
        · dsimp only
          rw [← peelMAux_sound a0 b0 f (acc + 1) s1, spop10110_sound a0 b0 E, repTok_add]; rfl

def push000P2 : ℕ → SSide → SSide
  | 0, r => r
  | n + 1, r => spushc .b0 3 (spushc .p2 1 (push000P2 n r))

private theorem exSide_push000P2 (a0 b0 : ℕ) :
    ∀ (n : ℕ) (r : SSide),
    exSide a0 b0 (push000P2 n r) = rep000P2 n (exSide a0 b0 r)
  | 0, _ => rfl
  | n + 1, r => by
    dsimp only [push000P2, rep000P2]
    rw [exSide_spushc, exSide_spushc, exSide_push000P2 a0 b0 n r]
    rfl

def sweepRightQCase (L R : SSide) : Option (SSide × SSide) :=
  match L with
  | ⟨.q, kq⟩ :: Lrest =>
    if 1 ≤ kq.c0 then
      match spop0100001 R with
      | some R' => some (spushc .s 1 (sdec kq .q Lrest), R')
      | none =>
        match spop11 R with
        | some R11 =>
          match speelP R11 with
          | some (pm, R11p) =>
            match spop000 R11p with
            | some R' => some (spushc .m 1 (spush .q pm L), R')
            | none => none
          | none => none
        | none => none
    else none
  | _ => none

private theorem sweepRightQCase_sound (a0 b0 : ℕ) {L R L' R' : SSide}
    (H : sweepRightQCase L R = some (L', R')) :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 L') {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R')) := by
  unfold sweepRightQCase at H
  cases L with
  | nil => nomatch H
  | cons hd Lrest =>
    rcases hd with ⟨t, kq⟩
    cases t with
    | q =>
      dsimp only at H
      split_ifs at H with hge
      rcases E1 : spop0100001 R with _ | Ra
      · rw [E1] at H; dsimp only at H
        rcases E2 : spop11 R with _ | R11
        · rw [E2] at H; nomatch H
        · rw [E2] at H; dsimp only at H
          rcases E3 : speelP R11 with _ | ⟨pm, R11p⟩
          · rw [E3] at H; nomatch H
          · rw [E3] at H; dsimp only at H
            rcases E4 : spop000 R11p with _ | Rb
            · rw [E4] at H; nomatch H
            · rw [E4] at H; injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
              have hdec := exSide_sdec a0 b0 .q kq Lrest hge
              rw [hdec, spop11_sound a0 b0 E2, speelP_sound a0 b0 E3, spop000_sound a0 b0 E4]
              rw [exSide_spushc, exSide_spush, hdec]
              have hsh : repTok .q (pm.eval a0 b0) (tokStep .q (exSide a0 b0 (sdec kq .q Lrest))) =
                  repTok .q (pm.eval a0 b0 + 1) (exSide a0 b0 (sdec kq .q Lrest)) := by
                rw [repTok_shift .q]; rfl
              rw [hsh]
              exact reach_R_11Pm000 (pm.eval a0 b0) (exSide a0 b0 (sdec kq .q Lrest)) (exSide a0
                b0 Rb)
      · rw [E1] at H; injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
        rw [exSide_sdec a0 b0 .q kq Lrest hge, spop0100001_sound a0 b0 E1, exSide_spushc]
        exact reach_R_P1_000 (exSide a0 b0 (sdec kq .q Lrest)) (exSide a0 b0 Ra)
    | _ => nomatch H

def sweepRightStep (L R : SSide) : Option (SSide × SSide) :=
  match speelP R with
  | none => none
  | some (kp, R1) =>
    if !kp.isZero then
      if 1 ≤ kp.c0 then some (spush .q kp L, R1) else none
    else
      match sweepRightQCase L R with
      | some res => some res
      | none =>
        match spop000 R with
        | none => none
        | some R' =>
          let (kq, L1) := match L with
            | ⟨.q, kq⟩ :: Lr => (kq, Lr)
            | _ => (⟨0, 0, 0⟩, L)
          match L1 with
          | ⟨.s, ks⟩ :: Lrest =>
            if 1 ≤ ks.c0 then
              some (spushc .m 1 (spush .q (kq.add ⟨0, 0, 1⟩) (spushc .m 1 (sdec ks .s Lrest))), R')
            else none
          | _ => none

private theorem sweepRightStep_sound (a0 b0 : ℕ) {L R L' R' : SSide}
    (H : sweepRightStep L R = some (L', R')) :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 L') {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R')) := by
  unfold sweepRightStep at H
  rcases EP : speelP R with _ | ⟨kp, R1⟩
  · rw [EP] at H; nomatch H
  · rw [EP] at H; dsimp only at H
    by_cases hnz : (!kp.isZero) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hnz))] at H
      split_ifs at H with hge
      injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
      rw [speelP_sound a0 b0 EP, exSide_spush]
      have hpos : 1 ≤ kp.eval a0 b0 := by simp only [SN.eval]; omega
      exact reach_peelP_pos (kp.eval a0 b0) hpos (exSide a0 b0 L) (exSide a0 b0 R1)
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hnz))] at H
      rcases hq_case : sweepRightQCase L R with _ | ⟨Lq, Rq⟩
      · rw [hq_case] at H; dsimp only at H
        rcases E0 : spop000 R with _ | Ra
        · rw [E0] at H; nomatch H
        · rw [E0] at H; dsimp only at H
          have hR0 := spop000_sound a0 b0 E0
          cases L with
          | nil => nomatch H
          | cons hd Lr =>
            rcases hd with ⟨t, kt⟩
            cases t with
            | q =>
              dsimp only at H
              cases Lr with
              | nil => nomatch H
              | cons hd2 Lrest =>
                rcases hd2 with ⟨t2, ks⟩
                cases t2 with
                | s =>
                  dsimp only at H
                  split_ifs at H with hge
                  injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
                  have hdec := exSide_sdec a0 b0 .s ks Lrest hge
                  simp only [exSide] at hdec ⊢
                  rw [hdec, hR0, exSide_spushc, exSide_spush, exSide_spushc]
                  have hev : (kt.add ⟨0, 0, 1⟩).eval a0 b0 = kt.eval a0 b0 + 1 := by
                    simp only [SN.add, SN.eval, Nat.add_zero]; omega
                  rw [hev]
                  exact reach_R_000S (kt.eval a0 b0) (exSide a0 b0 (sdec ks .s Lrest)) (exSide a0
                    b0 Ra)
                | _ => nomatch H
            | s =>
              dsimp only at H
              split_ifs at H with hge
              injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
              have hdec := exSide_sdec a0 b0 .s kt Lr hge
              rw [hdec, hR0, exSide_spushc, exSide_spush, exSide_spushc]
              have h0 := reach_R_000S 0 (exSide a0 b0 (sdec kt .s Lr)) (exSide a0 b0 Ra)
              simpa only [SN.add, SN.eval, Nat.zero_mul, Nat.add_zero, repTok] using h0
            | _ => nomatch H
      · rw [hq_case] at H; injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
        exact sweepRightQCase_sound a0 b0 hq_case

def sweepRightLoop : ℕ → SSide → SSide → SSide × SSide
  | 0, L, R => (L, R)
  | f + 1, L, R =>
    match sweepRightStep L R with
    | some (L1, R1) => sweepRightLoop f L1 R1
    | none => (L, R)

private theorem sweepRightLoop_sound (a0 b0 : ℕ) :
    ∀ (f : ℕ) (L R : SSide),
    ReachesStar target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 (sweepRightLoop f L R).1) {{sB}}> ((0 : Fin 2) >> exSide a0 b0
        (sweepRightLoop f L R).2))
  | 0, _, _ => reachesStar_refl _
  | f + 1, L, R => by
    dsimp only [sweepRightLoop]
    rcases E : sweepRightStep L R with _ | ⟨L1, R1⟩
    · exact reachesStar_refl _
    · exact (reachesPlus_trans_star (sweepRightStep_sound a0 b0 E) (sweepRightLoop_sound a0 b0 f
      L1 R1)).to_star

def sweepRightB0 (L R : SSide) : Option (SSide × SSide) :=
  match sweepRightStep L R with
  | none => none
  | some (L1, R1) => some (sweepRightLoop 27 L1 R1)

private theorem sweepRightB0_sound (a0 b0 : ℕ) {L R L' R' : SSide}
    (H : sweepRightB0 L R = some (L', R')) :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 L') {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R')) := by
  unfold sweepRightB0 at H
  rcases E : sweepRightStep L R with _ | ⟨L1, R1⟩
  · rw [E] at H; nomatch H
  · rw [E] at H; injection H with hp
    have hL' : (sweepRightLoop 27 L1 R1).1 = L' := congrArg Prod.fst hp
    have hR' : (sweepRightLoop 27 L1 R1).2 = R' := congrArg Prod.snd hp
    rw [← hL', ← hR']
    exact reachesPlus_trans_star (sweepRightStep_sound a0 b0 E) (sweepRightLoop_sound a0 b0 27 L1
      R1)

def sweepRightB0Opt (L R : SSide) : SSide × SSide := sweepRightLoop 28 L R

private theorem sweepRightB0Opt_sound (a0 b0 : ℕ) (L R : SSide) :
    ReachesStar target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 (sweepRightB0Opt L R).1) {{sB}}> ((0 : Fin 2) >> exSide a0 b0
        (sweepRightB0Opt L R).2)) :=
  sweepRightLoop_sound a0 b0 28 L R

def sweepLeftStep (L R : SSide) : Option (SSide × SSide) :=
  let (kq, L1) := speelQ L
  if !kq.isZero then
    if 1 ≤ kq.c0 then some (L1, spush .p2 kq.mul3 R) else none
  else
    let (km, Lm) := peelMAux 8 0 L
    if 1 ≤ km then
      let qRes : Option SSide :=
        match Lm with
        | ⟨.q, k⟩ :: Lr => if 1 ≤ k.c0 then some (sdec k .q Lr) else none
        | _ => spop100110 Lm
      match qRes with
      | some L' =>
        let R' := spushc .p2 2 (push000P2 (km - 1) (spushc .b0 3 (spushc .p2 2 R)))
        some (L', R')
      | none => none
    else none

private theorem sweepLeftStep_sound (a0 b0 : ℕ) {L R L' R' : SSide}
    (H : sweepLeftStep L R = some (L', R')) :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 L') {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 R'))
        := by
  unfold sweepLeftStep at H
  have hQ := speelQ_sound a0 b0 L
  rcases EQ : speelQ L with ⟨kq, L1⟩
  rw [EQ] at hQ H; dsimp only at hQ H
  by_cases hnz : (!kq.isZero) = true
  · rw [(ite_eq_left_of_eq_true _ _ (eq_true hnz))] at H
    split_ifs at H with hge
    injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
    rw [hQ, exSide_spush]
    have hmul : kq.mul3.eval a0 b0 = 3 * kq.eval a0 b0 := by
      simp only [SN.mul3, SN.eval]; ring
    rw [hmul]
    have hpos : 1 ≤ kq.eval a0 b0 := by simp only [SN.eval]; omega
    exact reach_peelQ_pos (kq.eval a0 b0) hpos (exSide a0 b0 L1) (exSide a0 b0 R)
  · rw [(ite_eq_right_of_eq_false _ _ (eq_false hnz))] at H
    have hM := peelMAux_sound a0 b0 8 0 L
    rcases EM : peelMAux 8 0 L with ⟨km, Lm⟩
    rw [EM] at hM H; dsimp only [repTok] at hM; dsimp only at H
    split_ifs at H with hkm
    have hq_ex : ∃ Lq, exSide a0 b0 Lm = tokStep .q (exSide a0 b0 Lq) ∧
        L' = Lq ∧ R' = spushc .p2 2 (push000P2 (km - 1) (spushc .b0 3 (spushc .p2 2 R))) := by
      cases Lm with
      | nil =>
        try dsimp only at H
        rcases hq : spop100110 [] with _ | Lq <;> rw [hq] at H
        · nomatch H
        · injection H with hp; injection hp with h1 h2
          exact ⟨Lq, spop100110_sound a0 b0 hq, h1.symm, h2.symm⟩
      | cons hd Lr =>
        rcases hd with ⟨t, k⟩
        cases t with
        | q =>
          try dsimp only at H
          split_ifs at H with hk1
          injection H with hp; injection hp with h1 h2
          exact ⟨sdec k .q Lr, exSide_sdec a0 b0 .q k Lr hk1, h1.symm, h2.symm⟩
        | _ =>
          try dsimp only at H
          rcases hq : spop100110 (_ :: Lr) with _ | Lq <;> rw [hq] at H
          · nomatch H
          · injection H with hp; injection hp with h1 h2
            exact ⟨Lq, spop100110_sound a0 b0 hq, h1.symm, h2.symm⟩
    rcases hq_ex with ⟨Lq, hLm, rfl, rfl⟩
    rw [hM, hLm]
    have hkmEq : km = (km - 1) + 1 := by omega
    rw [hkmEq, exSide_spushc, exSide_push000P2, exSide_spushc, exSide_spushc]
    exact reach_L_MkQ (km - 1) (exSide a0 b0 L') (exSide a0 b0 R)

def sweepLeftLoop : ℕ → SSide → SSide → SSide × SSide
  | 0, L, R => (L, R)
  | f + 1, L, R =>
    match sweepLeftStep L R with
    | some (L1, R1) => sweepLeftLoop f L1 R1
    | none => (L, R)

private theorem sweepLeftLoop_sound (a0 b0 : ℕ) :
    ∀ (f : ℕ) (L R : SSide),
    ReachesStar target_tm
      ((exSide a0 b0 L) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 (sweepLeftLoop f L R).1) {{sA}}> ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2)
        >> exSide a0 b0 (sweepLeftLoop f L R).2))
  | 0, _, _ => reachesStar_refl _
  | f + 1, L, R => by
    dsimp only [sweepLeftLoop]
    rcases E : sweepLeftStep L R with _ | ⟨L1, R1⟩
    · exact reachesStar_refl _
    · exact (reachesPlus_trans_star (sweepLeftStep_sound a0 b0 E) (sweepLeftLoop_sound a0 b0 f L1
      R1)).to_star

def sweepLeftA1 (L R : SSide) : Option (SSide × SSide) :=
  match spop10 R with
  | none => none
  | some R0 =>
    match sweepLeftStep L R0 with
    | none => none
    | some (L1, R1) =>
      let (L2, R2) := sweepLeftLoop 23 L1 R1
      some (L2, spushc .b1 1 (spushc .b0 1 R2))

private theorem sweepLeftA1_sound (a0 b0 : ℕ) {L R L' R' : SSide}
    (H : sweepLeftA1 L R = some (L', R')) :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sA}}> ((1 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 L') {{sA}}> ((1 : Fin 2) >> exSide a0 b0 R')) := by
  unfold sweepLeftA1 at H
  rcases E10 : spop10 R with _ | R0
  · rw [E10] at H; nomatch H
  · rw [E10] at H; dsimp only at H
    rcases ES : sweepLeftStep L R0 with _ | ⟨L1, R1⟩
    · rw [ES] at H; nomatch H
    · rw [ES] at H; dsimp only at H
      injection H with hp; injection hp with hL' hR'; subst hL'; subst hR'
      rw [spop10_sound a0 b0 E10, exSide_spushc, exSide_spushc]
      exact reachesPlus_trans_star (sweepLeftStep_sound a0 b0 ES) (sweepLeftLoop_sound a0 b0 23 L1
        R1)

def sweepLeftA1Opt (L R : SSide) : SSide × SSide :=
  match sweepLeftA1 L R with
  | some res => res
  | none => (L, R)

private theorem sweepLeftA1Opt_sound (a0 b0 : ℕ) (L R : SSide) :
    ReachesStar target_tm
      ((exSide a0 b0 L) {{sA}}> ((1 : Fin 2) >> exSide a0 b0 R))
      ((exSide a0 b0 (sweepLeftA1Opt L R).1) {{sA}}> ((1 : Fin 2) >> exSide a0 b0 (sweepLeftA1Opt
        L R).2)) := by
  unfold sweepLeftA1Opt
  rcases E : sweepLeftA1 L R with _ | ⟨L1, R1⟩
  · exact reachesStar_refl _
  · exact (sweepLeftA1_sound a0 b0 E).to_star

/-! ### Top-Level `superStep` & Unconditional Soundness -/

def superStepB0Wall (L R : SSide) : Option SState :=
  match L with
  | [] =>
    match spop00 R with
    | some R1 =>
      let (L2, R2) := sweepRightB0Opt (spushc .b1 1 []) (spushc .p2 1 R1)
      some ⟨true, false, L2, R2⟩
    | none => none
  | _ => none

def superStepB0M (L R : SSide) : Option SState :=
  match L with
  | ⟨.m, km⟩ :: Lr =>
    if 1 ≤ km.c0 then
      match spop010000 R with
      | some R1 =>
        let R2 := spushc .b1 1 (spushc .b0 1 (spushc .p2 4 (spushc .b1 1 R1)))
        let (L3, R3) := sweepLeftA1Opt (sdec km .m Lr) R2
        some ⟨false, true, L3, R3⟩
      | none => none
    else none
  | _ => none

def superStepB0P2 (L R : SSide) : Option SState :=
  match L with
  | ⟨.q, kq⟩ :: Lr =>
    if 1 ≤ kq.c0 then
      match spop010100001 R with
      | some R1 =>
        let R2 := spushc .b1 1 (spushc .b0 1 (spushc .p2 2 (spushc .b0 3 (spushc .p2 3 R1))))
        let (L3, R3) := sweepLeftA1Opt (sdec kq .q Lr) R2
        some ⟨false, true, L3, R3⟩
      | none => none
    else none
  | _ => none

def superStepB0 (L R : SSide) : Option SState :=
  match superStepB0Wall L R with
  | some st => some st
  | none =>
    match sweepRightB0 L R with
    | some (L1, R1) => some ⟨true, false, L1, R1⟩
    | none =>
      match superStepB0M L R with
      | some st => some st
      | none =>
        match superStepB0P2 L R with
        | some st => some st
        | none =>
          match spop01010 R with
          | some R1 =>
            let (L2, R2) := sweepRightB0Opt (spushc .m 1 L) R1
            some ⟨true, false, L2, R2⟩
          | none =>
            match spopBit R with
            | none => none
            | some (false, R1) =>
              let (L2, R2) := sweepLeftA1Opt L (spushc .b1 1 R1)
              some ⟨false, true, L2, R2⟩
            | some (true, R1) =>
              some ⟨true, true, L, spushc .b0 1 R1⟩

def superStepB1 (L R : SSide) : Option SState :=
  match spopBit L with
  | none => none
  | some (true, L1) =>
    match spopBit R with
    | none => none
    | some (r1, R1) => some ⟨true, r1, spushc .b1 1 (spushc .b0 1 L1), R1⟩
  | some (false, L1) =>
    match spopBit L1 with
    | none => none
    | some (l2, L2) =>
      match spopBit L2 with
      | none => none
      | some (l3, L3) =>
        if !l2 then
          if !l3 then some ⟨true, true, spushc .b1 1 L3, spushc .b0 2 R⟩
          else some ⟨false, true, L3, spushc .b1 1 (spushc .b0 2 R)⟩
        else some ⟨true, l3, L3, spushc .b0 3 R⟩

def superStepA1Bounce (L R : SSide) : Option SState :=
  match spop10 R with
  | none => none
  | some R0 =>
    match L with
    | [⟨.b1, ⟨0, 0, 1⟩⟩] =>
      some ⟨true, false, [], spushc .b0 2 (spushc .p2 1 R0)⟩
    | ⟨.s, ks⟩ :: Lr =>
      if 1 ≤ ks.c0 then
        let (L2,
          R2) := sweepRightB0Opt (spushc .q 1 (spushc .m 1 (sdec ks .s Lr))) (spushc .p2 2 R0)
        some ⟨true, false, L2, R2⟩
      else none
    | ⟨.m, km⟩ :: Lr =>
      if 1 ≤ km.c0 then
        match sdec km .m Lr with
        | ⟨.s, ks⟩ :: Lr2 =>
          if 1 ≤ ks.c0 then
            let (L2,
              R2) := sweepRightB0Opt (spushc .s 1 (spushc .m 1 (sdec ks .s Lr2))) (spushc .p2 1 R0)
            some ⟨true, false, L2, R2⟩
          else none
        | _ => none
      else none
    | _ => none

def superStepA1 (L R : SSide) : Option SState :=
  match sweepLeftA1 L R with
  | some (L1, R1) => some ⟨false, true, L1, R1⟩
  | none =>
    match superStepA1Bounce L R with
    | some st => some st
    | none =>
      match spop1 R with
      | none => none
      | some R1 =>
        match spopBit R1 with
        | none => none
        | some (false, R2) => some ⟨true, true, spushc .b0 1 L, spushc .b1 1 R2⟩
        | some (true, R2) =>
          match spopBit R2 with
          | none => none
          | some (false, R3) =>
            match spopBit R3 with
            | none => none
            | some (r4, R4) => some ⟨true, r4, spushc .b1 1 (spushc .u 1 L), R4⟩
          | some (true, R3) => some ⟨false, true, spushc .u 1 L, R3⟩

def superStep (st : SState) : Option SState :=
  match st.isB, st.h with
  | true, false => superStepB0 st.L st.R
  | true, true => superStepB1 st.L st.R
  | false, false =>
    match spopBit st.R with
    | none => none
    | some (r1, R1) => some ⟨true, r1, spushc .b1 1 st.L, R1⟩
  | false, true => superStepA1 st.L st.R

private theorem superStepB0Wall_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepB0Wall L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepB0Wall at H
  cases L with
  | cons _ _ => nomatch H
  | nil =>
    dsimp only at H
    rcases E00 : spop00 R with _ | R1
    · rw [E00] at H; nomatch H
    · rw [E00] at H; injection H with hst; subst hst
      dsimp only [evalSym, exSide, boolToFin2]
      rw [spop00_sound a0 b0 E00]
      have hw := reach_wall00 (exSide a0 b0 R1)
      have hs := sweepRightB0Opt_sound a0 b0 (spushc .b1 1 []) (spushc .p2 1 R1)
      rw [exSide_spushc, exSide_spushc] at hs
      exact reachesPlus_trans_star hw hs

private theorem superStepB0M_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepB0M L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepB0M at H
  cases L with
  | nil => nomatch H
  | cons hd Lr =>
    rcases hd with ⟨t, km⟩
    cases t with
    | m =>
      dsimp only at H
      split_ifs at H with hk
      rcases E6 : spop010000 R with _ | R1
      · rw [E6] at H; nomatch H
      · rw [E6] at H; injection H with hst; subst hst
        dsimp only [evalSym, boolToFin2]
        rw [exSide_sdec a0 b0 .m km Lr hk, spop010000_sound a0 b0 E6]
        have h1 := reach_R_M_010000 (exSide a0 b0 (sdec km .m Lr)) (exSide a0 b0 R1)
        have h2 :=
          sweepLeftA1Opt_sound a0 b0 (sdec km .m Lr) (spushc .b1 1 (spushc .b0 1 (spushc .p2 4
          (spushc .b1 1 R1))))
        rw [exSide_spushc, exSide_spushc, exSide_spushc, exSide_spushc] at h2
        exact reachesPlus_trans_star h1 h2
    | _ => nomatch H

private theorem superStepB0P2_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepB0P2 L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepB0P2 at H
  cases L with
  | nil => nomatch H
  | cons hd Lr =>
    rcases hd with ⟨t, kq⟩
    cases t with
    | q =>
      dsimp only at H
      split_ifs at H with hk
      rcases E9 : spop010100001 R with _ | R1
      · rw [E9] at H; nomatch H
      · rw [E9] at H; injection H with hst; subst hst
        dsimp only [evalSym, boolToFin2]
        rw [exSide_sdec a0 b0 .q kq Lr hk, spop010100001_sound a0 b0 E9]
        have h1 := reach_R_P2_000 (exSide a0 b0 (sdec kq .q Lr)) (exSide a0 b0 R1)
        have h2 :=
          sweepLeftA1Opt_sound a0 b0 (sdec kq .q Lr) (spushc .b1 1 (spushc .b0 1 (spushc .p2 2
          (spushc .b0 3 (spushc .p2 3 R1)))))
        rw [exSide_spushc, exSide_spushc, exSide_spushc, exSide_spushc, exSide_spushc] at h2
        exact reachesPlus_trans_star h1 h2
    | _ => nomatch H

private theorem superStepB0_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepB0 L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((0 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepB0 at H
  rcases hW : superStepB0Wall L R with _ | st0
  · rw [hW] at H; dsimp only at H
    rcases ESW : sweepRightB0 L R with _ | ⟨L1, R1⟩
    · rw [ESW] at H; dsimp only at H
      rcases hM : superStepB0M L R with _ | st0
      · rw [hM] at H; dsimp only at H
        rcases hP2 : superStepB0P2 L R with _ | st0
        · rw [hP2] at H; dsimp only at H
          rcases E5 : spop01010 R with _ | R1
          · rw [E5] at H; dsimp only at H
            rcases EB : spopBit R with _ | ⟨r1, R1⟩
            · rw [EB] at H; nomatch H
            · rw [EB] at H; cases r1 with
              | false =>
                injection H with hst; subst hst
                dsimp only [evalSym, boolToFin2]
                rw [spopBit_sound a0 b0 EB]
                have h1 := reach_B0_0 (exSide a0 b0 L) (exSide a0 b0 R1)
                have h2 := sweepLeftA1Opt_sound a0 b0 L (spushc .b1 1 R1)
                rw [exSide_spushc] at h2
                exact reachesPlus_trans_star h1 h2
              | true =>
                injection H with hst; subst hst
                dsimp only [evalSym, boolToFin2]
                rw [spopBit_sound a0 b0 EB, exSide_spushc]
                exact reach_B0_1 (exSide a0 b0 L) (exSide a0 b0 R1)
          · rw [E5] at H; injection H with hst; subst hst
            dsimp only [evalSym, boolToFin2]
            rw [spop01010_sound a0 b0 E5]
            have h1 := reach_R_01010 (exSide a0 b0 L) (exSide a0 b0 R1)
            have h2 := sweepRightB0Opt_sound a0 b0 (spushc .m 1 L) R1
            rw [exSide_spushc] at h2
            exact reachesPlus_trans_star h1 h2
        · rw [hP2] at H; injection H with hst; subst hst
          exact superStepB0P2_sound a0 b0 hP2
      · rw [hM] at H; injection H with hst; subst hst
        exact superStepB0M_sound a0 b0 hM
    · rw [ESW] at H; injection H with hst; subst hst
      exact sweepRightB0_sound a0 b0 ESW
  · rw [hW] at H; injection H with hst; subst hst
    exact superStepB0Wall_sound a0 b0 hW

private theorem superStepB1_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepB1 L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sB}}> ((1 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepB1 at H
  rcases E1 : spopBit L with _ | ⟨l1, L1⟩
  · rw [E1] at H; nomatch H
  · rw [E1] at H; cases l1 with
    | true =>
      dsimp only at H
      rcases ER : spopBit R with _ | ⟨r1, R1⟩
      · rw [ER] at H; nomatch H
      · rw [ER] at H; injection H with hst; subst hst
        dsimp only [evalSym]
        rw [spopBit_sound a0 b0 E1, spopBit_sound a0 b0 ER, exSide_spushc, exSide_spushc]
        have h1 := reach_B1_1 (exSide a0 b0 L1) (boolToFin2 r1 >> exSide a0 b0 R1)
        have h2 := reach_A0 (boolToFin2 r1) ((0 : Fin 2) >> exSide a0 b0 L1) (exSide a0 b0 R1)
        exact reachesPlus_trans h1 h2
    | false =>
      dsimp only at H
      rcases E2 : spopBit L1 with _ | ⟨l2, L2⟩
      · rw [E2] at H; nomatch H
      · rw [E2] at H; dsimp only at H
        rcases E3 : spopBit L2 with _ | ⟨l3, L3⟩
        · rw [E3] at H; nomatch H
        · rw [E3] at H; dsimp only at H
          cases l2 with
          | false =>
            cases l3 with
            | false =>
              injection H with hst; subst hst
              dsimp only [evalSym, boolToFin2]
              rw [spopBit_sound a0 b0 E1, spopBit_sound a0 b0 E2, spopBit_sound a0 b0 E3,
                exSide_spushc, exSide_spushc]
              have h1 := reach_B1_00 0 (exSide a0 b0 L3) (exSide a0 b0 R)
              have h2 := reach_A0 1 (exSide a0 b0 L3) ((0 : Fin 2) >> (0 : Fin 2) >> exSide a0 b0 R)
              exact reachesPlus_trans h1 h2
            | true =>
              injection H with hst; subst hst
              dsimp only [evalSym, boolToFin2]
              rw [spopBit_sound a0 b0 E1, spopBit_sound a0 b0 E2, spopBit_sound a0 b0 E3,
                exSide_spushc, exSide_spushc]
              exact reach_B1_00 1 (exSide a0 b0 L3) (exSide a0 b0 R)
          | true =>
            injection H with hst; subst hst
            dsimp only [evalSym]
            rw [spopBit_sound a0 b0 E1, spopBit_sound a0 b0 E2, spopBit_sound a0 b0 E3,
              exSide_spushc]
            exact reach_B1_01 (boolToFin2 l3) (exSide a0 b0 L3) (exSide a0 b0 R)

private theorem superStepA1Bounce_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepA1Bounce L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sA}}> ((1 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepA1Bounce at H
  rcases E10 : spop10 R with _ | R0
  · rw [E10] at H; nomatch H
  · rw [E10] at H; dsimp only at H
    cases L with
    | nil => nomatch H
    | cons hd Lr =>
      rcases hd with ⟨t, k⟩
      cases t with
      | b1 =>
        rcases k with ⟨ca, cb, c0⟩
        cases ca with
        | succ _ => nomatch H
        | zero =>
          cases cb with
          | succ _ => nomatch H
          | zero =>
            cases c0 with
            | zero => nomatch H
            | succ c0' =>
              cases c0' with
              | succ _ => nomatch H
              | zero =>
                cases Lr with
                | cons _ _ => nomatch H
                | nil =>
                  injection H with hst; subst hst
                  rw [spop10_sound a0 b0 E10]
                  dsimp only [evalSym, boolToFin2]
                  rw [exSide_spushc, exSide_spushc]
                  simp only [exSide, SN.eval, Nat.zero_mul, Nat.zero_add, ↓reduceIte, repTok,
                    tokStep]
                  exact reach_L_wall1 (exSide a0 b0 R0)
      | m =>
        dsimp only at H
        split_ifs at H with hkm
        rcases ESD : sdec k .m Lr with _ | ⟨hd2, Lr2⟩
        · rw [ESD] at H; nomatch H
        · rw [ESD] at H; rcases hd2 with ⟨t2, ks⟩
          cases t2 with
          | s =>
            dsimp only at H
            split_ifs at H with hks
            injection H with hst; subst hst
            dsimp only [evalSym, boolToFin2]
            rw [exSide_sdec a0 b0 .m k Lr hkm, ESD, exSide_sdec a0 b0 .s ks Lr2 hks,
              spop10_sound a0 b0 E10]
            have h1 := reach_L_MS (exSide a0 b0 (sdec ks .s Lr2)) (exSide a0 b0 R0)
            have h2 :=
              sweepRightB0Opt_sound a0 b0 (spushc .s 1 (spushc .m 1 (sdec ks .s Lr2))) (spushc .p2
              1 R0)
            rw [exSide_spushc, exSide_spushc, exSide_spushc] at h2
            exact reachesPlus_trans_star h1 h2
          | _ => nomatch H
      | s =>
        dsimp only at H
        split_ifs at H with hks
        injection H with hst; subst hst
        dsimp only [evalSym, boolToFin2]
        rw [exSide_sdec a0 b0 .s k Lr hks, spop10_sound a0 b0 E10]
        have h1 := reach_L_S (exSide a0 b0 (sdec k .s Lr)) (exSide a0 b0 R0)
        have h2 :=
          sweepRightB0Opt_sound a0 b0 (spushc .q 1 (spushc .m 1 (sdec k .s Lr))) (spushc .p2 2 R0)
        rw [exSide_spushc, exSide_spushc, exSide_spushc] at h2
        exact reachesPlus_trans_star h1 h2
      | _ => nomatch H

private theorem superStepA1_sound (a0 b0 : ℕ) {L R : SSide} {st' : SState}
    (H : superStepA1 L R = some st') :
    ReachesPlus target_tm
      ((exSide a0 b0 L) {{sA}}> ((1 : Fin 2) >> exSide a0 b0 R))
      (evalSym a0 b0 st') := by
  unfold superStepA1 at H
  rcases ESW : sweepLeftA1 L R with _ | ⟨L1, R1⟩
  · rw [ESW] at H; dsimp only at H
    rcases hB : superStepA1Bounce L R with _ | st0
    · rw [hB] at H; dsimp only at H
      rcases E1 : spop1 R with _ | R1
      · rw [E1] at H; nomatch H
      · rw [E1] at H; dsimp only at H
        rcases E2 : spopBit R1 with _ | ⟨r2, R2⟩
        · rw [E2] at H; nomatch H
        · rw [E2] at H; cases r2 with
          | false =>
            injection H with hst; subst hst
            dsimp only [evalSym, boolToFin2]
            rw [spop1_sound a0 b0 E1, spopBit_sound a0 b0 E2, exSide_spushc, exSide_spushc]
            exact reach_A1_10 (exSide a0 b0 L) (exSide a0 b0 R2)
          | true =>
            dsimp only at H
            rcases E3 : spopBit R2 with _ | ⟨r3, R3⟩
            · rw [E3] at H; nomatch H
            · rw [E3] at H; cases r3 with
              | false =>
                dsimp only at H
                rcases E4 : spopBit R3 with _ | ⟨r4, R4⟩
                · rw [E4] at H; nomatch H
                · rw [E4] at H; injection H with hst; subst hst
                  dsimp only [evalSym]
                  rw [spop1_sound a0 b0 E1, spopBit_sound a0 b0 E2, spopBit_sound a0 b0 E3,
                      spopBit_sound a0 b0 E4, exSide_spushc, exSide_spushc]
                  have h1 := reach_A1_11 0 (exSide a0 b0 L) (boolToFin2 r4 >> exSide a0 b0 R4)
                  have h2 :=
                    reach_A0 (boolToFin2 r4) (tokStep .u (exSide a0 b0 L)) (exSide a0 b0 R4)
                  exact reachesPlus_trans h1 h2
              | true =>
                injection H with hst; subst hst
                dsimp only [evalSym, boolToFin2]
                rw [spop1_sound a0 b0 E1, spopBit_sound a0 b0 E2, spopBit_sound a0 b0 E3,
                  exSide_spushc]
                exact reach_A1_11 1 (exSide a0 b0 L) (exSide a0 b0 R3)
    · rw [hB] at H; injection H with hst; subst hst
      exact superStepA1Bounce_sound a0 b0 hB
  · rw [ESW] at H; injection H with hst; subst hst
    exact sweepLeftA1_sound a0 b0 ESW

private theorem superStep_sound (a0 b0 : ℕ) {st st' : SState} (H : superStep st = some st') :
    ReachesPlus target_tm (evalSym a0 b0 st) (evalSym a0 b0 st') := by
  rcases st with ⟨isB, h, L, R⟩
  cases isB <;> cases h
  · dsimp only [superStep] at H
    rcases E : spopBit R with _ | ⟨r1, R1⟩
    · rw [E] at H; nomatch H
    · rw [E] at H; injection H with hst; subst hst
      dsimp only [evalSym, boolToFin2]
      rw [spopBit_sound a0 b0 E, exSide_spushc]
      exact reach_A0 (boolToFin2 r1) (exSide a0 b0 L) (exSide a0 b0 R1)
  · exact superStepA1_sound a0 b0 H
  · exact superStepB0_sound a0 b0 H
  · exact superStepB1_sound a0 b0 H

/-! ### Binary-Doubling Execution & Range Checker -/

def symRunPow : ℕ → (SState → Option SState) → ℕ → SState → Option SState
  | 0, _, _, s => some s
  | k + 1, f, n, s =>
    if n == 0 then some s
    else
      let s1 := if n % 2 == 1 then f s else some s
      match s1 with
      | none => none
      | some sm => symRunPow k (fun x => (f x).bind f) (n / 2) sm

private theorem symRunPow_sound (a0 b0 : ℕ) :
    ∀ (k : ℕ) (f : SState → Option SState),
    (∀ s s', f s = some s' → ReachesStar target_tm (evalSym a0 b0 s) (evalSym a0 b0 s')) →
    ∀ (n : ℕ) (s s' : SState),
    symRunPow k f n s = some s' → ReachesStar target_tm (evalSym a0 b0 s) (evalSym a0 b0 s')
  | 0, _, _, _, s, s', H => by
    injection H with hs; subst hs; exact reachesStar_refl _
  | k + 1, f, hf, n, s, s', H => by
    dsimp only [symRunPow] at H
    by_cases hn : (n == 0) = true
    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hn))] at H
      injection H with hs
      subst hs
      exact reachesStar_refl _
    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hn))] at H
      have hf2 : ∀ x y,
        ((f x).bind f) = some y → ReachesStar target_tm (evalSym a0 b0 x) (evalSym a0 b0 y) := by
        intro x y hxy
        obtain ⟨m, h1, h2⟩ := bind_some_elim hxy
        exact reachesStar_trans (hf x m h1) (hf m y h2)
      by_cases hp : (n % 2 == 1) = true
      · rw [(ite_eq_left_of_eq_true _ _ (eq_true hp))] at H
        rcases E1 : f s with _ | sm
        · rw [E1] at H; nomatch H
        · rw [E1] at H
          exact reachesStar_trans (hf s sm E1) (symRunPow_sound a0 b0 k _ hf2 (n / 2) sm s' H)
      · rw [(ite_eq_right_of_eq_false _ _ (eq_false hp))] at H
        exact symRunPow_sound a0 b0 k _ hf2 (n / 2) s s' H

def symRunPos (n : ℕ) (s : SState) : Option SState :=
  (superStep s).bind (symRunPow 14 superStep n)

theorem symRunPos_sound (a0 b0 : ℕ) {n : ℕ} {s s' : SState}
    (H : symRunPos n s = some s') :
    ReachesPlus target_tm (evalSym a0 b0 s) (evalSym a0 b0 s') := by
  obtain ⟨s1, h1, h2⟩ := bind_some_elim H
  have hp1 := superStep_sound a0 b0 h1
  have hs2 :=
    symRunPow_sound a0 b0 14 superStep (fun x y hxy => (superStep_sound a0 b0 hxy).to_star) n s1
    s' h2
  exact reachesPlus_trans_star hp1 hs2

def checkRange (P : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 => P lo && checkRange P (lo + 1) n

private theorem checkRange_spec (P : ℕ → Bool) :
    ∀ (n lo i : ℕ), checkRange P lo n = true → lo ≤ i → i < lo + n → P i = true
  | 0, _, _, _, hlo, hhi => by omega
  | n + 1, lo, i, H, hlo, hhi => by
    dsimp only [checkRange] at H
    rw [Bool.and_eq_true] at H
    by_cases heq : i = lo
    · subst heq; exact H.1
    · exact checkRange_spec P n (lo + 1) i H.2 (by omega) (by omega)

/-! ### 98-Checkpoint Attractor Table & Concrete/Symbolic Closure -/

def cpTail : Nat → List (Tok × Nat)
  | 0 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 12), (.b1, 2), (.b0,
    3), (.p2, 2)]
  | 1 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 13), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 2)]
  | 2 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 10), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 3 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    12), (.b1, 2), (.p2, 1)]
  | 4 => [(.b1, 2), (.p2, 12), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 12), (.b1, 2), (.p2, 1)]
  | 5 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 6 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 9), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 7 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 8 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 24), (.b1, 2), (.p2, 6), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 9 => [(.b1, 2), (.p2, 23), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0,
    3), (.p2, 2)]
  | 10 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 11 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    18), (.b1, 2), (.p2, 1)]
  | 12 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 15), (.b1, 2), (.p2, 17), (.b1, 2), (.p2,
    1)]
  | 13 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 28), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 14 => [(.b1, 2), (.p2, 27), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2,
    2)]
  | 15 => [(.p2, 1), (.b0, 3), (.p2, 21), (.b1, 2), (.p2, 3), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 16 => [(.p2, 1), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 17 => [(.p2, 1), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 12), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 18 => [(.p2, 1), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 19 => [(.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 20 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 18), (.b1, 2), (.p2, 9), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 21 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 13), (.b0, 3),
    (.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3),
    (.p2, 2)]
  | 22 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 10), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 1), (.b0, 3),
    (.p2, 2)]
  | 23 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 28), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    12), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 24 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 31), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    13), (.b0, 3), (.p2, 15), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | 25 => [(.b1, 2), (.p2, 30), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 15),
    (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | 26 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 19), (.b0, 3), (.p2,
    13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 27 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 16), (.b0, 3), (.p2,
    21), (.b1, 2), (.p2, 1)]
  | 28 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 13), (.b0, 3), (.p2,
    22), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 29 => [(.b1, 2), (.p2, 15), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 6),
    (.b1, 2), (.b0, 3), (.p2, 2)]
  | 30 => [(.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 10), (.b0, 3),
    (.p2, 1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 31 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 12), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 32 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 33 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 28), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 34 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 36), (.b1, 2), (.p2, 9), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 35 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 40), (.b0, 3), (.p2, 13), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 36 => [(.b1, 2), (.p2, 39), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 4), (.b0,
    3), (.p2, 4), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 37 => [(.p2, 1), (.b0, 3), (.p2, 33), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | 38 => [(.p2, 1), (.b0, 3), (.p2, 40), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 39 => [(.p2, 1), (.b0, 3), (.p2, 37), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    2)]
  | 40 => [(.p2, 1), (.b0, 3), (.p2, 34), (.b0, 3), (.p2, 12), (.b1, 2), (.p2, 1)]
  | 41 => [(.p2, 1), (.b0, 3), (.p2, 31), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 6), (.b1, 2), (.b0,
    3), (.p2, 2)]
  | 42 => [(.p2, 1), (.b0, 3), (.p2, 28), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 2)]
  | 43 => [(.p2, 1), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 44 => [(.p2, 1), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    12), (.b1, 2), (.p2, 1)]
  | 45 => [(.p2, 1), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 30), (.b1, 2), (.p2, 11), (.b1, 2),
    (.p2, 1)]
  | 46 => [(.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 37), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 47 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 40), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 9), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 48 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 43), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 49 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 51), (.b1, 2), (.p2, 6), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 50 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 52), (.b0, 3), (.p2, 18), (.b1, 2), (.p2,
    6), (.b0, 3), (.p2, 2)]
  | 51 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 55), (.b0, 3), (.p2, 25), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 2)]
  | 52 => [(.b1, 2), (.p2, 54), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 53 => [(.p2, 1), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 54 => [(.p2, 1), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 9), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 55 => [(.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 56 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 24), (.b1, 2), (.p2, 6), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 57 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 18), (.b1, 2),
    (.p2, 6), (.b0, 3), (.p2, 2)]
  | 58 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 28), (.b0, 3), (.p2, 25), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 2)]
  | 59 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 31), (.b0, 3), (.p2, 22), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 60 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 34), (.b0, 3), (.p2, 19), (.b0, 3), (.p2,
    12), (.b1, 2), (.p2, 1)]
  | 61 => [(.b1, 2), (.p2, 33), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 12), (.b1, 2), (.p2, 1)]
  | 62 => [(.p2, 1), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    12), (.b1, 2), (.p2, 1)]
  | 63 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 64 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 65 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 18), (.b1, 2), (.p2,
    6), (.b0, 3), (.p2, 2)]
  | 66 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 67 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 68 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 13), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3),
    (.p2, 2)]
  | 69 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 30), (.b1, 2), (.p2,
    6), (.b0, 3), (.p2, 2)]
  | 70 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 13), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 71 => [(.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 28), (.b0, 3), (.p2, 10), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 72 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 73 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 21), (.b1, 2), (.p2,
    6), (.b0, 3), (.p2, 2)]
  | 74 => [(.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 10), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 75 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3),
    (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 76 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 77 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 78 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2,
    1)]
  | 79 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 21), (.b1, 2), (.p2,
    6), (.b0, 3), (.p2, 2)]
  | 80 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 81 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 82 => [(.p2, 1), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 83 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    4), (.b0, 3), (.p2, 15), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | 84 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3),
    (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 85 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 86 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2,
    1)]
  | 87 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 7), (.b0, 3), (.p2,
    1), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 88 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 15), (.b1, 2),
    (.p2, 6), (.b0, 3), (.p2, 2)]
  | 89 => [(.p2, 1), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 6), (.b1, 2), (.b0, 3), (.p2, 2)]
  | 90 => [(.p2, 1), (.b0, 3), (.p2, 16), (.b0, 3), (.p2, 10), (.b0, 3), (.p2, 10), (.b0, 3),
    (.p2, 1), (.b0, 3), (.p2, 9), (.b1, 2), (.p2, 1)]
  | 91 => [(.p2, 1), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    2)]
  | 92 => [(.p2, 1), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 19), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    7), (.b0, 3), (.p2, 7), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 93 => [(.p2, 1), (.b0, 3), (.p2, 22), (.b0, 3), (.p2, 13), (.b0, 3), (.p2, 1), (.b0, 3), (.p2,
    2)]
  | 94 => [(.p2, 1), (.b0, 3), (.p2, 25), (.b0, 3), (.p2, 4), (.b0, 3), (.p2, 4), (.b0, 3), (.p2,
    10), (.b0, 3), (.p2, 1), (.b0, 3), (.p2, 2)]
  | 95 => [(.p2, 1), (.b0, 3), (.p2, 45), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | 96 => [(.p2, 1), (.b0, 3), (.p2, 30), (.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | 97 => [(.b1, 2), (.p2, 6), (.b0, 3), (.p2, 2)]
  | _ => []

def remA : Nat → Nat
  | 62 => 9
  | 63 => 24
  | 64 => 8
  | 65 => 3
  | 66 => 76
  | 67 => 79
  | 68 => 27
  | 69 => 43
  | 70 => 27
  | 71 => 13
  | 72 => 73
  | 73 => 113
  | 74 => 41
  | 75 => 90
  | 76 => 98
  | 77 => 10
  | 78 => 35
  | 79 => 69
  | 80 => 46
  | 81 => 5
  | 82 => 98
  | 83 => 46
  | 84 => 24
  | 85 => 24
  | 86 => 1
  | 87 => 104
  | 88 => 13
  | 89 => 13
  | 90 => 7
  | 91 => 16
  | 92 => 15
  | 93 => 9
  | 94 => 10
  | 95 => 40
  | 96 => 24
  | 97 => 41
  | _ => 0

def bulkInfo : Nat → Nat × Nat × Nat
  | 0 => (1, 1, 4)
  | 1 => (2, 1, 4)
  | 2 => (3, 1, 3)
  | 3 => (4, 3, 3)
  | 4 => (5, 2, 167)
  | 5 => (6, 1, 44)
  | 6 => (7, 1, 4)
  | 7 => (8, 1, 3)
  | 8 => (9, 3, 3)
  | 9 => (10, 6, 98)
  | 10 => (11, 1, 3)
  | 11 => (12, 1, 3)
  | 12 => (13, 1, 142)
  | 13 => (14, 3, 3)
  | 14 => (0, 7, 80)
  | 15 => (16, 1, 3)
  | 16 => (17, 1, 64)
  | 17 => (18, 1, 4)
  | 18 => (19, 1, 4)
  | 19 => (20, 1, 3)
  | 20 => (21, 1, 85)
  | 21 => (22, 1, 4)
  | 22 => (23, 1, 3)
  | 23 => (24, 1, 26)
  | 24 => (25, 3, 3)
  | 25 => (26, 8, 97)
  | 26 => (27, 1, 3)
  | 27 => (28, 1, 77)
  | 28 => (29, 3, 3)
  | 29 => (30, 3, 82)
  | 30 => (31, 1, 64)
  | 31 => (32, 1, 4)
  | 32 => (33, 1, 4)
  | 33 => (34, 1, 3)
  | 34 => (35, 1, 85)
  | 35 => (36, 3, 3)
  | 36 => (15, 11, 87)
  | 37 => (38, 1, 4)
  | 38 => (39, 1, 4)
  | 39 => (40, 1, 3)
  | 40 => (41, 1, 77)
  | 41 => (42, 1, 4)
  | 42 => (43, 1, 4)
  | 43 => (44, 1, 3)
  | 44 => (45, 1, 3)
  | 45 => (46, 1, 142)
  | 46 => (47, 1, 44)
  | 47 => (48, 1, 4)
  | 48 => (49, 1, 3)
  | 49 => (50, 1, 26)
  | 50 => (51, 1, 4)
  | 51 => (52, 3, 3)
  | 52 => (37, 16, 26)
  | 53 => (54, 1, 44)
  | 54 => (55, 1, 4)
  | 55 => (56, 1, 3)
  | 56 => (57, 1, 26)
  | 57 => (58, 1, 4)
  | 58 => (59, 1, 4)
  | 59 => (60, 1, 3)
  | 60 => (61, 3, 3)
  | 61 => (53, 9, 167)
  | _ => (0, 0, 0)

def turnInfo : Nat → Nat × Nat × Nat × Nat
  | 0 => (67, 150, 5, 221)
  | 1 => (70, 149, 5, 367)
  | 2 => (71, 148, 5, 403)
  | 3 => (92, 147, 5, 386)
  | 4 => (97, 159, 6, 279)
  | 5 => (91, 148, 15, 405)
  | 6 => (96, 152, 7, 229)
  | 7 => (83, 140, 31, 639)
  | 8 => (93, 145, 25, 599)
  | 9 => (86, 162, 5, 439)
  | 10 => (86, 154, 8, 388)
  | 11 => (78, 153, 12, 414)
  | 12 => (73, 148, 16, 576)
  | 13 => (93, 145, 24, 533)
  | 14 => (62, 157, 5, 247)
  | 15 => (83, 128, 47, 645)
  | 16 => (83, 140, 24, 432)
  | 17 => (87, 115, 74, 986)
  | 18 => (88, 135, 32, 510)
  | 19 => (90, 88, 137, 1946)
  | 20 => (66, 154, 19, 408)
  | 21 => (73, 149, 23, 435)
  | 22 => (53, 152, 15, 398)
  | 23 => (69, 126, 70, 1213)
  | 24 => (72, 155, 26, 573)
  | 25 => (93, 152, 24, 612)
  | 26 => (80, 141, 29, 758)
  | 27 => (80, 129, 56, 1154)
  | 28 => (82, 129, 54, 905)
  | 29 => (74, 122, 68, 1235)
  | 30 => (95, 134, 37, 489)
  | 31 => (65, 157, 15, 409)
  | 32 => (90, 150, 22, 547)
  | 33 => (72, 156, 17, 502)
  | 34 => (85, 155, 17, 542)
  | 35 => (77, 154, 21, 497)
  | 36 => (94, 105, 116, 1912)
  | 37 => (66, 142, 23, 375)
  | 38 => (91, 141, 23, 378)
  | 39 => (93, 124, 59, 836)
  | 40 => (83, 133, 39, 615)
  | 41 => (53, 135, 36, 591)
  | 42 => (68, 134, 38, 772)
  | 43 => (87, 118, 72, 1093)
  | 44 => (84, 109, 92, 1664)
  | 45 => (93, 117, 82, 1158)
  | 46 => (68, 72, 173, 2686)
  | 47 => (63, 169, 7, 65)
  | 48 => (97, 166, 11, 94)
  | 49 => (0, 144, 51, 724)
  | 50 => (63, 166, 12, 62)
  | 51 => (81, 146, 45, 771)
  | 52 => (89, 164, 10, 135)
  | 53 => (65, 138, 33, 420)
  | 54 => (90, 137, 30, 404)
  | 55 => (76, 103, 109, 1840)
  | 56 => (89, 162, 5, 138)
  | 57 => (67, 157, 9, 221)
  | 58 => (70, 156, 9, 367)
  | 59 => (71, 155, 9, 403)
  | 60 => (92, 154, 9, 386)
  | 61 => (73, 147, 28, 553)
  | _ => (0, 0, 0, 0)

def mergeInfo : Nat → Nat × Nat × Nat × Nat
  | 0 => (65, 6, 13, 252)
  | 1 => (64, 16, 26, 446)
  | 2 => (81, 3, 3, 203)
  | 3 => (37, 3, 4, 33)
  | 4 => (72, 3, 6, 129)
  | 5 => (66, 3, 7, 174)
  | 6 => (84, 3, 7, 101)
  | 7 => (95, 3, 7, 33)
  | 8 => (85, 3, 8, 149)
  | 9 => (77, 3, 12, 149)
  | 10 => (79, 4, 5, 101)
  | 11 => (82, 15, 26, 317)
  | 12 => (96, 17, 41, 561)
  | 13 => (79, 21, 48, 799)
  | 14 => (75, 8, 14, 242)
  | 15 => (26, 10, 16, 297)
  | 16 => (96, 11, 17, 226)
  | 17 => (83, 23, 47, 633)
  | 18 => (74, 5, 12, 180)
  | 19 => (10, 5, 13, 152)
  | 20 => (75, 8, 17, 272)
  | 21 => (69, 3, 3, 33)
  | 22 => (88, 11, 21, 338)
  | 23 => (94, 14, 28, 443)
  | 24 => (0, 1, 1, 64)
  | 25 => (76, 6, 17, 200)
  | 26 => (90, 6, 16, 173)
  | 27 => (62, 4, 4, 55)
  | 28 => (15, 7, 16, 250)
  | 29 => (64, 8, 20, 269)
  | 30 => (90, 8, 20, 202)
  | 31 => (0, 9, 23, 319)
  | 32 => (37, 10, 24, 258)
  | 33 => (90, 33, 69, 744)
  | 34 => (93, 15, 31, 417)
  | 35 => (78, 6, 8, 187)
  | _ => (0, 0, 0, 0)


def constSide : List (Tok × ℕ) → SSide
  | [] => []
  | (t, c) :: rest => ⟨t, ⟨0, 0, c⟩⟩ :: constSide rest

def exConstSide : List (Tok × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (t, c) :: rest => repTok t c (exConstSide rest)

private theorem exSide_constSide (a0 b0 : ℕ) :
    ∀ (ts : List (Tok × ℕ)), exSide a0 b0 (constSide ts) = exConstSide ts
  | [] => rfl
  | (t, c) :: rest => by
    simp only [constSide, exSide, exConstSide, SN.eval, Nat.zero_mul, Nat.zero_add]
    rw [exSide_constSide a0 b0 rest]

def cpR (u : ℕ) (a b : SN) : SSide :=
  spushc .b0 2 (spush .p2 a.mul3 (spushc .b0 3 (spush .p2 b.mul3 (constSide (cpTail u)))))

def cpState (u : ℕ) (a b : SN) : SState :=
  ⟨true, false, [], cpR u a b⟩

def encodeCP (u a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) {{sB}}>
    ((0 : Fin 2) >> repTok .b0 2 (repTok .p2 (3 * a) (repTok .b0 3 (repTok .p2 (3 * b)
      (exConstSide (cpTail u))))))

theorem evalSym_cpState (a0 b0 u : ℕ) (a b : SN) :
    evalSym a0 b0 (cpState u a b) = encodeCP u (a.eval a0 b0) (b.eval a0 b0) := by
  simp only [evalSym, cpState, cpR, encodeCP, exSide, boolToFin2, ↓reduceIte]
  rw [exSide_spushc, exSide_spush, exSide_spushc, exSide_spush, exSide_constSide]
  have ha : a.mul3.eval a0 b0 = 3 * a.eval a0 b0 := by simp only [SN.mul3, SN.eval]; ring
  have hb : b.mul3.eval a0 b0 = 3 * b.eval a0 b0 := by simp only [SN.mul3, SN.eval]; ring
  rw [ha, hb]

def checkBulk (u : ℕ) : Bool :=
  let (v, db, st) := bulkInfo u
  decide (v < 62) && (remA v == 0) && decide (1 ≤ db) && decide (1 ≤ st) &&
  (symRunPos (st - 1) (cpState u ⟨1, 0, 5⟩ ⟨0, 1, 5⟩) == some (cpState v ⟨1, 0, 4⟩ ⟨0, 1, 5 + db⟩))

def checkTurn (u : ℕ) : Bool :=
  let (v, aPost, bPost, st) := turnInfo u
  (remA u == 0) && decide (v < 98) && decide (4 + remA v ≤ aPost) &&
  decide (5 ≤ bPost) && decide (148 ≤ aPost + bPost) && decide (1 ≤ st) &&
  (symRunPos (st - 1) (cpState u ⟨0, 0, 4⟩ ⟨0, 1, 144⟩) == some (cpState v ⟨0, 1, aPost⟩ ⟨0, 0,
    bPost⟩))

def checkMerge (i : ℕ) : Bool :=
  let u := 62 + i
  let (v, segLen, dbM, st) := mergeInfo i
  decide (v < 98) && (remA u == segLen + remA v) && decide (segLen ≤ dbM) && decide (1 ≤ st) &&
  (symRunPos (st - 1) (cpState u ⟨1, 0, 4 + segLen⟩ ⟨0, 1, 5⟩) == some (cpState v ⟨1, 0, 4⟩ ⟨0, 1,
    5 + dbM⟩))

private theorem checkBulk_ok : checkRange checkBulk 0 62 = true := rfl
private theorem checkMerge_0_ok : checkRange checkMerge 0 13 = true := rfl
private theorem checkMerge_1_ok : checkRange checkMerge 13 7 = true := rfl
private theorem checkMerge_2_ok : checkRange checkMerge 20 12 = true := rfl
private theorem checkMerge_3_ok : checkRange checkMerge 32 4 = true := rfl
private theorem checkTurn_0_ok : checkRange checkTurn 0 7 = true := rfl
private theorem checkTurn_1_ok : checkRange checkTurn 7 5 = true := rfl
private theorem checkTurn_2_ok : checkRange checkTurn 12 5 = true := rfl
private theorem checkTurn_3_ok : checkRange checkTurn 17 2 = true := rfl
private theorem checkTurn_4_ok : checkRange checkTurn 19 3 = true := rfl
private theorem checkTurn_5_ok : checkRange checkTurn 22 4 = true := rfl
private theorem checkTurn_6_ok : checkRange checkTurn 26 2 = true := rfl
private theorem checkTurn_7_ok : checkRange checkTurn 28 3 = true := rfl
private theorem checkTurn_8_ok : checkRange checkTurn 31 5 = true := rfl
private theorem checkTurn_9_ok : checkRange checkTurn 36 3 = true := rfl
private theorem checkTurn_10_ok : checkRange checkTurn 39 3 = true := rfl
private theorem checkTurn_11_ok : checkRange checkTurn 42 2 = true := rfl
private theorem checkTurn_12_ok : checkRange checkTurn 44 1 = true := rfl
private theorem checkTurn_13_ok : checkRange checkTurn 45 1 = true := rfl
private theorem checkTurn_14_ok : checkRange checkTurn 46 2 = true := rfl
private theorem checkTurn_15_ok : checkRange checkTurn 48 7 = true := rfl
private theorem checkTurn_16_ok : checkRange checkTurn 55 4 = true := rfl
private theorem checkTurn_17_ok : checkRange checkTurn 59 3 = true := rfl

def startState : SState := ⟨true, false, [], []⟩

private theorem checkEntry_ok :
    symRunPos 5813 startState = some (cpState 15 ⟨0, 0, 39⟩ ⟨0, 0, 165⟩) := rfl

/-! ### Invariant Closure & Blank-Tape Entry -/

def Inv (u a b : ℕ) : Prop :=
  u < 98 ∧ 4 + remA u ≤ a ∧ 5 ≤ b ∧ 148 ≤ a + b

def InAttractor (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ u a b, Inv u a b ∧ cfg = encodeCP u a b

private theorem init_reaches_entry :
    ReachesStar target_tm (init []) (encodeCP 15 39 165) := by
  have hrun := symRunPos_sound 0 0 checkEntry_ok
  rw [evalSym_cpState] at hrun
  have hinit : evalSym 0 0 startState = init [] := by
    dsimp only [evalSym, startState, exSide, boolToFin2, init, Tape.mk₁]
    rfl
  rw [hinit] at hrun
  exact hrun.to_star

private theorem inv_entry : Inv 15 39 165 := by
  have hr : remA 15 = 0 := rfl
  refine ⟨by omega, by omega, by omega, by omega⟩

private theorem checkTurn_all (u : ℕ) (hu : u < 62) : checkTurn u = true := by
  by_cases h0 : u < 7
  · exact checkRange_spec checkTurn 7 0 u checkTurn_0_ok (by omega) (by omega)
  ·
    by_cases h1 : u < 12
    · exact checkRange_spec checkTurn 5 7 u checkTurn_1_ok (by omega) (by omega)
    ·
      by_cases h2 : u < 17
      · exact checkRange_spec checkTurn 5 12 u checkTurn_2_ok (by omega) (by omega)
      ·
        by_cases h3 : u < 19
        · exact checkRange_spec checkTurn 2 17 u checkTurn_3_ok (by omega) (by omega)
        ·
          by_cases h4 : u < 22
          · exact checkRange_spec checkTurn 3 19 u checkTurn_4_ok (by omega) (by omega)
          ·
            by_cases h5 : u < 26
            · exact checkRange_spec checkTurn 4 22 u checkTurn_5_ok (by omega) (by omega)
            ·
              by_cases h6 : u < 28
              · exact checkRange_spec checkTurn 2 26 u checkTurn_6_ok (by omega) (by omega)
              ·
                by_cases h7 : u < 31
                · exact checkRange_spec checkTurn 3 28 u checkTurn_7_ok (by omega) (by omega)
                ·
                  by_cases h8 : u < 36
                  · exact checkRange_spec checkTurn 5 31 u checkTurn_8_ok (by omega) (by omega)
                  ·
                    by_cases h9 : u < 39
                    · exact checkRange_spec checkTurn 3 36 u checkTurn_9_ok (by omega) (by omega)
                    ·
                      by_cases h10 : u < 42
                      · exact checkRange_spec checkTurn 3 39 u checkTurn_10_ok (by omega) (by omega)
                      ·
                        by_cases h11 : u < 44
                        · exact checkRange_spec checkTurn 2 42 u checkTurn_11_ok (by omega)
                            (by omega)
                        ·
                          by_cases h12 : u < 45
                          · exact checkRange_spec checkTurn 1 44 u checkTurn_12_ok (by omega)
                              (by omega)
                          ·
                            by_cases h13 : u < 46
                            · exact checkRange_spec checkTurn 1 45 u checkTurn_13_ok (by omega)
                                (by omega)
                            ·
                              by_cases h14 : u < 48
                              · exact checkRange_spec checkTurn 2 46 u checkTurn_14_ok (by omega)
                                  (by omega)
                              ·
                                by_cases h15 : u < 55
                                · exact checkRange_spec checkTurn 7 48 u checkTurn_15_ok
                                    (by omega) (by omega)
                                ·
                                  by_cases h16 : u < 59
                                  · exact checkRange_spec checkTurn 4 55 u checkTurn_16_ok
                                      (by omega) (by omega)
                                  ·
                                    exact checkRange_spec checkTurn 3 59 u checkTurn_17_ok 
                                      (by omega) (by omega)

private theorem checkMerge_all (i : ℕ) (hi : i < 36) : checkMerge i = true := by
  by_cases h0 : i < 13
  · exact checkRange_spec checkMerge 13 0 i checkMerge_0_ok (by omega) (by omega)
  ·
    by_cases h1 : i < 20
    · exact checkRange_spec checkMerge 7 13 i checkMerge_1_ok (by omega) (by omega)
    ·
      by_cases h2 : i < 32
      · exact checkRange_spec checkMerge 12 20 i checkMerge_2_ok (by omega) (by omega)
      ·
        exact checkRange_spec checkMerge 4 32 i checkMerge_3_ok (by omega) (by omega)

theorem attractor_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : InAttractor cfg) :
    ∃ cfg', ReachesPlus target_tm cfg cfg' ∧ InAttractor cfg' := by
  rcases h with ⟨u, a, b, ⟨hu98, ha, hb, hab⟩, rfl⟩
  by_cases hu62 : u < 62
  · by_cases ha5 : 5 ≤ a
    · -- Case 1: Cycle bulk (u < 62, a ≥ 5)
      have hchk := checkRange_spec checkBulk 62 0 u checkBulk_ok (Nat.zero_le u) hu62
      unfold checkBulk at hchk
      rcases E : bulkInfo u with ⟨v, db, st⟩
      rw [E] at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
      rcases hchk with ⟨⟨⟨⟨hv62, hrv0⟩, hdb1⟩, _⟩, hsym⟩
      have hrun := symRunPos_sound (a - 5) (b - 5) hsym
      rw [evalSym_cpState, evalSym_cpState] at hrun
      have ha1 : (⟨1, 0, 5⟩ : SN).eval (a - 5) (b - 5) = a := by simp only [SN.eval]; omega
      have hb1 : (⟨0, 1, 5⟩ : SN).eval (a - 5) (b - 5) = b := by simp only [SN.eval]; omega
      have ha2 : (⟨1, 0, 4⟩ : SN).eval (a - 5) (b - 5) = a - 1 := by simp only [SN.eval]; omega
      have hb2 : (⟨0, 1, 5 + db⟩ : SN).eval (a - 5) (b - 5) = b + db := by
        simp only [SN.eval]
        omega
      rw [ha1, hb1, ha2, hb2] at hrun
      exact ⟨encodeCP v (a - 1) (b + db), hrun,
        ⟨v, a - 1, b + db, ⟨by omega, by omega, by omega, by omega⟩, rfl⟩⟩
    · -- Case 2: Turnaround (u < 62, a = 4)
      have hchk := checkTurn_all u hu62
      unfold checkTurn at hchk
      rcases E : turnInfo u with ⟨v, aPost, bPost, st⟩
      rw [E] at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
      rcases hchk with ⟨⟨⟨⟨⟨⟨hru0, hv98⟩, haPost⟩, hbPost⟩, hsum⟩, _⟩, hsym⟩
      have ha4 : a = 4 := by omega
      have hb144 : 144 ≤ b := by omega
      have hrun := symRunPos_sound 0 (b - 144) hsym
      rw [evalSym_cpState, evalSym_cpState] at hrun
      have ha1 : (⟨0, 0, 4⟩ : SN).eval 0 (b - 144) = a := by simp only [SN.eval]; omega
      have hb1 : (⟨0, 1, 144⟩ : SN).eval 0 (b - 144) = b := by simp only [SN.eval]; omega
      have ha2 : (⟨0, 1, aPost⟩ : SN).eval 0 (b - 144) = (b - 144) + aPost := by
        simp only [SN.eval]
        omega
      have hb2 : (⟨0, 0, bPost⟩ : SN).eval 0 (b - 144) = bPost := by simp only [SN.eval]; omega
      rw [ha1, hb1, ha2, hb2] at hrun
      exact ⟨encodeCP v ((b - 144) + aPost) bPost, hrun,
        ⟨v, (b - 144) + aPost, bPost, ⟨hv98, by omega, hbPost, by omega⟩, rfl⟩⟩
  · -- Case 3: Transient merge segment (62 ≤ u < 98)
    have hchk := checkMerge_all (u - 62) (by omega)
    unfold checkMerge at hchk
    rcases E : mergeInfo (u - 62) with ⟨v, segLen, dbM, st⟩
    rw [E] at hchk
    have hu_eq : 62 + (u - 62) = u := by omega
    rw [hu_eq] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨hv98, hrem⟩, hdbM⟩, _⟩, hsym⟩
    have hrun := symRunPos_sound (a - (4 + segLen)) (b - 5) hsym
    rw [evalSym_cpState, evalSym_cpState] at hrun
    have ha1 : (⟨1, 0, 4 + segLen⟩ : SN).eval (a - (4 + segLen)) (b - 5) = a := by
      simp only [SN.eval]
      omega
    have hb1 : (⟨0, 1, 5⟩ : SN).eval (a - (4 + segLen)) (b - 5) = b := by simp only [SN.eval]; omega
    have ha2 : (⟨1, 0, 4⟩ : SN).eval (a - (4 + segLen)) (b - 5) = a - segLen := by
      simp only [SN.eval]
      omega
    have hb2 : (⟨0, 1, 5 + dbM⟩ : SN).eval (a - (4 + segLen)) (b - 5) = b + dbM := by
      simp only [SN.eval]
      omega
    rw [ha1, hb1, ha2, hb2] at hrun
    exact ⟨encodeCP v (a - segLen) (b + dbM), hrun,
      ⟨v, a - segLen, b + dbM, ⟨hv98, by omega, by omega, by omega⟩, rfl⟩⟩

end

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  IsNotHalt.of_reachesPlus_invariant
    init_reaches_entry
    ⟨15, 39, 165, inv_entry, rfl⟩
    attractor_closed


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC
