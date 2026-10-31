/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 2
abbrev B : Fin 6 := 3
abbrev C : Fin 6 := 4
abbrev D : Fin 6 := 0
abbrev E : Fin 6 := 1
abbrev F : Fin 6 := 5
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000

open WordVKQ Word WordVKQ.Traj103

abbrev z04 (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (z04 c1) [tm]⊢⁺ (z04 c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

abbrev pref24 : zF := [0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0]


def zCs : Call -> Fin 6
  | .ch => B
  | .ca => A

def zCR (w : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (w <{{zCs c}} ([1] +> r))

def zCL (w : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> w) {{C}}> r)

def zCf (w : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> pref24 +> w) {{C}}> default)

abbrev z0f (c : Call) (w1 w2 : zB) : Prop :=
  ∀ r, (zCR w1 c r) [tm]⊢⁺ (zCL w2 r)

abbrev Side := SideP z0f
abbrev Seg := SegP z0f

lemma seg_ch_V : Seg [.ch] [.ch, .ch] V_u V_u :=
  zS5 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun u r => by unfold zCR zCs V_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL zCR zCs; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL V_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_V : Seg [.ca] [.ch] V_u Vp :=
  zS2 (mid := [0, 1, 0, 1])
    (fun u r => by unfold zCR zCs V_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_Vp : Seg [.ca] [.ca, .ca] Vp Vp :=
  zS5 (mid1 := [0, 1, 1, 1]) (mid2 := [0, 1, 0, 1])
    (fun u r => by unfold zCR zCs Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL zCR zCs; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_K : Seg [.ch] [] K_u Q_u :=
  zS4 (fun u r => by unfold zCR zCL zCs K_u Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_Q : Seg [.ch] [.ch] Q_u K_u :=
  zS2 (mid := [1, 1])
    (fun u r => by unfold zCR zCs Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL K_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_VpQ : Seg [.ca] [.ca] (Vp ++ Q_u) (Kp ++ Vp) :=
  zS2 (mid := [0, 1, 0, 1, 1, 1])
    (fun u r => by unfold zCR zCs Vp Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Kp Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_KpVp : Seg [.ca] [] (Kp ++ Vp) (Qp ++ Vp) :=
  zS4 (fun u r => by unfold zCR zCL zCs Kp Vp Qp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_QpVp : Seg [.ca] [.ca, .ca] (Qp ++ Vp) (Kp ++ Vp) :=
  zS5 (mid1 := [0, 1, 1, 1, 1, 1]) (mid2 := [0, 1, 0, 1, 1, 1])
    (fun u r => by unfold zCR zCs Qp Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL zCR zCs; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Kp Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_Kp : Seg [.ca] [] Kp Qp :=
  zS4 (fun u r => by unfold zCR zCL zCs Kp Qp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_Qp : Seg [.ca] [.ca] Qp Kp :=
  zS2 (mid := [1, 1])
    (fun u r => by unfold zCR zCs Qp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Kp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_KQ : Seg [.ca] [] (K_u ++ Q_u) Vp :=
  zS4 (fun u r => by unfold zCR zCL zCs K_u Q_u Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ca_QQ : Seg [.ca] [.ca] (Q_u ++ Q_u) Vp :=
  zS2 (mid := [0, 1, 0, 1])
    (fun u r => by unfold zCR zCs Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

-- Turnaround zP0..zP6
abbrev tr1 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1]
abbrev tr2 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1]
abbrev tr3 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1]
abbrev tr4 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1]
abbrev tr5 : zF := [0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1]
abbrev tr6 : zF := [0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1]

lemma zP0 (w : zB) : (zCf w) [tm]⊢⁺ (zCR w .ca (tr1 +> default)) := by
  unfold zCf zCR zCs pref24 tr1
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

lemma zP1 (w : zB) : (zCL w (tr1 +> default)) [tm]⊢⁺ (zCR w .ca (tr2 +> default)) := by
  unfold zCL zCR zCs tr1 tr2
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

lemma zP2 (w : zB) : (zCL w (tr2 +> default)) [tm]⊢⁺ (zCR w .ca (tr3 +> default)) := by
  unfold zCL zCR zCs tr2 tr3
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

lemma zP3 (w : zB) : (zCL w (tr3 +> default)) [tm]⊢⁺ (zCR w .ca (tr4 +> default)) := by
  unfold zCL zCR zCs tr3 tr4
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

lemma zP4 (w : zB) : (zCL w (tr4 +> default)) [tm]⊢⁺ (zCR w .ca (tr5 +> default)) := by
  unfold zCL zCR zCs tr4 tr5
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

lemma zP5 (w : zB) : (zCL w (tr5 +> default)) [tm]⊢⁺ (zCR w .ca (tr6 +> default)) := by
  unfold zCL zCR zCs tr5 tr6
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

lemma zP6 (w : zB) : (zCL w (tr6 +> default)) [tm]⊢⁺ (zCf ([1, 1, 0] +> w)) := by
  unfold zCL zCf tr6 pref24
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

-- Section 2: Words, Shift Identity, zDg, Parse, Scan, Step
lemma segSpec : SegSpec z0f :=
  ⟨seg_ch_V, seg_ca_V, seg_ca_Vp, seg_ch_K, seg_ch_Q,
   seg_ca_VpQ, seg_ca_KpVp, seg_ca_QpVp, seg_ca_Kp, seg_ca_Qp,
   seg_ca_KQ, seg_ca_QQ⟩

lemma Side_turnaround {w w' : zB} (h : Side ([Call.ca] ^ 6) w w') :
    (zCf w) [tm]⊢⁺ (zCf ([1, 1, 0] +> w')) := by
  rcases h with _ | ⟨hc1, h⟩
  rcases h with _ | ⟨hc2, h⟩
  rcases h with _ | ⟨hc3, h⟩
  rcases h with _ | ⟨hc4, h⟩
  rcases h with _ | ⟨hc5, h⟩
  rcases h with _ | ⟨hc6, h⟩
  cases h
  exact zPt (zP0 w)
    (zPt (hc1 (tr1 +> default))
      (zPt (zP1 _)
        (zPt (hc2 (tr2 +> default))
          (zPt (zP2 _)
            (zPt (hc3 (tr3 +> default))
              (zPt (zP3 _)
                (zPt (hc4 (tr4 +> default))
                  (zPt (zP4 _)
                    (zPt (hc5 (tr5 +> default))
                      (zPt (zP5 _)
                        (zPt (hc6 (tr6 +> default)) (zP6 w'))))))))))))

lemma Step_exec {u u' : List Word} (h : Step u u') :
    (zCf (zTs u default)) [tm]⊢⁺ (zCf (zTs u' default)) := by
  rcases h with ⟨n, b', v, da, H, g, hScan, hDg, rfl⟩
  have hSeg := Seg_of_Scan segSpec hScan
  dsimp at hSeg
  have hSide0 := zSc hSeg (Side_ca_default segSpec hDg)
  rw [zWt_zTs, zTs_append, zTs_rep_K, zWt'_zTs', <- zTs'_append] at hSide0
  have hTurn := Side_turnaround hSide0
  rwa [zTs_V_shift] at hTurn

lemma Rounds_exec {u v : List Word} (h : Rounds u v) :
    (zCf (zTs u default)) [tm]⊢* (zCf (zTs v default)) := by
  induction h with
  | refl _ => exact ⟨0, rfl⟩
  | next hS _ ih => exact zPs (z02 (Step_exec hS) ih)

-- Section 3: Universal Parse_V_start, Scan_of_Parse, and Trace Evaluators

def zInitCCfg : CCfg := ⟨0, 0, [], []⟩
def zHit6CCfg : CCfg := ⟨4, 0, [0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], []⟩

set_option maxRecDepth 200000 in
lemma zCm_init_274 : zCm zInitCCfg 274 = some zHit6CCfg := by decide

lemma init_to_u0 : (init []) [tm]⊢* zCf (zTs u_0 default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = z04 zInitCCfg := rfl
  have h1 : z04 zHit6CCfg = zCf (zTs u_0 default) := by
    dsimp [z04, zHit6CCfg, zCf, pref24, u_0, zTs, V_u, K_u, Q_u]
    simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00, zDh, zDt]
  have hPlus := zTc (by decide : 0 < 274) zCm_init_274
  rw [<- h0, h1] at hPlus
  exact zPs hPlus

-- 17 finite rounds u_0 -> u_17
lemma reach_N (m : Nat) :
    ∃ N, m <= N ∧ ∃ u,
      multiStep tm (init []) N = some (zCf (zTs u default)) ∧
      Good u := by
  induction m with
  | zero =>
    rcases init_to_u0 with ⟨k1, hk1⟩
    rcases Rounds_exec rounds_0_17 with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, u_17, zMt tm _ _ _ k1 k2 hk1 hk2, good_u17⟩
  | succ m ih =>
    rcases ih with ⟨N, hN, u, h_ms, hG⟩
    rcases Good_step hG with ⟨u', hStep, hG'⟩
    rcases Step_exec hStep with ⟨k, hk_pos, h_step_k⟩
    exact ⟨N + k, Nat.add_le_add hN hk_pos, u', zMt tm _ _ _ N k h_ms h_step_k, hG'⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases reach_N (n + 1) with ⟨N, hN, _, h_N, _⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs, hn] at h_some
  exact h_some

end BusyBeaver.M_1RB0RC_1LC1LF_1LD0LB_1RE1LC_1RA0RE_0LCHHH
