/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Calculi.WordCalculusF
public import BusyBeaver.Calculi.WordCalculusG
public import BusyBeaver.Calculi.WordCalculusH


open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RAHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
abbrev A : Fin 6 := 2
abbrev B : Fin 6 := 3
abbrev C : Fin 6 := 0
abbrev D : Fin 6 := 4
abbrev E : Fin 6 := 1
abbrev F : Fin 6 := 5
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 2000000

open WordVKQ Word WordVKQ.Traj114

abbrev evalCCfgVKQ (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep tm n c
theorem zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (evalCCfgVKQ c1) [tm]⊢⁺ (evalCCfgVKQ c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

abbrev pref24 : BitWord := [1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0]


def zCs : Call -> Fin 6
  | .ch => E
  | .ca => C

def zCR (w : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([1] +> r) {{zCs c}}> w)

def zCL (w : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (r <{{A}} ([0] +> w))

def zCf (w : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (default <{{A}} ([0] +> pref24 +> w))

abbrev callStep (c : Call) (w1 w2 : HalfTape) : Prop :=
  ∀ r, (zCR w1 c r) [tm]⊢⁺ (zCL w2 r)

abbrev Side := SideP callStep
abbrev Seg := SegP callStep

theorem seg_ch_V : Seg [.ch] [.ch, .ch] V_u V_u :=
  segP_of_step_two (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun u r => by unfold zCR zCs V_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL zCR zCs; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL V_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_V : Seg [.ca] [.ch] V_u Vp :=
  segP_of_step_one (mid := [0, 1, 0, 1])
    (fun u r => by unfold zCR zCs V_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_Vp : Seg [.ca] [.ca, .ca] Vp Vp :=
  segP_of_step_two (mid1 := [0, 1, 1, 1]) (mid2 := [0, 1, 0, 1])
    (fun u r => by unfold zCR zCs Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL zCR zCs; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ch_K : Seg [.ch] [] K_u Q_u :=
  segP_of_step_nil (fun u r => by unfold zCR zCL zCs K_u Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ch_Q : Seg [.ch] [.ch] Q_u K_u :=
  segP_of_step_one (mid := [1, 1])
    (fun u r => by unfold zCR zCs Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL K_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_VpQ : Seg [.ca] [.ca] (Vp ++ Q_u) (Kp ++ Vp) :=
  segP_of_step_one (mid := [0, 1, 0, 1, 1, 1])
    (fun u r => by unfold zCR zCs Vp Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Kp Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_KpVp : Seg [.ca] [] (Kp ++ Vp) (Qp ++ Vp) :=
  segP_of_step_nil (fun u r => by unfold zCR zCL zCs Kp Vp Qp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_QpVp : Seg [.ca] [.ca, .ca] (Qp ++ Vp) (Kp ++ Vp) :=
  segP_of_step_two (mid1 := [0, 1, 1, 1, 1, 1]) (mid2 := [0, 1, 0, 1, 1, 1])
    (fun u r => by unfold zCR zCs Qp Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL zCR zCs; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Kp Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_Kp : Seg [.ca] [] Kp Qp :=
  segP_of_step_nil (fun u r => by unfold zCR zCL zCs Kp Qp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_Qp : Seg [.ca] [.ca] Qp Kp :=
  segP_of_step_one (mid := [1, 1])
    (fun u r => by unfold zCR zCs Qp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Kp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_KQ : Seg [.ca] [] (K_u ++ Q_u) Vp :=
  segP_of_step_nil (fun u r => by unfold zCR zCL zCs K_u Q_u Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

theorem seg_ca_QQ : Seg [.ca] [.ca] (Q_u ++ Q_u) Vp :=
  segP_of_step_one (mid := [0, 1, 0, 1])
    (fun u r => by unfold zCR zCs Q_u; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by unfold zCL Vp; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

-- Turnaround zP0..zP6
abbrev tr1 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr2 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr3 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr4 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr5 : BitWord := [0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr6 : BitWord := [0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]

theorem zP0 (w : HalfTape) : (zCf w) [tm]⊢⁺ (zCR w .ca (tr1 +> default)) := by
  unfold zCf zCR zCs pref24 tr1
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP1 (w : HalfTape) : (zCL w (tr1 +> default)) [tm]⊢⁺ (zCR w .ca (tr2 +> default)) := by
  unfold zCL zCR zCs tr1 tr2
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP2 (w : HalfTape) : (zCL w (tr2 +> default)) [tm]⊢⁺ (zCR w .ca (tr3 +> default)) := by
  unfold zCL zCR zCs tr2 tr3
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP3 (w : HalfTape) : (zCL w (tr3 +> default)) [tm]⊢⁺ (zCR w .ca (tr4 +> default)) := by
  unfold zCL zCR zCs tr3 tr4
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP4 (w : HalfTape) : (zCL w (tr4 +> default)) [tm]⊢⁺ (zCR w .ca (tr5 +> default)) := by
  unfold zCL zCR zCs tr4 tr5
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP5 (w : HalfTape) : (zCL w (tr5 +> default)) [tm]⊢⁺ (zCR w .ca (tr6 +> default)) := by
  unfold zCL zCR zCs tr5 tr6
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP6 (w : HalfTape) : (zCL w (tr6 +> default)) [tm]⊢⁺ (zCf ([1, 1, 0] +> w)) := by
  unfold zCL zCf tr6 pref24
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

-- Section 2: Words, Shift Identity, DigitVal, Parse, Scan, Step
theorem segSpec : SegSpec callStep :=
  ⟨seg_ch_V, seg_ca_V, seg_ca_Vp, seg_ch_K, seg_ch_Q,
   seg_ca_VpQ, seg_ca_KpVp, seg_ca_QpVp, seg_ca_Kp, seg_ca_Qp,
   seg_ca_KQ, seg_ca_QQ⟩

theorem Side_turnaround {w w' : HalfTape} (h : Side ([Call.ca] ^ 6) w w') :
    (zCf w) [tm]⊢⁺ (zCf ([1, 1, 0] +> w')) := by
  rcases h with _ | ⟨hc1, h⟩
  rcases h with _ | ⟨hc2, h⟩
  rcases h with _ | ⟨hc3, h⟩
  rcases h with _ | ⟨hc4, h⟩
  rcases h with _ | ⟨hc5, h⟩
  rcases h with _ | ⟨hc6, h⟩
  cases h
  exact stepPlus_trans_vkq (zP0 w)
    (stepPlus_trans_vkq (hc1 (tr1 +> default))
      (stepPlus_trans_vkq (zP1 _)
        (stepPlus_trans_vkq (hc2 (tr2 +> default))
          (stepPlus_trans_vkq (zP2 _)
            (stepPlus_trans_vkq (hc3 (tr3 +> default))
              (stepPlus_trans_vkq (zP3 _)
                (stepPlus_trans_vkq (hc4 (tr4 +> default))
                  (stepPlus_trans_vkq (zP4 _)
                    (stepPlus_trans_vkq (hc5 (tr5 +> default))
                      (stepPlus_trans_vkq (zP5 _)
                        (stepPlus_trans_vkq (hc6 (tr6 +> default)) (zP6 w'))))))))))))

theorem Step_exec {u u' : List Word} (h : Step u u') :
    (zCf (evalWords u default)) [tm]⊢⁺ (zCf (evalWords u' default)) := by
  rcases h with ⟨n, b', v, da, H, g, hScan, hDg, rfl⟩
  have hSeg := Seg_of_Scan segSpec hScan
  dsimp at hSeg
  have hSide0 := sideP_of_segP hSeg (Side_ca_default segSpec hDg)
  rw [wordsToBits_append_tape, evalWords_append, evalWords_replicate_K, wordsToBitsShifted_append_tape, <- evalWordsShifted_append] at hSide0
  have hTurn := Side_turnaround hSide0
  rwa [evalWords_V_shift] at hTurn

theorem Rounds_exec {u v : List Word} (h : Rounds u v) :
    (zCf (evalWords u default)) [tm]⊢* (zCf (evalWords v default)) := by
  induction h with
  | refl _ => exact ⟨0, rfl⟩
  | next hS _ ih => exact stepStar_of_stepPlus_vkq (stepPlus_stepStar_trans_vkq (Step_exec hS) ih)

-- Section 3: Universal Parse_V_start, Scan_of_Parse, and Trace Evaluators

def zInitCCfg : CCfg := ⟨0, 0, [], []⟩
def zHit5CCfg : CCfg := ⟨2, 0, [], [0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,0,1]⟩

set_option maxRecDepth 200000 in
theorem zCm_init_979 : zCm zInitCCfg 979 = some zHit5CCfg := by decide

theorem init_to_u0 : (init []) [tm]⊢* zCf (evalWords u_0 default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = evalCCfgVKQ zInitCCfg := rfl
  have h1 : evalCCfgVKQ zHit5CCfg = zCf (evalWords u_0 default) := by
    dsimp [evalCCfgVKQ, zHit5CCfg, zCf, pref24, u_0, evalWords, V_u, K_u, Q_u]
    simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  have hPlus := zTc (by decide : 0 < 979) zCm_init_979
  rw [<- h0, h1] at hPlus
  exact stepStar_of_stepPlus_vkq hPlus

-- 14 finite rounds u_0 -> u_14
theorem reach_N (m : Nat) :
    ∃ N, m <= N ∧ ∃ u,
      multiStep tm (init []) N = some (zCf (evalWords u default)) ∧
      Good u := by
  induction m with
  | zero =>
    rcases init_to_u0 with ⟨k1, hk1⟩
    rcases Rounds_exec rounds_0_14 with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, u_14, multiStep_trans_vkq tm _ _ _ k1 k2 hk1 hk2, good_u14⟩
  | succ m ih =>
    rcases ih with ⟨N, hN, u, h_ms, hG⟩
    rcases Good_step hG with ⟨u', hStep, hG'⟩
    rcases Step_exec hStep with ⟨k, hk_pos, h_step_k⟩
    exact ⟨N + k, Nat.add_le_add hN hk_pos, u', multiStep_trans_vkq tm _ _ _ N k h_ms h_step_k, hG'⟩



theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases reach_N (n + 1) with ⟨N, hN, _, h_N, _⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := multiStep_add_intermediate_vkq h_N
  rw [multiStep_succ_vkq, hn] at h_some
  exact h_some

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RAHHH
