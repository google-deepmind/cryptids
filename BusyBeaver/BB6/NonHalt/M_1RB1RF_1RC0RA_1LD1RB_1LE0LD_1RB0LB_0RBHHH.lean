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

namespace BusyBeaver.M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RBHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 2000000

open WordVKQ Word

abbrev evalCCfgVKQ (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep tm n c
theorem zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (evalCCfgVKQ c1) [tm]⊢⁺ (evalCCfgVKQ c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

abbrev pref28 : BitWord := [1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0]


def zCs : Call -> Fin 6
  | .ch => C
  | .ca => B

def zCR (w : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([1] +> r) {{zCs c}}> w)

def zCL (w : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (r <{{D}} ([0] +> w))

def zCf (w : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (default <{{D}} ([0] +> pref28 +> w))

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


-- Turnaround zP0..zP14
abbrev tr1 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr2 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr3 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr4 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr5 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr6 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr7 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr8 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1]
abbrev tr9 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr10 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr11 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr12 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr13 : BitWord := [0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1]
abbrev tr14 : BitWord := [0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1]

theorem zP0 (w : HalfTape) : (zCf w) [tm]⊢⁺ (zCR w .ca (tr1 +> default)) := by
  unfold zCf zCR zCs pref28 tr1
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

theorem zP6 (w : HalfTape) : (zCL w (tr6 +> default)) [tm]⊢⁺ (zCR w .ca (tr7 +> default)) := by
  unfold zCL zCR zCs tr6 tr7
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP7 (w : HalfTape) : (zCL w (tr7 +> default)) [tm]⊢⁺ (zCR w .ca (tr8 +> default)) := by
  unfold zCL zCR zCs tr7 tr8
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP8 (w : HalfTape) : (zCL w (tr8 +> default)) [tm]⊢⁺ (zCR w .ca (tr9 +> default)) := by
  unfold zCL zCR zCs tr8 tr9
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP9 (w : HalfTape) : (zCL w (tr9 +> default)) [tm]⊢⁺ (zCR w .ca (tr10 +> default)) := by
  unfold zCL zCR zCs tr9 tr10
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP10 (w : HalfTape) : (zCL w (tr10 +> default)) [tm]⊢⁺ (zCR w .ca (tr11 +> default)) := by
  unfold zCL zCR zCs tr10 tr11
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP11 (w : HalfTape) : (zCL w (tr11 +> default)) [tm]⊢⁺ (zCR w .ca (tr12 +> default)) := by
  unfold zCL zCR zCs tr11 tr12
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP12 (w : HalfTape) : (zCL w (tr12 +> default)) [tm]⊢⁺ (zCR w .ca (tr13 +> default)) := by
  unfold zCL zCR zCs tr12 tr13
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP13 (w : HalfTape) : (zCL w (tr13 +> default)) [tm]⊢⁺ (zCR w .ca (tr14 +> default)) := by
  unfold zCL zCR zCs tr13 tr14
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

theorem zP14 (w : HalfTape) : (zCL w (tr14 +> default)) [tm]⊢⁺ (zCf ([1, 1, 0] +> w)) := by
  unfold zCL zCf tr14 pref28
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

-- Section 2: Words, Shift Identity, DigitVal, Parse, Scan, Step
theorem segSpec : SegSpec callStep :=
  ⟨seg_ch_V, seg_ca_V, seg_ca_Vp, seg_ch_K, seg_ch_Q,
   seg_ca_VpQ, seg_ca_KpVp, seg_ca_QpVp, seg_ca_Kp, seg_ca_Qp,
   seg_ca_KQ, seg_ca_QQ⟩

abbrev Step := StepB 14
abbrev Rounds := RoundsB 14
abbrev Rounds.refl := @RoundsB.refl 14
abbrev Rounds.next := @RoundsB.next 14
abbrev checkStep := checkStepB 14
abbrev checkStep_sound := checkStepB_sound 14

theorem Side_turnaround {w w' : HalfTape} (h : Side ([Call.ca] ^ 14) w w') :
    (zCf w) [tm]⊢⁺ (zCf ([1, 1, 0] +> w')) := by
  rcases h with _ | ⟨hc1, h⟩
  rcases h with _ | ⟨hc2, h⟩
  rcases h with _ | ⟨hc3, h⟩
  rcases h with _ | ⟨hc4, h⟩
  rcases h with _ | ⟨hc5, h⟩
  rcases h with _ | ⟨hc6, h⟩
  rcases h with _ | ⟨hc7, h⟩
  rcases h with _ | ⟨hc8, h⟩
  rcases h with _ | ⟨hc9, h⟩
  rcases h with _ | ⟨hc10, h⟩
  rcases h with _ | ⟨hc11, h⟩
  rcases h with _ | ⟨hc12, h⟩
  rcases h with _ | ⟨hc13, h⟩
  rcases h with _ | ⟨hc14, h⟩
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
                        (stepPlus_trans_vkq (hc6 (tr6 +> default))
                          (stepPlus_trans_vkq (zP6 _)
                            (stepPlus_trans_vkq (hc7 (tr7 +> default))
                              (stepPlus_trans_vkq (zP7 _)
                                (stepPlus_trans_vkq (hc8 (tr8 +> default))
                                  (stepPlus_trans_vkq (zP8 _)
                                    (stepPlus_trans_vkq (hc9 (tr9 +> default))
                                      (stepPlus_trans_vkq (zP9 _)
                                        (stepPlus_trans_vkq (hc10 (tr10 +> default))
                                          (stepPlus_trans_vkq (zP10 _)
                                            (stepPlus_trans_vkq (hc11 (tr11 +> default))
                                              (stepPlus_trans_vkq (zP11 _)
                                                (stepPlus_trans_vkq (hc12 (tr12 +> default))
                                                  (stepPlus_trans_vkq (zP12 _)
                                                    (stepPlus_trans_vkq (hc13 (tr13 +> default))
                                                      (stepPlus_trans_vkq (zP13 _)
                                                        (stepPlus_trans_vkq (hc14 (tr14 +> default)) (zP14 w'))))))))))))))))))))))))))))

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

def u_0 : List Word := [K,K,K,Q]
def tags_0 : List Nat := [3,3,4]
def da_0 : List Word := [K,K,Q]
def n_0 : Nat := 0
def u_1 : List Word := [V,K,Q,V,K,K,Q]
def tags_1 : List Nat := [0,5,2,4]
def da_1 : List Word := [K,K,K,K,K,Q,Q]
def n_1 : Nat := 0
def u_2 : List Word := [V,V,V,Q,V,V,K,K,K,K,K,Q,Q]
def tags_2 : List Nat := [0,0,0,3,0,0,5,3,4,5]
def da_2 : List Word := [Q,Q,Q,Q,K,Q,Q,Q,K,Q]
def n_2 : Nat := 0
def u_3 : List Word := [V,V,V,V,K,V,V,V,Q,V,V,Q,Q,Q,Q,K,Q,Q,Q,K,Q]
def tags_3 : List Nat := [0,0,0,1,0,0,0,3,0,0,4,3,4,5,3,5]
def da_3 : List Word := [Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q]
def n_3 : Nat := 0
def u_4 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,Q,V,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q]
def tags_4 : List Nat := [0,0,0,1,0,0,0,1,0,0,1,0,0,3,0,4,5,4,4,5,3,5]
def da_4 : List Word := [Q,K,K,Q,K,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def n_4 : Nat := 0
def u_5 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,Q,V,Q,K,K,Q,K,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def tags_5 : List Nat := [0,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,3,0,4,4,3,4,4,3,5,4,5,3,5]
def da_5 : List Word := [Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def n_5 : Nat := 0
def u_6 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,Q,V,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def tags_6 : List Nat := [0,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0,1,0,0,0,3,0,4,5,4,3,5,5,4,4,3,5,4,5,3,5]
def da_6 : List Word := [Q,K,Q,Q,K,Q,K,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def n_6 : Nat := 0
def u_7 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,Q,V,Q,K,Q,Q,K,Q,K,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def tags_7 : List Nat := [0,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,3,0,4,5,4,3,3,3,5,3,4,4,5,5,4,4,3,5,4,5,3,5]
def da_7 : List Word := [Q,K,Q,Q,K,Q,K,K,Q,Q,K,K,Q,Q,K,Q,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def n_7 : Nat := 0
def u_8 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,K,Q,V,Q,V,V,V,V,V,V,K,V,V,V,Q,V,Q,K,Q,Q,K,Q,K,K,Q,Q,K,K,Q,Q,K,Q,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def tags_8 : List Nat := [0,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,5,3,0,3,0,0,0,0,0,1,0,0,0,3,0,4,5,4,3,4,4,3,5,3,5,3,5,3,4,4,5,5,4,4,3,5,4,5,3,5]
def da_8 : List Word := [Q,K,Q,Q,K,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def n_8 : Nat := 0
def u_9 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,Q,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,Q,V,Q,V,V,V,V,V,V,K,V,V,V,Q,V,Q,K,Q,Q,K,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def head41 : List Word := [V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V]
def tags_head41 : List Nat := [0,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0,1,0,0,0,1,0,0,0]
def v_head41 : List Word := [V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,V]
def a_41 : Nat := 33554431
def b_41 : Nat := 397770042
def A_top24 : Nat := 12430313
def s12 : List Word := [V,V,V,V,V,V,K,V,V,V,Q,V]
def s18 : List Word := s12 ++ [Q,K,Q,Q,K,Q]
def tags_s18 : List Nat := [0,0,0,0,0,1,0,0,0,3,0,4,5,4]
def v_s18 : List Word := [V,V,V,V,V,K,V,V,V,V,K,V,V,V,V]
def top22 : List Word := [K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,Q]
def tags_top22 : List Nat := [4,4,5,5,4,4,3,5,4,5,3,5]
def p_41_init : List Word := [V,K,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,Q,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,Q,V,Q]
def ds_core_init : List Word := [K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,K,Q]
def A_core_init : Nat := 47935404

-- Initial 568 steps from init [] to zCf (evalWords u_0 default)
def zInitCCfg : CCfg := ⟨0, 0, [], []⟩
def zHit14CCfg : CCfg := ⟨3, 0, [], [0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

set_option maxRecDepth 200000 in
theorem zCm_init_568 : zCm zInitCCfg 568 = some zHit14CCfg := by decide

theorem init_to_u0 : (init []) [tm]⊢* zCf (evalWords u_0 default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = evalCCfgVKQ zInitCCfg := rfl
  have h1 : evalCCfgVKQ zHit14CCfg = zCf (evalWords u_0 default) := by
    dsimp [evalCCfgVKQ, zHit14CCfg, zCf, pref28, u_0, evalWords, V_u, K_u, Q_u]
    simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq, default_head_vkq, default_tail_vkq]
  have hPlus := zTc (by decide : 0 < 568) zCm_init_568
  rw [<- h0, h1] at hPlus
  exact stepStar_of_stepPlus_vkq hPlus

-- 9 finite rounds u_0 -> u_9
set_option maxRecDepth 200000 in
theorem step_0 : Step u_0 u_1 := checkStep_sound n_0 tags_0 u_0 da_0 u_1 (by decide)
set_option maxRecDepth 200000 in
theorem step_1 : Step u_1 u_2 := checkStep_sound n_1 tags_1 u_1 da_1 u_2 (by decide)
set_option maxRecDepth 200000 in
theorem step_2 : Step u_2 u_3 := checkStep_sound n_2 tags_2 u_2 da_2 u_3 (by decide)
set_option maxRecDepth 200000 in
theorem step_3 : Step u_3 u_4 := checkStep_sound n_3 tags_3 u_3 da_3 u_4 (by decide)
set_option maxRecDepth 200000 in
theorem step_4 : Step u_4 u_5 := checkStep_sound n_4 tags_4 u_4 da_4 u_5 (by decide)
set_option maxRecDepth 200000 in
theorem step_5 : Step u_5 u_6 := checkStep_sound n_5 tags_5 u_5 da_5 u_6 (by decide)
set_option maxRecDepth 200000 in
theorem step_6 : Step u_6 u_7 := checkStep_sound n_6 tags_6 u_6 da_6 u_7 (by decide)
set_option maxRecDepth 200000 in
theorem step_7 : Step u_7 u_8 := checkStep_sound n_7 tags_7 u_7 da_7 u_8 (by decide)
set_option maxRecDepth 200000 in
theorem step_8 : Step u_8 u_9 := checkStep_sound n_8 tags_8 u_8 da_8 u_9 (by decide)

theorem rounds_0_9 : Rounds u_0 u_9 :=
  Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3 (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7 (Rounds.next step_8 (Rounds.refl u_9)))))))))

-- Invariant Good u (5-piece decomposition)
abbrev Good (u : List Word) : Prop :=
  ∃ p_41 ds_core A_core m,
    u = head41 ++ p_41 ++ s12 ++ [Q, K, Q, Q, K, Q, K, K] ++ ds_core ++ [Q, K] ++ top22 ∧
    (∃ p_tail, p_41 = V :: p_tail) ∧
    m = 4 + ds_core.length ∧
    12 <= m ∧
    DigitVal A_core (m - 4) ds_core ∧
    A_core * 32 <= 25 * 2 ^ (m - 4) ∧
    wordScale p_41 * ((2 ^ m : Nat) : Rat) = 256 ∧
    wordPot p_41 <= 21 / 4

set_option maxRecDepth 200000 in
theorem good_u9 : Good u_9 := by
  refine ⟨p_41_init, ds_core_init, A_core_init, 30, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨p_41_init.tail, rfl⟩
  · decide
  · decide
  · exact checkDg_sound A_core_init ds_core_init (by decide)
  · decide
  · have h := checkScalePow_sound p_41_init 30 8 (by decide)
    norm_num at h
    exact h
  · have h := checkWordPotLe_sound p_41_init 21 4 (by decide)
    norm_num at h
    linarith

-- Fixed-piece Scan lemmas
set_option maxRecDepth 200000 in
theorem Scan_head41 : Scan 0 14 head41 a_41 b_41 v_head41 0 := by
  have h := checkAffineScan_sound tags_head41 0 0 0 14 head41 0 a_41 0 b_41 v_head41 0 0 0 (by decide)
  simpa using h

theorem v_head41_eq : V :: v_head41 = head41 ++ [V] := rfl

theorem Scan_s18 (ap bp : Nat) (hbp : 3 <= bp) :
    Scan ap bp s18 (4 * ap + 4) (2048 * (bp - 3) + 1972) v_s18 3 := by
  have h := checkAffineScan_sound tags_s18 1 0 1 3 s18 4 4 2048 1972 v_s18 3 ap (bp - 3) (by decide)
  have h_bp : 1 * (bp - 3) + 3 = bp := by omega
  have h_ap : 1 * ap + 0 = ap := by omega
  rwa [h_ap, h_bp] at h

theorem Scan_top22 (b_top22 : Nat) (hb : 2 <= b_top22) :
    Scan (2 ^ 19) b_top22 top22 0 (256 * (b_top22 - 2) + 45) s12 10 := by
  have h := checkAffineScan_sound tags_top22 0 (2 ^ 19) 1 2 top22 0 0 256 45 s12 10 0 (b_top22 - 2) (by decide)
  have h_in : 1 * (b_top22 - 2) + 2 = b_top22 := by omega
  dsimp at h
  rwa [h_in] at h

theorem Parse_s18_split {ap a_end g_all : Nat} {rest : List Word}
    (h : Parse ap (s18 ++ K :: rest) a_end g_all) :
    ∃ g_mid, Parse (4 * (ap + 1)) (K :: rest) a_end g_mid := by
  change Parse ap ([V,V,V,V,V,V,K,V,V,V,Q,V,Q,K,Q,Q,K,Q,K] ++ rest) a_end g_all at h
  simp only [List.cons_append, List.nil_append] at h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  rcases Parse_VK_inv h with h | h
  · -- VK at i=5
    have h := Parse_VV_inv h
    have h := Parse_VV_inv h
    have h := Parse_VQ_inv h
    cases h with
    | @D _ q1_10 _ _ _ _ _ hq1_10 h =>
      have hq1_10_eq : q1_10 = 128 + ap * 128 := by dsimp [dVal] at hq1_10; omega
      subst hq1_10_eq
      have h := Parse_VQ_inv h
      cases h with
      | @D _ q1_12 _ _ _ _ _ hq1_12 h =>
        have hq1_12_eq : q1_12 = 129 + ap * 128 := by dsimp [dVal] at hq1_12; omega
        subst hq1_12_eq
        cases h with
        | D _ hq1_13 _ => dsimp [dVal] at hq1_13; omega
        | @P _ q2_13 _ _ _ _ _ _ _ hq2_13 h =>
          have hq2_13_eq : q2_13 = 32 + ap * 32 := by dsimp [dVal] at hq2_13; omega
          subst hq2_13_eq
          cases h with
          | D _ hq1_15 _ => dsimp [dVal] at hq1_15; omega
          | P _ _ hq2_15 _ => dsimp [dVal] at hq2_15; omega
      | @P _ q2_12 _ _ _ _ _ _ _ hq2_12 h =>
        have hq2_12_eq : q2_12 = 64 + ap * 64 := by dsimp [dVal] at hq2_12; omega
        subst hq2_12_eq
        cases h with
        | D _ hq1_14 _ => dsimp [dVal] at hq1_14; omega
        | @P _ q2_14 _ _ _ _ _ _ _ hq2_14 h =>
          have hq2_14_eq : q2_14 = 16 + ap * 16 := by dsimp [dVal] at hq2_14; omega
          subst hq2_14_eq
          cases h with
          | @D _ q1_16 _ _ _ _ _ hq1_16 h =>
            have hq1_16_eq : q1_16 = 8 + ap * 8 := by dsimp [dVal] at hq1_16; omega
            subst hq1_16_eq
            cases h with
            | D _ hq1_17 _ => dsimp [dVal] at hq1_17; omega
            | P _ _ hq2_17 _ => dsimp [dVal] at hq2_17; omega
          | @P _ q2_16 _ _ _ _ _ _ _ hq2_16 h =>
            have hq2_16_eq : q2_16 = 4 + ap * 4 := by dsimp [dVal] at hq2_16; omega
            subst hq2_16_eq
            have h_end : 4 + ap * 4 = 4 * (ap + 1) := by omega
            rw [h_end] at h
            exact ⟨_, h⟩
    | P _ hw1 _ _ => exact False.elim (hw1 rfl)
  · -- T at i=5
    cases h with
    | D _ hq1_6 _ => dsimp [dVal] at hq1_6; omega
    | P _ hw1 _ _ => exact False.elim (hw1 rfl)

-- Section 6: Main Invariant Closure and Goal Proof
theorem zDg_top24 : DigitVal A_top24 24 ([Q, K] ++ top22) :=
  checkDg_sound A_top24 ([Q, K] ++ top22) (by decide)

theorem zDg_bot8 : DigitVal 45 8 [Q, K, Q, Q, K, Q, K, K] :=
  checkDg_sound 45 [Q, K, Q, Q, K, Q, K, K] (by decide)

theorem digitVal_mid {A_core m : Nat} {ds_core : List Word}
    (hm : 12 <= m) (hD : DigitVal A_core (m - 4) ds_core)
    (hA_core : A_core * 32 <= 25 * 2 ^ (m - 4)) :
    ∃ A_mid,
      DigitVal A_mid m ([K, K] ++ ds_core ++ [Q, K]) ∧
      2 <= A_mid ∧
      A_mid <= 2 + 57 * 2 ^ (m - 7) := by
  have h_kk : DigitVal 0 2 [K, K] := checkDg_sound 0 [K, K] (by decide)
  have h_qk : DigitVal 1 2 [Q, K] := checkDg_sound 1 [Q, K] (by decide)
  have h1 := digitVal_append h_kk hD
  have h2 := digitVal_append h1 h_qk
  have hlen1 : 2 + (m - 4) = m - 2 := by omega
  have hlen2 : (m - 2) + 2 = m := by omega
  rw [hlen1] at h2
  rw [hlen2] at h2
  have h_pow1 : 2 ^ (m - 4) = 8 * 2 ^ (m - 7) := by
    have heq : m - 4 = 3 + (m - 7) := by omega
    rw [heq, Nat.pow_add]
  have h_pow2 : 2 ^ (m - 2) = 32 * 2 ^ (m - 7) := by
    have heq : m - 2 = 5 + (m - 7) := by omega
    rw [heq, Nat.pow_add]
  have h_pos_m7 : 1 <= 2 ^ (m - 7) := pow_two_pos (m - 7)
  exact ⟨0 + A_core * 4 + 1 * 2 ^ (m - 2),
         by simpa [List.append_assoc] using h2,
         by omega,
         by omega⟩

theorem force_a19 {p_41 ds_mid : List Word} {ap gp m A_mid a_top g_mid : Nat}
    (hm : 12 <= m)
    (hP_p : Parse a_41 p_41 ap gp)
    (hz13 : wordScale p_41 * ((2 ^ m : Nat) : Rat) = 256)
    (hzW : wordPot p_41 <= 21 / 4)
    (hD_mid : DigitVal A_mid m ds_mid)
    (hA_lo : 2 <= A_mid)
    (hA_hi : A_mid <= 2 + 57 * 2 ^ (m - 7))
    (hP_mid : Parse (4 * (ap + 1)) ds_mid a_top g_mid) :
    a_top = 2 ^ 19 := by
  rcases Parse_la hP_p with ⟨hla_lo, hla_hi⟩
  have hz12 := wordValQ_nonneg p_41
  have hz10_le := two_wordVal_add_wordValQ_le p_41
  have h_diff_hi : ((ap : Rat) + 1) * wordScale p_41 - ((a_41 : Rat) + 1) < 11 := by linarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
  have h_mul_lo : ((a_41 : Rat) + 1) * ((2 ^ m : Nat) : Rat) <= ((ap : Rat) + 1) * (wordScale p_41 * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((ap : Rat) + 1) * (wordScale p_41 * ((2 ^ m : Nat) : Rat)) < (((a_41 : Rat) + 1) + 11) * ((2 ^ m : Nat) : Rat) := by
    nlinarith
  rw [hz13] at h_mul_lo h_mul_hi
  have ha41_val : a_41 + 1 = 2 ^ 25 := by decide
  have ha41_r : (a_41 : Rat) + 1 = ((2 ^ 25 : Nat) : Rat) := by exact_mod_cast ha41_val
  rw [ha41_r] at h_mul_lo h_mul_hi
  have h_nat_lo : 2 ^ 25 * 2 ^ m <= (ap + 1) * 256 := by exact_mod_cast h_mul_lo
  have h_nat_hi : (ap + 1) * 256 < (2 ^ 25 + 11) * 2 ^ m := by exact_mod_cast h_mul_hi
  have h_256 : (ap + 1) * 256 = (4 * (ap + 1)) * 64 := by ring
  rw [h_256] at h_nat_lo h_nat_hi
  have h_split1 : 2 ^ 25 * 2 ^ m = (2 ^ 19 * 2 ^ m) * 64 := by
    have : (2 ^ 25 : Nat) = 2 ^ 19 * 64 := by decide
    rw [this]; ring
  have h_split2 : (2 ^ 25 + 11) * 2 ^ m = (2 ^ 19 * 2 ^ m + 11 * 2 ^ (m - 6)) * 64 := by
    have h25 : (2 ^ 25 : Nat) = 2 ^ 19 * 64 := by decide
    have hm6 : 2 ^ m = 2 ^ (m - 6) * 64 := by
      have h6 : (64 : Nat) = 2 ^ 6 := rfl
      rw [h6, <- Nat.pow_add, Nat.sub_add_cancel (by omega : 6 <= m)]
    calc (2 ^ 25 + 11) * 2 ^ m
      _ = 2 ^ 25 * 2 ^ m + 11 * 2 ^ m := by ring
      _ = (2 ^ 19 * 64) * 2 ^ m + 11 * (2 ^ (m - 6) * 64) := by rw [h25, hm6]
      _ = (2 ^ 19 * 2 ^ m + 11 * 2 ^ (m - 6)) * 64 := by ring
  rw [h_split1] at h_nat_lo
  rw [h_split2] at h_nat_hi
  have h_pos64 : 0 < 64 := by decide
  have hap_lo : 2 ^ 19 * 2 ^ m <= 4 * (ap + 1) := Nat.le_of_mul_le_mul_right h_nat_lo h_pos64
  have hap_hi : 4 * (ap + 1) < 2 ^ 19 * 2 ^ m + 11 * 2 ^ (m - 6) := Nat.lt_of_mul_lt_mul_right h_nat_hi
  have h_pow_m6 : 2 ^ (m - 6) = 2 * 2 ^ (m - 7) := by
    have heq : m - 6 = 1 + (m - 7) := by omega
    rw [heq, Nat.pow_add]
  have h_pow_m : 2 ^ m = 128 * 2 ^ (m - 7) := by
    have h7 : (128 : Nat) = 2 ^ 7 := rfl
    rw [h7, <- Nat.pow_add, Nat.add_sub_of_le (by omega : 7 <= m)]
  have h_pow_m7_ge : 32 <= 2 ^ (m - 7) := by
    have h5 : 5 <= m - 7 := by omega
    have hle := Nat.pow_le_pow_right (by decide : 1 <= 2) h5
    simpa using hle
  rcases parse_digitVal_a hP_mid hD_mid with ⟨h_atop_lo, h_atop_hi⟩
  have h_sum_lo : 2 ^ 19 * 2 ^ m < 4 * (ap + 1) + A_mid := by omega
  have h_sum_hi : 4 * (ap + 1) + A_mid < (2 ^ 19 + 1) * 2 ^ m := by
    have : (2 ^ 19 + 1) * 2 ^ m = 2 ^ 19 * 2 ^ m + 128 * 2 ^ (m - 7) := by
      rw [Nat.add_mul, Nat.one_mul, h_pow_m]
    omega
  have h_pos_m : 0 < 2 ^ m := pow_two_pos m
  have h_lt1 : a_top < 2 ^ 19 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_atop_lo h_sum_hi)
  have h_lt2 : 2 ^ 19 < a_top + 1 := Nat.lt_of_mul_lt_mul_right (lt_trans h_sum_lo h_atop_hi)
  omega

theorem bound_b_mid0 {p_41 v_p ds_mid : List Word}
    {ap bp gp m A_mid b_mid0 : Nat}
    (hm : 12 <= m)
    (hS_p : Scan a_41 b_41 p_41 ap bp v_p gp)
    (hbp : 3 <= bp)
    (hz13 : wordScale p_41 * ((2 ^ m : Nat) : Rat) = 256)
    (hzW : wordPot p_41 <= 21 / 4)
    (hb_mid0 : b_mid0 = 2048 * (bp - 3) + 1972)
    (hD_mid : DigitVal A_mid m ds_mid) :
    2 + 4 * wordVal ds_mid < (b_mid0 : Rat) := by
  have h_delta_p := (Scan_delta hS_p).2
  have h_4wv_p := two_wordVal_add_wordValQ_le_four_wordPotV v_p
  have h_cw_p := scan_wordPot_contract hS_p
  have hc_b41 := (cPar_bounds b_41).2
  have h_wv_p_lt : wordPotV v_p < 6 := by linarith
  have h_z13_p := scan_wordScale_eq hS_p
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (pow_two_pos (3 * gp))
  have h_z13_vp_pos := wordScale_pos v_p
  have h_z13_vp_le : wordScale v_p <= wordScale p_41 := by nlinarith
  have h_b41_big : ((2 ^ 28 : Nat) : Rat) + 26 < (b_41 : Rat) := by norm_num [b_41]
  have h_bp2_pos : (0 : Rat) <= (bp : Rat) - 2 := by
    have : (2 : Rat) <= (bp : Rat) := by exact_mod_cast (by omega : 2 <= bp)
    linarith
  have h_prod_p : ((2 ^ 28 : Nat) : Rat) < ((bp : Rat) - 2) * wordScale p_41 := by nlinarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
  have h_mul_m : ((2 ^ 28 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < ((bp : Rat) - 2) * (wordScale p_41 * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  rw [hz13] at h_mul_m
  have h_pow28 : ((2 ^ 28 : Nat) : Rat) = ((2 ^ 20 : Nat) : Rat) * 256 := by norm_num
  rw [h_pow28] at h_mul_m
  have h_bp2_gt : ((2 ^ 20 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < (bp : Rat) - 2 := by linarith
  have h_bmid0_r : (b_mid0 : Rat) = 2048 * ((bp : Rat) - 3) + 1972 := by
    rw [hb_mid0, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbp]; push_cast; ring
  have h_z10_mid := (digitVal_scale_and_val hD_mid).2
  have h_pow20_val : ((2 ^ 20 : Nat) : Rat) = 1048576 := by norm_num
  have h_powm_ge1 : (1 : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
  rw [h_z10_mid, h_bmid0_r]
  rw [h_pow20_val] at h_bp2_gt
  linarith

theorem bound_zW_p41' {p_41 v_p ds_mid v_mid : List Word}
    {ap bp gp m A_mid b_mid0 b_top22 g_mid : Nat}
    (hm : 12 <= m)
    (hS_p : Scan a_41 b_41 p_41 ap bp v_p gp)
    (hz13 : wordScale p_41 * ((2 ^ m : Nat) : Rat) = 256)
    (hzW : wordPot p_41 <= 21 / 4)
    (hD_mid : DigitVal A_mid m ds_mid)
    (hS_mid : Scan (4 * (ap + 1)) b_mid0 ds_mid (2 ^ 19) b_top22 v_mid g_mid) :
    wordPotV (v_p ++ v_s18 ++ v_mid) <= 21 / 4 := by
  -- Step A: wordPotV v_p <= 327 / 64
  have h_cw_p := scan_wordPot_contract hS_p
  have hc_b41 : cPar b_41 = 3 / 16 := by
    unfold cPar
    have hmod : b_41 % 2 = 0 := by decide
    rw [hmod]; rfl
  rw [hc_b41] at h_cw_p
  have hA : wordPotV v_p <= 327 / 64 := by linarith
  -- wordScale bounds
  have h_z13_p := scan_wordScale_eq hS_p
  have h_z13_s18 : wordScale v_s18 = 1 / 2048 := by
    have h := checkScalePow_sound v_s18 11 0 (by decide)
    norm_num at h
    linarith
  have h_wv_s18 : wordPotV v_s18 <= 9 / 256 := by
    have h := checkWordPotVLe_sound v_s18 9 256 (by decide)
    norm_num at h
    linarith
  -- Step B: wordScale v_p * wordPotV v_s18 <= 9 / 4096
  have h_powm_ge12 : (2 ^ 12 : Nat) <= 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have h_powm_r : ((2 ^ 12 : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_powm_ge12
  have h_z13_p_le : wordScale p_41 <= 1 / 16 := by
    have h_pos_p := wordScale_pos p_41
    have h_mul := mul_le_mul_of_nonneg_left h_powm_r (le_of_lt h_pos_p)
    rw [hz13] at h_mul
    norm_num at h_mul
    linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (pow_two_pos (3 * gp))
  have h_z13_vp_pos := wordScale_pos v_p
  have h_z13_vp_le : wordScale v_p <= 1 / 16 := by nlinarith
  have hB : wordScale v_p * wordPotV v_s18 <= 9 / 4096 := by
    have h_wv_nn := wordPotV_nonneg v_s18
    nlinarith
  -- Step C: wordScale (v_p ++ v_s18) * wordPotV v_mid <= 1 / 8
  have h_dc_eq := digitVal_scan_dCount hS_mid hD_mid
  have h_wv_mid_dc := (dCount_bound v_mid).2
  have h_vp_m : wordScale v_p * ((2 ^ m : Nat) : Rat) <= 256 := by
    have h_eq : wordScale v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat) = 256 := by
      calc wordScale v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat)
        _ = (wordScale v_p * ((2 ^ (3 * gp) : Nat) : Rat)) * ((2 ^ m : Nat) : Rat) := by ring
        _ = wordScale p_41 * ((2 ^ m : Nat) : Rat) := by rw [h_z13_p]
        _ = 256 := hz13
    have h_pos_m : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
    have h_nn : 0 <= wordScale v_p * ((2 ^ m : Nat) : Rat) := mul_nonneg (le_of_lt h_z13_vp_pos) (le_of_lt h_pos_m)
    nlinarith
  have h_prod_ps : wordScale v_p * wordScale v_s18 * ((2 ^ m : Nat) : Rat) <= 1 / 8 := by
    rw [h_z13_s18]
    linarith
  have hC : wordScale (v_p ++ v_s18) * wordPotV v_mid <= 1 / 8 := by
    rw [wordScale_append]
    have h_wv_mid_le : wordPotV v_mid <= ((2 ^ m : Nat) : Rat) := by
      have h_dc_le_m : 2 ^ (dCount v_mid) <= 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have h_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_dc_le_m
      linarith
    have h_wv_mid_nn := wordPotV_nonneg v_mid
    have h_z13_ps_pos : 0 < wordScale v_p * wordScale v_s18 := mul_pos h_z13_vp_pos (wordScale_pos v_s18)
    nlinarith
  -- Combine A + B + C
  have h_app1 := wordPotV_append_le v_p v_s18
  have h_app2 := wordPotV_append_le (v_p ++ v_s18) v_mid
  linarith

theorem bound_b_end_digitVal {w_41 v_w41 : List Word} {b_top22 g_w41 k : Nat}
    (hk : 3 <= k)
    (hb_top22 : 2 <= b_top22)
    (hS_w : Scan a_41 b_41 w_41 (2 ^ 19) b_top22 v_w41 g_w41)
    (hz13_vw : wordScale v_w41 * ((2 ^ k : Nat) : Rat) = 1)
    (hWV_vw : wordPotV v_w41 <= 21 / 4) :
    ∃ A_core' ds_core',
      DigitVal A_core' (k + 5) ds_core' ∧
      ds_core'.length = k + 5 ∧
      A_core' * 32 <= 25 * 2 ^ (k + 5) ∧
      DigitVal (256 * (b_top22 - 2) + 45) (k + 37)
          ([Q, K, Q, Q, K, Q, K, K] ++ ds_core' ++ [Q, K] ++ top22) := by
  rcases Scan_delta hS_w with ⟨hd_lo, hd_hi⟩
  have h_4wv := two_wordVal_add_wordValQ_le_four_wordPotV v_w41
  have hd_hi' : ((b_41 : Rat) - 2) - ((b_top22 : Rat) - 2) * wordScale v_w41 <= 21 := by linarith
  have h_powk_pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by exact_mod_cast (pow_two_pos k)
  have h_mul_lo : (((b_41 : Rat) - 2) - 21) * ((2 ^ k : Nat) : Rat) <= ((b_top22 : Rat) - 2) * (wordScale v_w41 * ((2 ^ k : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((b_top22 : Rat) - 2) * (wordScale v_w41 * ((2 ^ k : Nat) : Rat)) <= ((b_41 : Rat) - 1) * ((2 ^ k : Nat) : Rat) := by
    nlinarith
  rw [hz13_vw, mul_one] at h_mul_lo h_mul_hi
  have hb41_r : (b_41 : Rat) - 2 = (A_top24 : Rat) * 32 + 24 := by norm_num [b_41, A_top24]
  have hb41_1_r : (b_41 : Rat) - 1 = (A_top24 : Rat) * 32 + 25 := by norm_num [b_41, A_top24]
  rw [hb41_r] at h_mul_lo
  rw [hb41_1_r] at h_mul_hi
  let b_end := 256 * (b_top22 - 2) + 45
  have hb_end_r : (b_end : Rat) = 256 * ((b_top22 : Rat) - 2) + 45 := by
    dsimp [b_end]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb_top22]
    push_cast; ring
  have h_pow_k13 : ((2 ^ (k + 13) : Nat) : Rat) = 8192 * ((2 ^ k : Nat) : Rat) := by
    have h13 : ((2 ^ 13 : Nat) : Rat) = 8192 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h13]; ring
  have h_powk_ge1 : (1 : Rat) <= ((2 ^ k : Nat) : Rat) := by exact_mod_cast (pow_two_pos k)
  have h_bend_lo_r : (A_top24 : Rat) * ((2 ^ (k + 13) : Nat) : Rat) < (b_end : Rat) := by
    rw [hb_end_r, h_pow_k13]; linarith
  have h_bend_mid_r : (b_end : Rat) <= (A_top24 : Rat) * ((2 ^ (k + 13) : Nat) : Rat) + 256 * 25 * ((2 ^ k : Nat) : Rat) + 45 := by
    rw [hb_end_r, h_pow_k13]; linarith
  have h_bend_hi_r : (b_end : Rat) < ((A_top24 : Rat) + 1) * ((2 ^ (k + 13) : Nat) : Rat) := by
    rw [hb_end_r, h_pow_k13]; linarith
  have h_bend_lo : A_top24 * 2 ^ (k + 13) < b_end := by exact_mod_cast h_bend_lo_r
  have h_bend_mid : b_end <= A_top24 * 2 ^ (k + 13) + 256 * 25 * 2 ^ k + 45 := by exact_mod_cast h_bend_mid_r
  have h_bend_hi : b_end < (A_top24 + 1) * 2 ^ (k + 13) := by exact_mod_cast h_bend_hi_r
  have h_bend_mod256 : b_end % 256 = 45 := by dsimp [b_end]; omega
  let A_core' := (b_end / 256) % (2 ^ (k + 5))
  have h_Acore'_lt : A_core' < 2 ^ (k + 5) := Nat.mod_lt _ (pow_two_pos (k + 5))
  rcases exists_digitVal_of_lt_pow (k + 5) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_len_core' := length_of_digitVal hD_core'
  have h_bot_mid := digitVal_append zDg_bot8 hD_core'
  have h_all := digitVal_append h_bot_mid zDg_top24
  have h_len_all : (8 + (k + 5)) + 24 = k + 37 := by omega
  have h_pow_k13_eq : 2 ^ (k + 13) = 256 * 2 ^ (k + 5) := by
    have : k + 13 = 8 + (k + 5) := by omega
    rw [this, Nat.pow_add]
  have h_div_top : b_end / (2 ^ (k + 13)) = A_top24 := by
    have h_pos_k13 : 0 < 2 ^ (k + 13) := pow_two_pos (k + 13)
    have h1 := (Nat.le_div_iff_mul_le h_pos_k13).mpr (le_of_lt h_bend_lo)
    have h2 := (Nat.div_lt_iff_lt_mul h_pos_k13).mpr h_bend_hi
    omega
  have h_val_all : 45 + A_core' * 2 ^ 8 + A_top24 * 2 ^ (8 + (k + 5)) = b_end := by
    have h1 : 2 ^ 8 = 256 := by decide
    have h2 : 2 ^ (8 + (k + 5)) = 256 * 2 ^ (k + 5) := by rw [Nat.pow_add]
    rw [h1, h2]
    have h_assoc : A_top24 * (256 * 2 ^ (k + 5)) = 256 * (A_top24 * 2 ^ (k + 5)) := by ring
    rw [h_assoc]
    dsimp [A_core']
    have h_div256 : (b_end / 256) / (2 ^ (k + 5)) = A_top24 := by
      rw [Nat.div_div_eq_div_mul, <- h_pow_k13_eq, h_div_top]
    have h_mod_div := Nat.div_add_mod (b_end / 256) (2 ^ (k + 5))
    rw [h_div256, Nat.mul_comm (2 ^ (k + 5)) A_top24] at h_mod_div
    have h_mod256 := Nat.div_add_mod b_end 256
    omega
  have h_Acore'_le_k : A_core' <= 25 * 2 ^ k := by
    have h_eq8 : 2 ^ 8 = 256 := by decide
    have h_eq_k13 : 2 ^ (8 + (k + 5)) = 2 ^ (k + 13) := by
      have : 8 + (k + 5) = k + 13 := by omega
      rw [this]
    rw [h_eq8, h_eq_k13] at h_val_all
    omega
  have h_Acore'_32 : A_core' * 32 <= 25 * 2 ^ (k + 5) := by
    have h_pow_k5 : 2 ^ (k + 5) = 32 * 2 ^ k := by
      have : k + 5 = 5 + k := by omega
      rw [this, Nat.pow_add]
    omega
  rw [h_len_all, h_val_all] at h_all
  exact ⟨A_core', ds_core', hD_core', h_len_core', h_Acore'_32, by simpa [List.append_assoc] using h_all⟩

theorem Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_41, ds_core, A_core, m, rfl, ⟨p_tail, hp_start⟩, hm_def, hm, hD_core, hA_core, hz13, hzW⟩
  -- Piece 2: p_41
  have hP_p_ex : ∃ ap gp, Parse a_41 p_41 ap gp := by
    rw [hp_start]; exact Parse_V_start a_41 p_tail
  rcases hP_p_ex with ⟨ap, gp, hP_p⟩
  have hb_41_ok : 2 + 4 * wordVal p_41 < (b_41 : Rat) := by
    have hz12 := wordValQ_nonneg p_41
    have hz10_le := two_wordVal_add_wordValQ_le p_41
    have hb41_gt : (25 : Rat) < (b_41 : Rat) := by norm_num [b_41]
    linarith
  rcases Scan_of_Parse hP_p b_41 hb_41_ok with ⟨bp, v_p, hS_p, hbp⟩
  -- Piece 3: s18
  have hS_s18 := Scan_s18 ap bp hbp
  let b_mid0 := 2048 * (bp - 3) + 1972
  -- Piece 4: ds_mid = [K, K] ++ ds_core ++ [Q, K]
  let ds_mid := [K, K] ++ ds_core ++ [Q, K]
  rcases digitVal_mid hm hD_core hA_core with ⟨A_mid, hD_mid, hA_lo, hA_hi⟩
  have hP_s18_all : ∃ a_top g_all, Parse ap (s18 ++ ds_mid) a_top g_all := by
    change ∃ a_top g_all, Parse ap (V :: (s18.tail ++ ds_mid)) a_top g_all
    exact Parse_V_start ap _
  rcases hP_s18_all with ⟨a_top, g_all, hP_all⟩
  have hP_mid_ex : ∃ g_mid, Parse (4 * (ap + 1)) ds_mid a_top g_mid := by
    dsimp [ds_mid] at hP_all ⊢
    exact Parse_s18_split hP_all
  rcases hP_mid_ex with ⟨g_mid, hP_mid⟩
  have hatop_eq := force_a19 hm hP_p hz13 hzW hD_mid hA_lo hA_hi hP_mid
  subst hatop_eq
  have hb_mid0_ok := bound_b_mid0 hm hS_p hbp hz13 hzW rfl hD_mid
  rcases Scan_of_Parse hP_mid b_mid0 hb_mid0_ok with ⟨b_top22, v_mid, hS_mid, hb_top22_ge3⟩
  -- Piece 5: top22
  have hb_top22 : 2 <= b_top22 := by omega
  have hS_top22 := Scan_top22 b_top22 hb_top22
  -- Combine Pieces 2 + 3 + 4 into w_41
  let w_41 := p_41 ++ s18 ++ ds_mid
  let v_w41 := v_p ++ v_s18 ++ v_mid
  let g_w41 := gp + 3 + g_mid
  have h_ap_eq : 4 * ap + 4 = 4 * (ap + 1) := by omega
  rw [h_ap_eq] at hS_s18
  have hS_w41 : Scan a_41 b_41 w_41 (2 ^ 19) b_top22 v_w41 g_w41 := by
    have h23 := Scan_append hS_p hS_s18
    have h234 := Scan_append h23 hS_mid
    simpa [w_41, v_w41, g_w41, List.append_assoc, Nat.add_assoc] using h234
  -- Combine Piece 1 + w_41 + Piece 5
  have h_u_rep0 :
      (head41 ++ p_41 ++ s12 ++ [Q, K, Q, Q, K, Q, K, K] ++ ds_core ++ [Q, K] ++ top22) ++ List.replicate 0 K =
      head41 ++ w_41 ++ top22 := by
    dsimp [w_41, s18, ds_mid, List.replicate]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  have hS_full :
      Scan 0 14 ((head41 ++ p_41 ++ s12 ++ [Q, K, Q, Q, K, Q, K, K] ++ ds_core ++ [Q, K] ++ top22) ++ List.replicate 0 K)
           0 (256 * (b_top22 - 2) + 45) (v_head41 ++ v_w41 ++ s12) (0 + g_w41 + 10) := by
    rw [h_u_rep0]
    exact Scan_append (Scan_append Scan_head41 hS_w41) hS_top22
  -- Closure bounds for p_41' = V :: v_w41 and b_end
  let k := 3 + 3 * gp + 3 * g_mid
  have hk : 3 <= k := by omega
  have hWV_vw : wordPotV v_w41 <= 21 / 4 :=
    bound_zW_p41' hm hS_p hz13 hzW hD_mid hS_mid
  have hz13_vw : wordScale v_w41 * ((2 ^ k : Nat) : Rat) = 1 := by
    have h_z13_w := scan_wordScale_eq hS_w41
    have h_w_eq : wordScale w_41 = 64 := by
      dsimp only [w_41]
      rw [wordScale_append, wordScale_append]
      have h_s18 : wordScale s18 = 1 / 4 := by
        have h := checkScalePow_sound s18 2 0 (by decide)
        norm_num at h
        linarith
      have h_mid := (digitVal_scale_and_val hD_mid).1
      rw [h_s18, h_mid]
      linarith
    rw [h_w_eq] at h_z13_w
    have h_3gw : 3 * g_w41 = k + 6 := by dsimp [g_w41, k]; omega
    have h6 : ((2 ^ 6 : Nat) : Rat) = 64 := by norm_num
    rw [h_3gw, Nat.pow_add, Nat.cast_mul, h6] at h_z13_w
    linarith
  rcases bound_b_end_digitVal hk hb_top22 hS_w41 hz13_vw hWV_vw
    with ⟨A_core', ds_core', hD_core', hlen_core', hA_core', hD_bend⟩
  let da := [Q, K, Q, Q, K, Q, K, K] ++ ds_core' ++ [Q, K] ++ top22
  let u' := V :: (v_head41 ++ v_w41 ++ s12 ++ da)
  refine ⟨u', ⟨0, 256 * (b_top22 - 2) + 45, v_head41 ++ v_w41 ++ s12, da, k + 37, 0 + g_w41 + 10, hS_full, hD_bend, rfl⟩, ?_⟩
  -- Prove Good u'
  let p_41' := V :: v_w41
  let m' := k + 9
  refine ⟨p_41', ds_core', A_core', m', ?_, ⟨v_w41, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [u', p_41', da, v_head41, head41]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · dsimp [m']; omega
  · dsimp [m']; omega
  · have h_m'_4 : m' - 4 = k + 5 := by dsimp [m']; omega
    rwa [h_m'_4]
  · have h_m'_4 : m' - 4 = k + 5 := by dsimp [m']; omega
    rwa [h_m'_4]
  · dsimp only [p_41', m', wordScale]
    have h_m'_split : k + 9 = k + 1 + 8 := by omega
    have h1 : ((2 ^ 1 : Nat) : Rat) = 2 := by norm_num
    have h8 : ((2 ^ 8 : Nat) : Rat) = 256 := by norm_num
    rw [h_m'_split, Nat.pow_add, Nat.pow_add, Nat.cast_mul, Nat.cast_mul, h1, h8]
    linarith
  · dsimp only [p_41']
    rw [wordPot_cons_V]
    exact hWV_vw

theorem reach_N (m : Nat) :
    ∃ N, m <= N ∧ ∃ u,
      multiStep tm (init []) N = some (zCf (evalWords u default)) ∧
      Good u := by
  induction m with
  | zero =>
    rcases init_to_u0 with ⟨k1, hk1⟩
    rcases Rounds_exec rounds_0_9 with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, u_9, multiStep_trans_vkq tm _ _ _ k1 k2 hk1 hk2, good_u9⟩
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

end BusyBeaver.M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RBHHH
