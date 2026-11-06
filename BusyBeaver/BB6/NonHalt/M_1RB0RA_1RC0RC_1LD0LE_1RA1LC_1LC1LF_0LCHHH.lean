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

namespace BusyBeaver.M_1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 4
abbrev E : Fin 6 := 3
abbrev F : Fin 6 := 5
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 8000000

open WordVKQ Word

abbrev evalCCfgVKQ (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep tm n c
theorem zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (evalCCfgVKQ c1) [tm]⊢⁺ (evalCCfgVKQ c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
abbrev pref_cap : BitWord := [1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0]


def zCs : Call -> Fin 6
  | .ch => E
  | .ca => C

def zCR (w : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (w <{{zCs c}} ([1] +> r))

def zCL (w : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> w) {{A}}> r)

def zCf (w : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> pref_cap +> w) {{A}}> default)
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


-- Turnaround zP0..zP126
abbrev tr1 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr2 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr3 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr4 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr5 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr6 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr7 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr8 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr9 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr10 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr11 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr12 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr13 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr14 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr15 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr16 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr17 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr18 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr19 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr20 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr21 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr22 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr23 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr24 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr25 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr26 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr27 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr28 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr29 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr30 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr31 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr32 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr33 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr34 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr35 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr36 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr37 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr38 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr39 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr40 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr41 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr42 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr43 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr44 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr45 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr46 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr47 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr48 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr49 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr50 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr51 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr52 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr53 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr54 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr55 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr56 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr57 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr58 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr59 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr60 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr61 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr62 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr63 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr64 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr65 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr66 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr67 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr68 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr69 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr70 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr71 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr72 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr73 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr74 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr75 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr76 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr77 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr78 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr79 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr80 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr81 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr82 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr83 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr84 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr85 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr86 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr87 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr88 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr89 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr90 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr91 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr92 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr93 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr94 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr95 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr96 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr97 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr98 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr99 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr100 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr101 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr102 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr103 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr104 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr105 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr106 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr107 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr108 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr109 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr110 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr111 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr112 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr113 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr114 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr115 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr116 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr117 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr118 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr119 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr120 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr121 : BitWord := [0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr122 : BitWord := [0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr123 : BitWord := [0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr124 : BitWord := [0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr125 : BitWord := [0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr126 : BitWord := [0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]

theorem zP0 (w : HalfTape) : (zCf w) [tm]⊢⁺ (zCR w .ca (tr1 +> default)) := by
  unfold zCf zCR zCs pref_cap tr1
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
theorem zP14 (w : HalfTape) : (zCL w (tr14 +> default)) [tm]⊢⁺ (zCR w .ca (tr15 +> default)) := by
  unfold zCL zCR zCs tr14 tr15
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP15 (w : HalfTape) : (zCL w (tr15 +> default)) [tm]⊢⁺ (zCR w .ca (tr16 +> default)) := by
  unfold zCL zCR zCs tr15 tr16
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP16 (w : HalfTape) : (zCL w (tr16 +> default)) [tm]⊢⁺ (zCR w .ca (tr17 +> default)) := by
  unfold zCL zCR zCs tr16 tr17
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP17 (w : HalfTape) : (zCL w (tr17 +> default)) [tm]⊢⁺ (zCR w .ca (tr18 +> default)) := by
  unfold zCL zCR zCs tr17 tr18
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP18 (w : HalfTape) : (zCL w (tr18 +> default)) [tm]⊢⁺ (zCR w .ca (tr19 +> default)) := by
  unfold zCL zCR zCs tr18 tr19
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP19 (w : HalfTape) : (zCL w (tr19 +> default)) [tm]⊢⁺ (zCR w .ca (tr20 +> default)) := by
  unfold zCL zCR zCs tr19 tr20
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP20 (w : HalfTape) : (zCL w (tr20 +> default)) [tm]⊢⁺ (zCR w .ca (tr21 +> default)) := by
  unfold zCL zCR zCs tr20 tr21
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP21 (w : HalfTape) : (zCL w (tr21 +> default)) [tm]⊢⁺ (zCR w .ca (tr22 +> default)) := by
  unfold zCL zCR zCs tr21 tr22
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP22 (w : HalfTape) : (zCL w (tr22 +> default)) [tm]⊢⁺ (zCR w .ca (tr23 +> default)) := by
  unfold zCL zCR zCs tr22 tr23
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP23 (w : HalfTape) : (zCL w (tr23 +> default)) [tm]⊢⁺ (zCR w .ca (tr24 +> default)) := by
  unfold zCL zCR zCs tr23 tr24
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP24 (w : HalfTape) : (zCL w (tr24 +> default)) [tm]⊢⁺ (zCR w .ca (tr25 +> default)) := by
  unfold zCL zCR zCs tr24 tr25
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP25 (w : HalfTape) : (zCL w (tr25 +> default)) [tm]⊢⁺ (zCR w .ca (tr26 +> default)) := by
  unfold zCL zCR zCs tr25 tr26
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP26 (w : HalfTape) : (zCL w (tr26 +> default)) [tm]⊢⁺ (zCR w .ca (tr27 +> default)) := by
  unfold zCL zCR zCs tr26 tr27
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP27 (w : HalfTape) : (zCL w (tr27 +> default)) [tm]⊢⁺ (zCR w .ca (tr28 +> default)) := by
  unfold zCL zCR zCs tr27 tr28
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP28 (w : HalfTape) : (zCL w (tr28 +> default)) [tm]⊢⁺ (zCR w .ca (tr29 +> default)) := by
  unfold zCL zCR zCs tr28 tr29
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP29 (w : HalfTape) : (zCL w (tr29 +> default)) [tm]⊢⁺ (zCR w .ca (tr30 +> default)) := by
  unfold zCL zCR zCs tr29 tr30
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP30 (w : HalfTape) : (zCL w (tr30 +> default)) [tm]⊢⁺ (zCR w .ca (tr31 +> default)) := by
  unfold zCL zCR zCs tr30 tr31
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP31 (w : HalfTape) : (zCL w (tr31 +> default)) [tm]⊢⁺ (zCR w .ca (tr32 +> default)) := by
  unfold zCL zCR zCs tr31 tr32
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP32 (w : HalfTape) : (zCL w (tr32 +> default)) [tm]⊢⁺ (zCR w .ca (tr33 +> default)) := by
  unfold zCL zCR zCs tr32 tr33
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP33 (w : HalfTape) : (zCL w (tr33 +> default)) [tm]⊢⁺ (zCR w .ca (tr34 +> default)) := by
  unfold zCL zCR zCs tr33 tr34
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP34 (w : HalfTape) : (zCL w (tr34 +> default)) [tm]⊢⁺ (zCR w .ca (tr35 +> default)) := by
  unfold zCL zCR zCs tr34 tr35
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP35 (w : HalfTape) : (zCL w (tr35 +> default)) [tm]⊢⁺ (zCR w .ca (tr36 +> default)) := by
  unfold zCL zCR zCs tr35 tr36
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP36 (w : HalfTape) : (zCL w (tr36 +> default)) [tm]⊢⁺ (zCR w .ca (tr37 +> default)) := by
  unfold zCL zCR zCs tr36 tr37
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP37 (w : HalfTape) : (zCL w (tr37 +> default)) [tm]⊢⁺ (zCR w .ca (tr38 +> default)) := by
  unfold zCL zCR zCs tr37 tr38
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP38 (w : HalfTape) : (zCL w (tr38 +> default)) [tm]⊢⁺ (zCR w .ca (tr39 +> default)) := by
  unfold zCL zCR zCs tr38 tr39
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP39 (w : HalfTape) : (zCL w (tr39 +> default)) [tm]⊢⁺ (zCR w .ca (tr40 +> default)) := by
  unfold zCL zCR zCs tr39 tr40
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP40 (w : HalfTape) : (zCL w (tr40 +> default)) [tm]⊢⁺ (zCR w .ca (tr41 +> default)) := by
  unfold zCL zCR zCs tr40 tr41
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP41 (w : HalfTape) : (zCL w (tr41 +> default)) [tm]⊢⁺ (zCR w .ca (tr42 +> default)) := by
  unfold zCL zCR zCs tr41 tr42
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP42 (w : HalfTape) : (zCL w (tr42 +> default)) [tm]⊢⁺ (zCR w .ca (tr43 +> default)) := by
  unfold zCL zCR zCs tr42 tr43
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP43 (w : HalfTape) : (zCL w (tr43 +> default)) [tm]⊢⁺ (zCR w .ca (tr44 +> default)) := by
  unfold zCL zCR zCs tr43 tr44
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP44 (w : HalfTape) : (zCL w (tr44 +> default)) [tm]⊢⁺ (zCR w .ca (tr45 +> default)) := by
  unfold zCL zCR zCs tr44 tr45
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP45 (w : HalfTape) : (zCL w (tr45 +> default)) [tm]⊢⁺ (zCR w .ca (tr46 +> default)) := by
  unfold zCL zCR zCs tr45 tr46
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP46 (w : HalfTape) : (zCL w (tr46 +> default)) [tm]⊢⁺ (zCR w .ca (tr47 +> default)) := by
  unfold zCL zCR zCs tr46 tr47
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP47 (w : HalfTape) : (zCL w (tr47 +> default)) [tm]⊢⁺ (zCR w .ca (tr48 +> default)) := by
  unfold zCL zCR zCs tr47 tr48
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP48 (w : HalfTape) : (zCL w (tr48 +> default)) [tm]⊢⁺ (zCR w .ca (tr49 +> default)) := by
  unfold zCL zCR zCs tr48 tr49
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP49 (w : HalfTape) : (zCL w (tr49 +> default)) [tm]⊢⁺ (zCR w .ca (tr50 +> default)) := by
  unfold zCL zCR zCs tr49 tr50
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP50 (w : HalfTape) : (zCL w (tr50 +> default)) [tm]⊢⁺ (zCR w .ca (tr51 +> default)) := by
  unfold zCL zCR zCs tr50 tr51
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP51 (w : HalfTape) : (zCL w (tr51 +> default)) [tm]⊢⁺ (zCR w .ca (tr52 +> default)) := by
  unfold zCL zCR zCs tr51 tr52
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP52 (w : HalfTape) : (zCL w (tr52 +> default)) [tm]⊢⁺ (zCR w .ca (tr53 +> default)) := by
  unfold zCL zCR zCs tr52 tr53
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP53 (w : HalfTape) : (zCL w (tr53 +> default)) [tm]⊢⁺ (zCR w .ca (tr54 +> default)) := by
  unfold zCL zCR zCs tr53 tr54
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP54 (w : HalfTape) : (zCL w (tr54 +> default)) [tm]⊢⁺ (zCR w .ca (tr55 +> default)) := by
  unfold zCL zCR zCs tr54 tr55
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP55 (w : HalfTape) : (zCL w (tr55 +> default)) [tm]⊢⁺ (zCR w .ca (tr56 +> default)) := by
  unfold zCL zCR zCs tr55 tr56
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP56 (w : HalfTape) : (zCL w (tr56 +> default)) [tm]⊢⁺ (zCR w .ca (tr57 +> default)) := by
  unfold zCL zCR zCs tr56 tr57
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP57 (w : HalfTape) : (zCL w (tr57 +> default)) [tm]⊢⁺ (zCR w .ca (tr58 +> default)) := by
  unfold zCL zCR zCs tr57 tr58
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP58 (w : HalfTape) : (zCL w (tr58 +> default)) [tm]⊢⁺ (zCR w .ca (tr59 +> default)) := by
  unfold zCL zCR zCs tr58 tr59
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP59 (w : HalfTape) : (zCL w (tr59 +> default)) [tm]⊢⁺ (zCR w .ca (tr60 +> default)) := by
  unfold zCL zCR zCs tr59 tr60
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP60 (w : HalfTape) : (zCL w (tr60 +> default)) [tm]⊢⁺ (zCR w .ca (tr61 +> default)) := by
  unfold zCL zCR zCs tr60 tr61
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP61 (w : HalfTape) : (zCL w (tr61 +> default)) [tm]⊢⁺ (zCR w .ca (tr62 +> default)) := by
  unfold zCL zCR zCs tr61 tr62
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP62 (w : HalfTape) : (zCL w (tr62 +> default)) [tm]⊢⁺ (zCR w .ca (tr63 +> default)) := by
  unfold zCL zCR zCs tr62 tr63
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP63 (w : HalfTape) : (zCL w (tr63 +> default)) [tm]⊢⁺ (zCR w .ca (tr64 +> default)) := by
  unfold zCL zCR zCs tr63 tr64
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP64 (w : HalfTape) : (zCL w (tr64 +> default)) [tm]⊢⁺ (zCR w .ca (tr65 +> default)) := by
  unfold zCL zCR zCs tr64 tr65
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP65 (w : HalfTape) : (zCL w (tr65 +> default)) [tm]⊢⁺ (zCR w .ca (tr66 +> default)) := by
  unfold zCL zCR zCs tr65 tr66
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP66 (w : HalfTape) : (zCL w (tr66 +> default)) [tm]⊢⁺ (zCR w .ca (tr67 +> default)) := by
  unfold zCL zCR zCs tr66 tr67
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP67 (w : HalfTape) : (zCL w (tr67 +> default)) [tm]⊢⁺ (zCR w .ca (tr68 +> default)) := by
  unfold zCL zCR zCs tr67 tr68
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP68 (w : HalfTape) : (zCL w (tr68 +> default)) [tm]⊢⁺ (zCR w .ca (tr69 +> default)) := by
  unfold zCL zCR zCs tr68 tr69
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP69 (w : HalfTape) : (zCL w (tr69 +> default)) [tm]⊢⁺ (zCR w .ca (tr70 +> default)) := by
  unfold zCL zCR zCs tr69 tr70
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP70 (w : HalfTape) : (zCL w (tr70 +> default)) [tm]⊢⁺ (zCR w .ca (tr71 +> default)) := by
  unfold zCL zCR zCs tr70 tr71
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP71 (w : HalfTape) : (zCL w (tr71 +> default)) [tm]⊢⁺ (zCR w .ca (tr72 +> default)) := by
  unfold zCL zCR zCs tr71 tr72
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP72 (w : HalfTape) : (zCL w (tr72 +> default)) [tm]⊢⁺ (zCR w .ca (tr73 +> default)) := by
  unfold zCL zCR zCs tr72 tr73
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP73 (w : HalfTape) : (zCL w (tr73 +> default)) [tm]⊢⁺ (zCR w .ca (tr74 +> default)) := by
  unfold zCL zCR zCs tr73 tr74
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP74 (w : HalfTape) : (zCL w (tr74 +> default)) [tm]⊢⁺ (zCR w .ca (tr75 +> default)) := by
  unfold zCL zCR zCs tr74 tr75
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP75 (w : HalfTape) : (zCL w (tr75 +> default)) [tm]⊢⁺ (zCR w .ca (tr76 +> default)) := by
  unfold zCL zCR zCs tr75 tr76
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP76 (w : HalfTape) : (zCL w (tr76 +> default)) [tm]⊢⁺ (zCR w .ca (tr77 +> default)) := by
  unfold zCL zCR zCs tr76 tr77
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP77 (w : HalfTape) : (zCL w (tr77 +> default)) [tm]⊢⁺ (zCR w .ca (tr78 +> default)) := by
  unfold zCL zCR zCs tr77 tr78
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP78 (w : HalfTape) : (zCL w (tr78 +> default)) [tm]⊢⁺ (zCR w .ca (tr79 +> default)) := by
  unfold zCL zCR zCs tr78 tr79
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP79 (w : HalfTape) : (zCL w (tr79 +> default)) [tm]⊢⁺ (zCR w .ca (tr80 +> default)) := by
  unfold zCL zCR zCs tr79 tr80
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP80 (w : HalfTape) : (zCL w (tr80 +> default)) [tm]⊢⁺ (zCR w .ca (tr81 +> default)) := by
  unfold zCL zCR zCs tr80 tr81
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP81 (w : HalfTape) : (zCL w (tr81 +> default)) [tm]⊢⁺ (zCR w .ca (tr82 +> default)) := by
  unfold zCL zCR zCs tr81 tr82
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP82 (w : HalfTape) : (zCL w (tr82 +> default)) [tm]⊢⁺ (zCR w .ca (tr83 +> default)) := by
  unfold zCL zCR zCs tr82 tr83
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP83 (w : HalfTape) : (zCL w (tr83 +> default)) [tm]⊢⁺ (zCR w .ca (tr84 +> default)) := by
  unfold zCL zCR zCs tr83 tr84
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP84 (w : HalfTape) : (zCL w (tr84 +> default)) [tm]⊢⁺ (zCR w .ca (tr85 +> default)) := by
  unfold zCL zCR zCs tr84 tr85
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP85 (w : HalfTape) : (zCL w (tr85 +> default)) [tm]⊢⁺ (zCR w .ca (tr86 +> default)) := by
  unfold zCL zCR zCs tr85 tr86
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP86 (w : HalfTape) : (zCL w (tr86 +> default)) [tm]⊢⁺ (zCR w .ca (tr87 +> default)) := by
  unfold zCL zCR zCs tr86 tr87
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP87 (w : HalfTape) : (zCL w (tr87 +> default)) [tm]⊢⁺ (zCR w .ca (tr88 +> default)) := by
  unfold zCL zCR zCs tr87 tr88
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP88 (w : HalfTape) : (zCL w (tr88 +> default)) [tm]⊢⁺ (zCR w .ca (tr89 +> default)) := by
  unfold zCL zCR zCs tr88 tr89
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP89 (w : HalfTape) : (zCL w (tr89 +> default)) [tm]⊢⁺ (zCR w .ca (tr90 +> default)) := by
  unfold zCL zCR zCs tr89 tr90
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP90 (w : HalfTape) : (zCL w (tr90 +> default)) [tm]⊢⁺ (zCR w .ca (tr91 +> default)) := by
  unfold zCL zCR zCs tr90 tr91
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP91 (w : HalfTape) : (zCL w (tr91 +> default)) [tm]⊢⁺ (zCR w .ca (tr92 +> default)) := by
  unfold zCL zCR zCs tr91 tr92
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP92 (w : HalfTape) : (zCL w (tr92 +> default)) [tm]⊢⁺ (zCR w .ca (tr93 +> default)) := by
  unfold zCL zCR zCs tr92 tr93
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP93 (w : HalfTape) : (zCL w (tr93 +> default)) [tm]⊢⁺ (zCR w .ca (tr94 +> default)) := by
  unfold zCL zCR zCs tr93 tr94
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP94 (w : HalfTape) : (zCL w (tr94 +> default)) [tm]⊢⁺ (zCR w .ca (tr95 +> default)) := by
  unfold zCL zCR zCs tr94 tr95
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP95 (w : HalfTape) : (zCL w (tr95 +> default)) [tm]⊢⁺ (zCR w .ca (tr96 +> default)) := by
  unfold zCL zCR zCs tr95 tr96
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP96 (w : HalfTape) : (zCL w (tr96 +> default)) [tm]⊢⁺ (zCR w .ca (tr97 +> default)) := by
  unfold zCL zCR zCs tr96 tr97
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP97 (w : HalfTape) : (zCL w (tr97 +> default)) [tm]⊢⁺ (zCR w .ca (tr98 +> default)) := by
  unfold zCL zCR zCs tr97 tr98
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP98 (w : HalfTape) : (zCL w (tr98 +> default)) [tm]⊢⁺ (zCR w .ca (tr99 +> default)) := by
  unfold zCL zCR zCs tr98 tr99
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP99 (w : HalfTape) : (zCL w (tr99 +> default)) [tm]⊢⁺ (zCR w .ca (tr100 +> default)) := by
  unfold zCL zCR zCs tr99 tr100
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP100 (w : HalfTape) : (zCL w (tr100 +> default)) [tm]⊢⁺ (zCR w .ca (tr101 +> default)) := by
  unfold zCL zCR zCs tr100 tr101
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP101 (w : HalfTape) : (zCL w (tr101 +> default)) [tm]⊢⁺ (zCR w .ca (tr102 +> default)) := by
  unfold zCL zCR zCs tr101 tr102
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP102 (w : HalfTape) : (zCL w (tr102 +> default)) [tm]⊢⁺ (zCR w .ca (tr103 +> default)) := by
  unfold zCL zCR zCs tr102 tr103
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP103 (w : HalfTape) : (zCL w (tr103 +> default)) [tm]⊢⁺ (zCR w .ca (tr104 +> default)) := by
  unfold zCL zCR zCs tr103 tr104
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP104 (w : HalfTape) : (zCL w (tr104 +> default)) [tm]⊢⁺ (zCR w .ca (tr105 +> default)) := by
  unfold zCL zCR zCs tr104 tr105
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP105 (w : HalfTape) : (zCL w (tr105 +> default)) [tm]⊢⁺ (zCR w .ca (tr106 +> default)) := by
  unfold zCL zCR zCs tr105 tr106
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP106 (w : HalfTape) : (zCL w (tr106 +> default)) [tm]⊢⁺ (zCR w .ca (tr107 +> default)) := by
  unfold zCL zCR zCs tr106 tr107
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP107 (w : HalfTape) : (zCL w (tr107 +> default)) [tm]⊢⁺ (zCR w .ca (tr108 +> default)) := by
  unfold zCL zCR zCs tr107 tr108
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP108 (w : HalfTape) : (zCL w (tr108 +> default)) [tm]⊢⁺ (zCR w .ca (tr109 +> default)) := by
  unfold zCL zCR zCs tr108 tr109
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP109 (w : HalfTape) : (zCL w (tr109 +> default)) [tm]⊢⁺ (zCR w .ca (tr110 +> default)) := by
  unfold zCL zCR zCs tr109 tr110
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP110 (w : HalfTape) : (zCL w (tr110 +> default)) [tm]⊢⁺ (zCR w .ca (tr111 +> default)) := by
  unfold zCL zCR zCs tr110 tr111
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP111 (w : HalfTape) : (zCL w (tr111 +> default)) [tm]⊢⁺ (zCR w .ca (tr112 +> default)) := by
  unfold zCL zCR zCs tr111 tr112
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP112 (w : HalfTape) : (zCL w (tr112 +> default)) [tm]⊢⁺ (zCR w .ca (tr113 +> default)) := by
  unfold zCL zCR zCs tr112 tr113
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP113 (w : HalfTape) : (zCL w (tr113 +> default)) [tm]⊢⁺ (zCR w .ca (tr114 +> default)) := by
  unfold zCL zCR zCs tr113 tr114
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP114 (w : HalfTape) : (zCL w (tr114 +> default)) [tm]⊢⁺ (zCR w .ca (tr115 +> default)) := by
  unfold zCL zCR zCs tr114 tr115
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP115 (w : HalfTape) : (zCL w (tr115 +> default)) [tm]⊢⁺ (zCR w .ca (tr116 +> default)) := by
  unfold zCL zCR zCs tr115 tr116
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP116 (w : HalfTape) : (zCL w (tr116 +> default)) [tm]⊢⁺ (zCR w .ca (tr117 +> default)) := by
  unfold zCL zCR zCs tr116 tr117
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP117 (w : HalfTape) : (zCL w (tr117 +> default)) [tm]⊢⁺ (zCR w .ca (tr118 +> default)) := by
  unfold zCL zCR zCs tr117 tr118
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP118 (w : HalfTape) : (zCL w (tr118 +> default)) [tm]⊢⁺ (zCR w .ca (tr119 +> default)) := by
  unfold zCL zCR zCs tr118 tr119
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP119 (w : HalfTape) : (zCL w (tr119 +> default)) [tm]⊢⁺ (zCR w .ca (tr120 +> default)) := by
  unfold zCL zCR zCs tr119 tr120
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP120 (w : HalfTape) : (zCL w (tr120 +> default)) [tm]⊢⁺ (zCR w .ca (tr121 +> default)) := by
  unfold zCL zCR zCs tr120 tr121
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP121 (w : HalfTape) : (zCL w (tr121 +> default)) [tm]⊢⁺ (zCR w .ca (tr122 +> default)) := by
  unfold zCL zCR zCs tr121 tr122
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP122 (w : HalfTape) : (zCL w (tr122 +> default)) [tm]⊢⁺ (zCR w .ca (tr123 +> default)) := by
  unfold zCL zCR zCs tr122 tr123
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP123 (w : HalfTape) : (zCL w (tr123 +> default)) [tm]⊢⁺ (zCR w .ca (tr124 +> default)) := by
  unfold zCL zCR zCs tr123 tr124
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP124 (w : HalfTape) : (zCL w (tr124 +> default)) [tm]⊢⁺ (zCR w .ca (tr125 +> default)) := by
  unfold zCL zCR zCs tr124 tr125
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP125 (w : HalfTape) : (zCL w (tr125 +> default)) [tm]⊢⁺ (zCR w .ca (tr126 +> default)) := by
  unfold zCL zCR zCs tr125 tr126
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute
theorem zP126 (w : HalfTape) : (zCL w (tr126 +> default)) [tm]⊢⁺ (zCf ([1, 1, 0] +> w)) := by
  unfold zCL zCf tr126 pref_cap
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq]
  execute

-- Section 2: Words, Shift Identity, DigitVal, Parse, Scan, Step
theorem segSpec : SegSpec callStep :=
  ⟨seg_ch_V, seg_ca_V, seg_ca_Vp, seg_ch_K, seg_ch_Q,
   seg_ca_VpQ, seg_ca_KpVp, seg_ca_QpVp, seg_ca_Kp, seg_ca_Qp,
   seg_ca_KQ, seg_ca_QQ⟩

abbrev Step := StepB 126
abbrev Rounds := RoundsB 126
abbrev Rounds.refl := @RoundsB.refl 126
abbrev Rounds.next := @RoundsB.next 126
abbrev checkStep := checkStepB 126
abbrev checkStep_sound := checkStepB_sound 126

theorem Side_turnaround {w w' : HalfTape} (h : Side ([Call.ca] ^ 126) w w') :
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
  rcases h with _ | ⟨hc15, h⟩
  rcases h with _ | ⟨hc16, h⟩
  rcases h with _ | ⟨hc17, h⟩
  rcases h with _ | ⟨hc18, h⟩
  rcases h with _ | ⟨hc19, h⟩
  rcases h with _ | ⟨hc20, h⟩
  rcases h with _ | ⟨hc21, h⟩
  rcases h with _ | ⟨hc22, h⟩
  rcases h with _ | ⟨hc23, h⟩
  rcases h with _ | ⟨hc24, h⟩
  rcases h with _ | ⟨hc25, h⟩
  rcases h with _ | ⟨hc26, h⟩
  rcases h with _ | ⟨hc27, h⟩
  rcases h with _ | ⟨hc28, h⟩
  rcases h with _ | ⟨hc29, h⟩
  rcases h with _ | ⟨hc30, h⟩
  rcases h with _ | ⟨hc31, h⟩
  rcases h with _ | ⟨hc32, h⟩
  rcases h with _ | ⟨hc33, h⟩
  rcases h with _ | ⟨hc34, h⟩
  rcases h with _ | ⟨hc35, h⟩
  rcases h with _ | ⟨hc36, h⟩
  rcases h with _ | ⟨hc37, h⟩
  rcases h with _ | ⟨hc38, h⟩
  rcases h with _ | ⟨hc39, h⟩
  rcases h with _ | ⟨hc40, h⟩
  rcases h with _ | ⟨hc41, h⟩
  rcases h with _ | ⟨hc42, h⟩
  rcases h with _ | ⟨hc43, h⟩
  rcases h with _ | ⟨hc44, h⟩
  rcases h with _ | ⟨hc45, h⟩
  rcases h with _ | ⟨hc46, h⟩
  rcases h with _ | ⟨hc47, h⟩
  rcases h with _ | ⟨hc48, h⟩
  rcases h with _ | ⟨hc49, h⟩
  rcases h with _ | ⟨hc50, h⟩
  rcases h with _ | ⟨hc51, h⟩
  rcases h with _ | ⟨hc52, h⟩
  rcases h with _ | ⟨hc53, h⟩
  rcases h with _ | ⟨hc54, h⟩
  rcases h with _ | ⟨hc55, h⟩
  rcases h with _ | ⟨hc56, h⟩
  rcases h with _ | ⟨hc57, h⟩
  rcases h with _ | ⟨hc58, h⟩
  rcases h with _ | ⟨hc59, h⟩
  rcases h with _ | ⟨hc60, h⟩
  rcases h with _ | ⟨hc61, h⟩
  rcases h with _ | ⟨hc62, h⟩
  rcases h with _ | ⟨hc63, h⟩
  rcases h with _ | ⟨hc64, h⟩
  rcases h with _ | ⟨hc65, h⟩
  rcases h with _ | ⟨hc66, h⟩
  rcases h with _ | ⟨hc67, h⟩
  rcases h with _ | ⟨hc68, h⟩
  rcases h with _ | ⟨hc69, h⟩
  rcases h with _ | ⟨hc70, h⟩
  rcases h with _ | ⟨hc71, h⟩
  rcases h with _ | ⟨hc72, h⟩
  rcases h with _ | ⟨hc73, h⟩
  rcases h with _ | ⟨hc74, h⟩
  rcases h with _ | ⟨hc75, h⟩
  rcases h with _ | ⟨hc76, h⟩
  rcases h with _ | ⟨hc77, h⟩
  rcases h with _ | ⟨hc78, h⟩
  rcases h with _ | ⟨hc79, h⟩
  rcases h with _ | ⟨hc80, h⟩
  rcases h with _ | ⟨hc81, h⟩
  rcases h with _ | ⟨hc82, h⟩
  rcases h with _ | ⟨hc83, h⟩
  rcases h with _ | ⟨hc84, h⟩
  rcases h with _ | ⟨hc85, h⟩
  rcases h with _ | ⟨hc86, h⟩
  rcases h with _ | ⟨hc87, h⟩
  rcases h with _ | ⟨hc88, h⟩
  rcases h with _ | ⟨hc89, h⟩
  rcases h with _ | ⟨hc90, h⟩
  rcases h with _ | ⟨hc91, h⟩
  rcases h with _ | ⟨hc92, h⟩
  rcases h with _ | ⟨hc93, h⟩
  rcases h with _ | ⟨hc94, h⟩
  rcases h with _ | ⟨hc95, h⟩
  rcases h with _ | ⟨hc96, h⟩
  rcases h with _ | ⟨hc97, h⟩
  rcases h with _ | ⟨hc98, h⟩
  rcases h with _ | ⟨hc99, h⟩
  rcases h with _ | ⟨hc100, h⟩
  rcases h with _ | ⟨hc101, h⟩
  rcases h with _ | ⟨hc102, h⟩
  rcases h with _ | ⟨hc103, h⟩
  rcases h with _ | ⟨hc104, h⟩
  rcases h with _ | ⟨hc105, h⟩
  rcases h with _ | ⟨hc106, h⟩
  rcases h with _ | ⟨hc107, h⟩
  rcases h with _ | ⟨hc108, h⟩
  rcases h with _ | ⟨hc109, h⟩
  rcases h with _ | ⟨hc110, h⟩
  rcases h with _ | ⟨hc111, h⟩
  rcases h with _ | ⟨hc112, h⟩
  rcases h with _ | ⟨hc113, h⟩
  rcases h with _ | ⟨hc114, h⟩
  rcases h with _ | ⟨hc115, h⟩
  rcases h with _ | ⟨hc116, h⟩
  rcases h with _ | ⟨hc117, h⟩
  rcases h with _ | ⟨hc118, h⟩
  rcases h with _ | ⟨hc119, h⟩
  rcases h with _ | ⟨hc120, h⟩
  rcases h with _ | ⟨hc121, h⟩
  rcases h with _ | ⟨hc122, h⟩
  rcases h with _ | ⟨hc123, h⟩
  rcases h with _ | ⟨hc124, h⟩
  rcases h with _ | ⟨hc125, h⟩
  rcases h with _ | ⟨hc126, h⟩
  cases h
  exact stepPlus_trans_vkq (zP0 w) (stepPlus_trans_vkq (hc1 (tr1 +> default)) (stepPlus_trans_vkq (zP1 _) (stepPlus_trans_vkq (hc2 (tr2 +> default)) (stepPlus_trans_vkq (zP2 _) (stepPlus_trans_vkq (hc3 (tr3 +> default)) (stepPlus_trans_vkq (zP3 _) (stepPlus_trans_vkq (hc4 (tr4 +> default)) (stepPlus_trans_vkq (zP4 _) (stepPlus_trans_vkq (hc5 (tr5 +> default)) (stepPlus_trans_vkq (zP5 _) (stepPlus_trans_vkq (hc6 (tr6 +> default)) (stepPlus_trans_vkq (zP6 _) (stepPlus_trans_vkq (hc7 (tr7 +> default)) (stepPlus_trans_vkq (zP7 _) (stepPlus_trans_vkq (hc8 (tr8 +> default)) (stepPlus_trans_vkq (zP8 _) (stepPlus_trans_vkq (hc9 (tr9 +> default)) (stepPlus_trans_vkq (zP9 _) (stepPlus_trans_vkq (hc10 (tr10 +> default)) (stepPlus_trans_vkq (zP10 _) (stepPlus_trans_vkq (hc11 (tr11 +> default)) (stepPlus_trans_vkq (zP11 _) (stepPlus_trans_vkq (hc12 (tr12 +> default)) (stepPlus_trans_vkq (zP12 _) (stepPlus_trans_vkq (hc13 (tr13 +> default)) (stepPlus_trans_vkq (zP13 _) (stepPlus_trans_vkq (hc14 (tr14 +> default)) (stepPlus_trans_vkq (zP14 _) (stepPlus_trans_vkq (hc15 (tr15 +> default)) (stepPlus_trans_vkq (zP15 _) (stepPlus_trans_vkq (hc16 (tr16 +> default)) (stepPlus_trans_vkq (zP16 _) (stepPlus_trans_vkq (hc17 (tr17 +> default)) (stepPlus_trans_vkq (zP17 _) (stepPlus_trans_vkq (hc18 (tr18 +> default)) (stepPlus_trans_vkq (zP18 _) (stepPlus_trans_vkq (hc19 (tr19 +> default)) (stepPlus_trans_vkq (zP19 _) (stepPlus_trans_vkq (hc20 (tr20 +> default)) (stepPlus_trans_vkq (zP20 _) (stepPlus_trans_vkq (hc21 (tr21 +> default)) (stepPlus_trans_vkq (zP21 _) (stepPlus_trans_vkq (hc22 (tr22 +> default)) (stepPlus_trans_vkq (zP22 _) (stepPlus_trans_vkq (hc23 (tr23 +> default)) (stepPlus_trans_vkq (zP23 _) (stepPlus_trans_vkq (hc24 (tr24 +> default)) (stepPlus_trans_vkq (zP24 _) (stepPlus_trans_vkq (hc25 (tr25 +> default)) (stepPlus_trans_vkq (zP25 _) (stepPlus_trans_vkq (hc26 (tr26 +> default)) (stepPlus_trans_vkq (zP26 _) (stepPlus_trans_vkq (hc27 (tr27 +> default)) (stepPlus_trans_vkq (zP27 _) (stepPlus_trans_vkq (hc28 (tr28 +> default)) (stepPlus_trans_vkq (zP28 _) (stepPlus_trans_vkq (hc29 (tr29 +> default)) (stepPlus_trans_vkq (zP29 _) (stepPlus_trans_vkq (hc30 (tr30 +> default)) (stepPlus_trans_vkq (zP30 _) (stepPlus_trans_vkq (hc31 (tr31 +> default)) (stepPlus_trans_vkq (zP31 _) (stepPlus_trans_vkq (hc32 (tr32 +> default)) (stepPlus_trans_vkq (zP32 _) (stepPlus_trans_vkq (hc33 (tr33 +> default)) (stepPlus_trans_vkq (zP33 _) (stepPlus_trans_vkq (hc34 (tr34 +> default)) (stepPlus_trans_vkq (zP34 _) (stepPlus_trans_vkq (hc35 (tr35 +> default)) (stepPlus_trans_vkq (zP35 _) (stepPlus_trans_vkq (hc36 (tr36 +> default)) (stepPlus_trans_vkq (zP36 _) (stepPlus_trans_vkq (hc37 (tr37 +> default)) (stepPlus_trans_vkq (zP37 _) (stepPlus_trans_vkq (hc38 (tr38 +> default)) (stepPlus_trans_vkq (zP38 _) (stepPlus_trans_vkq (hc39 (tr39 +> default)) (stepPlus_trans_vkq (zP39 _) (stepPlus_trans_vkq (hc40 (tr40 +> default)) (stepPlus_trans_vkq (zP40 _) (stepPlus_trans_vkq (hc41 (tr41 +> default)) (stepPlus_trans_vkq (zP41 _) (stepPlus_trans_vkq (hc42 (tr42 +> default)) (stepPlus_trans_vkq (zP42 _) (stepPlus_trans_vkq (hc43 (tr43 +> default)) (stepPlus_trans_vkq (zP43 _) (stepPlus_trans_vkq (hc44 (tr44 +> default)) (stepPlus_trans_vkq (zP44 _) (stepPlus_trans_vkq (hc45 (tr45 +> default)) (stepPlus_trans_vkq (zP45 _) (stepPlus_trans_vkq (hc46 (tr46 +> default)) (stepPlus_trans_vkq (zP46 _) (stepPlus_trans_vkq (hc47 (tr47 +> default)) (stepPlus_trans_vkq (zP47 _) (stepPlus_trans_vkq (hc48 (tr48 +> default)) (stepPlus_trans_vkq (zP48 _) (stepPlus_trans_vkq (hc49 (tr49 +> default)) (stepPlus_trans_vkq (zP49 _) (stepPlus_trans_vkq (hc50 (tr50 +> default)) (stepPlus_trans_vkq (zP50 _) (stepPlus_trans_vkq (hc51 (tr51 +> default)) (stepPlus_trans_vkq (zP51 _) (stepPlus_trans_vkq (hc52 (tr52 +> default)) (stepPlus_trans_vkq (zP52 _) (stepPlus_trans_vkq (hc53 (tr53 +> default)) (stepPlus_trans_vkq (zP53 _) (stepPlus_trans_vkq (hc54 (tr54 +> default)) (stepPlus_trans_vkq (zP54 _) (stepPlus_trans_vkq (hc55 (tr55 +> default)) (stepPlus_trans_vkq (zP55 _) (stepPlus_trans_vkq (hc56 (tr56 +> default)) (stepPlus_trans_vkq (zP56 _) (stepPlus_trans_vkq (hc57 (tr57 +> default)) (stepPlus_trans_vkq (zP57 _) (stepPlus_trans_vkq (hc58 (tr58 +> default)) (stepPlus_trans_vkq (zP58 _) (stepPlus_trans_vkq (hc59 (tr59 +> default)) (stepPlus_trans_vkq (zP59 _) (stepPlus_trans_vkq (hc60 (tr60 +> default)) (stepPlus_trans_vkq (zP60 _) (stepPlus_trans_vkq (hc61 (tr61 +> default)) (stepPlus_trans_vkq (zP61 _) (stepPlus_trans_vkq (hc62 (tr62 +> default)) (stepPlus_trans_vkq (zP62 _) (stepPlus_trans_vkq (hc63 (tr63 +> default)) (stepPlus_trans_vkq (zP63 _) (stepPlus_trans_vkq (hc64 (tr64 +> default)) (stepPlus_trans_vkq (zP64 _) (stepPlus_trans_vkq (hc65 (tr65 +> default)) (stepPlus_trans_vkq (zP65 _) (stepPlus_trans_vkq (hc66 (tr66 +> default)) (stepPlus_trans_vkq (zP66 _) (stepPlus_trans_vkq (hc67 (tr67 +> default)) (stepPlus_trans_vkq (zP67 _) (stepPlus_trans_vkq (hc68 (tr68 +> default)) (stepPlus_trans_vkq (zP68 _) (stepPlus_trans_vkq (hc69 (tr69 +> default)) (stepPlus_trans_vkq (zP69 _) (stepPlus_trans_vkq (hc70 (tr70 +> default)) (stepPlus_trans_vkq (zP70 _) (stepPlus_trans_vkq (hc71 (tr71 +> default)) (stepPlus_trans_vkq (zP71 _) (stepPlus_trans_vkq (hc72 (tr72 +> default)) (stepPlus_trans_vkq (zP72 _) (stepPlus_trans_vkq (hc73 (tr73 +> default)) (stepPlus_trans_vkq (zP73 _) (stepPlus_trans_vkq (hc74 (tr74 +> default)) (stepPlus_trans_vkq (zP74 _) (stepPlus_trans_vkq (hc75 (tr75 +> default)) (stepPlus_trans_vkq (zP75 _) (stepPlus_trans_vkq (hc76 (tr76 +> default)) (stepPlus_trans_vkq (zP76 _) (stepPlus_trans_vkq (hc77 (tr77 +> default)) (stepPlus_trans_vkq (zP77 _) (stepPlus_trans_vkq (hc78 (tr78 +> default)) (stepPlus_trans_vkq (zP78 _) (stepPlus_trans_vkq (hc79 (tr79 +> default)) (stepPlus_trans_vkq (zP79 _) (stepPlus_trans_vkq (hc80 (tr80 +> default)) (stepPlus_trans_vkq (zP80 _) (stepPlus_trans_vkq (hc81 (tr81 +> default)) (stepPlus_trans_vkq (zP81 _) (stepPlus_trans_vkq (hc82 (tr82 +> default)) (stepPlus_trans_vkq (zP82 _) (stepPlus_trans_vkq (hc83 (tr83 +> default)) (stepPlus_trans_vkq (zP83 _) (stepPlus_trans_vkq (hc84 (tr84 +> default)) (stepPlus_trans_vkq (zP84 _) (stepPlus_trans_vkq (hc85 (tr85 +> default)) (stepPlus_trans_vkq (zP85 _) (stepPlus_trans_vkq (hc86 (tr86 +> default)) (stepPlus_trans_vkq (zP86 _) (stepPlus_trans_vkq (hc87 (tr87 +> default)) (stepPlus_trans_vkq (zP87 _) (stepPlus_trans_vkq (hc88 (tr88 +> default)) (stepPlus_trans_vkq (zP88 _) (stepPlus_trans_vkq (hc89 (tr89 +> default)) (stepPlus_trans_vkq (zP89 _) (stepPlus_trans_vkq (hc90 (tr90 +> default)) (stepPlus_trans_vkq (zP90 _) (stepPlus_trans_vkq (hc91 (tr91 +> default)) (stepPlus_trans_vkq (zP91 _) (stepPlus_trans_vkq (hc92 (tr92 +> default)) (stepPlus_trans_vkq (zP92 _) (stepPlus_trans_vkq (hc93 (tr93 +> default)) (stepPlus_trans_vkq (zP93 _) (stepPlus_trans_vkq (hc94 (tr94 +> default)) (stepPlus_trans_vkq (zP94 _) (stepPlus_trans_vkq (hc95 (tr95 +> default)) (stepPlus_trans_vkq (zP95 _) (stepPlus_trans_vkq (hc96 (tr96 +> default)) (stepPlus_trans_vkq (zP96 _) (stepPlus_trans_vkq (hc97 (tr97 +> default)) (stepPlus_trans_vkq (zP97 _) (stepPlus_trans_vkq (hc98 (tr98 +> default)) (stepPlus_trans_vkq (zP98 _) (stepPlus_trans_vkq (hc99 (tr99 +> default)) (stepPlus_trans_vkq (zP99 _) (stepPlus_trans_vkq (hc100 (tr100 +> default)) (stepPlus_trans_vkq (zP100 _) (stepPlus_trans_vkq (hc101 (tr101 +> default)) (stepPlus_trans_vkq (zP101 _) (stepPlus_trans_vkq (hc102 (tr102 +> default)) (stepPlus_trans_vkq (zP102 _) (stepPlus_trans_vkq (hc103 (tr103 +> default)) (stepPlus_trans_vkq (zP103 _) (stepPlus_trans_vkq (hc104 (tr104 +> default)) (stepPlus_trans_vkq (zP104 _) (stepPlus_trans_vkq (hc105 (tr105 +> default)) (stepPlus_trans_vkq (zP105 _) (stepPlus_trans_vkq (hc106 (tr106 +> default)) (stepPlus_trans_vkq (zP106 _) (stepPlus_trans_vkq (hc107 (tr107 +> default)) (stepPlus_trans_vkq (zP107 _) (stepPlus_trans_vkq (hc108 (tr108 +> default)) (stepPlus_trans_vkq (zP108 _) (stepPlus_trans_vkq (hc109 (tr109 +> default)) (stepPlus_trans_vkq (zP109 _) (stepPlus_trans_vkq (hc110 (tr110 +> default)) (stepPlus_trans_vkq (zP110 _) (stepPlus_trans_vkq (hc111 (tr111 +> default)) (stepPlus_trans_vkq (zP111 _) (stepPlus_trans_vkq (hc112 (tr112 +> default)) (stepPlus_trans_vkq (zP112 _) (stepPlus_trans_vkq (hc113 (tr113 +> default)) (stepPlus_trans_vkq (zP113 _) (stepPlus_trans_vkq (hc114 (tr114 +> default)) (stepPlus_trans_vkq (zP114 _) (stepPlus_trans_vkq (hc115 (tr115 +> default)) (stepPlus_trans_vkq (zP115 _) (stepPlus_trans_vkq (hc116 (tr116 +> default)) (stepPlus_trans_vkq (zP116 _) (stepPlus_trans_vkq (hc117 (tr117 +> default)) (stepPlus_trans_vkq (zP117 _) (stepPlus_trans_vkq (hc118 (tr118 +> default)) (stepPlus_trans_vkq (zP118 _) (stepPlus_trans_vkq (hc119 (tr119 +> default)) (stepPlus_trans_vkq (zP119 _) (stepPlus_trans_vkq (hc120 (tr120 +> default)) (stepPlus_trans_vkq (zP120 _) (stepPlus_trans_vkq (hc121 (tr121 +> default)) (stepPlus_trans_vkq (zP121 _) (stepPlus_trans_vkq (hc122 (tr122 +> default)) (stepPlus_trans_vkq (zP122 _) (stepPlus_trans_vkq (hc123 (tr123 +> default)) (stepPlus_trans_vkq (zP123 _) (stepPlus_trans_vkq (hc124 (tr124 +> default)) (stepPlus_trans_vkq (zP124 _) (stepPlus_trans_vkq (hc125 (tr125 +> default)) (stepPlus_trans_vkq (zP125 _) (stepPlus_trans_vkq (hc126 (tr126 +> default)) (zP126 w'))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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

def u_0 : List Word := [K,K,K,K,V,K,Q,Q]
def tags_0 : List Nat := [3,3,3,3,2,5]
def da_0 : List Word := [Q,K,K,Q]
def n_0 : Nat := 0
def u_1 : List Word := [V,K,Q,Q,Q,Q,V,V,Q,K,K,Q]
def tags_1 : List Nat := [1,5,5,0,0,3,3,5]
def da_1 : List Word := [Q,K,Q,Q,Q,K,Q,Q,Q,Q]
def n_1 : Nat := 0
def u_2 : List Word := [V,K,V,V,V,V,V,K,Q,V,Q,K,Q,Q,Q,K,Q,Q,Q,Q]
def tags_2 : List Nat := [1,0,0,0,0,1,3,0,4,5,4,5,5]
def da_2 : List Word := [Q,K,Q,Q,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_2 : Nat := 0
def u_3 : List Word := [V,K,V,V,V,V,V,K,V,Q,V,V,V,V,V,V,Q,K,Q,Q,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_3 : List Nat := [1,0,0,0,0,1,0,3,0,0,0,0,0,0,3,3,5,3,4,5,3,4,5,5]
def da_3 : List Word := [Q,K,Q,Q,K,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_3 : Nat := 0
def u_4 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,Q,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,K,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_4 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,3,0,3,0,0,3,0,0,0,3,4,4,5,5,3,5,3,4,5,5]
def da_4 : List Word := [Q,K,Q,Q,Q,Q,K,Q,K,K,K,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_4 : Nat := 0
def u_5 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,Q,V,K,V,V,K,V,V,V,K,V,V,V,V,Q,V,Q,V,V,V,Q,K,Q,Q,Q,Q,K,Q,K,K,K,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_5 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,3,1,0,1,0,0,1,0,0,0,0,3,0,3,0,0,0,3,3,5,3,3,5,4,3,5,3,4,5,3,4,5,5]
def da_5 : List Word := [Q,K,Q,Q,K,K,Q,K,K,Q,K,K,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_5 : Nat := 0
def u_6 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,K,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,K,V,V,V,K,Q,V,Q,Q,V,V,K,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,K,K,Q,K,K,Q,K,K,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_6 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,5,0,1,0,0,1,0,0,0,0,1,2,0,0,1,3,0,3,3,0,1,0,3,0,0,3,0,0,0,3,4,3,4,4,4,3,3,4,5,3,4,5,3,4,5,5]
def da_6 : List Word := [Q,K,Q,Q,K,Q,K,K,K,Q,K,K,K,Q,K,Q,K,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_6 : Nat := 0
def u_7 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,Q,V,V,V,K,V,Q,V,K,Q,V,K,V,V,K,V,V,K,V,V,V,K,V,K,V,V,V,K,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,K,Q,K,K,K,Q,K,K,K,Q,K,Q,K,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_7 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,3,0,0,1,0,3,0,5,2,0,1,0,1,0,0,1,2,0,0,1,3,0,0,3,0,0,3,0,0,0,3,4,3,3,5,3,4,5,4,4,3,3,3,4,5,5,3,4,5,3,4,5,5]
def da_7 : List Word := [Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_7 : Nat := 0
def u_8 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,Q,V,V,K,V,V,K,V,V,V,K,V,Q,V,V,V,K,V,Q,V,V,K,V,V,K,V,V,V,K,V,K,K,V,Q,V,V,V,V,K,Q,Q,V,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_8 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,0,3,0,1,0,1,0,0,1,0,3,0,0,1,0,3,0,1,0,1,0,0,1,0,5,0,3,0,0,0,1,4,0,0,0,3,0,0,3,0,0,0,3,4,4,3,5,5,5,3,3,3,3,3,3,5,3,5,4,4,5,3,5,5,3,4,5,3,4,5,5]
def da_8 : List Word := [Q,K,Q,Q,Q,K,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_8 : Nat := 0
def u_9 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,V,K,V,V,K,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,Q,K,K,K,Q,Q,V,Q,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,K,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_9 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,0,1,2,0,1,0,0,1,0,1,0,1,0,1,2,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,3,3,3,3,5,0,3,0,0,0,0,3,0,0,3,0,0,3,0,0,0,3,4,4,3,4,5,4,3,5,5,4,3,4,4,3,3,3,3,3,3,3,4,5,4,4,5,3,5,5,3,4,5,3,4,5,5]
def da_9 : List Word := [Q,K,Q,Q,Q,K,Q,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,K,Q,K,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_9 : Nat := 0
def u_10 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,Q,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,V,Q,V,V,K,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,Q,K,Q,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,K,V,V,V,K,V,V,K,Q,K,Q,K,K,Q,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,K,Q,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,K,Q,K,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_10 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,0,1,0,3,0,1,0,0,1,0,1,0,1,0,1,0,3,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,1,3,4,0,1,0,0,0,1,0,1,0,1,0,0,1,0,1,0,0,1,0,0,1,0,1,3,4,3,4,0,0,0,0,0,3,0,0,3,0,0,3,0,0,0,3,4,4,3,4,4,3,3,3,4,5,3,3,3,4,5,4,3,5,4,3,3,3,3,4,3,4,3,3,3,4,5,4,4,5,3,5,5,3,4,5,3,4,5,5]
def da_10 : List Word := [Q,K,Q,Q,Q,K,Q,K,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,K,K,Q,Q,K,Q,Q,K,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,Q,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_10 : Nat := 0
def u_11 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,K,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,Q,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,K,V,V,V,K,V,V,K,V,Q,V,K,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,Q,Q,V,V,Q,Q,K,V,V,V,K,V,V,K,K,Q,K,V,K,V,K,K,K,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,K,Q,K,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,K,K,Q,Q,K,Q,Q,K,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,Q,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_11 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,0,1,0,1,2,0,0,1,0,1,0,1,0,1,0,1,2,0,0,1,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,1,0,3,0,1,0,0,0,1,0,1,0,1,0,0,1,0,1,0,0,1,0,0,1,0,1,0,3,1,0,0,0,0,0,1,0,1,0,1,0,0,1,0,1,0,1,4,0,0,3,5,0,0,1,0,0,5,3,3,1,0,5,3,0,0,0,0,0,3,0,0,3,0,0,3,0,0,0,3,4,4,3,4,3,4,4,5,3,3,4,3,4,3,3,3,5,4,4,3,4,3,4,5,4,3,5,4,3,5,5,3,4,3,3,3,3,4,5,4,4,5,3,5,5,3,4,5,3,4,5,5]
def da_11 : List Word := [Q,K,Q,Q,Q,K,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,K,Q,Q,K,K,Q,K,K,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,K,K,K,Q,Q,K,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,Q,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_11 : Nat := 0
def u_12 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,Q,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,Q,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,K,V,V,V,K,V,V,K,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,Q,Q,K,V,V,V,Q,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,K,V,V,V,Q,Q,V,K,V,K,K,Q,V,V,V,K,V,K,V,V,V,K,V,V,K,V,V,Q,V,K,Q,K,K,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,K,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,K,Q,Q,K,K,Q,K,K,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,K,K,K,Q,Q,K,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,Q,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def tags_12 : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,0,1,0,1,0,3,0,0,1,0,1,0,1,0,1,0,1,0,3,0,0,1,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,1,0,1,2,0,0,0,1,0,1,0,1,0,0,1,0,1,0,0,1,0,0,1,0,1,0,0,5,0,0,0,0,0,1,0,1,0,1,0,0,1,0,1,0,1,0,0,0,1,0,0,1,0,0,0,0,4,3,0,0,0,3,0,0,0,0,1,0,1,0,1,0,0,1,0,1,2,0,0,0,4,1,2,4,0,0,1,2,0,0,1,0,1,0,0,3,0,5,3,3,0,0,0,0,0,3,0,0,3,0,0,3,0,0,0,3,4,4,3,4,3,5,5,5,5,4,5,3,4,3,5,3,3,4,3,3,3,5,5,4,3,4,3,4,3,3,3,5,4,4,3,4,3,4,5,4,3,5,4,3,3,3,3,4,3,4,3,3,3,4,5,4,4,5,3,5,5,3,4,5,3,4,5,5]
def da_12 : List Word := [Q,K,Q,Q,Q,K,Q,K,K,K,K,Q,Q,K,K,K,K,Q,Q,Q,K,Q,Q,K,K,K,Q,K,K,Q,Q,K,Q,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,K,K,K,Q,K,Q,K,Q,K,K,Q,K,K,K,Q,Q,K,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def n_12 : Nat := 0
def u_13 : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,Q,V,V,V,V,V,K,V,Q,V,V,V,V,K,V,Q,V,V,V,K,V,V,K,V,V,V,K,V,V,Q,Q,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,K,V,V,V,V,V,V,Q,V,K,V,Q,Q,V,K,Q,K,V,V,V,K,V,K,V,K,K,Q,V,V,V,K,V,K,V,V,V,K,V,V,K,K,Q,K,V,K,V,K,K,Q,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,K,Q,K,K,K,K,Q,Q,K,K,K,K,Q,Q,Q,K,Q,Q,K,K,K,Q,K,K,Q,Q,K,Q,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,K,K,K,Q,K,Q,K,Q,K,K,Q,K,K,K,Q,Q,K,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]

def head_w : List Word := [V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,V]
def tags_head : List Nat := [1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,0]
def v_head : List Word := [K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V]
def a_head : Nat := 536870911
def b_head : Nat := 65984224292
def A_top : Nat := 128875438

def s_base : List Word := [V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V]
def s_full : List Word := s_base ++ [Q,K,Q,Q,Q,K,Q,K]
def tags_s : List Nat := [0,0,0,0,0,3,0,0,3,0,0,3,0,0,0,3,4,4,3,4]
def v_s : List Word := [V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V]

def top_base : List Word := [K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q]
def top_full : List Word := top_base ++ []
def tags_top : List Nat := [4,5,4,4,5,3,5,5,3,4,5,3,4,5,5]

def p_init : List Word := [V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,Q,V,V,V,V,V,K,V,Q,V,V,V,V,K,V,Q,V,V,V,K,V,V,K,V,V,V,K,V,V,Q,Q,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,V,K,V,V,V,V,V,V,Q,V,K,V,Q,Q,V,K,Q,K,V,V,V,K,V,K,V,K,K,Q,V,V,V,K,V,K,V,V,V,K,V,V,K,K,Q,K,V,K,V,K,K,Q]
def ds_core_init : List Word := [K,K,Q,Q,K,K,K,K,Q,Q,Q,K,Q,Q,K,K,K,Q,K,K,Q,Q,K,Q,K,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,K,K,K,Q,K,Q,K,Q,K,K,Q,K,K,K,Q,Q,K,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,K,K]
def A_core_init : Nat := 69234923593231798136558728972

def zInitCCfg : CCfg := ⟨0, 0, [], []⟩
def zMidCCfg_1 : CCfg := ⟨2, 1, [0,0,1,0,0,0,1,0,1,0,1], [1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]⟩
def zMidCCfg_2 : CCfg := ⟨3, 0, [0,0,0,0,0,0,1], [1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]⟩
def zMidCCfg_3 : CCfg := ⟨4, 0, [0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,1,0,1,1], [0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]⟩
def zMidCCfg_4 : CCfg := ⟨0, 0, [0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,0,0,1,0,1,1,0,0,0,0,0,0,1], [1,0,1,0,1,1,1,0,1,0,1,0,1]⟩
def zHitCCfg : CCfg := ⟨0, 0, [0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,0,1], []⟩

set_option maxRecDepth 200000 in
theorem zCm_init_0 : zCm zInitCCfg 1000 = some zMidCCfg_1 := by decide
set_option maxRecDepth 200000 in
theorem zCm_init_1 : zCm zMidCCfg_1 1000 = some zMidCCfg_2 := by decide
set_option maxRecDepth 200000 in
theorem zCm_init_2 : zCm zMidCCfg_2 1000 = some zMidCCfg_3 := by decide
set_option maxRecDepth 200000 in
theorem zCm_init_3 : zCm zMidCCfg_3 1000 = some zMidCCfg_4 := by decide
set_option maxRecDepth 200000 in
theorem zCm_init_4 : zCm zMidCCfg_4 347 = some zHitCCfg := by decide

theorem init_to_u0 : (init []) [tm]⊢* zCf (evalWords u_0 default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = evalCCfgVKQ zInitCCfg := rfl
  have h1 : evalCCfgVKQ zHitCCfg = zCf (evalWords u_0 default) := by
    dsimp [evalCCfgVKQ, zHitCCfg, zCf, pref_cap, u_0, evalWords, V_u, K_u, Q_u]
    simp only [List.cons_append, List.nil_append, append_cons, append_nil, zero_cons_default_vkq, default_head_vkq, default_tail_vkq]
  have hPlus := stepPlus_trans_vkq (zTc (by decide : 0 < 1000) zCm_init_0) (stepPlus_trans_vkq (zTc (by decide : 0 < 1000) zCm_init_1) (stepPlus_trans_vkq (zTc (by decide : 0 < 1000) zCm_init_2) (stepPlus_trans_vkq (zTc (by decide : 0 < 1000) zCm_init_3) (zTc (by decide : 0 < 347) zCm_init_4))))
  rw [<- h0, h1] at hPlus
  exact stepStar_of_stepPlus_vkq hPlus

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
set_option maxRecDepth 200000 in
theorem step_9 : Step u_9 u_10 := checkStep_sound n_9 tags_9 u_9 da_9 u_10 (by decide)
set_option maxRecDepth 200000 in
theorem step_10 : Step u_10 u_11 := checkStep_sound n_10 tags_10 u_10 da_10 u_11 (by decide)
set_option maxRecDepth 200000 in
theorem step_11 : Step u_11 u_12 := checkStep_sound n_11 tags_11 u_11 da_11 u_12 (by decide)
set_option maxRecDepth 200000 in
theorem step_12 : Step u_12 u_13 := checkStep_sound n_12 tags_12 u_12 da_12 u_13 (by decide)

theorem rounds_0_13 : Rounds u_0 u_13 :=
  Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3 (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7 (Rounds.next step_8 (Rounds.next step_9 (Rounds.next step_10 (Rounds.next step_11 (Rounds.next step_12 (Rounds.refl u_13)))))))))))))

abbrev Good (u : List Word) : Prop :=
  ∃ p_w ds_core A_core m,
    u = head_w ++ p_w ++ s_base ++ [Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core ++ top_base ∧
    (∃ p_tail, p_w = V :: p_tail) ∧
    m = 1 + ds_core.length ∧
    11 <= m ∧
    DigitVal A_core (m - 1) ds_core ∧
    A_core * 512 <= 35 * 2 ^ (m - 1) ∧
    wordScale p_w * ((2 ^ m : Nat) : Rat) = 512 ∧
    wordPot p_w <= 29 / 4

set_option maxRecDepth 200000 in
theorem good_u13 : Good u_13 := by
  refine ⟨p_init, ds_core_init, A_core_init, 101, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨p_init.tail, rfl⟩
  · decide
  · decide
  · exact checkDg_sound A_core_init ds_core_init (by decide)
  · decide
  · have h := checkScalePow_sound p_init 101 9 (by decide)
    norm_num at h
    exact h
  · have h := checkWordPotLe_sound p_init 29 4 (by decide)
    norm_num at h
    linarith

set_option maxRecDepth 200000 in
theorem Scan_head : Scan 0 126 head_w a_head b_head v_head 0 := by
  have h := checkAffineScan_sound tags_head 0 0 0 126 head_w 0 a_head 0 b_head v_head 0 0 0 (by decide)
  simpa using h

theorem v_head_eq : V :: v_head = head_w ++ [V] := rfl

theorem Scan_s (ap bp : Nat) (hbp : 3 <= bp) :
    Scan ap bp s_full (2 * ap + 2) (1024 * (bp - 3) + 908) v_s 3 := by
  have h := checkAffineScan_sound tags_s 1 0 1 3 s_full 2 2 1024 908 v_s 3 ap (bp - 3) (by decide)
  have h_bp : 1 * (bp - 3) + 3 = bp := by omega
  have h_ap : 1 * ap + 0 = ap := by omega
  rwa [h_ap, h_bp] at h

theorem Scan_top (b_top : Nat) (hb : 2 <= b_top) :
    Scan (2 ^ 21) b_top top_full 0 (512 * (b_top - 2) + 93) s_base 12 := by
  have h := checkAffineScan_sound tags_top 0 (2 ^ 21) 1 2 top_full 0 0 512 93 s_base 12 0 (b_top - 2) (by decide)
  have h_in : 1 * (b_top - 2) + 2 = b_top := by omega
  dsimp at h
  rwa [h_in] at h

theorem Parse_s_split {ap a_end g_all : Nat} {rest : List Word}
    (h : Parse ap (s_full ++ K :: rest) a_end g_all) :
    ∃ g_mid, Parse (2 * (ap + 1)) (K :: rest) a_end g_mid := by
  change Parse ap ([V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,K,Q,Q,Q,K,Q,K,K] ++ rest) a_end g_all at h
  simp only [List.cons_append, List.nil_append] at h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VQ_inv h
  cases h with
  | @D _ q1_1 _ _ _ _ _ hq1_1 h =>
    have hq1_1_eq : q1_1 = 16 + ap * 16 := by dsimp [dVal] at hq1_1; omega
    subst hq1_1_eq
    have h := Parse_VV_inv h
    have h := Parse_VQ_inv h
    cases h with
    | @D _ q1_2 _ _ _ _ _ hq1_2 h =>
      have hq1_2_eq : q1_2 = 34 + ap * 32 := by dsimp [dVal] at hq1_2; omega
      subst hq1_2_eq
      have h := Parse_VV_inv h
      have h := Parse_VQ_inv h
      cases h with
      | @D _ q1_3 _ _ _ _ _ hq1_3 h =>
        have hq1_3_eq : q1_3 = 70 + ap * 64 := by dsimp [dVal] at hq1_3; omega
        subst hq1_3_eq
        have h := Parse_VV_inv h
        have h := Parse_VV_inv h
        have h := Parse_VQ_inv h
        cases h with
        | @D _ q1_4 _ _ _ _ _ hq1_4 h =>
          have hq1_4_eq : q1_4 = 284 + ap * 256 := by dsimp [dVal] at hq1_4; omega
          subst hq1_4_eq
          cases h with
          | @D _ q1_5 _ _ _ _ _ hq1_5 h =>
            have hq1_5_eq : q1_5 = 142 + ap * 128 := by dsimp [dVal] at hq1_5; omega
            subst hq1_5_eq
            cases h with
            | D _ hq1_6 _ => dsimp [dVal] at hq1_6; omega
            | P _ _ hq2_6 _ => dsimp [dVal] at hq2_6; omega
          | @P _ q2_5 _ _ _ _ _ _ _ hq2_5 h =>
            have hq2_5_eq : q2_5 = 71 + ap * 64 := by dsimp [dVal] at hq2_5; omega
            subst hq2_5_eq
            cases h with
            | @D _ q1_7 _ _ _ _ _ hq1_7 h =>
              have hq1_7_eq : q1_7 = 36 + ap * 32 := by dsimp [dVal] at hq1_7; omega
              subst hq1_7_eq
              cases h with
              | D _ hq1_8 _ => dsimp [dVal] at hq1_8; omega
              | P _ _ hq2_8 _ => dsimp [dVal] at hq2_8; omega
            | @P _ q2_7 _ _ _ _ _ _ _ hq2_7 h =>
              have hq2_7_eq : q2_7 = 18 + ap * 16 := by dsimp [dVal] at hq2_7; omega
              subst hq2_7_eq
              cases h with
              | @D _ q1_9 _ _ _ _ _ hq1_9 h =>
                have hq1_9_eq : q1_9 = 9 + ap * 8 := by dsimp [dVal] at hq1_9; omega
                subst hq1_9_eq
                cases h with
                | @D _ q1_10 _ _ _ _ _ hq1_10 h =>
                  have hq1_10_eq : q1_10 = 5 + ap * 4 := by dsimp [dVal] at hq1_10; omega
                  subst hq1_10_eq
                  cases h with
                  | D _ hq1_11 _ => dsimp [dVal] at hq1_11; omega
                  | P _ _ hq2_11 _ => dsimp [dVal] at hq2_11; omega
                | @P _ q2_10 _ _ _ _ _ _ _ hq2_10 h =>
                  have hq2_10_eq : q2_10 = 2 + ap * 2 := by dsimp [dVal] at hq2_10; omega
                  subst hq2_10_eq
                  have h_end : 2 + ap * 2 = 2 * (ap + 1) := by omega
                  rw [h_end] at h
                  exact ⟨_, h⟩
              | P _ _ hq2_9 _ => dsimp [dVal] at hq2_9; omega
        | P _ _ hq2_4 _ => dsimp [dVal] at hq2_4; omega
      | P _ hw1 _ _ => exact False.elim (hw1 rfl)
    | P _ hw1 _ _ => exact False.elim (hw1 rfl)
  | P _ hw1 _ _ => exact False.elim (hw1 rfl)

-- Section 6: Main Invariant Closure and Goal Proof
theorem zDg_top : DigitVal A_top 27 top_base :=
  checkDg_sound A_top top_base (by decide)

theorem zDg_bot : DigitVal 93 9 [Q,K,Q,Q,Q,K,Q,K,K] :=
  checkDg_sound 93 [Q,K,Q,Q,Q,K,Q,K,K] (by decide)

theorem digitVal_mid {A_core m : Nat} {ds_core : List Word}
    (hm : 11 <= m) (hD : DigitVal A_core (m - 1) ds_core)
    (hA_core : A_core * 512 <= 35 * 2 ^ (m - 1)) :
    ∃ A_mid,
      DigitVal A_mid m ([K] ++ ds_core) ∧
      A_mid <= 0 + 35 * 2 ^ (m - 9) := by
  have h_bs : DigitVal 0 1 [K] := checkDg_sound 0 [K] (by decide)
  have h1 := digitVal_append h_bs hD
  have hlen1 : 1 + (m - 1) = m := by omega
  rw [hlen1] at h1
  have h_pow1 : 2 ^ (m - 1) = 256 * 2 ^ (m - 9) := by
    have heq : m - 1 = 8 + (m - 9) := by omega
    rw [heq, Nat.pow_add]
  exact ⟨0 + A_core * 2, h1, by omega⟩

theorem force_a_top {p_w ds_mid : List Word} {ap gp m A_mid a_top g_mid : Nat}
    (hm : 11 <= m)
    (hP_p : Parse a_head p_w ap gp)
    (hz13 : wordScale p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : wordPot p_w <= 29 / 4)
    (hD_mid : DigitVal A_mid m ds_mid)
    (hA_hi : A_mid <= 0 + 35 * 2 ^ (m - 9))
    (hP_mid : Parse (2 * (ap + 1)) ds_mid a_top g_mid) :
    a_top = 2 ^ 21 := by
  rcases Parse_la hP_p with ⟨hla_lo, hla_hi⟩
  have hz12 := wordValQ_nonneg p_w
  have hz10_le := two_wordVal_add_wordValQ_le p_w
  have h_diff_hi : ((ap : Rat) + 1) * wordScale p_w - ((a_head : Rat) + 1) < 15 := by linarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
  have h_mul_lo : ((a_head : Rat) + 1) * ((2 ^ m : Nat) : Rat) <= ((ap : Rat) + 1) * (wordScale p_w * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((ap : Rat) + 1) * (wordScale p_w * ((2 ^ m : Nat) : Rat)) < (((a_head : Rat) + 1) + 15) * ((2 ^ m : Nat) : Rat) := by
    nlinarith
  rw [hz13] at h_mul_lo h_mul_hi
  have ha_val : a_head + 1 = 2 ^ 29 := by decide
  have ha_r : (a_head : Rat) + 1 = ((2 ^ 29 : Nat) : Rat) := by exact_mod_cast ha_val
  rw [ha_r] at h_mul_lo h_mul_hi
  have h_nat_lo : 2 ^ 29 * 2 ^ m <= (ap + 1) * 512 := by exact_mod_cast h_mul_lo
  have h_nat_hi : (ap + 1) * 512 < (2 ^ 29 + 15) * 2 ^ m := by exact_mod_cast h_mul_hi
  have h_ep : (ap + 1) * 512 = (2 * (ap + 1)) * 256 := by ring
  rw [h_ep] at h_nat_lo h_nat_hi
  have h_split1 : 2 ^ 29 * 2 ^ m = (2 ^ 21 * 2 ^ m) * 256 := by
    have : (2 ^ 29 : Nat) = 2 ^ 21 * 256 := by decide
    rw [this]; ring
  have h_split2 : (2 ^ 29 + 15) * 2 ^ m = (2 ^ 21 * 2 ^ m + 15 * 2 ^ (m - 8)) * 256 := by
    have h_eh : (2 ^ 29 : Nat) = 2 ^ 21 * 256 := by decide
    have hm_de : 2 ^ m = 2 ^ (m - 8) * 256 := by
      have h_de : (256 : Nat) = 2 ^ 8 := rfl
      rw [h_de, <- Nat.pow_add, Nat.sub_add_cancel (by omega : 8 <= m)]
    calc (2 ^ 29 + 15) * 2 ^ m
      _ = 2 ^ 29 * 2 ^ m + 15 * 2 ^ m := by ring
      _ = (2 ^ 21 * 256) * 2 ^ m + 15 * (2 ^ (m - 8) * 256) := by rw [h_eh, hm_de]
      _ = (2 ^ 21 * 2 ^ m + 15 * 2 ^ (m - 8)) * 256 := by ring
  rw [h_split1] at h_nat_lo
  rw [h_split2] at h_nat_hi
  have h_pos_de : 0 < 256 := by decide
  have hap_lo : 2 ^ 21 * 2 ^ m <= 2 * (ap + 1) := Nat.le_of_mul_le_mul_right h_nat_lo h_pos_de
  have hap_hi : 2 * (ap + 1) < 2 ^ 21 * 2 ^ m + 15 * 2 ^ (m - 8) := Nat.lt_of_mul_lt_mul_right h_nat_hi
  have h_pow_mde : 2 ^ (m - 8) = 2 * 2 ^ (m - 9) := by
    have heq : m - 8 = 1 + (m - 9) := by omega
    rw [heq, Nat.pow_add]
  have h_pow_m : 2 ^ m = 512 * 2 ^ (m - 9) := by
    have h_dg : (512 : Nat) = 2 ^ 9 := rfl
    rw [h_dg, <- Nat.pow_add, Nat.add_sub_of_le (by omega : 9 <= m)]
  have h_pow_mdg_ge : 4 <= 2 ^ (m - 9) := by
    have h_le_m : 2 <= m - 9 := by omega
    have hle := Nat.pow_le_pow_right (by decide : 1 <= 2) h_le_m
    simpa using hle
  rcases parse_digitVal_a hP_mid hD_mid with ⟨h_atop_lo, h_atop_hi⟩
  have h_sum_lo : 2 ^ 21 * 2 ^ m <= 2 * (ap + 1) + A_mid := by omega
  have h_sum_hi : 2 * (ap + 1) + A_mid < (2 ^ 21 + 1) * 2 ^ m := by
    have : (2 ^ 21 + 1) * 2 ^ m = 2 ^ 21 * 2 ^ m + 512 * 2 ^ (m - 9) := by
      rw [Nat.add_mul, Nat.one_mul, h_pow_m]
    omega
  have h_pos_m : 0 < 2 ^ m := pow_two_pos m
  have h_lt1 : a_top < 2 ^ 21 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_atop_lo h_sum_hi)
  have h_lt2 : 2 ^ 21 < a_top + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_sum_lo h_atop_hi)
  omega

theorem bound_b_mid0 {p_w v_p ds_mid : List Word}
    {ap bp gp m A_mid b_mid0 : Nat}
    (hm : 11 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hbp : 3 <= bp)
    (hz13 : wordScale p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : wordPot p_w <= 29 / 4)
    (hb_mid0 : b_mid0 = 1024 * (bp - 3) + 908)
    (hD_mid : DigitVal A_mid m ds_mid) :
    2 + 4 * wordVal ds_mid < (b_mid0 : Rat) := by
  have h_delta_p := (Scan_delta hS_p).2
  have h_4wv_p := two_wordVal_add_wordValQ_le_four_wordPotV v_p
  have h_cw_p := scan_wordPot_contract7 hS_p
  have hc_bh := (cPar77_bounds b_head).2
  have h_wv_p_lt : wordPotV v_p < 7 := by linarith
  have h_z13_p := scan_wordScale_eq hS_p
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (pow_two_pos (3 * gp))
  have h_z13_vp_pos := wordScale_pos v_p
  have h_z13_vp_le : wordScale v_p <= wordScale p_w := by nlinarith
  have h_bh_big : ((2 ^ 30 : Nat) : Rat) + 30 < (b_head : Rat) := by norm_num [b_head]
  have h_bp2_pos : (0 : Rat) <= (bp : Rat) - 2 := by
    have : (2 : Rat) <= (bp : Rat) := by exact_mod_cast (by omega : 2 <= bp)
    linarith
  have h_prod_p : ((2 ^ 30 : Nat) : Rat) < ((bp : Rat) - 2) * wordScale p_w := by nlinarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
  have h_mul_m : ((2 ^ 30 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < ((bp : Rat) - 2) * (wordScale p_w * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  rw [hz13] at h_mul_m
  have h_pow_ebh : ((2 ^ 30 : Nat) : Rat) = ((2 ^ 21 : Nat) : Rat) * 512 := by norm_num
  rw [h_pow_ebh] at h_mul_m
  have h_bp2_gt : ((2 ^ 21 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < (bp : Rat) - 2 := by linarith
  have h_bmid0_r : (b_mid0 : Rat) = 1024 * ((bp : Rat) - 3) + 908 := by
    rw [hb_mid0, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbp]; push_cast; ring
  have h_z10_mid := (digitVal_scale_and_val hD_mid).2
  have h_pow_val : ((2 ^ 21 : Nat) : Rat) = 2097152 := by norm_num
  have h_powm_ge1 : (1 : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
  rw [h_z10_mid, h_bmid0_r]
  rw [h_pow_val] at h_bp2_gt
  linarith

theorem bound_zW_p' {p_w v_p ds_mid v_mid : List Word}
    {ap bp gp m A_mid b_mid0 b_top g_mid : Nat}
    (hm : 11 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hz13 : wordScale p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : wordPot p_w <= 29 / 4)
    (hD_mid : DigitVal A_mid m ds_mid)
    (hS_mid : Scan (2 * (ap + 1)) b_mid0 ds_mid (2 ^ 21) b_top v_mid g_mid) :
    wordPotV (v_p ++ v_s ++ v_mid) <= 29 / 4 := by
  have h_cw_p := scan_wordPot_contract7 hS_p
  have hc_bh : cPar7 b_head = 2 / 7 := by
    unfold cPar7
    have hmod : b_head % 2 = 0 := by decide
    rw [hmod]; rfl
  rw [hc_bh] at h_cw_p
  have hA : wordPotV v_p <= 13 / 2 := by linarith
  have h_z13_p := scan_wordScale_eq hS_p
  have h_z13_vs : wordScale v_s = 1 / 1024 := by
    have h := checkScalePow_sound v_s 10 0 (by decide)
    norm_num at h
    linarith
  have h_wv_vs : wordPotV v_s <= 9 / 8 := by
    have h := checkWordPotVLe_sound v_s 9 8 (by decide)
    norm_num at h
    linarith
  have h_powm_ge : (2 ^ 11 : Nat) <= 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have h_powm_r : ((2 ^ 11 : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_powm_ge
  have h_z13_p_le : wordScale p_w <= 1 / 4 := by
    have h_pos_p := wordScale_pos p_w
    have h_mul := mul_le_mul_of_nonneg_left h_powm_r (le_of_lt h_pos_p)
    rw [hz13] at h_mul
    norm_num at h_mul
    linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (pow_two_pos (3 * gp))
  have h_z13_vp_pos := wordScale_pos v_p
  have h_z13_vp_le : wordScale v_p <= 1 / 4 := by nlinarith
  have hB : wordScale v_p * wordPotV v_s <= 9 / 32 := by
    have h_wv_nn := wordPotV_nonneg v_s
    nlinarith
  have h_dc_eq := digitVal_scan_dCount hS_mid hD_mid
  have h_wv_mid_dc := dCount_bound_WV v_mid
  have h_vp_m : wordScale v_p * ((2 ^ m : Nat) : Rat) <= 512 := by
    have h_eq : wordScale v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat) = 512 := by
      calc wordScale v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat)
        _ = (wordScale v_p * ((2 ^ (3 * gp) : Nat) : Rat)) * ((2 ^ m : Nat) : Rat) := by ring
        _ = wordScale p_w * ((2 ^ m : Nat) : Rat) := by rw [h_z13_p]
        _ = 512 := hz13
    have h_pos_m : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (pow_two_pos m)
    have h_nn : 0 <= wordScale v_p * ((2 ^ m : Nat) : Rat) := mul_nonneg (le_of_lt h_z13_vp_pos) (le_of_lt h_pos_m)
    nlinarith
  have h_prod_ps : wordScale v_p * wordScale v_s * ((2 ^ m : Nat) : Rat) <= 1 / 2 := by
    rw [h_z13_vs]
    linarith
  have hC : wordScale (v_p ++ v_s) * wordPotV v_mid <= 7 / 16 := by
    rw [wordScale_append]
    have h_wv_mid_le : wordPotV v_mid <= (7 / 8) * ((2 ^ m : Nat) : Rat) := by
      have h_dc_le_m : 2 ^ (dCount v_mid) <= 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have h_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_dc_le_m
      have hm_256 : (256 : Rat) <= ((2 ^ m : Nat) : Rat) := by
        have : (2048 : Rat) <= ((2 ^ 11 : Nat) : Rat) := by norm_num
        linarith
      linarith
    have h_wv_mid_nn := wordPotV_nonneg v_mid
    have h_z13_ps_pos : 0 < wordScale v_p * wordScale v_s := mul_pos h_z13_vp_pos (wordScale_pos v_s)
    nlinarith
  have h_app1 := wordPotV_append_le v_p v_s
  have h_app2 := wordPotV_append_le (v_p ++ v_s) v_mid
  linarith

theorem bound_b_end_digitVal {w_all v_w : List Word} {b_top g_w k : Nat}
    (hk : 1 <= k)
    (hb_top : 2 <= b_top)
    (hS_w : Scan a_head b_head w_all (2 ^ 21) b_top v_w g_w)
    (hz13_vw : wordScale v_w * ((2 ^ k : Nat) : Rat) = 1)
    (hWV_vw : wordPotV v_w <= 29 / 4) :
    ∃ A_core' ds_core',
      DigitVal A_core' (k + 9) ds_core' ∧
      ds_core'.length = k + 9 ∧
      A_core' * 512 <= 35 * 2 ^ (k + 9) ∧
      DigitVal (512 * (b_top - 2) + 93) (k + 45)
          ([Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core' ++ top_base) := by
  rcases Scan_delta hS_w with ⟨hd_lo, hd_hi⟩
  have h_4wv := two_wordVal_add_wordValQ_le_four_wordPotV v_w
  have hd_hi' : ((b_head : Rat) - 2) - ((b_top : Rat) - 2) * wordScale v_w <= 29 := by linarith
  have h_powk_pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by exact_mod_cast (pow_two_pos k)
  have h_mul_lo : (((b_head : Rat) - 2) - 29) * ((2 ^ k : Nat) : Rat) <= ((b_top : Rat) - 2) * (wordScale v_w * ((2 ^ k : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((b_top : Rat) - 2) * (wordScale v_w * ((2 ^ k : Nat) : Rat)) <= ((b_head : Rat) - 1) * ((2 ^ k : Nat) : Rat) := by
    nlinarith
  rw [hz13_vw, mul_one] at h_mul_lo h_mul_hi
  have hbh_r : (b_head : Rat) - 2 = (A_top : Rat) * 512 + 34 := by norm_num [b_head, A_top]
  have hbh_1_r : (b_head : Rat) - 1 = (A_top : Rat) * 512 + 35 := by norm_num [b_head, A_top]
  rw [hbh_r] at h_mul_lo
  rw [hbh_1_r] at h_mul_hi
  let b_end := 512 * (b_top - 2) + 93
  have hb_end_r : (b_end : Rat) = 512 * ((b_top : Rat) - 2) + 93 := by
    dsimp [b_end]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb_top]
    push_cast; ring
  have h_pow_ksh : ((2 ^ (k + 18) : Nat) : Rat) = 262144 * ((2 ^ k : Nat) : Rat) := by
    have h_sh : ((2 ^ 18 : Nat) : Rat) = 262144 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h_sh]; ring
  have h_powk_ge1 : (1 : Rat) <= ((2 ^ k : Nat) : Rat) := by exact_mod_cast (pow_two_pos k)
  have h_bend_lo_r : (A_top : Rat) * ((2 ^ (k + 18) : Nat) : Rat) < (b_end : Rat) := by
    rw [hb_end_r, h_pow_ksh]; linarith
  have h_bend_mid_r : (b_end : Rat) <= (A_top : Rat) * ((2 ^ (k + 18) : Nat) : Rat) + 512 * 35 * ((2 ^ k : Nat) : Rat) + 93 := by
    rw [hb_end_r, h_pow_ksh]; linarith
  have h_bend_hi_r : (b_end : Rat) < ((A_top : Rat) + 1) * ((2 ^ (k + 18) : Nat) : Rat) := by
    rw [hb_end_r, h_pow_ksh]; linarith
  have h_bend_lo : A_top * 2 ^ (k + 18) < b_end := by exact_mod_cast h_bend_lo_r
  have h_bend_mid : b_end <= A_top * 2 ^ (k + 18) + 512 * 35 * 2 ^ k + 93 := by exact_mod_cast h_bend_mid_r
  have h_bend_hi : b_end < (A_top + 1) * 2 ^ (k + 18) := by exact_mod_cast h_bend_hi_r
  let A_core' := (b_end / 512) % (2 ^ (k + 9))
  have h_Acore'_lt : A_core' < 2 ^ (k + 9) := Nat.mod_lt _ (pow_two_pos (k + 9))
  rcases exists_digitVal_of_lt_pow (k + 9) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_len_core' := length_of_digitVal hD_core'
  have h_bot_mid := digitVal_append zDg_bot hD_core'
  have h_all := digitVal_append h_bot_mid zDg_top
  have h_len_all : (9 + (k + 9)) + 27 = k + 45 := by omega
  have h_pow_ksh_eq : 2 ^ (k + 18) = 512 * 2 ^ (k + 9) := by
    have : k + 18 = 9 + (k + 9) := by omega
    rw [this, Nat.pow_add]
  have h_div_top : b_end / (2 ^ (k + 18)) = A_top := by
    have h_pos_ksh : 0 < 2 ^ (k + 18) := pow_two_pos (k + 18)
    have h1 := (Nat.le_div_iff_mul_le h_pos_ksh).mpr (le_of_lt h_bend_lo)
    have h2 := (Nat.div_lt_iff_lt_mul h_pos_ksh).mpr h_bend_hi
    omega
  have h_val_all : 93 + A_core' * 2 ^ 9 + A_top * 2 ^ (9 + (k + 9)) = b_end := by
    have h1 : 2 ^ 9 = 512 := by decide
    have h2 : 2 ^ (9 + (k + 9)) = 512 * 2 ^ (k + 9) := by rw [Nat.pow_add]
    rw [h1, h2]
    have h_assoc : A_top * (512 * 2 ^ (k + 9)) = 512 * (A_top * 2 ^ (k + 9)) := by ring
    rw [h_assoc]
    dsimp [A_core']
    have h_div_mb : (b_end / 512) / (2 ^ (k + 9)) = A_top := by
      rw [Nat.div_div_eq_div_mul, <- h_pow_ksh_eq, h_div_top]
    have h_mod_div := Nat.div_add_mod (b_end / 512) (2 ^ (k + 9))
    rw [h_div_mb, Nat.mul_comm (2 ^ (k + 9)) A_top] at h_mod_div
    have h_mod_mb := Nat.div_add_mod b_end 512
    omega
  have h_Acore'_le_k : A_core' <= 35 * 2 ^ k := by
    have h_eq_db : 2 ^ 9 = 512 := by decide
    have h_eq_ksh : 2 ^ (9 + (k + 9)) = 2 ^ (k + 18) := by
      have : 9 + (k + 9) = k + 18 := by omega
      rw [this]
    rw [h_eq_db, h_eq_ksh] at h_val_all
    omega
  have h_Acore'_dg : A_core' * 512 <= 35 * 2 ^ (k + 9) := by
    have h_pow_kdg : 2 ^ (k + 9) = 512 * 2 ^ k := by
      have : k + 9 = 9 + k := by omega
      rw [this, Nat.pow_add]
    omega
  rw [h_len_all, h_val_all] at h_all
  exact ⟨A_core', ds_core', hD_core', h_len_core', h_Acore'_dg, by simpa [List.append_assoc] using h_all⟩

theorem Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_w, ds_core, A_core, m, rfl, ⟨p_tail, hp_start⟩, hm_def, hm, hD_core, hA_core, hz13, hzW⟩
  have hP_p_ex : ∃ ap gp, Parse a_head p_w ap gp := by
    rw [hp_start]; exact Parse_V_start a_head p_tail
  rcases hP_p_ex with ⟨ap, gp, hP_p⟩
  have hb_head_ok : 2 + 4 * wordVal p_w < (b_head : Rat) := by
    have hz12 := wordValQ_nonneg p_w
    have hz10_le := two_wordVal_add_wordValQ_le p_w
    have hbh_gt : (31 : Rat) < (b_head : Rat) := by norm_num [b_head]
    linarith
  rcases Scan_of_Parse hP_p b_head hb_head_ok with ⟨bp, v_p, hS_p, hbp⟩
  have hS_s := Scan_s ap bp hbp
  let b_mid0 := 1024 * (bp - 3) + 908
  let ds_mid := [K] ++ ds_core
  rcases digitVal_mid hm hD_core hA_core with ⟨A_mid, hD_mid, hA_hi⟩
  have hP_s_all : ∃ a_top g_all, Parse ap (s_full ++ ds_mid) a_top g_all := by
    change ∃ a_top g_all, Parse ap (V :: (s_full.tail ++ ds_mid)) a_top g_all
    exact Parse_V_start ap _
  rcases hP_s_all with ⟨a_top, g_all, hP_all⟩
  have hP_mid_ex : ∃ g_mid, Parse (2 * (ap + 1)) ds_mid a_top g_mid := by
    dsimp [ds_mid] at hP_all ⊢
    exact Parse_s_split hP_all
  rcases hP_mid_ex with ⟨g_mid, hP_mid⟩
  have hatop_eq := force_a_top hm hP_p hz13 hzW hD_mid hA_hi hP_mid
  subst hatop_eq
  have hb_mid0_ok := bound_b_mid0 hm hS_p hbp hz13 hzW rfl hD_mid
  rcases Scan_of_Parse hP_mid b_mid0 hb_mid0_ok with ⟨b_top, v_mid, hS_mid, hb_top_ge3⟩
  have hb_top : 2 <= b_top := by omega
  have hS_top := Scan_top b_top hb_top
  let w_all := p_w ++ s_full ++ ds_mid
  let v_w := v_p ++ v_s ++ v_mid
  let g_w := gp + 3 + g_mid
  have h_ap_eq : 2 * ap + 2 = 2 * (ap + 1) := by omega
  rw [h_ap_eq] at hS_s
  have hS_w : Scan a_head b_head w_all (2 ^ 21) b_top v_w g_w := by
    have h23 := Scan_append hS_p hS_s
    have h234 := Scan_append h23 hS_mid
    simpa [w_all, v_w, g_w, List.append_assoc, Nat.add_assoc] using h234
  have h_u_rep1 :
      (head_w ++ p_w ++ s_base ++ [Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core ++ top_base) ++ List.replicate 0 K =
      head_w ++ w_all ++ top_full := by
    dsimp [w_all, s_full, ds_mid, top_full, List.replicate]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS_full :
      Scan 0 126 ((head_w ++ p_w ++ s_base ++ [Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core ++ top_base) ++ List.replicate 0 K)
           0 (512 * (b_top - 2) + 93) (v_head ++ v_w ++ s_base) (0 + g_w + 12) := by
    rw [h_u_rep1]
    exact Scan_append (Scan_append Scan_head hS_w) hS_top
  let k := 1 + 3 * gp + 3 * g_mid
  have hk : 1 <= k := by omega
  have hWV_vw : wordPotV v_w <= 29 / 4 :=
    bound_zW_p' hm hS_p hz13 hzW hD_mid hS_mid
  have hz13_vw : wordScale v_w * ((2 ^ k : Nat) : Rat) = 1 := by
    have h_z13_w := scan_wordScale_eq hS_w
    have h_w_eq : wordScale w_all = 256 := by
      dsimp only [w_all]
      rw [wordScale_append, wordScale_append]
      have h_s : wordScale s_full = 1 / 2 := by
        have h := checkScalePow_sound s_full 1 0 (by decide)
        norm_num at h
        linarith
      have h_mid := (digitVal_scale_and_val hD_mid).1
      rw [h_s, h_mid]
      linarith
    rw [h_w_eq] at h_z13_w
    have h_3gw : 3 * g_w = k + 8 := by dsimp [g_w, k]; omega
    have h_ew : ((2 ^ 8 : Nat) : Rat) = 256 := by norm_num
    rw [h_3gw, Nat.pow_add, Nat.cast_mul, h_ew] at h_z13_w
    linarith
  rcases bound_b_end_digitVal hk hb_top hS_w hz13_vw hWV_vw
    with ⟨A_core', ds_core', hD_core', hlen_core', hA_core', hD_bend⟩
  let da := [Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core' ++ top_base
  let u' := V :: (v_head ++ v_w ++ s_base ++ da)
  refine ⟨u', ⟨0, 512 * (b_top - 2) + 93, v_head ++ v_w ++ s_base, da, k + 45, 0 + g_w + 12, hS_full, hD_bend, rfl⟩, ?_⟩
  let p_w' := V :: v_w
  let m' := k + 10
  refine ⟨p_w', ds_core', A_core', m', ?_, ⟨v_w, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [u', p_w', da, v_head, head_w]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · dsimp [m']; omega
  · dsimp [m']; omega
  · have h_m'_sub : m' - 1 = k + 9 := by omega
    rw [h_m'_sub]; exact hD_core'
  · have h_m'_sub : m' - 1 = k + 9 := by omega
    rw [h_m'_sub]; exact hA_core'
  · dsimp only [p_w', m', wordScale]
    have h_m'_split : k + 10 = k + 1 + 9 := by omega
    have h1 : ((2 ^ 1 : Nat) : Rat) = 2 := by norm_num
    have h_ep : ((2 ^ 9 : Nat) : Rat) = 512 := by norm_num
    rw [h_m'_split, Nat.pow_add, Nat.pow_add, Nat.cast_mul, Nat.cast_mul, h1, h_ep]
    linarith
  · dsimp only [p_w']
    rw [wordPot_cons_V]
    exact hWV_vw

theorem reach_N (m : Nat) :
    ∃ N, m <= N ∧ ∃ u,
      multiStep tm (init []) N = some (zCf (evalWords u default)) ∧
      Good u := by
  induction m with
  | zero =>
    rcases init_to_u0 with ⟨k1, hk1⟩
    rcases Rounds_exec rounds_0_13 with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, u_13, multiStep_trans_vkq tm _ _ _ k1 k2 hk1 hk2, good_u13⟩
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

end BusyBeaver.M_1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH
