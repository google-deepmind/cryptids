/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LD---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 1
abbrev B : Fin 6 := 2
abbrev C : Fin 6 := 3
abbrev D : Fin 6 := 4
abbrev E : Fin 6 := 0
abbrev F : Fin 6 := 5
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

open WordVKQ Word

abbrev z04 (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (z04 c1) [tm]⊢⁺ (z04 c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
abbrev pref_cap : zF := [1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0]


def zCs : Call -> Fin 6
  | .ch => E
  | .ca => C

def zCR (w : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (w <{{zCs c}} ([1] +> r))

def zCL (w : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> w) {{A}}> r)

def zCf (w : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> pref_cap +> w) {{A}}> default)
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
abbrev tr1 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr2 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr3 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr4 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr5 : zF := [0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]
abbrev tr6 : zF := [0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1]

lemma zP0 (w : zB) : (zCf w) [tm]⊢⁺ (zCR w .ca (tr1 +> default)) := by
  unfold zCf zCR zCs pref_cap tr1
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
  unfold zCL zCf tr6 pref_cap
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
  exact zPt (zP0 w) (zPt (hc1 (tr1 +> default)) (zPt (zP1 _) (zPt (hc2 (tr2 +> default)) (zPt (zP2 _) (zPt (hc3 (tr3 +> default)) (zPt (zP3 _) (zPt (hc4 (tr4 +> default)) (zPt (zP4 _) (zPt (hc5 (tr5 +> default)) (zPt (zP5 _) (zPt (hc6 (tr6 +> default)) (zP6 w'))))))))))))

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

def u_0 : List Word := [K,Q,Q]
def tags_0 : List Nat := [3,5]
def da_0 : List Word := [Q,K,Q]
def n_0 : Nat := 0
def u_1 : List Word := [V,K,V,Q,K,Q]
def tags_1 : List Nat := [1,0,3,5]
def da_1 : List Word := [Q,Q,Q]
def n_1 : Nat := 0
def u_2 : List Word := [V,K,V,V,K,V,Q,Q,Q]
def tags_2 : List Nat := [1,0,1,0,4,4]
def da_2 : List Word := [K,Q,K,Q,K,Q]
def n_2 : Nat := 1
def u_3 : List Word := [V,K,V,V,K,V,V,V,V,K,Q,K,Q,K,Q]
def tags_3 : List Nat := [1,0,1,0,0,0,1,3,4,3,4]
def da_3 : List Word := [K,K,Q,K,K,Q]
def n_3 : Nat := 1
def u_4 : List Word := [V,K,V,V,K,V,V,V,V,K,V,Q,V,K,V,K,K,Q,K,K,Q]
def tags_4 : List Nat := [1,0,1,0,0,0,1,0,3,1,2,4,3,3,4]
def da_4 : List Word := [K,Q,K,K,K,Q]
def n_4 : Nat := 1
def u_5 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,K,K,V,Q,V,V,K,K,V,K,Q,K,K,K,Q]
def tags_5 : List Nat := [1,0,1,0,0,0,1,0,0,5,0,3,0,0,5,0,5,3,3,3,4]
def da_5 : List Word := [K,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q]
def n_5 : Nat := 1
def u_6 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,Q,Q,Q,V,K,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_6 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,3,5,0,5,5,5,3,5,3,3,4]
def da_6 : List Word := [K,K,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_6 : Nat := 1
def u_7 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,Q,V,Q,Q,V,K,K,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_7 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,3,0,3,3,0,5,4,5,5,4,5,3,5,3,3,4]
def da_7 : List Word := [K,K,Q,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_7 : Nat := 1
def u_8 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,K,K,V,V,V,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_8 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,5,0,0,0,0,0,0,0,3,0,4,1,4,4,3,3,5,3,5,5,4,5,3,5,3,3,4]
def da_8 : List Word := [K,K,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_8 : Nat := 1
def u_9 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,Q,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_9 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,3,0,3,0,0,0,0,3,0,4,1,4,4,4,5,5,3,4,5,5,3,5,5,4,5,3,5,3,3,4]
def da_9 : List Word := [K,K,Q,K,K,K,K,K,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_9 : Nat := 1
def u_10 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,Q,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,K,K,K,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_10 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,3,1,0,0,0,1,0,1,0,0,0,0,0,0,3,0,0,0,3,0,0,0,0,3,0,4,1,3,5,4,3,3,3,5,4,5,5,4,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_10 : List Word := [K,K,Q,K,K,Q,K,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_10 : Nat := 1
def u_11 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,V,K,K,Q,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,K,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_11 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,5,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,3,0,1,5,0,0,0,0,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,3,5,5,3,5,3,5,4,4,3,5,5,3,3,5,3,3,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_11 : List Word := [K,K,Q,K,K,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_11 : Nat := 1
def u_12 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,V,Q,V,Q,V,V,V,K,V,V,Q,K,V,Q,Q,K,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_12 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,1,2,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,3,0,0,3,0,3,0,0,1,0,0,3,3,0,3,3,5,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,4,5,5,3,3,5,3,3,5,5,5,4,5,4,4,4,5,5,3,3,5,3,3,3,5,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_12 : List Word := [K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,K,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_12 : Nat := 1
def u_13 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,K,V,V,K,V,V,V,K,Q,V,K,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,K,V,Q,K,V,V,V,V,V,V,V,V,V,V,Q,K,V,Q,K,K,V,Q,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,K,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_13 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,1,0,3,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1,2,0,1,0,0,1,3,1,3,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,3,3,0,4,0,0,0,0,0,0,0,0,0,0,3,3,0,4,3,0,3,3,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,4,5,5,3,4,5,4,3,5,3,3,5,3,4,4,4,3,3,5,5,5,5,3,3,3,5,4,4,5,5,3,4,5,5,4,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_13 : List Word := [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q,K,K,K,K,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_13 : Nat := 1
def u_14 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,Q,V,V,K,V,V,V,K,V,Q,K,V,Q,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,K,V,K,K,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,V,V,K,V,Q,Q,V,Q,V,V,V,K,Q,V,V,V,V,Q,K,K,V,V,V,V,V,Q,V,V,V,V,K,K,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,K,K,K,K,K,Q,K,K,K,K,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_14 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,3,0,1,0,0,1,0,3,3,0,3,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,3,0,0,0,0,0,0,0,0,0,0,0,1,3,0,1,0,5,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,3,0,0,1,0,4,0,3,0,0,1,3,0,0,0,0,3,3,3,0,0,0,0,0,3,0,0,0,0,5,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,4,5,5,3,4,3,4,5,3,3,3,5,3,5,3,3,5,3,3,5,5,5,5,4,3,3,5,3,3,5,5,5,5,4,3,4,5,5,5,5,5,4,4,4,5,5,3,4,5,5,4,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_14 : List Word := [K,K,Q,K,K,Q,Q,K,K,K,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,Q,K,K,K,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_14 : Nat := 1
def u_15 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,K,V,V,V,K,V,V,K,K,V,K,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,K,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,Q,V,V,V,V,K,Q,K,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,K,V,V,Q,Q,Q,V,Q,V,Q,Q,V,Q,K,V,V,V,V,V,K,K,V,Q,Q,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,K,K,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,K,K,K,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,Q,K,K,K,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_15 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,1,2,0,0,1,0,0,5,2,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,0,3,0,0,0,0,0,0,0,0,0,0,1,0,3,1,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,0,1,0,3,0,0,0,1,3,3,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,3,2,0,0,4,3,0,3,0,3,3,0,4,0,0,0,0,0,5,0,4,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,5,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,4,5,5,3,4,3,3,4,5,5,3,4,5,4,3,3,5,3,3,5,3,3,3,3,3,5,5,3,3,4,4,3,5,3,3,5,3,3,5,3,4,4,5,5,5,5,3,5,3,3,5,3,3,5,4,4,5,4,3,4,5,5,5,3,3,3,3,5,4,4,5,5,3,4,5,5,4,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_15 : List Word := [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q,K,Q,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_15 : Nat := 1
def u_16 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,Q,V,V,V,K,V,V,V,V,Q,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,Q,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,K,V,K,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,K,Q,V,V,V,Q,V,V,V,K,K,V,Q,K,V,Q,Q,Q,Q,Q,V,V,Q,K,V,V,K,V,Q,K,V,Q,K,V,Q,V,V,V,V,V,V,Q,V,Q,Q,V,Q,K,V,V,V,V,V,K,V,V,V,V,Q,K,K,Q,V,V,V,V,V,Q,V,V,V,V,K,K,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,K,K,K,K,K,Q,K,Q,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def tags_16 : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,1,0,3,0,0,1,0,0,0,0,3,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,0,5,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,1,0,3,3,0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,3,0,0,0,1,2,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,3,0,5,0,0,0,3,0,0,0,5,0,3,3,0,4,4,3,0,0,3,3,0,1,0,3,3,0,3,3,0,3,0,0,0,0,0,0,3,0,3,3,0,3,3,0,0,0,0,1,0,0,0,0,3,3,4,0,0,0,0,0,3,0,0,0,0,5,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,4,5,5,3,4,3,3,5,5,4,3,4,4,3,3,5,3,3,3,3,3,5,5,5,5,5,4,5,5,3,3,3,3,3,3,3,3,3,3,5,3,3,5,3,4,5,5,5,4,5,3,5,4,3,4,5,3,3,5,3,3,5,5,3,4,5,5,5,5,3,5,3,3,5,3,4,3,3,3,5,3,3,3,3,3,5,3,4,5,5,5,3,3,3,3,5,4,4,5,5,3,4,5,5,4,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]
def da_16 : List Word := [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q,Q,K,Q,K,K,Q,K,Q,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,K,K,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def n_16 : Nat := 1
def u_17 : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,K,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,Q,V,V,V,K,V,Q,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,K,V,V,V,K,V,V,K,Q,V,K,V,V,K,K,V,K,K,V,K,V,V,V,V,V,V,K,V,K,K,V,K,Q,V,V,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,K,Q,V,V,V,K,V,V,K,Q,V,Q,Q,K,K,K,V,V,V,V,V,V,V,V,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,V,Q,Q,V,Q,V,V,V,V,V,V,Q,V,V,K,V,V,Q,Q,V,Q,Q,V,V,Q,V,V,V,V,V,Q,V,Q,Q,V,Q,V,K,Q,K,V,Q,Q,Q,Q,K,V,Q,V,V,V,V,Q,K,K,Q,V,V,V,V,V,Q,V,V,V,V,K,K,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,K,K,K,K,K,Q,Q,K,Q,K,K,Q,K,Q,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,K,K,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]

def head_w : List Word := [V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V]
def tags_head : List Nat := [1,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,0]
def v_head : List Word := [K,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V]
def a_head : Nat := 36028797018963967
def b_head : Nat := 87674919322905362
def A_top : Nat := 342480153605099

def s_base : List Word := [V,V,V,V,V,Q,V,V,V,V,K,K,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V]
def s_full : List Word := s_base ++ [K,K,Q,K,K,Q,Q,K,K,K,K]
def tags_s : List Nat := [0,0,0,0,0,3,0,0,0,0,5,0,0,0,0,3,0,0,3,0,0,0,0,3,0,4,1,4,5,5,3,4,3]
def v_s : List Word := [V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,K]

def top_base : List Word := [Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q]
def top_full : List Word := top_base ++ [K]
def tags_top : List Nat := [5,4,4,5,5,3,4,5,5,4,3,3,5,5,5,5,3,5,5,3,5,5,4,5,3,5,3,3,4]

def p_init : List Word := [V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,K,V,V,V,K,V,V,K,K,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,Q,V,V,V,K,V,Q,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,K,V,V,V,K,V,V,K,Q,V,K,V,V,K,K,V,K,K,V,K,V,V,V,V,V,V,K,V,K,K,V,K,Q,V,V,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,K,Q,V,V,V,K,V,V,K,Q,V,Q,Q,K,K,K,V,V,V,V,V,V,V,V,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,V,Q,Q,V,Q,V,V,V,V,V,V,Q,V,V,K,V,V,Q,Q,V,Q,Q,V,V,Q,V,V,V,V,V,Q,V,Q,Q,V,Q,V,K,Q,K,V,Q,Q,Q,Q,K,V,Q,V,V,V,V,Q,K,K,Q]
def ds_core_init : List Word := [Q,K,Q,K,K,Q,K,Q,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,K,K,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K]
def A_core_init : Nat := 5808871908250397171278560619621236457036654829733

def zInitCCfg : CCfg := ⟨0, 0, [], []⟩
def zHitCCfg : CCfg := ⟨1, 0, [0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,1,0,1], []⟩

set_option maxRecDepth 200000 in
lemma zCm_init : zCm zInitCCfg 1694 = some zHitCCfg := by decide

lemma init_to_u0 : (init []) [tm]⊢* zCf (zTs u_0 default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = z04 zInitCCfg := rfl
  have h1 : z04 zHitCCfg = zCf (zTs u_0 default) := by
    dsimp [z04, zHitCCfg, zCf, pref_cap, u_0, zTs, V_u, K_u, Q_u]
    simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00, zDh, zDt]
  have hPlus := zTc (by decide : 0 < 1694) zCm_init
  rw [<- h0, h1] at hPlus
  exact zPs hPlus

set_option maxRecDepth 200000 in
lemma step_0 : Step u_0 u_1 := checkStep_sound n_0 tags_0 u_0 da_0 u_1 (by decide)
set_option maxRecDepth 200000 in
lemma step_1 : Step u_1 u_2 := checkStep_sound n_1 tags_1 u_1 da_1 u_2 (by decide)
set_option maxRecDepth 200000 in
lemma step_2 : Step u_2 u_3 := checkStep_sound n_2 tags_2 u_2 da_2 u_3 (by decide)
set_option maxRecDepth 200000 in
lemma step_3 : Step u_3 u_4 := checkStep_sound n_3 tags_3 u_3 da_3 u_4 (by decide)
set_option maxRecDepth 200000 in
lemma step_4 : Step u_4 u_5 := checkStep_sound n_4 tags_4 u_4 da_4 u_5 (by decide)
set_option maxRecDepth 200000 in
lemma step_5 : Step u_5 u_6 := checkStep_sound n_5 tags_5 u_5 da_5 u_6 (by decide)
set_option maxRecDepth 200000 in
lemma step_6 : Step u_6 u_7 := checkStep_sound n_6 tags_6 u_6 da_6 u_7 (by decide)
set_option maxRecDepth 200000 in
lemma step_7 : Step u_7 u_8 := checkStep_sound n_7 tags_7 u_7 da_7 u_8 (by decide)
set_option maxRecDepth 200000 in
lemma step_8 : Step u_8 u_9 := checkStep_sound n_8 tags_8 u_8 da_8 u_9 (by decide)
set_option maxRecDepth 200000 in
lemma step_9 : Step u_9 u_10 := checkStep_sound n_9 tags_9 u_9 da_9 u_10 (by decide)
set_option maxRecDepth 200000 in
lemma step_10 : Step u_10 u_11 := checkStep_sound n_10 tags_10 u_10 da_10 u_11 (by decide)
set_option maxRecDepth 200000 in
lemma step_11 : Step u_11 u_12 := checkStep_sound n_11 tags_11 u_11 da_11 u_12 (by decide)
set_option maxRecDepth 200000 in
lemma step_12 : Step u_12 u_13 := checkStep_sound n_12 tags_12 u_12 da_12 u_13 (by decide)
set_option maxRecDepth 200000 in
lemma step_13 : Step u_13 u_14 := checkStep_sound n_13 tags_13 u_13 da_13 u_14 (by decide)
set_option maxRecDepth 200000 in
lemma step_14 : Step u_14 u_15 := checkStep_sound n_14 tags_14 u_14 da_14 u_15 (by decide)
set_option maxRecDepth 200000 in
lemma step_15 : Step u_15 u_16 := checkStep_sound n_15 tags_15 u_15 da_15 u_16 (by decide)
set_option maxRecDepth 200000 in
lemma step_16 : Step u_16 u_17 := checkStep_sound n_16 tags_16 u_16 da_16 u_17 (by decide)

lemma rounds_0_17 : Rounds u_0 u_17 :=
  Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3 (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7 (Rounds.next step_8 (Rounds.next step_9 (Rounds.next step_10 (Rounds.next step_11 (Rounds.next step_12 (Rounds.next step_13 (Rounds.next step_14 (Rounds.next step_15 (Rounds.next step_16 (Rounds.refl u_17)))))))))))))))))

abbrev Good (u : List Word) : Prop :=
  ∃ p_w ds_core A_core m,
    u = head_w ++ p_w ++ s_base ++ [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] ++ ds_core ++ top_base ∧
    (∃ p_tail, p_w = V :: p_tail) ∧
    m = 2 + ds_core.length ∧
    21 <= m ∧
    zDg A_core (m - 2) ds_core ∧
    A_core * 256 <= 17 * 2 ^ (m - 2) ∧
    z13 p_w * ((2 ^ m : Nat) : Rat) = 512 ∧
    zW p_w <= 13 / 4

set_option maxRecDepth 200000 in
lemma good_u17 : Good u_17 := by
  refine ⟨p_init, ds_core_init, A_core_init, 168, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨p_init.tail, rfl⟩
  · decide
  · decide
  · exact checkDg_sound A_core_init ds_core_init (by decide)
  · decide
  · have h := checkZ13Pow_sound p_init 168 9 (by decide)
    norm_num at h
    exact h
  · have h := checkZWLe_sound p_init 13 4 (by decide)
    norm_num at h
    linarith

set_option maxRecDepth 200000 in
lemma Scan_head : Scan 0 6 head_w a_head b_head v_head 0 := by
  have h := checkAffineScan_sound tags_head 0 0 0 6 head_w 0 a_head 0 b_head v_head 0 0 0 (by decide)
  simpa using h

lemma v_head_eq : V :: v_head = head_w ++ [V] := rfl

lemma Scan_s (ap bp : Nat) (hbp : 3 <= bp) :
    Scan ap bp s_full (4 * ap + 4) (1048576 * (bp - 3) + 984685) v_s 6 := by
  have h := checkAffineScan_sound tags_s 1 0 1 3 s_full 4 4 1048576 984685 v_s 6 ap (bp - 3) (by decide)
  have h_bp : 1 * (bp - 3) + 3 = bp := by omega
  have h_ap : 1 * ap + 0 = ap := by omega
  rwa [h_ap, h_bp] at h

lemma Scan_top (b_top : Nat) (hb : 2 <= b_top) :
    Scan (2 ^ 48) b_top top_full 0 (8192 * (b_top - 2) + 4196) s_base 21 := by
  have h := checkAffineScan_sound tags_top 0 (2 ^ 48) 1 2 top_full 0 0 8192 4196 s_base 21 0 (b_top - 2) (by decide)
  have h_in : 1 * (b_top - 2) + 2 = b_top := by omega
  dsimp at h
  rwa [h_in] at h

lemma Parse_s_split {ap a_end g_all : Nat} {rest : List Word}
    (h : Parse ap (s_full ++ K :: rest) a_end g_all) :
    ∃ g_mid, Parse (4 * (ap + 1)) (K :: rest) a_end g_mid := by
  change Parse ap ([V,V,V,V,V,Q,V,V,V,V,K,K,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,K,V,K,K,Q,K,K,Q,Q,K,K,K,K,K] ++ rest) a_end g_all at h
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
    have h := Parse_VV_inv h
    have h := Parse_VV_inv h
    rcases Parse_VK_inv h with h | h
    · -- VK at i=9
      cases h with
      | D _ hq1_2 _ => dsimp [dVal] at hq1_2; omega
      | P _ hw1 _ _ => exact False.elim (hw1 rfl)
    · -- T at i=9
      cases h with
      | D _ hq1_3 _ => dsimp [dVal] at hq1_3; omega
      | @P _ q2_3 _ _ _ _ _ _ _ hq2_3 h =>
        have hq2_3_eq : q2_3 = 67 + ap * 64 := by dsimp [dVal] at hq2_3; omega
        subst hq2_3_eq
        have h := Parse_VV_inv h
        have h := Parse_VV_inv h
        have h := Parse_VV_inv h
        have h := Parse_VQ_inv h
        cases h with
        | @D _ q1_4 _ _ _ _ _ hq1_4 h =>
          have hq1_4_eq : q1_4 = 544 + ap * 512 := by dsimp [dVal] at hq1_4; omega
          subst hq1_4_eq
          have h := Parse_VV_inv h
          have h := Parse_VQ_inv h
          cases h with
          | @D _ q1_5 _ _ _ _ _ hq1_5 h =>
            have hq1_5_eq : q1_5 = 1090 + ap * 1024 := by dsimp [dVal] at hq1_5; omega
            subst hq1_5_eq
            have h := Parse_VV_inv h
            have h := Parse_VV_inv h
            have h := Parse_VV_inv h
            have h := Parse_VQ_inv h
            cases h with
            | @D _ q1_6 _ _ _ _ _ hq1_6 h =>
              have hq1_6_eq : q1_6 = 8728 + ap * 8192 := by dsimp [dVal] at hq1_6; omega
              subst hq1_6_eq
              have h := Parse_VQ_inv h
              cases h with
              | @D _ q1_7 _ _ _ _ _ hq1_7 h =>
                have hq1_7_eq : q1_7 = 8729 + ap * 8192 := by dsimp [dVal] at hq1_7; omega
                subst hq1_7_eq
                cases h with
                | D _ hq1_8 _ => dsimp [dVal] at hq1_8; omega
                | P _ hw1 _ _ => exact False.elim (hw1 rfl)
              | @P _ q2_7 _ _ _ _ _ _ _ hq2_7 h =>
                have hq2_7_eq : q2_7 = 4364 + ap * 4096 := by dsimp [dVal] at hq2_7; omega
                subst hq2_7_eq
                rcases Parse_VK_inv h with h | h
                · -- VK at i=28
                  cases h with
                  | @D _ q1_9 _ _ _ _ _ hq1_9 h =>
                    have hq1_9_eq : q1_9 = 2182 + ap * 2048 := by dsimp [dVal] at hq1_9; omega
                    subst hq1_9_eq
                    cases h with
                    | D _ hq1_10 _ => dsimp [dVal] at hq1_10; omega
                    | @P _ q2_10 _ _ _ _ _ _ _ hq2_10 h =>
                      have hq2_10_eq : q2_10 = 545 + ap * 512 := by dsimp [dVal] at hq2_10; omega
                      subst hq2_10_eq
                      cases h with
                      | D _ hq1_11 _ => dsimp [dVal] at hq1_11; omega
                      | @P _ q2_11 _ _ _ _ _ _ _ hq2_11 h =>
                        have hq2_11_eq : q2_11 = 136 + ap * 128 := by dsimp [dVal] at hq2_11; omega
                        subst hq2_11_eq
                        cases h with
                        | D _ hq1_12 _ => dsimp [dVal] at hq1_12; omega
                        | P _ _ hq2_12 _ => dsimp [dVal] at hq2_12; omega
                  | @P _ q2_9 _ _ _ _ _ _ _ hq2_9 h =>
                    have hq2_9_eq : q2_9 = 1091 + ap * 1024 := by dsimp [dVal] at hq2_9; omega
                    subst hq2_9_eq
                    cases h with
                    | D _ hq1_13 _ => dsimp [dVal] at hq1_13; omega
                    | @P _ q2_13 _ _ _ _ _ _ _ hq2_13 h =>
                      have hq2_13_eq : q2_13 = 272 + ap * 256 := by dsimp [dVal] at hq2_13; omega
                      subst hq2_13_eq
                      cases h with
                      | D _ hq1_14 _ => dsimp [dVal] at hq1_14; omega
                      | @P _ q2_14 _ _ _ _ _ _ _ hq2_14 h =>
                        have hq2_14_eq : q2_14 = 68 + ap * 64 := by dsimp [dVal] at hq2_14; omega
                        subst hq2_14_eq
                        cases h with
                        | @D _ q1_15 _ _ _ _ _ hq1_15 h =>
                          have hq1_15_eq : q1_15 = 34 + ap * 32 := by dsimp [dVal] at hq1_15; omega
                          subst hq1_15_eq
                          cases h with
                          | @D _ q1_16 _ _ _ _ _ hq1_16 h =>
                            have hq1_16_eq : q1_16 = 17 + ap * 16 := by dsimp [dVal] at hq1_16; omega
                            subst hq1_16_eq
                            cases h with
                            | D _ hq1_17 _ => dsimp [dVal] at hq1_17; omega
                            | P _ _ hq2_17 _ => dsimp [dVal] at hq2_17; omega
                          | @P _ q2_16 _ _ _ _ _ _ _ hq2_16 h =>
                            have hq2_16_eq : q2_16 = 8 + ap * 8 := by dsimp [dVal] at hq2_16; omega
                            subst hq2_16_eq
                            cases h with
                            | @D _ q1_18 _ _ _ _ _ hq1_18 h =>
                              have hq1_18_eq : q1_18 = 4 + ap * 4 := by dsimp [dVal] at hq1_18; omega
                              subst hq1_18_eq
                              have h_end : 4 + ap * 4 = 4 * (ap + 1) := by omega
                              rw [h_end] at h
                              exact ⟨_, h⟩
                            | P _ _ hq2_18 _ => dsimp [dVal] at hq2_18; omega
                        | P _ _ hq2_15 _ => dsimp [dVal] at hq2_15; omega
                · -- T at i=28
                  cases h with
                  | D _ hq1_19 _ => dsimp [dVal] at hq1_19; omega
                  | P _ _ hq2_19 _ => dsimp [dVal] at hq2_19; omega
            | P _ hw1 _ _ => exact False.elim (hw1 rfl)
          | P _ hw1 _ _ => exact False.elim (hw1 rfl)
        | P _ hw1 _ _ => exact False.elim (hw1 rfl)
  | P _ hw1 _ _ => exact False.elim (hw1 rfl)

-- Section 6: Main Invariant Closure and Goal Proof
lemma zDg_top : zDg A_top 49 top_base :=
  checkDg_sound A_top top_base (by decide)

lemma zDg_bot : zDg 4196 13 [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] :=
  checkDg_sound 4196 [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] (by decide)

lemma zDg_mid {A_core m : Nat} {ds_core : List Word}
    (hm : 21 <= m) (hD : zDg A_core (m - 2) ds_core)
    (hA_core : A_core * 256 <= 17 * 2 ^ (m - 2)) :
    ∃ A_mid,
      zDg A_mid m ([K,Q] ++ ds_core) ∧
      A_mid <= 2 + 17 * 2 ^ (m - 8) := by
  have h_bs : zDg 2 2 [K,Q] := checkDg_sound 2 [K,Q] (by decide)
  have h1 := zDg_append h_bs hD
  have hlen1 : 2 + (m - 2) = m := by omega
  rw [hlen1] at h1
  have h_pow1 : 2 ^ (m - 2) = 64 * 2 ^ (m - 8) := by
    have heq : m - 2 = 6 + (m - 8) := by omega
    rw [heq, Nat.pow_add]
  exact ⟨2 + A_core * 4, h1, by omega⟩

lemma force_a_top {p_w ds_mid : List Word} {ap gp m A_mid a_top g_mid : Nat}
    (hm : 21 <= m)
    (hP_p : Parse a_head p_w ap gp)
    (hz13 : z13 p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : zW p_w <= 13 / 4)
    (hD_mid : zDg A_mid m ds_mid)
    (hA_hi : A_mid <= 2 + 17 * 2 ^ (m - 8))
    (hP_mid : Parse (4 * (ap + 1)) ds_mid a_top g_mid) :
    a_top = 2 ^ 48 := by
  rcases Parse_la hP_p with ⟨hla_lo, hla_hi⟩
  have hz12 := z12_nonneg p_w
  have hz10_le := z10_z12_le_zW p_w
  have h_diff_hi : ((ap : Rat) + 1) * z13 p_w - ((a_head : Rat) + 1) < 7 := by linarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  have h_mul_lo : ((a_head : Rat) + 1) * ((2 ^ m : Nat) : Rat) <= ((ap : Rat) + 1) * (z13 p_w * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((ap : Rat) + 1) * (z13 p_w * ((2 ^ m : Nat) : Rat)) < (((a_head : Rat) + 1) + 7) * ((2 ^ m : Nat) : Rat) := by
    nlinarith
  rw [hz13] at h_mul_lo h_mul_hi
  have ha_val : a_head + 1 = 2 ^ 55 := by decide
  have ha_r : (a_head : Rat) + 1 = ((2 ^ 55 : Nat) : Rat) := by exact_mod_cast ha_val
  rw [ha_r] at h_mul_lo h_mul_hi
  have h_nat_lo : 2 ^ 55 * 2 ^ m <= (ap + 1) * 512 := by exact_mod_cast h_mul_lo
  have h_nat_hi : (ap + 1) * 512 < (2 ^ 55 + 7) * 2 ^ m := by exact_mod_cast h_mul_hi
  have h_ep : (ap + 1) * 512 = (4 * (ap + 1)) * 128 := by ring
  rw [h_ep] at h_nat_lo h_nat_hi
  have h_split1 : 2 ^ 55 * 2 ^ m = (2 ^ 48 * 2 ^ m) * 128 := by
    have : (2 ^ 55 : Nat) = 2 ^ 48 * 128 := by decide
    rw [this]; ring
  have h_split2 : (2 ^ 55 + 7) * 2 ^ m = (2 ^ 48 * 2 ^ m + 7 * 2 ^ (m - 7)) * 128 := by
    have h_eh : (2 ^ 55 : Nat) = 2 ^ 48 * 128 := by decide
    have hm_de : 2 ^ m = 2 ^ (m - 7) * 128 := by
      have h_de : (128 : Nat) = 2 ^ 7 := rfl
      rw [h_de, <- Nat.pow_add, Nat.sub_add_cancel (by omega : 7 <= m)]
    calc (2 ^ 55 + 7) * 2 ^ m
      _ = 2 ^ 55 * 2 ^ m + 7 * 2 ^ m := by ring
      _ = (2 ^ 48 * 128) * 2 ^ m + 7 * (2 ^ (m - 7) * 128) := by rw [h_eh, hm_de]
      _ = (2 ^ 48 * 2 ^ m + 7 * 2 ^ (m - 7)) * 128 := by ring
  rw [h_split1] at h_nat_lo
  rw [h_split2] at h_nat_hi
  have h_pos_de : 0 < 128 := by decide
  have hap_lo : 2 ^ 48 * 2 ^ m <= 4 * (ap + 1) := Nat.le_of_mul_le_mul_right h_nat_lo h_pos_de
  have hap_hi : 4 * (ap + 1) < 2 ^ 48 * 2 ^ m + 7 * 2 ^ (m - 7) := Nat.lt_of_mul_lt_mul_right h_nat_hi
  have h_pow_mde : 2 ^ (m - 7) = 2 * 2 ^ (m - 8) := by
    have heq : m - 7 = 1 + (m - 8) := by omega
    rw [heq, Nat.pow_add]
  have h_pow_m : 2 ^ m = 256 * 2 ^ (m - 8) := by
    have h_dg : (256 : Nat) = 2 ^ 8 := rfl
    rw [h_dg, <- Nat.pow_add, Nat.add_sub_of_le (by omega : 8 <= m)]
  have h_pow_mdg_ge : 8192 <= 2 ^ (m - 8) := by
    have h_le_m : 13 <= m - 8 := by omega
    have hle := Nat.pow_le_pow_right (by decide : 1 <= 2) h_le_m
    simpa using hle
  rcases Parse_zDg_a hP_mid hD_mid with ⟨h_atop_lo, h_atop_hi⟩
  have h_sum_lo : 2 ^ 48 * 2 ^ m <= 4 * (ap + 1) + A_mid := by omega
  have h_sum_hi : 4 * (ap + 1) + A_mid < (2 ^ 48 + 1) * 2 ^ m := by
    have : (2 ^ 48 + 1) * 2 ^ m = 2 ^ 48 * 2 ^ m + 256 * 2 ^ (m - 8) := by
      rw [Nat.add_mul, Nat.one_mul, h_pow_m]
    omega
  have h_pos_m : 0 < 2 ^ m := zPp m
  have h_lt1 : a_top < 2 ^ 48 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_atop_lo h_sum_hi)
  have h_lt2 : 2 ^ 48 < a_top + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_sum_lo h_atop_hi)
  omega

lemma bound_b_mid0 {p_w v_p ds_mid : List Word}
    {ap bp gp m A_mid b_mid0 : Nat}
    (hm : 21 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hbp : 3 <= bp)
    (hz13 : z13 p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : zW p_w <= 13 / 4)
    (hb_mid0 : b_mid0 = 1048576 * (bp - 3) + 984685)
    (hD_mid : zDg A_mid m ds_mid) :
    2 + 4 * z10 ds_mid < (b_mid0 : Rat) := by
  have h_delta_p := (Scan_delta hS_p).2
  have h_4wv_p := z10_z12_le_four_zW_V v_p
  have h_cw_p := Scan_zW_contract7 hS_p
  have hc_bh := (cPar77_bounds b_head).2
  have h_wv_p_lt : zW_V v_p < 4 := by linarith
  have h_z13_p := z13_Scan hS_p
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= z13 p_w := by nlinarith
  have h_bh_big : ((2 ^ 56 : Nat) : Rat) + 18 < (b_head : Rat) := by norm_num [b_head]
  have h_bp2_pos : (0 : Rat) <= (bp : Rat) - 2 := by
    have : (2 : Rat) <= (bp : Rat) := by exact_mod_cast (by omega : 2 <= bp)
    linarith
  have h_prod_p : ((2 ^ 56 : Nat) : Rat) < ((bp : Rat) - 2) * z13 p_w := by nlinarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  have h_mul_m : ((2 ^ 56 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < ((bp : Rat) - 2) * (z13 p_w * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  rw [hz13] at h_mul_m
  have h_pow_ebh : ((2 ^ 56 : Nat) : Rat) = ((2 ^ 47 : Nat) : Rat) * 512 := by norm_num
  rw [h_pow_ebh] at h_mul_m
  have h_bp2_gt : ((2 ^ 47 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < (bp : Rat) - 2 := by linarith
  have h_bmid0_r : (b_mid0 : Rat) = 1048576 * ((bp : Rat) - 3) + 984685 := by
    rw [hb_mid0, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbp]; push_cast; ring
  have h_z10_mid := (zDg_z13_z10 hD_mid).2
  have h_pow_val : ((2 ^ 47 : Nat) : Rat) = 140737488355328 := by norm_num
  have h_powm_ge1 : (1 : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  rw [h_z10_mid, h_bmid0_r]
  rw [h_pow_val] at h_bp2_gt
  linarith

lemma bound_zW_p' {p_w v_p ds_mid v_mid : List Word}
    {ap bp gp m A_mid b_mid0 b_top g_mid : Nat}
    (hm : 21 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hz13 : z13 p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : zW p_w <= 13 / 4)
    (hD_mid : zDg A_mid m ds_mid)
    (hS_mid : Scan (4 * (ap + 1)) b_mid0 ds_mid (2 ^ 48) b_top v_mid g_mid) :
    zW_V (v_p ++ v_s ++ v_mid) <= 13 / 4 := by
  have h_cw_p := Scan_zW_contract7 hS_p
  have hc_bh : cPar7 b_head = 2 / 7 := by
    unfold cPar7
    have hmod : b_head % 2 = 0 := by decide
    rw [hmod]; rfl
  rw [hc_bh] at h_cw_p
  have hA : zW_V v_p <= 43 / 14 := by linarith
  have h_z13_p := z13_Scan hS_p
  have h_z13_vs : z13 v_s = 1 / 1048576 := by
    have h := checkZ13Pow_sound v_s 20 0 (by decide)
    norm_num at h
    linarith
  have h_wv_vs : zW_V v_s <= 9 / 8 := by
    have h := checkZWVLe_sound v_s 9 8 (by decide)
    norm_num at h
    linarith
  have h_powm_ge : (2 ^ 21 : Nat) <= 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have h_powm_r : ((2 ^ 21 : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_powm_ge
  have h_z13_p_le : z13 p_w <= 1 / 4096 := by
    have h_pos_p := z13_pos p_w
    have h_mul := mul_le_mul_of_nonneg_left h_powm_r (le_of_lt h_pos_p)
    rw [hz13] at h_mul
    norm_num at h_mul
    linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= 1 / 4096 := by nlinarith
  have hB : z13 v_p * zW_V v_s <= 9 / 32768 := by
    have h_wv_nn := zW_V_nonneg v_s
    nlinarith
  have h_dc_eq := zDg_Scan_dCount hS_mid hD_mid
  have h_wv_mid_dc := dCount_bound_WV v_mid
  have h_vp_m : z13 v_p * ((2 ^ m : Nat) : Rat) <= 512 := by
    have h_eq : z13 v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat) = 512 := by
      calc z13 v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat)
        _ = (z13 v_p * ((2 ^ (3 * gp) : Nat) : Rat)) * ((2 ^ m : Nat) : Rat) := by ring
        _ = z13 p_w * ((2 ^ m : Nat) : Rat) := by rw [h_z13_p]
        _ = 512 := hz13
    have h_pos_m : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
    have h_nn : 0 <= z13 v_p * ((2 ^ m : Nat) : Rat) := mul_nonneg (le_of_lt h_z13_vp_pos) (le_of_lt h_pos_m)
    nlinarith
  have h_prod_ps : z13 v_p * z13 v_s * ((2 ^ m : Nat) : Rat) <= 1 / 2048 := by
    rw [h_z13_vs]
    linarith
  have hC : z13 (v_p ++ v_s) * zW_V v_mid <= 7 / 16384 := by
    rw [z13_append]
    have h_wv_mid_le : zW_V v_mid <= (7 / 8) * ((2 ^ m : Nat) : Rat) := by
      have h_dc_le_m : 2 ^ (dCount v_mid) <= 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have h_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_dc_le_m
      have hm_256 : (256 : Rat) <= ((2 ^ m : Nat) : Rat) := by
        have : (2097152 : Rat) <= ((2 ^ 21 : Nat) : Rat) := by norm_num
        linarith
      linarith
    have h_wv_mid_nn := zW_V_nonneg v_mid
    have h_z13_ps_pos : 0 < z13 v_p * z13 v_s := mul_pos h_z13_vp_pos (z13_pos v_s)
    nlinarith
  have h_app1 := zW_V_append v_p v_s
  have h_app2 := zW_V_append (v_p ++ v_s) v_mid
  linarith

lemma bound_b_end_zDg {w_all v_w : List Word} {b_top g_w k : Nat}
    (hk : 11 <= k)
    (hb_top : 2 <= b_top)
    (hS_w : Scan a_head b_head w_all (2 ^ 48) b_top v_w g_w)
    (hz13_vw : z13 v_w * ((2 ^ k : Nat) : Rat) = 1)
    (hWV_vw : zW_V v_w <= 13 / 4) :
    ∃ A_core' ds_core',
      zDg A_core' (k + 8) ds_core' ∧
      ds_core'.length = k + 8 ∧
      A_core' * 256 <= 17 * 2 ^ (k + 8) ∧
      zDg (8192 * (b_top - 2) + 4196) (k + 70)
          ([K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] ++ ds_core' ++ top_base) := by
  rcases Scan_delta hS_w with ⟨hd_lo, hd_hi⟩
  have h_4wv := z10_z12_le_four_zW_V v_w
  have hd_hi' : ((b_head : Rat) - 2) - ((b_top : Rat) - 2) * z13 v_w <= 13 := by linarith
  have h_powk_pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
  have h_mul_lo : (((b_head : Rat) - 2) - 13) * ((2 ^ k : Nat) : Rat) <= ((b_top : Rat) - 2) * (z13 v_w * ((2 ^ k : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((b_top : Rat) - 2) * (z13 v_w * ((2 ^ k : Nat) : Rat)) <= ((b_head : Rat) - 1) * ((2 ^ k : Nat) : Rat) := by
    nlinarith
  rw [hz13_vw, mul_one] at h_mul_lo h_mul_hi
  have hbh_r : (b_head : Rat) - 2 = (A_top : Rat) * 256 + 16 := by norm_num [b_head, A_top]
  have hbh_1_r : (b_head : Rat) - 1 = (A_top : Rat) * 256 + 17 := by norm_num [b_head, A_top]
  rw [hbh_r] at h_mul_lo
  rw [hbh_1_r] at h_mul_hi
  let b_end := 8192 * (b_top - 2) + 4196
  have hb_end_r : (b_end : Rat) = 8192 * ((b_top : Rat) - 2) + 4196 := by
    dsimp [b_end]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb_top]
    push_cast; ring
  have h_pow_ksh : ((2 ^ (k + 21) : Nat) : Rat) = 2097152 * ((2 ^ k : Nat) : Rat) := by
    have h_sh : ((2 ^ 21 : Nat) : Rat) = 2097152 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h_sh]; ring
  have h_powk_ge1 : (1 : Rat) <= ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
  have h_bend_lo_r : (A_top : Rat) * ((2 ^ (k + 21) : Nat) : Rat) < (b_end : Rat) := by
    rw [hb_end_r, h_pow_ksh]; linarith
  have h_bend_mid_r : (b_end : Rat) <= (A_top : Rat) * ((2 ^ (k + 21) : Nat) : Rat) + 8192 * 17 * ((2 ^ k : Nat) : Rat) + 4196 := by
    rw [hb_end_r, h_pow_ksh]; linarith
  have h_bend_hi_r : (b_end : Rat) < ((A_top : Rat) + 1) * ((2 ^ (k + 21) : Nat) : Rat) := by
    rw [hb_end_r, h_pow_ksh]; linarith
  have h_bend_lo : A_top * 2 ^ (k + 21) < b_end := by exact_mod_cast h_bend_lo_r
  have h_bend_mid : b_end <= A_top * 2 ^ (k + 21) + 8192 * 17 * 2 ^ k + 4196 := by exact_mod_cast h_bend_mid_r
  have h_bend_hi : b_end < (A_top + 1) * 2 ^ (k + 21) := by exact_mod_cast h_bend_hi_r
  let A_core' := (b_end / 8192) % (2 ^ (k + 8))
  have h_Acore'_lt : A_core' < 2 ^ (k + 8) := Nat.mod_lt _ (zPp (k + 8))
  rcases zDg_exists (k + 8) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_len_core' := zDg_len hD_core'
  have h_bot_mid := zDg_append zDg_bot hD_core'
  have h_all := zDg_append h_bot_mid zDg_top
  have h_len_all : (13 + (k + 8)) + 49 = k + 70 := by omega
  have h_pow_ksh_eq : 2 ^ (k + 21) = 8192 * 2 ^ (k + 8) := by
    have : k + 21 = 13 + (k + 8) := by omega
    rw [this, Nat.pow_add]
  have h_div_top : b_end / (2 ^ (k + 21)) = A_top := by
    have h_pos_ksh : 0 < 2 ^ (k + 21) := zPp (k + 21)
    have h1 := (Nat.le_div_iff_mul_le h_pos_ksh).mpr (le_of_lt h_bend_lo)
    have h2 := (Nat.div_lt_iff_lt_mul h_pos_ksh).mpr h_bend_hi
    omega
  have h_val_all : 4196 + A_core' * 2 ^ 13 + A_top * 2 ^ (13 + (k + 8)) = b_end := by
    have h1 : 2 ^ 13 = 8192 := by decide
    have h2 : 2 ^ (13 + (k + 8)) = 8192 * 2 ^ (k + 8) := by rw [Nat.pow_add]
    rw [h1, h2]
    have h_assoc : A_top * (8192 * 2 ^ (k + 8)) = 8192 * (A_top * 2 ^ (k + 8)) := by ring
    rw [h_assoc]
    dsimp [A_core']
    have h_div_mb : (b_end / 8192) / (2 ^ (k + 8)) = A_top := by
      rw [Nat.div_div_eq_div_mul, <- h_pow_ksh_eq, h_div_top]
    have h_mod_div := Nat.div_add_mod (b_end / 8192) (2 ^ (k + 8))
    rw [h_div_mb, Nat.mul_comm (2 ^ (k + 8)) A_top] at h_mod_div
    have h_mod_mb := Nat.div_add_mod b_end 8192
    omega
  have h_Acore'_le_k : A_core' <= 17 * 2 ^ k := by
    have h_eq_db : 2 ^ 13 = 8192 := by decide
    have h_eq_ksh : 2 ^ (13 + (k + 8)) = 2 ^ (k + 21) := by
      have : 13 + (k + 8) = k + 21 := by omega
      rw [this]
    rw [h_eq_db, h_eq_ksh] at h_val_all
    omega
  have h_Acore'_dg : A_core' * 256 <= 17 * 2 ^ (k + 8) := by
    have h_pow_kdg : 2 ^ (k + 8) = 256 * 2 ^ k := by
      have : k + 8 = 8 + k := by omega
      rw [this, Nat.pow_add]
    omega
  rw [h_len_all, h_val_all] at h_all
  exact ⟨A_core', ds_core', hD_core', h_len_core', h_Acore'_dg, by simpa [List.append_assoc] using h_all⟩

lemma Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_w, ds_core, A_core, m, rfl, ⟨p_tail, hp_start⟩, hm_def, hm, hD_core, hA_core, hz13, hzW⟩
  have hP_p_ex : ∃ ap gp, Parse a_head p_w ap gp := by
    rw [hp_start]; exact Parse_V_start a_head p_tail
  rcases hP_p_ex with ⟨ap, gp, hP_p⟩
  have hb_head_ok : 2 + 4 * z10 p_w < (b_head : Rat) := by
    have hz12 := z12_nonneg p_w
    have hz10_le := z10_z12_le_zW p_w
    have hbh_gt : (15 : Rat) < (b_head : Rat) := by norm_num [b_head]
    linarith
  rcases Scan_of_Parse hP_p b_head hb_head_ok with ⟨bp, v_p, hS_p, hbp⟩
  have hS_s := Scan_s ap bp hbp
  let b_mid0 := 1048576 * (bp - 3) + 984685
  let ds_mid := [K,Q] ++ ds_core
  rcases zDg_mid hm hD_core hA_core with ⟨A_mid, hD_mid, hA_hi⟩
  have hP_s_all : ∃ a_top g_all, Parse ap (s_full ++ ds_mid) a_top g_all := by
    change ∃ a_top g_all, Parse ap (V :: (s_full.tail ++ ds_mid)) a_top g_all
    exact Parse_V_start ap _
  rcases hP_s_all with ⟨a_top, g_all, hP_all⟩
  have hP_mid_ex : ∃ g_mid, Parse (4 * (ap + 1)) ds_mid a_top g_mid := by
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
  let g_w := gp + 6 + g_mid
  have h_ap_eq : 4 * ap + 4 = 4 * (ap + 1) := by omega
  rw [h_ap_eq] at hS_s
  have hS_w : Scan a_head b_head w_all (2 ^ 48) b_top v_w g_w := by
    have h23 := Scan_append hS_p hS_s
    have h234 := Scan_append h23 hS_mid
    simpa [w_all, v_w, g_w, List.append_assoc, Nat.add_assoc] using h234
  have h_u_rep1 :
      (head_w ++ p_w ++ s_base ++ [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] ++ ds_core ++ top_base) ++ List.replicate 1 K =
      head_w ++ w_all ++ top_full := by
    dsimp [w_all, s_full, ds_mid, top_full, List.replicate]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS_full :
      Scan 0 6 ((head_w ++ p_w ++ s_base ++ [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] ++ ds_core ++ top_base) ++ List.replicate 1 K)
           0 (8192 * (b_top - 2) + 4196) (v_head ++ v_w ++ s_base) (0 + g_w + 21) := by
    rw [h_u_rep1]
    exact Scan_append (Scan_append Scan_head hS_w) hS_top
  let k := 11 + 3 * gp + 3 * g_mid
  have hk : 11 <= k := by omega
  have hWV_vw : zW_V v_w <= 13 / 4 :=
    bound_zW_p' hm hS_p hz13 hzW hD_mid hS_mid
  have hz13_vw : z13 v_w * ((2 ^ k : Nat) : Rat) = 1 := by
    have h_z13_w := z13_Scan hS_w
    have h_w_eq : z13 w_all = 128 := by
      dsimp only [w_all]
      rw [z13_append, z13_append]
      have h_s : z13 s_full = 1 / 4 := by
        have h := checkZ13Pow_sound s_full 2 0 (by decide)
        norm_num at h
        linarith
      have h_mid := (zDg_z13_z10 hD_mid).1
      rw [h_s, h_mid]
      linarith
    rw [h_w_eq] at h_z13_w
    have h_3gw : 3 * g_w = k + 7 := by dsimp [g_w, k]; omega
    have h_ew : ((2 ^ 7 : Nat) : Rat) = 128 := by norm_num
    rw [h_3gw, Nat.pow_add, Nat.cast_mul, h_ew] at h_z13_w
    linarith
  rcases bound_b_end_zDg hk hb_top hS_w hz13_vw hWV_vw
    with ⟨A_core', ds_core', hD_core', hlen_core', hA_core', hD_bend⟩
  let da := [K,K,Q,K,K,Q,Q,K,K,K,K,K,Q] ++ ds_core' ++ top_base
  let u' := V :: (v_head ++ v_w ++ s_base ++ da)
  refine ⟨u', ⟨1, 8192 * (b_top - 2) + 4196, v_head ++ v_w ++ s_base, da, k + 70, 0 + g_w + 21, hS_full, hD_bend, rfl⟩, ?_⟩
  let p_w' := V :: v_w
  let m' := k + 10
  refine ⟨p_w', ds_core', A_core', m', ?_, ⟨v_w, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [u', p_w', da, v_head, head_w]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · dsimp [m']; omega
  · dsimp [m']; omega
  · have h_m'_sub : m' - 2 = k + 8 := by omega
    rw [h_m'_sub]; exact hD_core'
  · have h_m'_sub : m' - 2 = k + 8 := by omega
    rw [h_m'_sub]; exact hA_core'
  · dsimp only [p_w', m', z13]
    have h_m'_split : k + 10 = k + 1 + 9 := by omega
    have h1 : ((2 ^ 1 : Nat) : Rat) = 2 := by norm_num
    have h_ep : ((2 ^ 9 : Nat) : Rat) = 512 := by norm_num
    rw [h_m'_split, Nat.pow_add, Nat.pow_add, Nat.cast_mul, Nat.cast_mul, h1, h_ep]
    linarith
  · dsimp only [p_w']
    rw [zW_cons_V]
    exact hWV_vw

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

end BusyBeaver.M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LDHHH
