/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 4
abbrev E : Fin 6 := 3
abbrev F : Fin 6 := 5
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
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
abbrev pref_cap : zF := [1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0]


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


-- Turnaround zP0..zP126
abbrev tr1 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr2 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr3 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr4 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr5 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr6 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr7 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr8 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr9 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr10 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr11 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr12 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr13 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr14 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr15 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr16 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr17 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr18 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr19 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr20 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr21 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr22 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr23 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr24 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr25 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr26 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr27 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr28 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr29 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr30 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr31 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr32 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1]
abbrev tr33 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr34 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr35 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr36 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr37 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr38 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr39 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr40 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr41 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr42 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr43 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr44 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr45 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr46 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr47 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr48 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr49 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr50 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr51 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr52 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr53 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr54 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr55 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr56 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr57 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr58 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr59 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr60 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr61 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr62 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr63 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr64 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1]
abbrev tr65 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr66 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr67 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr68 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr69 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr70 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr71 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr72 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr73 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr74 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr75 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr76 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr77 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr78 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr79 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr80 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1]
abbrev tr81 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr82 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr83 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr84 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr85 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr86 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr87 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr88 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr89 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr90 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr91 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr92 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr93 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr94 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr95 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr96 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1]
abbrev tr97 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr98 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr99 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr100 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr101 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr102 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr103 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr104 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr105 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr106 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr107 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr108 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr109 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr110 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr111 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr112 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1]
abbrev tr113 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr114 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr115 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr116 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr117 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr118 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr119 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr120 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr121 : zF := [0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr122 : zF := [0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr123 : zF := [0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr124 : zF := [0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr125 : zF := [0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]
abbrev tr126 : zF := [0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1]

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
lemma zP6 (w : zB) : (zCL w (tr6 +> default)) [tm]⊢⁺ (zCR w .ca (tr7 +> default)) := by
  unfold zCL zCR zCs tr6 tr7
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP7 (w : zB) : (zCL w (tr7 +> default)) [tm]⊢⁺ (zCR w .ca (tr8 +> default)) := by
  unfold zCL zCR zCs tr7 tr8
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP8 (w : zB) : (zCL w (tr8 +> default)) [tm]⊢⁺ (zCR w .ca (tr9 +> default)) := by
  unfold zCL zCR zCs tr8 tr9
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP9 (w : zB) : (zCL w (tr9 +> default)) [tm]⊢⁺ (zCR w .ca (tr10 +> default)) := by
  unfold zCL zCR zCs tr9 tr10
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP10 (w : zB) : (zCL w (tr10 +> default)) [tm]⊢⁺ (zCR w .ca (tr11 +> default)) := by
  unfold zCL zCR zCs tr10 tr11
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP11 (w : zB) : (zCL w (tr11 +> default)) [tm]⊢⁺ (zCR w .ca (tr12 +> default)) := by
  unfold zCL zCR zCs tr11 tr12
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP12 (w : zB) : (zCL w (tr12 +> default)) [tm]⊢⁺ (zCR w .ca (tr13 +> default)) := by
  unfold zCL zCR zCs tr12 tr13
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP13 (w : zB) : (zCL w (tr13 +> default)) [tm]⊢⁺ (zCR w .ca (tr14 +> default)) := by
  unfold zCL zCR zCs tr13 tr14
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP14 (w : zB) : (zCL w (tr14 +> default)) [tm]⊢⁺ (zCR w .ca (tr15 +> default)) := by
  unfold zCL zCR zCs tr14 tr15
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP15 (w : zB) : (zCL w (tr15 +> default)) [tm]⊢⁺ (zCR w .ca (tr16 +> default)) := by
  unfold zCL zCR zCs tr15 tr16
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP16 (w : zB) : (zCL w (tr16 +> default)) [tm]⊢⁺ (zCR w .ca (tr17 +> default)) := by
  unfold zCL zCR zCs tr16 tr17
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP17 (w : zB) : (zCL w (tr17 +> default)) [tm]⊢⁺ (zCR w .ca (tr18 +> default)) := by
  unfold zCL zCR zCs tr17 tr18
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP18 (w : zB) : (zCL w (tr18 +> default)) [tm]⊢⁺ (zCR w .ca (tr19 +> default)) := by
  unfold zCL zCR zCs tr18 tr19
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP19 (w : zB) : (zCL w (tr19 +> default)) [tm]⊢⁺ (zCR w .ca (tr20 +> default)) := by
  unfold zCL zCR zCs tr19 tr20
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP20 (w : zB) : (zCL w (tr20 +> default)) [tm]⊢⁺ (zCR w .ca (tr21 +> default)) := by
  unfold zCL zCR zCs tr20 tr21
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP21 (w : zB) : (zCL w (tr21 +> default)) [tm]⊢⁺ (zCR w .ca (tr22 +> default)) := by
  unfold zCL zCR zCs tr21 tr22
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP22 (w : zB) : (zCL w (tr22 +> default)) [tm]⊢⁺ (zCR w .ca (tr23 +> default)) := by
  unfold zCL zCR zCs tr22 tr23
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP23 (w : zB) : (zCL w (tr23 +> default)) [tm]⊢⁺ (zCR w .ca (tr24 +> default)) := by
  unfold zCL zCR zCs tr23 tr24
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP24 (w : zB) : (zCL w (tr24 +> default)) [tm]⊢⁺ (zCR w .ca (tr25 +> default)) := by
  unfold zCL zCR zCs tr24 tr25
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP25 (w : zB) : (zCL w (tr25 +> default)) [tm]⊢⁺ (zCR w .ca (tr26 +> default)) := by
  unfold zCL zCR zCs tr25 tr26
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP26 (w : zB) : (zCL w (tr26 +> default)) [tm]⊢⁺ (zCR w .ca (tr27 +> default)) := by
  unfold zCL zCR zCs tr26 tr27
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP27 (w : zB) : (zCL w (tr27 +> default)) [tm]⊢⁺ (zCR w .ca (tr28 +> default)) := by
  unfold zCL zCR zCs tr27 tr28
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP28 (w : zB) : (zCL w (tr28 +> default)) [tm]⊢⁺ (zCR w .ca (tr29 +> default)) := by
  unfold zCL zCR zCs tr28 tr29
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP29 (w : zB) : (zCL w (tr29 +> default)) [tm]⊢⁺ (zCR w .ca (tr30 +> default)) := by
  unfold zCL zCR zCs tr29 tr30
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP30 (w : zB) : (zCL w (tr30 +> default)) [tm]⊢⁺ (zCR w .ca (tr31 +> default)) := by
  unfold zCL zCR zCs tr30 tr31
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP31 (w : zB) : (zCL w (tr31 +> default)) [tm]⊢⁺ (zCR w .ca (tr32 +> default)) := by
  unfold zCL zCR zCs tr31 tr32
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP32 (w : zB) : (zCL w (tr32 +> default)) [tm]⊢⁺ (zCR w .ca (tr33 +> default)) := by
  unfold zCL zCR zCs tr32 tr33
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP33 (w : zB) : (zCL w (tr33 +> default)) [tm]⊢⁺ (zCR w .ca (tr34 +> default)) := by
  unfold zCL zCR zCs tr33 tr34
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP34 (w : zB) : (zCL w (tr34 +> default)) [tm]⊢⁺ (zCR w .ca (tr35 +> default)) := by
  unfold zCL zCR zCs tr34 tr35
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP35 (w : zB) : (zCL w (tr35 +> default)) [tm]⊢⁺ (zCR w .ca (tr36 +> default)) := by
  unfold zCL zCR zCs tr35 tr36
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP36 (w : zB) : (zCL w (tr36 +> default)) [tm]⊢⁺ (zCR w .ca (tr37 +> default)) := by
  unfold zCL zCR zCs tr36 tr37
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP37 (w : zB) : (zCL w (tr37 +> default)) [tm]⊢⁺ (zCR w .ca (tr38 +> default)) := by
  unfold zCL zCR zCs tr37 tr38
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP38 (w : zB) : (zCL w (tr38 +> default)) [tm]⊢⁺ (zCR w .ca (tr39 +> default)) := by
  unfold zCL zCR zCs tr38 tr39
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP39 (w : zB) : (zCL w (tr39 +> default)) [tm]⊢⁺ (zCR w .ca (tr40 +> default)) := by
  unfold zCL zCR zCs tr39 tr40
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP40 (w : zB) : (zCL w (tr40 +> default)) [tm]⊢⁺ (zCR w .ca (tr41 +> default)) := by
  unfold zCL zCR zCs tr40 tr41
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP41 (w : zB) : (zCL w (tr41 +> default)) [tm]⊢⁺ (zCR w .ca (tr42 +> default)) := by
  unfold zCL zCR zCs tr41 tr42
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP42 (w : zB) : (zCL w (tr42 +> default)) [tm]⊢⁺ (zCR w .ca (tr43 +> default)) := by
  unfold zCL zCR zCs tr42 tr43
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP43 (w : zB) : (zCL w (tr43 +> default)) [tm]⊢⁺ (zCR w .ca (tr44 +> default)) := by
  unfold zCL zCR zCs tr43 tr44
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP44 (w : zB) : (zCL w (tr44 +> default)) [tm]⊢⁺ (zCR w .ca (tr45 +> default)) := by
  unfold zCL zCR zCs tr44 tr45
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP45 (w : zB) : (zCL w (tr45 +> default)) [tm]⊢⁺ (zCR w .ca (tr46 +> default)) := by
  unfold zCL zCR zCs tr45 tr46
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP46 (w : zB) : (zCL w (tr46 +> default)) [tm]⊢⁺ (zCR w .ca (tr47 +> default)) := by
  unfold zCL zCR zCs tr46 tr47
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP47 (w : zB) : (zCL w (tr47 +> default)) [tm]⊢⁺ (zCR w .ca (tr48 +> default)) := by
  unfold zCL zCR zCs tr47 tr48
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP48 (w : zB) : (zCL w (tr48 +> default)) [tm]⊢⁺ (zCR w .ca (tr49 +> default)) := by
  unfold zCL zCR zCs tr48 tr49
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP49 (w : zB) : (zCL w (tr49 +> default)) [tm]⊢⁺ (zCR w .ca (tr50 +> default)) := by
  unfold zCL zCR zCs tr49 tr50
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP50 (w : zB) : (zCL w (tr50 +> default)) [tm]⊢⁺ (zCR w .ca (tr51 +> default)) := by
  unfold zCL zCR zCs tr50 tr51
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP51 (w : zB) : (zCL w (tr51 +> default)) [tm]⊢⁺ (zCR w .ca (tr52 +> default)) := by
  unfold zCL zCR zCs tr51 tr52
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP52 (w : zB) : (zCL w (tr52 +> default)) [tm]⊢⁺ (zCR w .ca (tr53 +> default)) := by
  unfold zCL zCR zCs tr52 tr53
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP53 (w : zB) : (zCL w (tr53 +> default)) [tm]⊢⁺ (zCR w .ca (tr54 +> default)) := by
  unfold zCL zCR zCs tr53 tr54
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP54 (w : zB) : (zCL w (tr54 +> default)) [tm]⊢⁺ (zCR w .ca (tr55 +> default)) := by
  unfold zCL zCR zCs tr54 tr55
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP55 (w : zB) : (zCL w (tr55 +> default)) [tm]⊢⁺ (zCR w .ca (tr56 +> default)) := by
  unfold zCL zCR zCs tr55 tr56
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP56 (w : zB) : (zCL w (tr56 +> default)) [tm]⊢⁺ (zCR w .ca (tr57 +> default)) := by
  unfold zCL zCR zCs tr56 tr57
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP57 (w : zB) : (zCL w (tr57 +> default)) [tm]⊢⁺ (zCR w .ca (tr58 +> default)) := by
  unfold zCL zCR zCs tr57 tr58
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP58 (w : zB) : (zCL w (tr58 +> default)) [tm]⊢⁺ (zCR w .ca (tr59 +> default)) := by
  unfold zCL zCR zCs tr58 tr59
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP59 (w : zB) : (zCL w (tr59 +> default)) [tm]⊢⁺ (zCR w .ca (tr60 +> default)) := by
  unfold zCL zCR zCs tr59 tr60
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP60 (w : zB) : (zCL w (tr60 +> default)) [tm]⊢⁺ (zCR w .ca (tr61 +> default)) := by
  unfold zCL zCR zCs tr60 tr61
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP61 (w : zB) : (zCL w (tr61 +> default)) [tm]⊢⁺ (zCR w .ca (tr62 +> default)) := by
  unfold zCL zCR zCs tr61 tr62
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP62 (w : zB) : (zCL w (tr62 +> default)) [tm]⊢⁺ (zCR w .ca (tr63 +> default)) := by
  unfold zCL zCR zCs tr62 tr63
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP63 (w : zB) : (zCL w (tr63 +> default)) [tm]⊢⁺ (zCR w .ca (tr64 +> default)) := by
  unfold zCL zCR zCs tr63 tr64
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP64 (w : zB) : (zCL w (tr64 +> default)) [tm]⊢⁺ (zCR w .ca (tr65 +> default)) := by
  unfold zCL zCR zCs tr64 tr65
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP65 (w : zB) : (zCL w (tr65 +> default)) [tm]⊢⁺ (zCR w .ca (tr66 +> default)) := by
  unfold zCL zCR zCs tr65 tr66
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP66 (w : zB) : (zCL w (tr66 +> default)) [tm]⊢⁺ (zCR w .ca (tr67 +> default)) := by
  unfold zCL zCR zCs tr66 tr67
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP67 (w : zB) : (zCL w (tr67 +> default)) [tm]⊢⁺ (zCR w .ca (tr68 +> default)) := by
  unfold zCL zCR zCs tr67 tr68
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP68 (w : zB) : (zCL w (tr68 +> default)) [tm]⊢⁺ (zCR w .ca (tr69 +> default)) := by
  unfold zCL zCR zCs tr68 tr69
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP69 (w : zB) : (zCL w (tr69 +> default)) [tm]⊢⁺ (zCR w .ca (tr70 +> default)) := by
  unfold zCL zCR zCs tr69 tr70
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP70 (w : zB) : (zCL w (tr70 +> default)) [tm]⊢⁺ (zCR w .ca (tr71 +> default)) := by
  unfold zCL zCR zCs tr70 tr71
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP71 (w : zB) : (zCL w (tr71 +> default)) [tm]⊢⁺ (zCR w .ca (tr72 +> default)) := by
  unfold zCL zCR zCs tr71 tr72
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP72 (w : zB) : (zCL w (tr72 +> default)) [tm]⊢⁺ (zCR w .ca (tr73 +> default)) := by
  unfold zCL zCR zCs tr72 tr73
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP73 (w : zB) : (zCL w (tr73 +> default)) [tm]⊢⁺ (zCR w .ca (tr74 +> default)) := by
  unfold zCL zCR zCs tr73 tr74
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP74 (w : zB) : (zCL w (tr74 +> default)) [tm]⊢⁺ (zCR w .ca (tr75 +> default)) := by
  unfold zCL zCR zCs tr74 tr75
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP75 (w : zB) : (zCL w (tr75 +> default)) [tm]⊢⁺ (zCR w .ca (tr76 +> default)) := by
  unfold zCL zCR zCs tr75 tr76
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP76 (w : zB) : (zCL w (tr76 +> default)) [tm]⊢⁺ (zCR w .ca (tr77 +> default)) := by
  unfold zCL zCR zCs tr76 tr77
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP77 (w : zB) : (zCL w (tr77 +> default)) [tm]⊢⁺ (zCR w .ca (tr78 +> default)) := by
  unfold zCL zCR zCs tr77 tr78
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP78 (w : zB) : (zCL w (tr78 +> default)) [tm]⊢⁺ (zCR w .ca (tr79 +> default)) := by
  unfold zCL zCR zCs tr78 tr79
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP79 (w : zB) : (zCL w (tr79 +> default)) [tm]⊢⁺ (zCR w .ca (tr80 +> default)) := by
  unfold zCL zCR zCs tr79 tr80
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP80 (w : zB) : (zCL w (tr80 +> default)) [tm]⊢⁺ (zCR w .ca (tr81 +> default)) := by
  unfold zCL zCR zCs tr80 tr81
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP81 (w : zB) : (zCL w (tr81 +> default)) [tm]⊢⁺ (zCR w .ca (tr82 +> default)) := by
  unfold zCL zCR zCs tr81 tr82
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP82 (w : zB) : (zCL w (tr82 +> default)) [tm]⊢⁺ (zCR w .ca (tr83 +> default)) := by
  unfold zCL zCR zCs tr82 tr83
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP83 (w : zB) : (zCL w (tr83 +> default)) [tm]⊢⁺ (zCR w .ca (tr84 +> default)) := by
  unfold zCL zCR zCs tr83 tr84
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP84 (w : zB) : (zCL w (tr84 +> default)) [tm]⊢⁺ (zCR w .ca (tr85 +> default)) := by
  unfold zCL zCR zCs tr84 tr85
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP85 (w : zB) : (zCL w (tr85 +> default)) [tm]⊢⁺ (zCR w .ca (tr86 +> default)) := by
  unfold zCL zCR zCs tr85 tr86
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP86 (w : zB) : (zCL w (tr86 +> default)) [tm]⊢⁺ (zCR w .ca (tr87 +> default)) := by
  unfold zCL zCR zCs tr86 tr87
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP87 (w : zB) : (zCL w (tr87 +> default)) [tm]⊢⁺ (zCR w .ca (tr88 +> default)) := by
  unfold zCL zCR zCs tr87 tr88
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP88 (w : zB) : (zCL w (tr88 +> default)) [tm]⊢⁺ (zCR w .ca (tr89 +> default)) := by
  unfold zCL zCR zCs tr88 tr89
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP89 (w : zB) : (zCL w (tr89 +> default)) [tm]⊢⁺ (zCR w .ca (tr90 +> default)) := by
  unfold zCL zCR zCs tr89 tr90
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP90 (w : zB) : (zCL w (tr90 +> default)) [tm]⊢⁺ (zCR w .ca (tr91 +> default)) := by
  unfold zCL zCR zCs tr90 tr91
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP91 (w : zB) : (zCL w (tr91 +> default)) [tm]⊢⁺ (zCR w .ca (tr92 +> default)) := by
  unfold zCL zCR zCs tr91 tr92
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP92 (w : zB) : (zCL w (tr92 +> default)) [tm]⊢⁺ (zCR w .ca (tr93 +> default)) := by
  unfold zCL zCR zCs tr92 tr93
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP93 (w : zB) : (zCL w (tr93 +> default)) [tm]⊢⁺ (zCR w .ca (tr94 +> default)) := by
  unfold zCL zCR zCs tr93 tr94
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP94 (w : zB) : (zCL w (tr94 +> default)) [tm]⊢⁺ (zCR w .ca (tr95 +> default)) := by
  unfold zCL zCR zCs tr94 tr95
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP95 (w : zB) : (zCL w (tr95 +> default)) [tm]⊢⁺ (zCR w .ca (tr96 +> default)) := by
  unfold zCL zCR zCs tr95 tr96
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP96 (w : zB) : (zCL w (tr96 +> default)) [tm]⊢⁺ (zCR w .ca (tr97 +> default)) := by
  unfold zCL zCR zCs tr96 tr97
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP97 (w : zB) : (zCL w (tr97 +> default)) [tm]⊢⁺ (zCR w .ca (tr98 +> default)) := by
  unfold zCL zCR zCs tr97 tr98
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP98 (w : zB) : (zCL w (tr98 +> default)) [tm]⊢⁺ (zCR w .ca (tr99 +> default)) := by
  unfold zCL zCR zCs tr98 tr99
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP99 (w : zB) : (zCL w (tr99 +> default)) [tm]⊢⁺ (zCR w .ca (tr100 +> default)) := by
  unfold zCL zCR zCs tr99 tr100
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP100 (w : zB) : (zCL w (tr100 +> default)) [tm]⊢⁺ (zCR w .ca (tr101 +> default)) := by
  unfold zCL zCR zCs tr100 tr101
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP101 (w : zB) : (zCL w (tr101 +> default)) [tm]⊢⁺ (zCR w .ca (tr102 +> default)) := by
  unfold zCL zCR zCs tr101 tr102
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP102 (w : zB) : (zCL w (tr102 +> default)) [tm]⊢⁺ (zCR w .ca (tr103 +> default)) := by
  unfold zCL zCR zCs tr102 tr103
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP103 (w : zB) : (zCL w (tr103 +> default)) [tm]⊢⁺ (zCR w .ca (tr104 +> default)) := by
  unfold zCL zCR zCs tr103 tr104
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP104 (w : zB) : (zCL w (tr104 +> default)) [tm]⊢⁺ (zCR w .ca (tr105 +> default)) := by
  unfold zCL zCR zCs tr104 tr105
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP105 (w : zB) : (zCL w (tr105 +> default)) [tm]⊢⁺ (zCR w .ca (tr106 +> default)) := by
  unfold zCL zCR zCs tr105 tr106
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP106 (w : zB) : (zCL w (tr106 +> default)) [tm]⊢⁺ (zCR w .ca (tr107 +> default)) := by
  unfold zCL zCR zCs tr106 tr107
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP107 (w : zB) : (zCL w (tr107 +> default)) [tm]⊢⁺ (zCR w .ca (tr108 +> default)) := by
  unfold zCL zCR zCs tr107 tr108
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP108 (w : zB) : (zCL w (tr108 +> default)) [tm]⊢⁺ (zCR w .ca (tr109 +> default)) := by
  unfold zCL zCR zCs tr108 tr109
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP109 (w : zB) : (zCL w (tr109 +> default)) [tm]⊢⁺ (zCR w .ca (tr110 +> default)) := by
  unfold zCL zCR zCs tr109 tr110
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP110 (w : zB) : (zCL w (tr110 +> default)) [tm]⊢⁺ (zCR w .ca (tr111 +> default)) := by
  unfold zCL zCR zCs tr110 tr111
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP111 (w : zB) : (zCL w (tr111 +> default)) [tm]⊢⁺ (zCR w .ca (tr112 +> default)) := by
  unfold zCL zCR zCs tr111 tr112
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP112 (w : zB) : (zCL w (tr112 +> default)) [tm]⊢⁺ (zCR w .ca (tr113 +> default)) := by
  unfold zCL zCR zCs tr112 tr113
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP113 (w : zB) : (zCL w (tr113 +> default)) [tm]⊢⁺ (zCR w .ca (tr114 +> default)) := by
  unfold zCL zCR zCs tr113 tr114
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP114 (w : zB) : (zCL w (tr114 +> default)) [tm]⊢⁺ (zCR w .ca (tr115 +> default)) := by
  unfold zCL zCR zCs tr114 tr115
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP115 (w : zB) : (zCL w (tr115 +> default)) [tm]⊢⁺ (zCR w .ca (tr116 +> default)) := by
  unfold zCL zCR zCs tr115 tr116
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP116 (w : zB) : (zCL w (tr116 +> default)) [tm]⊢⁺ (zCR w .ca (tr117 +> default)) := by
  unfold zCL zCR zCs tr116 tr117
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP117 (w : zB) : (zCL w (tr117 +> default)) [tm]⊢⁺ (zCR w .ca (tr118 +> default)) := by
  unfold zCL zCR zCs tr117 tr118
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP118 (w : zB) : (zCL w (tr118 +> default)) [tm]⊢⁺ (zCR w .ca (tr119 +> default)) := by
  unfold zCL zCR zCs tr118 tr119
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP119 (w : zB) : (zCL w (tr119 +> default)) [tm]⊢⁺ (zCR w .ca (tr120 +> default)) := by
  unfold zCL zCR zCs tr119 tr120
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP120 (w : zB) : (zCL w (tr120 +> default)) [tm]⊢⁺ (zCR w .ca (tr121 +> default)) := by
  unfold zCL zCR zCs tr120 tr121
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP121 (w : zB) : (zCL w (tr121 +> default)) [tm]⊢⁺ (zCR w .ca (tr122 +> default)) := by
  unfold zCL zCR zCs tr121 tr122
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP122 (w : zB) : (zCL w (tr122 +> default)) [tm]⊢⁺ (zCR w .ca (tr123 +> default)) := by
  unfold zCL zCR zCs tr122 tr123
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP123 (w : zB) : (zCL w (tr123 +> default)) [tm]⊢⁺ (zCR w .ca (tr124 +> default)) := by
  unfold zCL zCR zCs tr123 tr124
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP124 (w : zB) : (zCL w (tr124 +> default)) [tm]⊢⁺ (zCR w .ca (tr125 +> default)) := by
  unfold zCL zCR zCs tr124 tr125
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP125 (w : zB) : (zCL w (tr125 +> default)) [tm]⊢⁺ (zCR w .ca (tr126 +> default)) := by
  unfold zCL zCR zCs tr125 tr126
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute
lemma zP126 (w : zB) : (zCL w (tr126 +> default)) [tm]⊢⁺ (zCf ([1, 1, 0] +> w)) := by
  unfold zCL zCf tr126 pref_cap
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

-- Section 2: Words, Shift Identity, zDg, Parse, Scan, Step
lemma segSpec : SegSpec z0f :=
  ⟨seg_ch_V, seg_ca_V, seg_ca_Vp, seg_ch_K, seg_ch_Q,
   seg_ca_VpQ, seg_ca_KpVp, seg_ca_QpVp, seg_ca_Kp, seg_ca_Qp,
   seg_ca_KQ, seg_ca_QQ⟩

abbrev Step := StepB 126
abbrev Rounds := RoundsB 126
abbrev Rounds.refl := @RoundsB.refl 126
abbrev Rounds.next := @RoundsB.next 126
abbrev checkStep := checkStepB 126
abbrev checkStep_sound := checkStepB_sound 126

lemma Side_turnaround {w w' : zB} (h : Side ([Call.ca] ^ 126) w w') :
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
  exact zPt (zP0 w) (zPt (hc1 (tr1 +> default)) (zPt (zP1 _) (zPt (hc2 (tr2 +> default)) (zPt (zP2 _) (zPt (hc3 (tr3 +> default)) (zPt (zP3 _) (zPt (hc4 (tr4 +> default)) (zPt (zP4 _) (zPt (hc5 (tr5 +> default)) (zPt (zP5 _) (zPt (hc6 (tr6 +> default)) (zPt (zP6 _) (zPt (hc7 (tr7 +> default)) (zPt (zP7 _) (zPt (hc8 (tr8 +> default)) (zPt (zP8 _) (zPt (hc9 (tr9 +> default)) (zPt (zP9 _) (zPt (hc10 (tr10 +> default)) (zPt (zP10 _) (zPt (hc11 (tr11 +> default)) (zPt (zP11 _) (zPt (hc12 (tr12 +> default)) (zPt (zP12 _) (zPt (hc13 (tr13 +> default)) (zPt (zP13 _) (zPt (hc14 (tr14 +> default)) (zPt (zP14 _) (zPt (hc15 (tr15 +> default)) (zPt (zP15 _) (zPt (hc16 (tr16 +> default)) (zPt (zP16 _) (zPt (hc17 (tr17 +> default)) (zPt (zP17 _) (zPt (hc18 (tr18 +> default)) (zPt (zP18 _) (zPt (hc19 (tr19 +> default)) (zPt (zP19 _) (zPt (hc20 (tr20 +> default)) (zPt (zP20 _) (zPt (hc21 (tr21 +> default)) (zPt (zP21 _) (zPt (hc22 (tr22 +> default)) (zPt (zP22 _) (zPt (hc23 (tr23 +> default)) (zPt (zP23 _) (zPt (hc24 (tr24 +> default)) (zPt (zP24 _) (zPt (hc25 (tr25 +> default)) (zPt (zP25 _) (zPt (hc26 (tr26 +> default)) (zPt (zP26 _) (zPt (hc27 (tr27 +> default)) (zPt (zP27 _) (zPt (hc28 (tr28 +> default)) (zPt (zP28 _) (zPt (hc29 (tr29 +> default)) (zPt (zP29 _) (zPt (hc30 (tr30 +> default)) (zPt (zP30 _) (zPt (hc31 (tr31 +> default)) (zPt (zP31 _) (zPt (hc32 (tr32 +> default)) (zPt (zP32 _) (zPt (hc33 (tr33 +> default)) (zPt (zP33 _) (zPt (hc34 (tr34 +> default)) (zPt (zP34 _) (zPt (hc35 (tr35 +> default)) (zPt (zP35 _) (zPt (hc36 (tr36 +> default)) (zPt (zP36 _) (zPt (hc37 (tr37 +> default)) (zPt (zP37 _) (zPt (hc38 (tr38 +> default)) (zPt (zP38 _) (zPt (hc39 (tr39 +> default)) (zPt (zP39 _) (zPt (hc40 (tr40 +> default)) (zPt (zP40 _) (zPt (hc41 (tr41 +> default)) (zPt (zP41 _) (zPt (hc42 (tr42 +> default)) (zPt (zP42 _) (zPt (hc43 (tr43 +> default)) (zPt (zP43 _) (zPt (hc44 (tr44 +> default)) (zPt (zP44 _) (zPt (hc45 (tr45 +> default)) (zPt (zP45 _) (zPt (hc46 (tr46 +> default)) (zPt (zP46 _) (zPt (hc47 (tr47 +> default)) (zPt (zP47 _) (zPt (hc48 (tr48 +> default)) (zPt (zP48 _) (zPt (hc49 (tr49 +> default)) (zPt (zP49 _) (zPt (hc50 (tr50 +> default)) (zPt (zP50 _) (zPt (hc51 (tr51 +> default)) (zPt (zP51 _) (zPt (hc52 (tr52 +> default)) (zPt (zP52 _) (zPt (hc53 (tr53 +> default)) (zPt (zP53 _) (zPt (hc54 (tr54 +> default)) (zPt (zP54 _) (zPt (hc55 (tr55 +> default)) (zPt (zP55 _) (zPt (hc56 (tr56 +> default)) (zPt (zP56 _) (zPt (hc57 (tr57 +> default)) (zPt (zP57 _) (zPt (hc58 (tr58 +> default)) (zPt (zP58 _) (zPt (hc59 (tr59 +> default)) (zPt (zP59 _) (zPt (hc60 (tr60 +> default)) (zPt (zP60 _) (zPt (hc61 (tr61 +> default)) (zPt (zP61 _) (zPt (hc62 (tr62 +> default)) (zPt (zP62 _) (zPt (hc63 (tr63 +> default)) (zPt (zP63 _) (zPt (hc64 (tr64 +> default)) (zPt (zP64 _) (zPt (hc65 (tr65 +> default)) (zPt (zP65 _) (zPt (hc66 (tr66 +> default)) (zPt (zP66 _) (zPt (hc67 (tr67 +> default)) (zPt (zP67 _) (zPt (hc68 (tr68 +> default)) (zPt (zP68 _) (zPt (hc69 (tr69 +> default)) (zPt (zP69 _) (zPt (hc70 (tr70 +> default)) (zPt (zP70 _) (zPt (hc71 (tr71 +> default)) (zPt (zP71 _) (zPt (hc72 (tr72 +> default)) (zPt (zP72 _) (zPt (hc73 (tr73 +> default)) (zPt (zP73 _) (zPt (hc74 (tr74 +> default)) (zPt (zP74 _) (zPt (hc75 (tr75 +> default)) (zPt (zP75 _) (zPt (hc76 (tr76 +> default)) (zPt (zP76 _) (zPt (hc77 (tr77 +> default)) (zPt (zP77 _) (zPt (hc78 (tr78 +> default)) (zPt (zP78 _) (zPt (hc79 (tr79 +> default)) (zPt (zP79 _) (zPt (hc80 (tr80 +> default)) (zPt (zP80 _) (zPt (hc81 (tr81 +> default)) (zPt (zP81 _) (zPt (hc82 (tr82 +> default)) (zPt (zP82 _) (zPt (hc83 (tr83 +> default)) (zPt (zP83 _) (zPt (hc84 (tr84 +> default)) (zPt (zP84 _) (zPt (hc85 (tr85 +> default)) (zPt (zP85 _) (zPt (hc86 (tr86 +> default)) (zPt (zP86 _) (zPt (hc87 (tr87 +> default)) (zPt (zP87 _) (zPt (hc88 (tr88 +> default)) (zPt (zP88 _) (zPt (hc89 (tr89 +> default)) (zPt (zP89 _) (zPt (hc90 (tr90 +> default)) (zPt (zP90 _) (zPt (hc91 (tr91 +> default)) (zPt (zP91 _) (zPt (hc92 (tr92 +> default)) (zPt (zP92 _) (zPt (hc93 (tr93 +> default)) (zPt (zP93 _) (zPt (hc94 (tr94 +> default)) (zPt (zP94 _) (zPt (hc95 (tr95 +> default)) (zPt (zP95 _) (zPt (hc96 (tr96 +> default)) (zPt (zP96 _) (zPt (hc97 (tr97 +> default)) (zPt (zP97 _) (zPt (hc98 (tr98 +> default)) (zPt (zP98 _) (zPt (hc99 (tr99 +> default)) (zPt (zP99 _) (zPt (hc100 (tr100 +> default)) (zPt (zP100 _) (zPt (hc101 (tr101 +> default)) (zPt (zP101 _) (zPt (hc102 (tr102 +> default)) (zPt (zP102 _) (zPt (hc103 (tr103 +> default)) (zPt (zP103 _) (zPt (hc104 (tr104 +> default)) (zPt (zP104 _) (zPt (hc105 (tr105 +> default)) (zPt (zP105 _) (zPt (hc106 (tr106 +> default)) (zPt (zP106 _) (zPt (hc107 (tr107 +> default)) (zPt (zP107 _) (zPt (hc108 (tr108 +> default)) (zPt (zP108 _) (zPt (hc109 (tr109 +> default)) (zPt (zP109 _) (zPt (hc110 (tr110 +> default)) (zPt (zP110 _) (zPt (hc111 (tr111 +> default)) (zPt (zP111 _) (zPt (hc112 (tr112 +> default)) (zPt (zP112 _) (zPt (hc113 (tr113 +> default)) (zPt (zP113 _) (zPt (hc114 (tr114 +> default)) (zPt (zP114 _) (zPt (hc115 (tr115 +> default)) (zPt (zP115 _) (zPt (hc116 (tr116 +> default)) (zPt (zP116 _) (zPt (hc117 (tr117 +> default)) (zPt (zP117 _) (zPt (hc118 (tr118 +> default)) (zPt (zP118 _) (zPt (hc119 (tr119 +> default)) (zPt (zP119 _) (zPt (hc120 (tr120 +> default)) (zPt (zP120 _) (zPt (hc121 (tr121 +> default)) (zPt (zP121 _) (zPt (hc122 (tr122 +> default)) (zPt (zP122 _) (zPt (hc123 (tr123 +> default)) (zPt (zP123 _) (zPt (hc124 (tr124 +> default)) (zPt (zP124 _) (zPt (hc125 (tr125 +> default)) (zPt (zP125 _) (zPt (hc126 (tr126 +> default)) (zP126 w'))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
lemma zCm_init_0 : zCm zInitCCfg 1000 = some zMidCCfg_1 := by decide
set_option maxRecDepth 200000 in
lemma zCm_init_1 : zCm zMidCCfg_1 1000 = some zMidCCfg_2 := by decide
set_option maxRecDepth 200000 in
lemma zCm_init_2 : zCm zMidCCfg_2 1000 = some zMidCCfg_3 := by decide
set_option maxRecDepth 200000 in
lemma zCm_init_3 : zCm zMidCCfg_3 1000 = some zMidCCfg_4 := by decide
set_option maxRecDepth 200000 in
lemma zCm_init_4 : zCm zMidCCfg_4 347 = some zHitCCfg := by decide

lemma init_to_u0 : (init []) [tm]⊢* zCf (zTs u_0 default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = z04 zInitCCfg := rfl
  have h1 : z04 zHitCCfg = zCf (zTs u_0 default) := by
    dsimp [z04, zHitCCfg, zCf, pref_cap, u_0, zTs, V_u, K_u, Q_u]
    simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00, zDh, zDt]
  have hPlus := zPt (zTc (by decide : 0 < 1000) zCm_init_0) (zPt (zTc (by decide : 0 < 1000) zCm_init_1) (zPt (zTc (by decide : 0 < 1000) zCm_init_2) (zPt (zTc (by decide : 0 < 1000) zCm_init_3) (zTc (by decide : 0 < 347) zCm_init_4))))
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

lemma rounds_0_13 : Rounds u_0 u_13 :=
  Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3 (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7 (Rounds.next step_8 (Rounds.next step_9 (Rounds.next step_10 (Rounds.next step_11 (Rounds.next step_12 (Rounds.refl u_13)))))))))))))

abbrev Good (u : List Word) : Prop :=
  ∃ p_w ds_core A_core m,
    u = head_w ++ p_w ++ s_base ++ [Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core ++ top_base ∧
    (∃ p_tail, p_w = V :: p_tail) ∧
    m = 1 + ds_core.length ∧
    11 <= m ∧
    zDg A_core (m - 1) ds_core ∧
    A_core * 512 <= 35 * 2 ^ (m - 1) ∧
    z13 p_w * ((2 ^ m : Nat) : Rat) = 512 ∧
    zW p_w <= 29 / 4

set_option maxRecDepth 200000 in
lemma good_u13 : Good u_13 := by
  refine ⟨p_init, ds_core_init, A_core_init, 101, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨p_init.tail, rfl⟩
  · decide
  · decide
  · exact checkDg_sound A_core_init ds_core_init (by decide)
  · decide
  · have h := checkZ13Pow_sound p_init 101 9 (by decide)
    norm_num at h
    exact h
  · have h := checkZWLe_sound p_init 29 4 (by decide)
    norm_num at h
    linarith

set_option maxRecDepth 200000 in
lemma Scan_head : Scan 0 126 head_w a_head b_head v_head 0 := by
  have h := checkAffineScan_sound tags_head 0 0 0 126 head_w 0 a_head 0 b_head v_head 0 0 0 (by decide)
  simpa using h

lemma v_head_eq : V :: v_head = head_w ++ [V] := rfl

lemma Scan_s (ap bp : Nat) (hbp : 3 <= bp) :
    Scan ap bp s_full (2 * ap + 2) (1024 * (bp - 3) + 908) v_s 3 := by
  have h := checkAffineScan_sound tags_s 1 0 1 3 s_full 2 2 1024 908 v_s 3 ap (bp - 3) (by decide)
  have h_bp : 1 * (bp - 3) + 3 = bp := by omega
  have h_ap : 1 * ap + 0 = ap := by omega
  rwa [h_ap, h_bp] at h

lemma Scan_top (b_top : Nat) (hb : 2 <= b_top) :
    Scan (2 ^ 21) b_top top_full 0 (512 * (b_top - 2) + 93) s_base 12 := by
  have h := checkAffineScan_sound tags_top 0 (2 ^ 21) 1 2 top_full 0 0 512 93 s_base 12 0 (b_top - 2) (by decide)
  have h_in : 1 * (b_top - 2) + 2 = b_top := by omega
  dsimp at h
  rwa [h_in] at h

lemma Parse_s_split {ap a_end g_all : Nat} {rest : List Word}
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
lemma zDg_top : zDg A_top 27 top_base :=
  checkDg_sound A_top top_base (by decide)

lemma zDg_bot : zDg 93 9 [Q,K,Q,Q,Q,K,Q,K,K] :=
  checkDg_sound 93 [Q,K,Q,Q,Q,K,Q,K,K] (by decide)

lemma zDg_mid {A_core m : Nat} {ds_core : List Word}
    (hm : 11 <= m) (hD : zDg A_core (m - 1) ds_core)
    (hA_core : A_core * 512 <= 35 * 2 ^ (m - 1)) :
    ∃ A_mid,
      zDg A_mid m ([K] ++ ds_core) ∧
      A_mid <= 0 + 35 * 2 ^ (m - 9) := by
  have h_bs : zDg 0 1 [K] := checkDg_sound 0 [K] (by decide)
  have h1 := zDg_append h_bs hD
  have hlen1 : 1 + (m - 1) = m := by omega
  rw [hlen1] at h1
  have h_pow1 : 2 ^ (m - 1) = 256 * 2 ^ (m - 9) := by
    have heq : m - 1 = 8 + (m - 9) := by omega
    rw [heq, Nat.pow_add]
  exact ⟨0 + A_core * 2, h1, by omega⟩

lemma force_a_top {p_w ds_mid : List Word} {ap gp m A_mid a_top g_mid : Nat}
    (hm : 11 <= m)
    (hP_p : Parse a_head p_w ap gp)
    (hz13 : z13 p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : zW p_w <= 29 / 4)
    (hD_mid : zDg A_mid m ds_mid)
    (hA_hi : A_mid <= 0 + 35 * 2 ^ (m - 9))
    (hP_mid : Parse (2 * (ap + 1)) ds_mid a_top g_mid) :
    a_top = 2 ^ 21 := by
  rcases Parse_la hP_p with ⟨hla_lo, hla_hi⟩
  have hz12 := z12_nonneg p_w
  have hz10_le := z10_z12_le_zW p_w
  have h_diff_hi : ((ap : Rat) + 1) * z13 p_w - ((a_head : Rat) + 1) < 15 := by linarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  have h_mul_lo : ((a_head : Rat) + 1) * ((2 ^ m : Nat) : Rat) <= ((ap : Rat) + 1) * (z13 p_w * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((ap : Rat) + 1) * (z13 p_w * ((2 ^ m : Nat) : Rat)) < (((a_head : Rat) + 1) + 15) * ((2 ^ m : Nat) : Rat) := by
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
  rcases Parse_zDg_a hP_mid hD_mid with ⟨h_atop_lo, h_atop_hi⟩
  have h_sum_lo : 2 ^ 21 * 2 ^ m <= 2 * (ap + 1) + A_mid := by omega
  have h_sum_hi : 2 * (ap + 1) + A_mid < (2 ^ 21 + 1) * 2 ^ m := by
    have : (2 ^ 21 + 1) * 2 ^ m = 2 ^ 21 * 2 ^ m + 512 * 2 ^ (m - 9) := by
      rw [Nat.add_mul, Nat.one_mul, h_pow_m]
    omega
  have h_pos_m : 0 < 2 ^ m := zPp m
  have h_lt1 : a_top < 2 ^ 21 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_atop_lo h_sum_hi)
  have h_lt2 : 2 ^ 21 < a_top + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_sum_lo h_atop_hi)
  omega

lemma bound_b_mid0 {p_w v_p ds_mid : List Word}
    {ap bp gp m A_mid b_mid0 : Nat}
    (hm : 11 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hbp : 3 <= bp)
    (hz13 : z13 p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : zW p_w <= 29 / 4)
    (hb_mid0 : b_mid0 = 1024 * (bp - 3) + 908)
    (hD_mid : zDg A_mid m ds_mid) :
    2 + 4 * z10 ds_mid < (b_mid0 : Rat) := by
  have h_delta_p := (Scan_delta hS_p).2
  have h_4wv_p := z10_z12_le_four_zW_V v_p
  have h_cw_p := Scan_zW_contract7 hS_p
  have hc_bh := (cPar77_bounds b_head).2
  have h_wv_p_lt : zW_V v_p < 7 := by linarith
  have h_z13_p := z13_Scan hS_p
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= z13 p_w := by nlinarith
  have h_bh_big : ((2 ^ 30 : Nat) : Rat) + 30 < (b_head : Rat) := by norm_num [b_head]
  have h_bp2_pos : (0 : Rat) <= (bp : Rat) - 2 := by
    have : (2 : Rat) <= (bp : Rat) := by exact_mod_cast (by omega : 2 <= bp)
    linarith
  have h_prod_p : ((2 ^ 30 : Nat) : Rat) < ((bp : Rat) - 2) * z13 p_w := by nlinarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  have h_mul_m : ((2 ^ 30 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < ((bp : Rat) - 2) * (z13 p_w * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  rw [hz13] at h_mul_m
  have h_pow_ebh : ((2 ^ 30 : Nat) : Rat) = ((2 ^ 21 : Nat) : Rat) * 512 := by norm_num
  rw [h_pow_ebh] at h_mul_m
  have h_bp2_gt : ((2 ^ 21 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < (bp : Rat) - 2 := by linarith
  have h_bmid0_r : (b_mid0 : Rat) = 1024 * ((bp : Rat) - 3) + 908 := by
    rw [hb_mid0, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbp]; push_cast; ring
  have h_z10_mid := (zDg_z13_z10 hD_mid).2
  have h_pow_val : ((2 ^ 21 : Nat) : Rat) = 2097152 := by norm_num
  have h_powm_ge1 : (1 : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  rw [h_z10_mid, h_bmid0_r]
  rw [h_pow_val] at h_bp2_gt
  linarith

lemma bound_zW_p' {p_w v_p ds_mid v_mid : List Word}
    {ap bp gp m A_mid b_mid0 b_top g_mid : Nat}
    (hm : 11 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hz13 : z13 p_w * ((2 ^ m : Nat) : Rat) = 512)
    (hzW : zW p_w <= 29 / 4)
    (hD_mid : zDg A_mid m ds_mid)
    (hS_mid : Scan (2 * (ap + 1)) b_mid0 ds_mid (2 ^ 21) b_top v_mid g_mid) :
    zW_V (v_p ++ v_s ++ v_mid) <= 29 / 4 := by
  have h_cw_p := Scan_zW_contract7 hS_p
  have hc_bh : cPar7 b_head = 2 / 7 := by
    unfold cPar7
    have hmod : b_head % 2 = 0 := by decide
    rw [hmod]; rfl
  rw [hc_bh] at h_cw_p
  have hA : zW_V v_p <= 13 / 2 := by linarith
  have h_z13_p := z13_Scan hS_p
  have h_z13_vs : z13 v_s = 1 / 1024 := by
    have h := checkZ13Pow_sound v_s 10 0 (by decide)
    norm_num at h
    linarith
  have h_wv_vs : zW_V v_s <= 9 / 8 := by
    have h := checkZWVLe_sound v_s 9 8 (by decide)
    norm_num at h
    linarith
  have h_powm_ge : (2 ^ 11 : Nat) <= 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have h_powm_r : ((2 ^ 11 : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_powm_ge
  have h_z13_p_le : z13 p_w <= 1 / 4 := by
    have h_pos_p := z13_pos p_w
    have h_mul := mul_le_mul_of_nonneg_left h_powm_r (le_of_lt h_pos_p)
    rw [hz13] at h_mul
    norm_num at h_mul
    linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= 1 / 4 := by nlinarith
  have hB : z13 v_p * zW_V v_s <= 9 / 32 := by
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
  have h_prod_ps : z13 v_p * z13 v_s * ((2 ^ m : Nat) : Rat) <= 1 / 2 := by
    rw [h_z13_vs]
    linarith
  have hC : z13 (v_p ++ v_s) * zW_V v_mid <= 7 / 16 := by
    rw [z13_append]
    have h_wv_mid_le : zW_V v_mid <= (7 / 8) * ((2 ^ m : Nat) : Rat) := by
      have h_dc_le_m : 2 ^ (dCount v_mid) <= 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have h_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_dc_le_m
      have hm_256 : (256 : Rat) <= ((2 ^ m : Nat) : Rat) := by
        have : (2048 : Rat) <= ((2 ^ 11 : Nat) : Rat) := by norm_num
        linarith
      linarith
    have h_wv_mid_nn := zW_V_nonneg v_mid
    have h_z13_ps_pos : 0 < z13 v_p * z13 v_s := mul_pos h_z13_vp_pos (z13_pos v_s)
    nlinarith
  have h_app1 := zW_V_append v_p v_s
  have h_app2 := zW_V_append (v_p ++ v_s) v_mid
  linarith

lemma bound_b_end_zDg {w_all v_w : List Word} {b_top g_w k : Nat}
    (hk : 1 <= k)
    (hb_top : 2 <= b_top)
    (hS_w : Scan a_head b_head w_all (2 ^ 21) b_top v_w g_w)
    (hz13_vw : z13 v_w * ((2 ^ k : Nat) : Rat) = 1)
    (hWV_vw : zW_V v_w <= 29 / 4) :
    ∃ A_core' ds_core',
      zDg A_core' (k + 9) ds_core' ∧
      ds_core'.length = k + 9 ∧
      A_core' * 512 <= 35 * 2 ^ (k + 9) ∧
      zDg (512 * (b_top - 2) + 93) (k + 45)
          ([Q,K,Q,Q,Q,K,Q,K,K] ++ ds_core' ++ top_base) := by
  rcases Scan_delta hS_w with ⟨hd_lo, hd_hi⟩
  have h_4wv := z10_z12_le_four_zW_V v_w
  have hd_hi' : ((b_head : Rat) - 2) - ((b_top : Rat) - 2) * z13 v_w <= 29 := by linarith
  have h_powk_pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
  have h_mul_lo : (((b_head : Rat) - 2) - 29) * ((2 ^ k : Nat) : Rat) <= ((b_top : Rat) - 2) * (z13 v_w * ((2 ^ k : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((b_top : Rat) - 2) * (z13 v_w * ((2 ^ k : Nat) : Rat)) <= ((b_head : Rat) - 1) * ((2 ^ k : Nat) : Rat) := by
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
  have h_powk_ge1 : (1 : Rat) <= ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
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
  have h_Acore'_lt : A_core' < 2 ^ (k + 9) := Nat.mod_lt _ (zPp (k + 9))
  rcases zDg_exists (k + 9) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_len_core' := zDg_len hD_core'
  have h_bot_mid := zDg_append zDg_bot hD_core'
  have h_all := zDg_append h_bot_mid zDg_top
  have h_len_all : (9 + (k + 9)) + 27 = k + 45 := by omega
  have h_pow_ksh_eq : 2 ^ (k + 18) = 512 * 2 ^ (k + 9) := by
    have : k + 18 = 9 + (k + 9) := by omega
    rw [this, Nat.pow_add]
  have h_div_top : b_end / (2 ^ (k + 18)) = A_top := by
    have h_pos_ksh : 0 < 2 ^ (k + 18) := zPp (k + 18)
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

lemma Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_w, ds_core, A_core, m, rfl, ⟨p_tail, hp_start⟩, hm_def, hm, hD_core, hA_core, hz13, hzW⟩
  have hP_p_ex : ∃ ap gp, Parse a_head p_w ap gp := by
    rw [hp_start]; exact Parse_V_start a_head p_tail
  rcases hP_p_ex with ⟨ap, gp, hP_p⟩
  have hb_head_ok : 2 + 4 * z10 p_w < (b_head : Rat) := by
    have hz12 := z12_nonneg p_w
    have hz10_le := z10_z12_le_zW p_w
    have hbh_gt : (31 : Rat) < (b_head : Rat) := by norm_num [b_head]
    linarith
  rcases Scan_of_Parse hP_p b_head hb_head_ok with ⟨bp, v_p, hS_p, hbp⟩
  have hS_s := Scan_s ap bp hbp
  let b_mid0 := 1024 * (bp - 3) + 908
  let ds_mid := [K] ++ ds_core
  rcases zDg_mid hm hD_core hA_core with ⟨A_mid, hD_mid, hA_hi⟩
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
  have hWV_vw : zW_V v_w <= 29 / 4 :=
    bound_zW_p' hm hS_p hz13 hzW hD_mid hS_mid
  have hz13_vw : z13 v_w * ((2 ^ k : Nat) : Rat) = 1 := by
    have h_z13_w := z13_Scan hS_w
    have h_w_eq : z13 w_all = 256 := by
      dsimp only [w_all]
      rw [z13_append, z13_append]
      have h_s : z13 s_full = 1 / 2 := by
        have h := checkZ13Pow_sound s_full 1 0 (by decide)
        norm_num at h
        linarith
      have h_mid := (zDg_z13_z10 hD_mid).1
      rw [h_s, h_mid]
      linarith
    rw [h_w_eq] at h_z13_w
    have h_3gw : 3 * g_w = k + 8 := by dsimp [g_w, k]; omega
    have h_ew : ((2 ^ 8 : Nat) : Rat) = 256 := by norm_num
    rw [h_3gw, Nat.pow_add, Nat.cast_mul, h_ew] at h_z13_w
    linarith
  rcases bound_b_end_zDg hk hb_top hS_w hz13_vw hWV_vw
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
    rcases Rounds_exec rounds_0_13 with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, u_13, zMt tm _ _ _ k1 k2 hk1 hk2, good_u13⟩
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

end BusyBeaver.M_1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH
