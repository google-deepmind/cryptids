/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048

open WordVKQ Word

local macro "finish" : tactic =>
  `(tactic| exact ⟨0, rfl⟩)
local macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
local macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | gstep)))

inductive Call where
  | ch
  | cb
  | cf
  | ck

def zInQ : Call -> Fin 6
  | .ch | .cb => 4
  | .cf | .ck => 2

def zInB : Call -> Fin 2
  | .ch | .cb => 1
  | .cf | .ck => 0

def zExQ : Call -> Fin 6
  | .ch => 0
  | .cb => 1
  | .cf => 5
  | .ck => 1

def zExB : Call -> Fin 2
  | .ch | .cb => 1
  | .cf | .ck => 0

def zCR (w : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (w <{{zInQ c}} ([zInB c] +> r))

def zCL (w : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (w {{zExQ c}}> ([zExB c] +> r))

def zCf (w : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> w) {{0}}> default)

abbrev z0f (c : Call) (w1 w2 : zB) : Prop :=
  ∀ r, (zCR w1 c r) [tm]⊢⁺ (zCL w2 c r)

abbrev Side := SideP z0f
abbrev Seg := SegP z0f
abbrev zLp1 := @zLp'

lemma zSC0 {c : Call} {w1 w2 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c r) [tm]⊢⁺ (zCL (w2 +> u) c r)) :
    Seg [c] [] w1 w2 := by
  intro u1 u2 h; cases h
  exact SideP.cons (fun r => h1 u1 r) (SideP.nil _)

lemma zSC1 {c_in c1 : Call} {w1 w2 mid1 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c_in r) [tm]⊢⁺ (zCR u c1 (mid1 +> r)))
    (h2 : ∀ u r, (zCL u c1 (mid1 +> r)) [tm]⊢⁺ (zCL (w2 +> u) c_in r)) :
    Seg [c_in] [c1] w1 w2 := by
  intro u1 u2 h
  rcases h with _ | ⟨hc1, hnil⟩
  cases hnil
  refine SideP.cons (fun r => ?_) (SideP.nil _)
  exact zPt (h1 u1 r) (zPt (hc1 (mid1 +> r)) (h2 u2 r))

lemma zSC2 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c_in r) [tm]⊢⁺ (zCR u c1 (mid1 +> r)))
    (h2 : ∀ u r, (zCL u c1 (mid1 +> r)) [tm]⊢⁺ (zCR u c2 (mid2 +> r)))
    (h3 : ∀ u r, (zCL u c2 (mid2 +> r)) [tm]⊢⁺ (zCL (w2 +> u) c_in r)) :
    Seg [c_in] [c1, c2] w1 w2 := by
  intro u1 u3 h
  rcases h with _ | ⟨hc1, _ | ⟨hc2, hnil⟩⟩
  cases hnil
  refine SideP.cons (fun r => ?_) (SideP.nil _)
  exact zPt (h1 u1 r) (zPt (hc1 (mid1 +> r)) (zPt (h2 _ r) (zPt (hc2 (mid2 +> r)) (h3 u3 r))))

lemma zSC3 {c_in c1 c2 c3 : Call} {w1 w2 mid1 mid2 mid3 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c_in r) [tm]⊢⁺ (zCR u c1 (mid1 +> r)))
    (h2 : ∀ u r, (zCL u c1 (mid1 +> r)) [tm]⊢⁺ (zCR u c2 (mid2 +> r)))
    (h3 : ∀ u r, (zCL u c2 (mid2 +> r)) [tm]⊢⁺ (zCR u c3 (mid3 +> r)))
    (h4 : ∀ u r, (zCL u c3 (mid3 +> r)) [tm]⊢⁺ (zCL (w2 +> u) c_in r)) :
    Seg [c_in] [c1, c2, c3] w1 w2 := by
  intro u1 u4 h
  rcases h with _ | ⟨hc1, _ | ⟨hc2, _ | ⟨hc3, hnil⟩⟩⟩
  cases hnil
  refine SideP.cons (fun r => ?_) (SideP.nil _)
  exact zPt (h1 u1 r) (zPt (hc1 (mid1 +> r)) (zPt (h2 _ r) (zPt (hc2 (mid2 +> r))
    (zPt (h3 _ r) (zPt (hc3 (mid3 +> r)) (h4 u4 r))))))

lemma zSC4 {c_in c1 c2 c3 c4 : Call} {w1 w2 mid1 mid2 mid3 mid4 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c_in r) [tm]⊢⁺ (zCR u c1 (mid1 +> r)))
    (h2 : ∀ u r, (zCL u c1 (mid1 +> r)) [tm]⊢⁺ (zCR u c2 (mid2 +> r)))
    (h3 : ∀ u r, (zCL u c2 (mid2 +> r)) [tm]⊢⁺ (zCR u c3 (mid3 +> r)))
    (h4 : ∀ u r, (zCL u c3 (mid3 +> r)) [tm]⊢⁺ (zCR u c4 (mid4 +> r)))
    (h5 : ∀ u r, (zCL u c4 (mid4 +> r)) [tm]⊢⁺ (zCL (w2 +> u) c_in r)) :
    Seg [c_in] [c1, c2, c3, c4] w1 w2 := by
  intro u1 u5 h
  rcases h with _ | ⟨hc1, _ | ⟨hc2, _ | ⟨hc3, _ | ⟨hc4, hnil⟩⟩⟩⟩
  cases hnil
  refine SideP.cons (fun r => ?_) (SideP.nil _)
  exact zPt (h1 u1 r) (zPt (hc1 (mid1 +> r)) (zPt (h2 _ r) (zPt (hc2 (mid2 +> r))
    (zPt (h3 _ r) (zPt (hc3 (mid3 +> r)) (zPt (h4 _ r) (zPt (hc4 (mid4 +> r)) (h5 u5 r))))))))

lemma seg_cf_1 : Seg [.cf] [] [1] [1] :=
  zSC0 
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_Q_ch : Seg [.cb] [.ch] [1, 0] [1, 0] :=
  zSC1 (mid1 := [0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_Vj_nil : Seg [.cb] [] [1, 0, 0, 0] [1, 0, 0, 1] :=
  zSC0 
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_Va_dbl : Seg [.cb] [.cb, .cf, .cb, .cf] [1, 0, 0, 1] [1, 0, 0, 1] :=
  zSC4 (mid1 := [1, 1, 0, 1]) (mid2 := [1, 1, 0, 1]) (mid3 := [0, 1, 0, 1]) (mid4 := [0, 1, 0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_Va_ch : Seg [.cb] [.ch] [1, 0, 0, 1] [1, 0, 0, 0] :=
  zSC1 (mid1 := [1, 1, 0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_11_ckch : Seg [.cb] [.ck, .ch] [1, 1] [1, 0] :=
  zSC2 (mid1 := [0, 1]) (mid2 := [0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_V_cf : Seg [.cb] [.cf] [1, 1, 0, 0] [1, 0, 0, 1] :=
  zSC1 (mid1 := [0, 1, 0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_cb_V_ck : Seg [.cb] [.ck, .cb, .cf] [1, 1, 0, 0] [1, 0, 0, 1] :=
  zSC3 (mid1 := [0, 1, 0, 1]) (mid2 := [0, 1, 0, 1]) (mid3 := [0, 1, 0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_K : Seg [.ch] [] [0, 0] [0, 1] :=
  zSC0 
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_Qp_dbl : Seg [.ch] [.cb, .cf, .cb, .cf] [0, 1] [0, 1] :=
  zSC4 (mid1 := [1, 1]) (mid2 := [1, 1]) (mid3 := [0, 1]) (mid4 := [0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_Qp_ch : Seg [.ch] [.ch] [0, 1] [0, 0] :=
  zSC1 (mid1 := [1, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_Vp_ch : Seg [.ch] [.ch, .ch] [0, 1, 1, 0] [0, 1, 1, 0] :=
  zSC2 (mid1 := [0, 1, 1, 1]) (mid2 := [0, 1, 0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_Q_cbcf : Seg [.ch] [.cb, .cf] [1, 0] [0, 1] :=
  zSC2 (mid1 := [0, 1]) (mid2 := [0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_11_cf : Seg [.ch] [.cf] [1, 1] [0, 1] :=
  zSC1 (mid1 := [0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_11_ck : Seg [.ch] [.ck, .cb, .cf] [1, 1] [0, 1] :=
  zSC3 (mid1 := [0, 1]) (mid2 := [0, 1]) (mid3 := [0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ch_V_ckch : Seg [.ch] [.ck, .ch] [1, 1, 0, 0] [0, 1, 1, 0] :=
  zSC2 (mid1 := [0, 1, 0, 1]) (mid2 := [0, 1, 0, 1])
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

lemma seg_ck_K : Seg [.ck] [] [0, 0] [1, 1] :=
  zSC0 
    (fun u r => by dsimp only [zCR, zCL, zInQ, zInB, zExQ, zExB]; simp only [List.cons_append, List.nil_append, append_cons, append_nil]; execute)

abbrev pairA : List Call := [.cb, .cf]

lemma seg_cf_keep (w : zF) : Seg [.cf] [] (1 :: w) (1 :: w) :=
  zS0 seg_cf_1 (z0l w)

lemma seg_pairA_Va_dbl : Seg pairA (pairA ^ 2) [1, 0, 0, 1] [1, 0, 0, 1] := by
  simpa using zSg seg_cb_Va_dbl (seg_cf_keep [0, 0, 1])

lemma seg_pairA_Va_pow (n : Nat) : Seg (pairA ^ n) (pairA ^ (n * 2)) [1, 0, 0, 1] [1, 0, 0, 1] := by
  induction n with
  | zero => exact z0l [1, 0, 0, 1]
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp, heq, z0i]
    exact zSg seg_pairA_Va_dbl ih

lemma seg_pairA_Va_half1 : Seg pairA [.ch] [1, 0, 0, 1] [1, 0, 0, 0] := by
  simpa using zSg seg_cb_Va_ch (seg_cf_keep [0, 0, 0])

lemma seg_pairA_Vj_restore : Seg pairA [] [1, 0, 0, 0] [1, 0, 0, 1] := by
  simpa using zSg seg_cb_Vj_nil (seg_cf_keep [0, 0, 1])

lemma seg_pairA_even_Va (q : Nat) : Seg (pairA ^ (q * 2)) ([.ch] ^ q) [1, 0, 0, 1] [1, 0, 0, 1] := by
  induction q with
  | zero => exact z0l [1, 0, 0, 1]
  | succ q ih =>
    have heq : (q + 1) * 2 = 2 + q * 2 := by omega
    rw [heq, z0i, zLp]
    have h2 : Seg (pairA ^ 2) [.ch] [1, 0, 0, 1] [1, 0, 0, 1] := by
      simpa using zSg seg_pairA_Va_half1 seg_pairA_Vj_restore
    exact zSg h2 ih

lemma seg_pairA_odd_Va (q : Nat) : Seg (pairA ^ (1 + q * 2)) ([.ch] ^ (1 + q)) [1, 0, 0, 1] [1, 0, 0, 0] := by
  have heq1 : 1 + q * 2 = q * 2 + 1 := by omega
  have heq2 : 1 + q = q + 1 := by omega
  rw [heq1, z0i, z0h, heq2, z0i, z0h]
  exact zSg (seg_pairA_even_Va q) seg_pairA_Va_half1

lemma seg_pairA_V_cf : Seg pairA [.cf] V_u [1, 0, 0, 1] := by
  simpa using zSg seg_cb_V_cf (seg_cf_keep [0, 0, 1])

lemma seg_pairA_V_ck : Seg pairA ([.ck] ++ pairA) V_u [1, 0, 0, 1] := by
  simpa using zSg seg_cb_V_ck (seg_cf_keep [0, 0, 1])

lemma seg_ch_Vp_pow (n : Nat) : Seg ([.ch] ^ n) ([.ch] ^ (n * 2)) Vp Vp := by
  induction n with
  | zero => exact z0l Vp
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp, heq, z0i]
    exact zSg seg_ch_Vp_ch ih

lemma seg_pairA_Q_pow (n : Nat) : Seg (pairA ^ n) ([.ch] ^ n) Q_u Q_u := by
  induction n with
  | zero => exact z0l Q_u
  | succ n ih =>
    rw [zLp, zLp]
    have h1 : Seg pairA [.ch] Q_u Q_u := by simpa using zSg seg_cb_Q_ch (seg_cf_keep [0])
    exact zSg h1 ih

lemma seg_ch_Qp_dbl_pow (n : Nat) : Seg ([.ch] ^ n) (pairA ^ (n * 2)) Qp Qp := by
  induction n with
  | zero => exact z0l Qp
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp, heq, z0i]
    have h1 : Seg [.ch] (pairA ^ 2) Qp Qp := by simpa using seg_ch_Qp_dbl
    exact zSg h1 ih

lemma seg_ch_K_even (q : Nat) : Seg ([.ch] ^ (q * 2)) ([.ch] ^ q) K_u K_u := by
  induction q with
  | zero => exact z0l K_u
  | succ q ih =>
    have heq : (q + 1) * 2 = 2 + q * 2 := by omega
    rw [heq, z0i, zLp]
    have h2 : Seg ([.ch] ^ 2) [.ch] K_u K_u := by simpa using zSg seg_ch_K seg_ch_Qp_ch
    exact zSg h2 ih

lemma seg_ch_K_odd (q : Nat) : Seg ([.ch] ^ (1 + q * 2)) ([.ch] ^ q) K_u Qp := by
  have heq : 1 + q * 2 = q * 2 + 1 := by omega
  rw [heq, z0i, z0h]
  simpa using zSg (seg_ch_K_even q) seg_ch_K

lemma seg_ch_Qp_even (q : Nat) : Seg ([.ch] ^ (q * 2)) ([.ch] ^ q) Qp Qp := by
  induction q with
  | zero => exact z0l Qp
  | succ q ih =>
    have heq : (q + 1) * 2 = 2 + q * 2 := by omega
    rw [heq, z0i, zLp]
    have h2 : Seg ([.ch] ^ 2) [.ch] Qp Qp := by simpa using zSg seg_ch_Qp_ch seg_ch_K
    exact zSg h2 ih

lemma seg_ch_Qp_odd (q : Nat) : Seg ([.ch] ^ (1 + q * 2)) ([.ch] ^ (1 + q)) Qp K_u := by
  rw [zLp1, zLp1]
  exact zSg seg_ch_Qp_ch (seg_ch_K_even q)

lemma raw_PureA_V_dbl2 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 2) :
    Seg (pairA ^ n1) ([.cf] ++ pairA ^ n2) V_u [1, 0, 0, 1] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out]
  exact zSg seg_pairA_V_cf (seg_pairA_Va_pow (n1 - 1))

lemma raw_PureA_V_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg (pairA ^ n1) ([.ck] ++ pairA ^ n2) V_u [1, 0, 0, 1] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = 1 + (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out, zLp1, <- List.append_assoc]
  exact zSg seg_pairA_V_ck (seg_pairA_Va_pow (n1 - 1))

lemma raw_PureA_V_half0 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 0) (h2 : n2 = n1 / 2) :
    Seg (pairA ^ n1) ([.cf] ++ [.ch] ^ n2) V_u [1, 0, 0, 0] := by
  let q := n2 - 1
  have h1 : n1 = 1 + (1 + q * 2) := by omega
  have h_out : n2 = 1 + q := by omega
  rw [h1, h_out, zLp1]
  exact zSg seg_pairA_V_cf (seg_pairA_odd_Va q)

lemma raw_PureA_V_half1 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 1) (h2 : n2 = n1 / 2) :
    Seg (pairA ^ n1) ([.cf] ++ [.ch] ^ n2) V_u [1, 0, 0, 1] := by
  have h1 : n1 = 1 + n2 * 2 := by omega
  rw [h1, zLp1]
  exact zSg seg_pairA_V_cf (seg_pairA_even_Va n2)

lemma raw_CfA_V_dbl2 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 2) :
    Seg ([.cf] ++ pairA ^ n1) ([.cf] ++ pairA ^ n2) V_u [1, 0, 0, 1] := by
  simpa using zSg (seg_cf_keep [1, 0, 0]) (raw_PureA_V_dbl2 hn h2)

lemma raw_CfA_V_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg ([.cf] ++ pairA ^ n1) ([.ck] ++ pairA ^ n2) V_u [1, 0, 0, 1] := by
  simpa using zSg (seg_cf_keep [1, 0, 0]) (raw_PureA_V_dbl1 hn h2)

lemma raw_CfA_V_half0 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 0) (h2 : n2 = n1 / 2) :
    Seg ([.cf] ++ pairA ^ n1) ([.cf] ++ [.ch] ^ n2) V_u [1, 0, 0, 0] := by
  simpa using zSg (seg_cf_keep [1, 0, 0]) (raw_PureA_V_half0 hn hp h2)

lemma raw_CfA_V_half1 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 1) (h2 : n2 = n1 / 2) :
    Seg ([.cf] ++ pairA ^ n1) ([.cf] ++ [.ch] ^ n2) V_u [1, 0, 0, 1] := by
  simpa using zSg (seg_cf_keep [1, 0, 0]) (raw_PureA_V_half1 hn hp h2)

lemma raw_PureH_V_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg ([.ch] ^ n1) ([.ck] ++ [.ch] ^ n2) V_u [0, 1, 1, 0] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = 1 + (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out, zLp1]
  simpa using zSg seg_ch_V_ckch (seg_ch_Vp_pow (n1 - 1))

lemma raw_CfH_V_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg ([.cf] ++ [.ch] ^ n1) ([.ck] ++ [.ch] ^ n2) V_u [0, 1, 1, 0] := by
  simpa using zSg (seg_cf_keep [1, 0, 0]) (raw_PureH_V_dbl1 hn h2)

lemma raw_CkA_K_keep {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = n1) :
    Seg ([.ck] ++ pairA ^ n1) ([.ck] ++ [.ch] ^ n2) K_u [1, 0] := by
  let q := n1 - 1
  have h1 : n1 = 1 + q := by omega
  have h_out : n2 = 1 + q := by omega
  rw [h1, h_out, zLp1, zLp1]
  have hp1 : Seg pairA [.ck, .ch] [1, 1] Q_u := by simpa using zSg seg_cb_11_ckch (seg_cf_keep [0])
  have hp_all : Seg (pairA ++ pairA ^ q) ([.ck, .ch] ++ [.ch] ^ q) [1, 1] Q_u :=
    zSg hp1 (seg_pairA_Q_pow q)
  simpa using zSg seg_ck_K hp_all

lemma raw_CkH_K_dbl2 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 2) :
    Seg ([.ck] ++ [.ch] ^ n1) ([.cf] ++ pairA ^ n2) K_u [0, 1] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out]
  have hh : Seg ([.ch] ++ [.ch] ^ (n1 - 1)) ([.cf] ++ pairA ^ ((n1 - 1) * 2)) [1, 1] Qp :=
    zSg seg_ch_11_cf (seg_ch_Qp_dbl_pow (n1 - 1))
  simpa using zSg seg_ck_K hh

lemma raw_CkH_K_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg ([.ck] ++ [.ch] ^ n1) ([.ck] ++ pairA ^ n2) K_u [0, 1] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = 1 + (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out, zLp1]
  have hh : Seg ([.ch] ++ [.ch] ^ (n1 - 1)) ([.ck] ++ (pairA ++ pairA ^ ((n1 - 1) * 2))) [1, 1] Qp := by
    simpa [List.append_assoc] using zSg seg_ch_11_ck (seg_ch_Qp_dbl_pow (n1 - 1))
  simpa using zSg seg_ck_K hh

lemma raw_CkH_K_half0 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 0) (h2 : n2 = n1 / 2) :
    Seg ([.ck] ++ [.ch] ^ n1) ([.cf] ++ [.ch] ^ n2) K_u [0, 0] := by
  let q := n2 - 1
  have h1 : n1 = 1 + (1 + q * 2) := by omega
  have h_out : n2 = 1 + q := by omega
  rw [h1, h_out, zLp1]
  have hh : Seg ([.ch] ++ [.ch] ^ (1 + q * 2)) ([.cf] ++ [.ch] ^ (1 + q)) [1, 1] K_u :=
    zSg seg_ch_11_cf (seg_ch_Qp_odd q)
  simpa using zSg seg_ck_K hh

lemma raw_CkH_K_half1 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 1) (h2 : n2 = n1 / 2) :
    Seg ([.ck] ++ [.ch] ^ n1) ([.cf] ++ [.ch] ^ n2) K_u [0, 1] := by
  have h1 : n1 = 1 + n2 * 2 := by omega
  rw [h1, zLp1]
  have hh : Seg ([.ch] ++ [.ch] ^ (n2 * 2)) ([.cf] ++ [.ch] ^ n2) [1, 1] Qp :=
    zSg seg_ch_11_cf (seg_ch_Qp_even n2)
  simpa using zSg seg_ck_K hh

lemma raw_PureH_K_half0 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 0) (h2 : n2 = n1 / 2) :
    Seg ([.ch] ^ n1) ([.ch] ^ n2) K_u [0, 0] := by
  have h1 : n1 = n2 * 2 := by omega
  rw [h1]; exact seg_ch_K_even n2

lemma raw_PureH_K_half1 {n1 n2 : Nat} (hn : 2 <= n1) (hp : n1 % 2 = 1) (h2 : n2 = n1 / 2) :
    Seg ([.ch] ^ n1) ([.ch] ^ n2) K_u [0, 1] := by
  have h1 : n1 = 1 + n2 * 2 := by omega
  rw [h1]; exact seg_ch_K_odd n2

lemma raw_PureH_K_dbl2 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 2) :
    Seg ([.ch] ^ n1) (pairA ^ n2) K_u [0, 1] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out]
  simpa using zSg seg_ch_K (seg_ch_Qp_dbl_pow (n1 - 1))

lemma raw_PureA_Q_keep {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = n1) :
    Seg (pairA ^ n1) ([.ch] ^ n2) Q_u [1, 0] := by
  subst h2; exact seg_pairA_Q_pow _

lemma raw_CfA_Q_keep {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = n1) :
    Seg ([.cf] ++ pairA ^ n1) ([.ch] ^ n2) Q_u [1, 0] := by
  simpa using zSg (seg_cf_keep [0]) (raw_PureA_Q_keep hn h2)

lemma raw_PureH_Q_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg ([.ch] ^ n1) (pairA ^ n2) Q_u [0, 1] := by
  have h1 : n1 = 1 + (n1 - 1) := by omega
  have h_out : n2 = 1 + (n1 - 1) * 2 := by omega
  rw [h1, zLp1]
  rw [h_out, zLp1]
  simpa using zSg seg_ch_Q_cbcf (seg_ch_Qp_dbl_pow (n1 - 1))

lemma raw_CfH_Q_dbl1 {n1 n2 : Nat} (hn : 2 <= n1) (h2 : n2 = 2 * n1 - 1) :
    Seg ([.cf] ++ [.ch] ^ n1) (pairA ^ n2) Q_u [0, 1] := by
  simpa using zSg (seg_cf_keep [0]) (raw_PureH_Q_dbl1 hn h2)

-- 7-leg Hub Turnaround (`pairA ^ 3` = 6 subcalls)
lemma zP0 (w : zB) : (zCf w) [tm]⊢⁺ (zCR w .cb ([0, 1] +> default)) := by
  unfold zCf zCR zInQ zInB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute
lemma zP1 (w : zB) : (zCL w .cb ([0, 1] +> default)) [tm]⊢⁺ (zCR w .cf ([0, 1] +> default)) := by
  unfold zCL zCR zInQ zInB zExQ zExB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute
lemma zP2 (w : zB) : (zCL w .cf ([0, 1] +> default)) [tm]⊢⁺ (zCR w .cb ([1, 1, 0, 1] +> default)) := by
  unfold zCL zCR zInQ zInB zExQ zExB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute
lemma zP3 (w : zB) : (zCL w .cb ([1, 1, 0, 1] +> default)) [tm]⊢⁺ (zCR w .cf ([1, 1, 0, 1] +> default)) := by
  unfold zCL zCR zInQ zInB zExQ zExB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute
lemma zP4 (w : zB) : (zCL w .cf ([1, 1, 0, 1] +> default)) [tm]⊢⁺ (zCR w .cb ([0, 1, 0, 1] +> default)) := by
  unfold zCL zCR zInQ zInB zExQ zExB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute
lemma zP5 (w : zB) : (zCL w .cb ([0, 1, 0, 1] +> default)) [tm]⊢⁺ (zCR w .cf ([0, 1, 0, 1] +> default)) := by
  unfold zCL zCR zInQ zInB zExQ zExB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute
lemma zP6 (w : zB) : (zCL w .cf ([0, 1, 0, 1] +> default)) [tm]⊢⁺ (zCf ([1, 1, 0, 0, 1] +> w)) := by
  unfold zCL zCf zExQ zExB; simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]; execute

lemma Side_turnaround {w w' : zB} (h : Side (pairA ^ 3) w w') :
    (zCf w) [tm]⊢⁺ (zCf ([1, 1, 0, 0, 1] +> w')) := by
  rcases h with _ | ⟨hc1, _ | ⟨hc2, _ | ⟨hc3, _ | ⟨hc4, _ | ⟨hc5, _ | ⟨hc6, hnil⟩⟩⟩⟩⟩⟩
  cases hnil
  exact zPt (zP0 w) (zPt (hc1 ([0, 1] +> default))
    (zPt (zP1 _) (zPt (hc2 ([0, 1] +> default))
      (zPt (zP2 _) (zPt (hc3 ([1, 1, 0, 1] +> default))
        (zPt (zP3 _) (zPt (hc4 ([1, 1, 0, 1] +> default))
          (zPt (zP4 _) (zPt (hc5 ([0, 1, 0, 1] +> default))
            (zPt (zP5 _) (zPt (hc6 ([0, 1, 0, 1] +> default)) (zP6 w'))))))))))))

abbrev zWt_zTs_aux := zWt'_zTs'

lemma Side_ch_default {b' H : Nat} {da : List Word} (h : zDg b' H da) :
    Side ([.ch] ^ b') default (zTs' da default) := by
  induction h with
  | nil => exact SideP.nil default
  | @zero A H u _ ih =>
    have hS := zSc (seg_ch_K_even A) ih
    simpa [zTs', K_u, Kp] using hS
  | @one A H u _ ih =>
    have hS := zSc (seg_ch_K_odd A) ih
    simpa [zTs', K_u, Kp] using hS

inductive Mode where
  | PA1 | FA1 | KA1 | KHV | PHV | FH0 | FH1 | PH0 | PH1
deriving DecidableEq, Repr

inductive DState where
  | S2 | S3 | S4 | S5
deriving DecidableEq, Repr

def modeCalls : Mode -> Nat -> List Call
  | .PA1, n => pairA ^ n
  | .FA1, n => [.cf] ++ pairA ^ n
  | .KA1, n => [.ck] ++ pairA ^ n
  | .KHV, n => [.ck] ++ [.ch] ^ n
  | .PHV, n => [.ch] ^ n
  | .FH0, n => [.cf] ++ [.ch] ^ n
  | .FH1, n => [.cf] ++ [.ch] ^ n
  | .PH0, n => [.ch] ^ n
  | .PH1, n => [.ch] ^ n

def modeRem : Mode -> zF
  | .PA1 | .FA1 | .KA1 => [1]
  | .KHV | .PHV => [1, 1, 0]
  | .FH0 | .PH0 => [0]
  | .FH1 | .PH1 => [1]

def modeMatches : Mode -> DState -> Bool
  | .PA1, .S2 | .FA1, .S2 => true
  | .KHV, .S3 | .PHV, .S3 | .PH0, .S3 | .PH1, .S3 => true
  | .PHV, .S4 | .FH0, .S4 | .PH0, .S4 | .FH1, .S4 | .PH1, .S4 => true
  | .KA1, .S5 | .PHV, .S5 | .PH0, .S5 | .PH1, .S5 => true
  | _, _ => false

def dfaStep : Word -> DState -> DState
  | V, .S3 => .S4
  | V, _ => .S2
  | K, .S3 => .S5
  | K, _ => .S3
  | Q, .S2 => .S4
  | Q, _ => .S2

def dfaRun : List Word -> DState -> DState
  | [], s => s
  | w :: u, s => dfaStep w (dfaRun u s)

lemma dfaStep_VV (s : DState) : dfaStep V (dfaStep V s) = .S2 := by
  cases s <;> rfl

inductive NKinds where
  | dbl2 | dbl1 | keep | half0 | half1
deriving DecidableEq, Repr

def validKind : NKinds -> Nat -> Nat -> Prop
  | .dbl2, n1, n2 => 2 <= n1 ∧ n2 = 2 * n1 - 2
  | .dbl1, n1, n2 => 2 <= n1 ∧ n2 = 2 * n1 - 1
  | .keep, n1, n2 => 2 <= n1 ∧ n2 = n1
  | .half0, n1, n2 => 2 <= n1 ∧ n1 % 2 = 0 ∧ n2 = n1 / 2
  | .half1, n1, n2 => 2 <= n1 ∧ n1 % 2 = 1 ∧ n2 = n1 / 2

inductive StepRule where
  | R00 | R01 | R02 | R03 | R04 | R05 | R06 | R07 | R08 | R09 | R10 | R11 | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 | R28 | R29 | R30 | R31 | R32 | R33
deriving DecidableEq, Repr

def rInMode : StepRule -> Mode
  | .R00 => .PA1
  | .R01 => .PA1
  | .R02 => .PA1
  | .R03 => .PA1
  | .R04 => .PA1
  | .R05 => .FA1
  | .R06 => .FA1
  | .R07 => .FA1
  | .R08 => .FA1
  | .R09 => .FA1
  | .R10 => .KA1
  | .R11 => .KHV
  | .R12 => .KHV
  | .R13 => .KHV
  | .R14 => .KHV
  | .R15 => .PHV
  | .R16 => .PHV
  | .R17 => .PHV
  | .R18 => .PHV
  | .R19 => .PHV
  | .R20 => .FH0
  | .R21 => .FH0
  | .R22 => .FH1
  | .R23 => .FH1
  | .R24 => .PH0
  | .R25 => .PH0
  | .R26 => .PH0
  | .R27 => .PH0
  | .R28 => .PH0
  | .R29 => .PH1
  | .R30 => .PH1
  | .R31 => .PH1
  | .R32 => .PH1
  | .R33 => .PH1

def rWord : StepRule -> Word
  | .R00 => V
  | .R01 => V
  | .R02 => V
  | .R03 => V
  | .R04 => Q
  | .R05 => V
  | .R06 => V
  | .R07 => V
  | .R08 => V
  | .R09 => Q
  | .R10 => K
  | .R11 => K
  | .R12 => K
  | .R13 => K
  | .R14 => K
  | .R15 => V
  | .R16 => K
  | .R17 => K
  | .R18 => K
  | .R19 => Q
  | .R20 => V
  | .R21 => Q
  | .R22 => V
  | .R23 => Q
  | .R24 => V
  | .R25 => K
  | .R26 => K
  | .R27 => K
  | .R28 => Q
  | .R29 => V
  | .R30 => K
  | .R31 => K
  | .R32 => K
  | .R33 => Q

def rKind : StepRule -> NKinds
  | .R00 => .dbl2
  | .R01 => .dbl1
  | .R02 => .half0
  | .R03 => .half1
  | .R04 => .keep
  | .R05 => .dbl2
  | .R06 => .dbl1
  | .R07 => .half0
  | .R08 => .half1
  | .R09 => .keep
  | .R10 => .keep
  | .R11 => .dbl2
  | .R12 => .dbl1
  | .R13 => .half0
  | .R14 => .half1
  | .R15 => .dbl1
  | .R16 => .half0
  | .R17 => .half1
  | .R18 => .dbl2
  | .R19 => .dbl1
  | .R20 => .dbl1
  | .R21 => .dbl1
  | .R22 => .dbl1
  | .R23 => .dbl1
  | .R24 => .dbl1
  | .R25 => .half0
  | .R26 => .half1
  | .R27 => .dbl2
  | .R28 => .dbl1
  | .R29 => .dbl1
  | .R30 => .half0
  | .R31 => .half1
  | .R32 => .dbl2
  | .R33 => .dbl1

def rOutMode : StepRule -> Mode
  | .R00 => .FA1
  | .R01 => .KA1
  | .R02 => .FH0
  | .R03 => .FH1
  | .R04 => .PHV
  | .R05 => .FA1
  | .R06 => .KA1
  | .R07 => .FH0
  | .R08 => .FH1
  | .R09 => .PHV
  | .R10 => .KHV
  | .R11 => .FA1
  | .R12 => .KA1
  | .R13 => .FH0
  | .R14 => .FH1
  | .R15 => .KHV
  | .R16 => .PH0
  | .R17 => .PH1
  | .R18 => .PA1
  | .R19 => .PA1
  | .R20 => .KHV
  | .R21 => .PA1
  | .R22 => .KHV
  | .R23 => .PA1
  | .R24 => .KHV
  | .R25 => .PH0
  | .R26 => .PH1
  | .R27 => .PA1
  | .R28 => .PA1
  | .R29 => .KHV
  | .R30 => .PH0
  | .R31 => .PH1
  | .R32 => .PA1
  | .R33 => .PA1

def rOb : StepRule -> zF
  | .R00 => [1, 0, 0, 1]
  | .R01 => [1, 0, 0, 1]
  | .R02 => [1, 0, 0, 0]
  | .R03 => [1, 0, 0, 1]
  | .R04 => [1, 0]
  | .R05 => [1, 0, 0, 1]
  | .R06 => [1, 0, 0, 1]
  | .R07 => [1, 0, 0, 0]
  | .R08 => [1, 0, 0, 1]
  | .R09 => [1, 0]
  | .R10 => [1, 0]
  | .R11 => [0, 1]
  | .R12 => [0, 1]
  | .R13 => [0, 0]
  | .R14 => [0, 1]
  | .R15 => [0, 1, 1, 0]
  | .R16 => [0, 0]
  | .R17 => [0, 1]
  | .R18 => [0, 1]
  | .R19 => [0, 1]
  | .R20 => [0, 1, 1, 0]
  | .R21 => [0, 1]
  | .R22 => [0, 1, 1, 0]
  | .R23 => [0, 1]
  | .R24 => [0, 1, 1, 0]
  | .R25 => [0, 0]
  | .R26 => [0, 1]
  | .R27 => [0, 1]
  | .R28 => [0, 1]
  | .R29 => [0, 1, 1, 0]
  | .R30 => [0, 0]
  | .R31 => [0, 1]
  | .R32 => [0, 1]
  | .R33 => [0, 1]

def rEmit : StepRule -> List Word
  | .R00 => [V]
  | .R01 => [V]
  | .R02 => [V]
  | .R03 => [V]
  | .R04 => []
  | .R05 => [V]
  | .R06 => [V]
  | .R07 => [V]
  | .R08 => [V]
  | .R09 => []
  | .R10 => []
  | .R11 => [V]
  | .R12 => [V]
  | .R13 => [V]
  | .R14 => [V]
  | .R15 => [V]
  | .R16 => [V]
  | .R17 => [V]
  | .R18 => [V]
  | .R19 => [V]
  | .R20 => [K]
  | .R21 => [K]
  | .R22 => [Q]
  | .R23 => [Q]
  | .R24 => [K]
  | .R25 => [K]
  | .R26 => [K]
  | .R27 => [K]
  | .R28 => [K]
  | .R29 => [Q]
  | .R30 => [Q]
  | .R31 => [Q]
  | .R32 => [Q]
  | .R33 => [Q]

def rG : StepRule -> Nat
  | .R00 => 0
  | .R01 => 2
  | .R02 => 0
  | .R03 => 0
  | .R04 => 3
  | .R05 => 0
  | .R06 => 2
  | .R07 => 0
  | .R08 => 0
  | .R09 => 3
  | .R10 => 1
  | .R11 => 0
  | .R12 => 2
  | .R13 => 0
  | .R14 => 0
  | .R15 => 0
  | .R16 => 0
  | .R17 => 0
  | .R18 => 0
  | .R19 => 0
  | .R20 => 0
  | .R21 => 0
  | .R22 => 0
  | .R23 => 0
  | .R24 => 0
  | .R25 => 0
  | .R26 => 0
  | .R27 => 0
  | .R28 => 0
  | .R29 => 0
  | .R30 => 0
  | .R31 => 0
  | .R32 => 0
  | .R33 => 0

lemma stepRule_rem (r : StepRule) :
    modeRem (rInMode r) ++ rOb r = zWt (rEmit r) ++ modeRem (rOutMode r) := by
  cases r <;> rfl

lemma stepRule_seg : ∀ (r : StepRule) (n1 n2 : Nat), validKind (rKind r) n1 n2 ->
    Seg (modeCalls (rInMode r) n1) (modeCalls (rOutMode r) n2) (zWt [rWord r]) (rOb r)
  | .R00, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureA_V_dbl2 hn h2
  | .R01, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureA_V_dbl1 hn h2
  | .R02, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureA_V_half0 hn hp h2
  | .R03, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureA_V_half1 hn hp h2
  | .R04, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureA_Q_keep hn h2
  | .R05, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfA_V_dbl2 hn h2
  | .R06, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfA_V_dbl1 hn h2
  | .R07, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfA_V_half0 hn hp h2
  | .R08, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfA_V_half1 hn hp h2
  | .R09, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfA_Q_keep hn h2
  | .R10, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CkA_K_keep hn h2
  | .R11, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CkH_K_dbl2 hn h2
  | .R12, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CkH_K_dbl1 hn h2
  | .R13, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CkH_K_half0 hn hp h2
  | .R14, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CkH_K_half1 hn hp h2
  | .R15, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_V_dbl1 hn h2
  | .R16, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_half0 hn hp h2
  | .R17, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_half1 hn hp h2
  | .R18, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_dbl2 hn h2
  | .R19, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_Q_dbl1 hn h2
  | .R20, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfH_V_dbl1 hn h2
  | .R21, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfH_Q_dbl1 hn h2
  | .R22, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfH_V_dbl1 hn h2
  | .R23, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_CfH_Q_dbl1 hn h2
  | .R24, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_V_dbl1 hn h2
  | .R25, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_half0 hn hp h2
  | .R26, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_half1 hn hp h2
  | .R27, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_dbl2 hn h2
  | .R28, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_Q_dbl1 hn h2
  | .R29, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_V_dbl1 hn h2
  | .R30, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_half0 hn hp h2
  | .R31, _, _, h => by rcases h with ⟨hn, hp, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_half1 hn hp h2
  | .R32, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_K_dbl2 hn h2
  | .R33, _, _, h => by rcases h with ⟨hn, h2⟩; simpa [rInMode, rOutMode, rWord, rOb, modeCalls, zWt] using raw_PureH_Q_dbl1 hn h2

inductive Scan : Mode -> DState -> Nat -> List Word -> Mode -> DState -> Nat -> List Word -> Nat -> Prop where
  | nil (m : Mode) (s : DState) (n : Nat) (hm : modeMatches m s = true) (hn : 2 <= n) :
      Scan m s n [] m s n [] 0
  | step {r : StepRule} {s1 s2 s3 : DState} {n1 n2 n3 g : Nat} {u v : List Word} {m3 : Mode}
      (hs : s1 = dfaStep (rWord r) s2)
      (hm1 : modeMatches (rInMode r) s1 = true)
      (hv : validKind (rKind r) n1 n2)
      (hrest : Scan (rOutMode r) s2 n2 u m3 s3 n3 v g) :
      Scan (rInMode r) s1 n1 (rWord r :: u) m3 s3 n3 (rEmit r ++ v) (rG r + g)

lemma Scan_match_in {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) : modeMatches m1 s1 = true := by
  cases h with
  | nil _ _ _ hm _ => exact hm
  | step _ hm1 _ _ => exact hm1

lemma Scan_exit_ge2 {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) : 2 <= n2 ∧ modeMatches m2 s2 = true := by
  induction h with
  | nil _ _ _ hm hn => exact ⟨hn, hm⟩
  | step _ _ _ _ ih => exact ih

lemma Scan_append {m1 : Mode} {s1 : DState} {n1 : Nat} {u1 : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v1 : List Word} {g1 : Nat}
    (h1 : Scan m1 s1 n1 u1 m2 s2 n2 v1 g1) :
    ∀ {m3 : Mode} {s3 : DState} {n3 : Nat} {u2 v2 : List Word} {g2 : Nat},
      Scan m2 s2 n2 u2 m3 s3 n3 v2 g2 ->
      Scan m1 s1 n1 (u1 ++ u2) m3 s3 n3 (v1 ++ v2) (g1 + g2) := by
  induction h1 with
  | nil _ _ _ _ _ => intro _ _ _ _ _ _ h2; simpa using h2
  | @step r s1 s2 _ n1 n2 _ g1 u1 v1 _ hs hm1 hv _ ih =>
    intro _ _ _ _ v2 g2 h2
    have hI := ih h2
    have h_v : rEmit r ++ (v1 ++ v2) = (rEmit r ++ v1) ++ v2 := by simp [List.append_assoc]
    have h_g : rG r + (g1 + g2) = rG r + g1 + g2 := by omega
    rw [<- h_v, <- h_g]
    exact Scan.step hs hm1 hv hI

lemma Side_of_Scan {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    ∀ (u_tail w_tail : zB),
      Side (modeCalls m2 n2) u_tail w_tail ->
      ∃ w_out,
        Side (modeCalls m1 n1) (zTs u u_tail) w_out ∧
        modeRem m1 +> w_out = zTs v (modeRem m2 +> w_tail) := by
  induction h with
  | nil _ _ _ _ _ =>
    intro u_tail w_tail hSide
    exact ⟨w_tail, hSide, rfl⟩
  | @step r _ _ _ n1 n2 _ _ u v m3 _ _ hv _ ih =>
    intro u_tail w_tail hSide
    rcases ih u_tail w_tail hSide with ⟨w_mid, hSide_mid, hEq_mid⟩
    have hSeg1 := stepRule_seg r n1 n2 hv
    have hSide1 := zSc hSeg1 hSide_mid
    have h_in_eq : zWt [rWord r] +> zTs u u_tail = zTs (rWord r :: u) u_tail := by
      cases hw : rWord r <;> simp [zWt, zTs]
    rw [h_in_eq] at hSide1
    refine ⟨rOb r +> w_mid, hSide1, ?_⟩
    rw [<- append_assoc, stepRule_rem r, append_assoc, hEq_mid, zWt_zTs, <- zTs_append]

def Step (u u' : List Word) : Prop :=
  ∃ body m_end n_end v_body da H g,
    u = body ++ [Q] ∧
    (m_end = .PA1 ∨ m_end = .FA1) ∧
    Scan .PA1 .S2 3 body m_end .S2 n_end v_body g ∧
    zDg n_end H da ∧
    u' = V :: (v_body ++ V :: da)

inductive Rounds : List Word -> List Word -> Prop where
  | refl (u : List Word) : Rounds u u
  | next {u v w : List Word} : Step u v -> Rounds v w -> Rounds u w

lemma Step_exec {u u' : List Word} (h : Step u u') :
    (zCf (zTs u default)) [tm]⊢⁺ (zCf (zTs u' default)) := by
  rcases h with ⟨body, m_end, n_end, v_body, da, H, g, rfl, hm_end, hScan, hDg, rfl⟩
  have hn_end : 2 <= n_end := (Scan_exit_ge2 hScan).1
  have hSide_da := Side_ch_default hDg
  have hSegQ : Seg (modeCalls m_end n_end) (modeCalls .PHV n_end) Q_u [1, 0] := by
    rcases hm_end with rfl | rfl
    · exact raw_PureA_Q_keep hn_end rfl
    · exact raw_CfA_Q_keep hn_end rfl
  have hSideQ := zSc hSegQ hSide_da
  rcases Side_of_Scan hScan (Q_u +> default) ([1, 0] +> zTs' da default) hSideQ with ⟨w_out, hSide0, hEq0⟩
  have h_u_eq : zTs body (Q_u +> default) = zTs (body ++ [Q]) default := by
    rw [zTs_append]; rfl
  rw [h_u_eq] at hSide0
  have h_rem_end : modeRem m_end = [1] := by rcases hm_end with rfl | rfl <;> rfl
  rw [h_rem_end] at hEq0
  dsimp [modeRem] at hEq0
  have h_mid : (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> zTs' da default = zTs (V :: da) default :=
    zTs_V_shift da
  rw [h_mid, <- zTs_append] at hEq0
  have hTurn := Side_turnaround hSide0
  have h_top : [1, 1, 0, 0, 1] +> w_out = zTs (V :: (v_body ++ V :: da)) default := by
    change V_u +> ((1 : Fin 2) >> w_out) = V_u +> zTs (v_body ++ V :: da) default
    rw [hEq0]
  rwa [h_top] at hTurn

lemma Rounds_exec {u v : List Word} (h : Rounds u v) :
    (zCf (zTs u default)) [tm]⊢* (zCf (zTs v default)) := by
  induction h with
  | refl _ => exact ⟨0, rfl⟩
  | next hS _ ih => exact zPs (z02 (Step_exec hS) ih)

-- Section 3: Affine Evaluator for Concrete Rounds and Symbolic `head_w`, `s_full`, `top_body`
def evalAffineScan : List StepRule -> Mode -> DState -> Nat -> Nat -> List Word ->
    Option (Mode × Nat × Nat × List Word × Nat)
  | [], m, s, mb, cb, [] =>
    if modeMatches m s && 2 <= cb then some (m, mb, cb, [], 0) else none
  | r :: rs, m, s, mb, cb, w :: u =>
    if m == rInMode r && w == rWord r && modeMatches m (dfaStep w (dfaRun u s)) && 2 <= cb then
      match rKind r with
      | .dbl2 =>
        match evalAffineScan rs (rOutMode r) s (2 * mb) (2 * cb - 2) u with
        | none => none
        | some (m_end, mb_end, cb_end, v, g) =>
          some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
      | .dbl1 =>
        match evalAffineScan rs (rOutMode r) s (2 * mb) (2 * cb - 1) u with
        | none => none
        | some (m_end, mb_end, cb_end, v, g) =>
          some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
      | .keep =>
        match evalAffineScan rs (rOutMode r) s mb cb u with
        | none => none
        | some (m_end, mb_end, cb_end, v, g) =>
          some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
      | .half0 =>
        if mb % 2 == 0 && cb % 2 == 0 then
          match evalAffineScan rs (rOutMode r) s (mb / 2) (cb / 2) u with
          | none => none
          | some (m_end, mb_end, cb_end, v, g) =>
            some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
        else none
      | .half1 =>
        if mb % 2 == 0 && cb % 2 == 1 then
          match evalAffineScan rs (rOutMode r) s (mb / 2) (cb / 2) u with
          | none => none
          | some (m_end, mb_end, cb_end, v, g) =>
            some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
        else none
    else none
  | _, _, _, _, _, _ => none

lemma evalAffineScan_sound :
    ∀ rs m s mb cb u m_end mb_end cb_end v g q,
      evalAffineScan rs m s mb cb u = some (m_end, mb_end, cb_end, v, g) ->
      Scan m (dfaRun u s) (mb * q + cb) u m_end s (mb_end * q + cb_end) v g := by
  intro rs
  induction rs with
  | nil =>
    intro m s mb cb u m_end mb_end cb_end v g q h
    cases u with
    | nil =>
      simp only [evalAffineScan] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact Scan.nil m s _ hc.1 (by omega)
    | cons _ _ => unfold evalAffineScan at h; contradiction
  | cons r rs ih =>
    intro m s mb cb u m_end mb_end cb_end v g q h
    cases u with
    | nil => unfold evalAffineScan at h; contradiction
    | cons w u =>
      change evalAffineScan (r :: rs) m s mb cb (w :: u) = _ at h
      unfold evalAffineScan at h
      cases hcond : (m == rInMode r && w == rWord r && modeMatches m (dfaStep w (dfaRun u s)) && 2 <= cb)
      · rw [hcond] at h; simp at h
      · rw [hcond, if_pos rfl] at h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        rcases hcond with ⟨⟨⟨rfl, rfl⟩, hm1⟩, hcb⟩
        cases hk : rKind r <;> simp only [hk] at h
        · -- dbl2
          cases hrec : evalAffineScan rs (rOutMode r) s (2 * mb) (2 * cb - 2) u with
          | none => rw [hrec] at h; contradiction
          | some val =>
            rw [hrec] at h; rcases val with ⟨me, mbe, cbe, v1, g1⟩
            simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
            have hI := ih _ _ _ _ _ _ _ _ _ _ q hrec
            have hm_eq : 2 * mb * q = 2 * (mb * q) := by ring
            have h_eq : 2 * mb * q + (2 * cb - 2) = 2 * (mb * q + cb) - 2 := by omega
            rw [h_eq] at hI
            exact Scan.step rfl hm1 (by rw [hk]; exact ⟨by omega, rfl⟩) hI
        · -- dbl1
          cases hrec : evalAffineScan rs (rOutMode r) s (2 * mb) (2 * cb - 1) u with
          | none => rw [hrec] at h; contradiction
          | some val =>
            rw [hrec] at h; rcases val with ⟨me, mbe, cbe, v1, g1⟩
            simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
            have hI := ih _ _ _ _ _ _ _ _ _ _ q hrec
            have hm_eq : 2 * mb * q = 2 * (mb * q) := by ring
            have h_eq : 2 * mb * q + (2 * cb - 1) = 2 * (mb * q + cb) - 1 := by omega
            rw [h_eq] at hI
            exact Scan.step rfl hm1 (by rw [hk]; exact ⟨by omega, rfl⟩) hI
        · -- keep
          cases hrec : evalAffineScan rs (rOutMode r) s mb cb u with
          | none => rw [hrec] at h; contradiction
          | some val =>
            rw [hrec] at h; rcases val with ⟨me, mbe, cbe, v1, g1⟩
            simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
            have hI := ih _ _ _ _ _ _ _ _ _ _ q hrec
            exact Scan.step rfl hm1 (by rw [hk]; exact ⟨by omega, rfl⟩) hI
        · -- half0
          cases hp0 : (mb % 2 == 0 && cb % 2 == 0)
          · rw [hp0] at h; simp at h
          · rw [hp0, if_pos rfl] at h
            simp only [Bool.and_eq_true, beq_iff_eq] at hp0
            cases hrec : evalAffineScan rs (rOutMode r) s (mb / 2) (cb / 2) u with
            | none => rw [hrec] at h; contradiction
            | some val =>
              rw [hrec] at h; rcases val with ⟨me, mbe, cbe, v1, g1⟩
              simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
              have hI := ih _ _ _ _ _ _ _ _ _ _ q hrec
              have hm2 : 2 * (mb / 2) = mb := by omega
              have hm_eq : 2 * (mb / 2 * q) = mb * q := by
                calc 2 * (mb / 2 * q) = (2 * (mb / 2)) * q := by ring
                  _ = mb * q := by rw [hm2]
              have h_eq : mb / 2 * q + cb / 2 = (mb * q + cb) / 2 := by omega
              rw [h_eq] at hI
              exact Scan.step rfl hm1 (by rw [hk]; exact ⟨by omega, by omega, rfl⟩) hI
        · -- half1
          cases hp1 : (mb % 2 == 0 && cb % 2 == 1)
          · rw [hp1] at h; simp at h
          · rw [hp1, if_pos rfl] at h
            simp only [Bool.and_eq_true, beq_iff_eq] at hp1
            cases hrec : evalAffineScan rs (rOutMode r) s (mb / 2) (cb / 2) u with
            | none => rw [hrec] at h; contradiction
            | some val =>
              rw [hrec] at h; rcases val with ⟨me, mbe, cbe, v1, g1⟩
              simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
              have hI := ih _ _ _ _ _ _ _ _ _ _ q hrec
              have hm2 : 2 * (mb / 2) = mb := by omega
              have hm_eq : 2 * (mb / 2 * q) = mb * q := by
                calc 2 * (mb / 2 * q) = (2 * (mb / 2)) * q := by ring
                  _ = mb * q := by rw [hm2]
              have h_eq : mb / 2 * q + cb / 2 = (mb * q + cb) / 2 := by omega
              rw [h_eq] at hI
              exact Scan.step rfl hm1 (by rw [hk]; exact ⟨by omega, by omega, rfl⟩) hI

def checkStep (rs : List StepRule) (body da u' : List Word) : Bool :=
  (dfaRun body .S2 == .S2) &&
  match evalAffineScan rs .PA1 .S2 0 3 body with
  | some (m_end, 0, n_end, v_body, _) =>
    (m_end == .PA1 || m_end == .FA1) && checkDg n_end da && (u' == V :: (v_body ++ V :: da))
  | _ => false

lemma checkStep_sound (rs : List StepRule) (body da u' : List Word)
    (h : checkStep rs body da u' = true) : Step (body ++ [Q]) u' := by
  unfold checkStep at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hdfa, hrest⟩
  rw [beq_iff_eq] at hdfa
  cases hrec : evalAffineScan rs .PA1 .S2 0 3 body with
  | none => rw [hrec] at hrest; contradiction
  | some val =>
    rw [hrec] at hrest
    rcases val with ⟨m_end, mb_end, n_end, v_body, g⟩
    rcases mb_end with _ | mb_end
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrest
      rcases hrest with ⟨⟨hm_end, hdg⟩, hu'⟩
      have hScan := evalAffineScan_sound rs .PA1 .S2 0 3 body m_end 0 n_end v_body g 0 hrec
      rw [hdfa] at hScan
      simp only [Nat.zero_mul, Nat.zero_add] at hScan
      exact ⟨body, m_end, n_end, v_body, da, da.length, g, rfl, hm_end, hScan, checkDg_sound n_end da hdg, hu'⟩
    · contradiction

-- Section 4: Algebraic Identities & Potential Bounds Across All 34 `StepRule`s
def zW : List Word -> Rat
  | [] => 0
  | V :: u => 1 / 8 + (1 / 2) * zW u
  | K :: u => 1 + 2 * zW u
  | Q :: u => 1 / 4 + 2 * zW u

lemma zW_nonneg (u : List Word) : 0 <= zW u := by
  induction u with
  | nil => simp [zW]
  | cons a u ih => cases a <;> (dsimp [zW]; linarith)

lemma zW_append (u t : List Word) : zW (u ++ t) = zW u + z13 u * zW t := by
  induction u with
  | nil => simp [zW, z13]
  | cons a u ih => cases a <;> (dsimp [zW, z13]; rw [ih]; ring)

def psi : Mode -> Rat
  | .KA1 | .KHV | .PHV => 1
  | _ => 4

def phi : Mode -> Rat
  | .FH0 | .FH1 | .PH0 | .PH1 => 4
  | _ => 1

def alpha : Mode -> Rat
  | .PA1 | .FA1 => 96
  | _ => 24

def addW : Word -> Rat
  | V => 1 / 8
  | K => 1
  | Q => 1 / 4

def mulW : Word -> Rat
  | V => 1 / 2
  | K => 2
  | Q => 2

lemma zW_cons (w : Word) (u : List Word) : zW (w :: u) = addW w + mulW w * zW u := by
  cases w <;> rfl

def multZW : Mode -> Rat
  | .KHV => 15 / 32
  | .PHV => 15 / 4
  | _ => 15 / 8

def cSt : Mode -> Nat -> Rat
  | .PA1, 0 | .FA1, 0 => 35 / 128
  | .PA1, 1 | .FA1, 1 => 7 / 256
  | .FH0, _ | .PH0, _ => 49 / 64
  | .FH1, _ | .PH1, _ => 1 / 64
  | .KA1, 0 | .KHV, 0 => 1
  | .KA1, 1 | .KHV, 1 => 0
  | _, _ => 0

def kqA : Mode -> DState -> Rat
  | .PA1, .S2 | .FA1, .S2 => 1 / 8
  | .KA1, .S5 => 1 / 64
  | .KHV, .S3 => 1 / 32
  | .PHV, .S4 => 1 / 32
  | .PHV, .S3 | .PHV, .S5 => 1 / 4
  | .FH0, .S4 | .PH0, .S4 | .FH1, .S4 | .PH1, .S4 => 1 / 8
  | .PH0, .S3 | .PH0, .S5 | .PH1, .S3 | .PH1, .S5 => 1
  | _, _ => 0

def kqC : Mode -> DState -> Rat
  | .PA1, .S2 | .FA1, .S2 => -1 / 8
  | .KA1, .S5 => 1 / 2
  | .KHV, .S3 => 1 / 2
  | .PHV, .S4 => 1 / 16
  | .PHV, .S3 | .PHV, .S5 => -3 / 8
  | .FH0, .S4 | .PH0, .S4 => 3 / 4
  | .FH1, .S4 | .PH1, .S4 => 0
  | .PH0, .S3 | .PH0, .S5 => -1
  | .PH1, .S3 | .PH1, .S5 => -7 / 4
  | _, _ => 0

lemma stepRule_z13 (r : StepRule) :
    psi (rOutMode r) * z13 (rEmit r) * ((2 ^ (rG r) : Nat) : Rat) = psi (rInMode r) * z13 [rWord r] := by
  cases r <;> norm_num [rInMode, rOutMode, rEmit, rG, rWord, psi, z13]

lemma Scan_z13 {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    psi m2 * z13 v * ((2 ^ g : Nat) : Rat) = psi m1 * z13 u := by
  induction h with
  | nil _ _ _ _ _ => simp [z13]
  | @step r _ _ _ _ _ _ g u v m3 _ _ _ _ ih =>
    have hr := stepRule_z13 r
    have hu : z13 (rWord r :: u) = z13 [rWord r] * z13 u := by
      cases rWord r <;> (dsimp [z13]; ring)
    rw [z13_append, Nat.pow_add, Nat.cast_mul, hu]
    calc psi m3 * (z13 (rEmit r) * z13 v) * (((2 ^ rG r : Nat) : Rat) * ((2 ^ g : Nat) : Rat))
      _ = (psi m3 * z13 v * ((2 ^ g : Nat) : Rat)) * (z13 (rEmit r) * ((2 ^ rG r : Nat) : Rat)) := by ring
      _ = (psi (rOutMode r) * z13 u) * (z13 (rEmit r) * ((2 ^ rG r : Nat) : Rat)) := by rw [ih]
      _ = (psi (rOutMode r) * z13 (rEmit r) * ((2 ^ rG r : Nat) : Rat)) * z13 u := by ring
      _ = (psi (rInMode r) * z13 [rWord r]) * z13 u := by rw [hr]
      _ = psi (rInMode r) * (z13 [rWord r] * z13 u) := by ring

def n2Slope : NKinds -> Rat
  | .dbl2 | .dbl1 => 2
  | .keep => 1
  | .half0 | .half1 => 1 / 2

def n2Const : NKinds -> Rat
  | .dbl2 => -2
  | .dbl1 => -1
  | .keep | .half0 => 0
  | .half1 => -1 / 2

lemma validKind_rat {k : NKinds} {n1 n2 : Nat} (hv : validKind k n1 n2) :
    (n2 : Rat) = n2Slope k * (n1 : Rat) + n2Const k := by
  cases k with
  | dbl2 =>
    rcases hv with ⟨hn, rfl⟩
    have h1 : (2 * n1 - 2 : Nat) + 2 = 2 * n1 := by omega
    have hr : ((2 * n1 - 2 : Nat) : Rat) + 2 = 2 * (n1 : Rat) := by exact_mod_cast h1
    dsimp [n2Slope, n2Const]; linarith
  | dbl1 =>
    rcases hv with ⟨hn, rfl⟩
    have h1 : (2 * n1 - 1 : Nat) + 1 = 2 * n1 := by omega
    have hr : ((2 * n1 - 1 : Nat) : Rat) + 1 = 2 * (n1 : Rat) := by exact_mod_cast h1
    dsimp [n2Slope, n2Const]; linarith
  | keep => rcases hv with ⟨_, rfl⟩; dsimp [n2Slope, n2Const]; ring
  | half0 =>
    rcases hv with ⟨_, hp, rfl⟩
    have h1 : (n1 / 2) * 2 = n1 := by omega
    have hr : ((n1 / 2 : Nat) : Rat) * 2 = (n1 : Rat) := by exact_mod_cast h1
    dsimp [n2Slope, n2Const]; linarith
  | half1 =>
    rcases hv with ⟨_, hp, rfl⟩
    have h1 : 1 + (n1 / 2) * 2 = n1 := by omega
    have hr : 1 + ((n1 / 2 : Nat) : Rat) * 2 = (n1 : Rat) := by exact_mod_cast h1
    dsimp [n2Slope, n2Const]; linarith

lemma delta_step_le (pIn pOut slope cst z13e zWe x : Rat)
    (hc : pIn = pOut * slope * z13e ∧ 0 <= -pOut * cst * z13e ∧ -pOut * cst * z13e <= 16 * zWe) :
    0 <= pIn * x - pOut * (slope * x + cst) * z13e ∧
    pIn * x - pOut * (slope * x + cst) * z13e <= 16 * zWe := by
  rcases hc with ⟨hs, hb1, hb2⟩
  have h_eq : pIn * x - pOut * (slope * x + cst) * z13e = -pOut * cst * z13e := by
    rw [hs]; ring
  rw [h_eq]; exact ⟨hb1, hb2⟩

lemma stepRule_delta (r : StepRule) (n1 n2 : Nat) (hv : validKind (rKind r) n1 n2) :
    0 <= phi (rInMode r) * (n1 : Rat) - phi (rOutMode r) * (n2 : Rat) * z13 (rEmit r) ∧
    phi (rInMode r) * (n1 : Rat) - phi (rOutMode r) * (n2 : Rat) * z13 (rEmit r) <= 16 * zW (rEmit r) := by
  rw [validKind_rat hv]
  cases r <;> refine delta_step_le _ _ _ _ _ _ _ ?_ <;>
    norm_num [rInMode, rOutMode, rKind, rEmit, phi, n2Slope, n2Const, z13, zW]

lemma Scan_delta {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    0 <= phi m1 * (n1 : Rat) - phi m2 * (n2 : Rat) * z13 v ∧
    phi m1 * (n1 : Rat) - phi m2 * (n2 : Rat) * z13 v <= 16 * zW v := by
  induction h with
  | nil _ _ _ _ _ => simp [z13, zW]
  | @step r _ _ _ n1 n2 n3 _ _ v m3 _ _ hv _ ih =>
    rcases stepRule_delta r n1 n2 hv with ⟨hs_lo, hs_hi⟩
    rcases ih with ⟨ih_lo, ih_hi⟩
    have hz_em : 0 <= z13 (rEmit r) := le_of_lt (z13_pos (rEmit r))
    have hm_lo := mul_le_mul_of_nonneg_left ih_lo hz_em
    have hm_hi := mul_le_mul_of_nonneg_left ih_hi hz_em
    rw [z13_append, zW_append]
    constructor <;> linarith

lemma survive_step_le (a1 aW muW slope cst a2 zw : Rat) {n1 n2 : Nat}
    (hz : 0 <= zw)
    (hq : (n2 : Rat) = slope * (n1 : Rat) + cst)
    (hb : a1 * (aW + muW * zw) <= (n1 : Rat) - 2)
    (hc : 0 <= slope ∧ 0 <= a2 ∧ 2 <= slope * (2 + a1 * aW) + cst ∧ a2 <= slope * a1 * muW) :
    2 <= n2 ∧ a2 * zw <= (n2 : Rat) - 2 := by
  rcases hc with ⟨hs_pos, ha2_pos, hb_n2, hs_ok⟩
  have h_lb : 2 + a1 * (aW + muW * zw) <= (n1 : Rat) := by linarith
  have hm1 : slope * (2 + a1 * (aW + muW * zw)) <= slope * (n1 : Rat) :=
    mul_le_mul_of_nonneg_left h_lb hs_pos
  have hm2 : 0 <= (slope * a1 * muW - a2) * zw := mul_nonneg (by linarith) hz
  have hm3 : 0 <= a2 * zw := mul_nonneg ha2_pos hz
  have h_lin : slope * (2 + a1 * (aW + muW * zw)) + cst =
      (slope * (2 + a1 * aW) + cst) + slope * a1 * muW * zw := by ring
  have hn2_rat : (2 : Rat) <= (n2 : Rat) := by linarith
  exact ⟨by exact_mod_cast hn2_rat, by linarith⟩

def pickRule : Mode -> Word -> DState -> Nat -> StepRule
  | .PA1, V, .S2, 0 => .R00
  | .PA1, V, .S2, 1 => .R00
  | .PA1, V, .S4, 0 => .R02
  | .PA1, V, .S4, 1 => .R03
  | .PA1, V, .S5, 0 => .R01
  | .PA1, V, .S5, 1 => .R01
  | .PA1, Q, .S3, 0 => .R04
  | .PA1, Q, .S3, 1 => .R04
  | .PA1, Q, .S4, 0 => .R04
  | .PA1, Q, .S4, 1 => .R04
  | .PA1, Q, .S5, 0 => .R04
  | .PA1, Q, .S5, 1 => .R04
  | .FA1, V, .S2, 0 => .R05
  | .FA1, V, .S2, 1 => .R05
  | .FA1, V, .S4, 0 => .R07
  | .FA1, V, .S4, 1 => .R08
  | .FA1, V, .S5, 0 => .R06
  | .FA1, V, .S5, 1 => .R06
  | .FA1, Q, .S3, 0 => .R09
  | .FA1, Q, .S3, 1 => .R09
  | .FA1, Q, .S4, 0 => .R09
  | .FA1, Q, .S4, 1 => .R09
  | .FA1, Q, .S5, 0 => .R09
  | .FA1, Q, .S5, 1 => .R09
  | .KA1, K, .S3, 0 => .R10
  | .KA1, K, .S3, 1 => .R10
  | .KHV, K, .S2, 0 => .R11
  | .KHV, K, .S2, 1 => .R11
  | .KHV, K, .S4, 0 => .R13
  | .KHV, K, .S4, 1 => .R14
  | .KHV, K, .S5, 0 => .R12
  | .KHV, K, .S5, 1 => .R12
  | .PHV, V, .S3, 0 => .R15
  | .PHV, V, .S3, 1 => .R15
  | .PHV, K, .S2, 0 => .R18
  | .PHV, K, .S2, 1 => .R18
  | .PHV, K, .S3, 0 => .R16
  | .PHV, K, .S3, 1 => .R17
  | .PHV, K, .S4, 0 => .R16
  | .PHV, K, .S4, 1 => .R17
  | .PHV, K, .S5, 0 => .R16
  | .PHV, K, .S5, 1 => .R17
  | .PHV, Q, .S2, 0 => .R19
  | .PHV, Q, .S2, 1 => .R19
  | .FH0, V, .S3, 0 => .R20
  | .FH0, V, .S3, 1 => .R20
  | .FH0, Q, .S2, 0 => .R21
  | .FH0, Q, .S2, 1 => .R21
  | .FH1, V, .S3, 0 => .R22
  | .FH1, V, .S3, 1 => .R22
  | .FH1, Q, .S2, 0 => .R23
  | .FH1, Q, .S2, 1 => .R23
  | .PH0, V, .S3, 0 => .R24
  | .PH0, V, .S3, 1 => .R24
  | .PH0, K, .S2, 0 => .R27
  | .PH0, K, .S2, 1 => .R27
  | .PH0, K, .S3, 0 => .R25
  | .PH0, K, .S3, 1 => .R26
  | .PH0, K, .S4, 0 => .R25
  | .PH0, K, .S4, 1 => .R26
  | .PH0, K, .S5, 0 => .R25
  | .PH0, K, .S5, 1 => .R26
  | .PH0, Q, .S2, 0 => .R28
  | .PH0, Q, .S2, 1 => .R28
  | .PH1, V, .S3, 0 => .R29
  | .PH1, V, .S3, 1 => .R29
  | .PH1, K, .S2, 0 => .R32
  | .PH1, K, .S2, 1 => .R32
  | .PH1, K, .S3, 0 => .R30
  | .PH1, K, .S3, 1 => .R31
  | .PH1, K, .S4, 0 => .R30
  | .PH1, K, .S4, 1 => .R31
  | .PH1, K, .S5, 0 => .R30
  | .PH1, K, .S5, 1 => .R31
  | .PH1, Q, .S2, 0 => .R33
  | .PH1, Q, .S2, 1 => .R33
  | _, _, _, _ => .R00

def evalKind : NKinds -> Nat -> Nat
  | .dbl2, n1 => 2 * n1 - 2
  | .dbl1, n1 => 2 * n1 - 1
  | .keep, n1 => n1
  | .half0, n1 | .half1, n1 => n1 / 2

def kindParOk : NKinds -> Nat -> Bool
  | .half0, p => p == 0
  | .half1, p => p == 1
  | _, _ => true

lemma validKind_eval {k : NKinds} {n1 : Nat} (hn1 : 2 <= n1)
    (hok : kindParOk k (n1 % 2) = true) : validKind k n1 (evalKind k n1) := by
  cases k with
  | dbl2 | dbl1 | keep => exact ⟨hn1, rfl⟩
  | half0 | half1 =>
    dsimp [kindParOk] at hok
    rw [beq_iff_eq] at hok
    exact ⟨hn1, hok, rfl⟩

def checkPickRule (m1 : Mode) (w : Word) (s2 : DState) (par : Nat) : Bool :=
  let r := pickRule m1 w s2 par
  if modeMatches m1 (dfaStep w s2) then
    (rInMode r == m1) && (rWord r == w) && modeMatches (rOutMode r) s2 && kindParOk (rKind r) par
  else
    true

lemma checkPickRule_all (m1 : Mode) (w : Word) (s2 : DState) (par : Nat)
    (hp : par = 0 ∨ par = 1) : checkPickRule m1 w s2 par = true := by
  rcases hp with rfl | rfl <;> cases m1 <;> cases w <;> cases s2 <;> decide

lemma stepRule_survive (r : StepRule) (n1 n2 : Nat) (zw : Rat)
    (hz : 0 <= zw) (hv : validKind (rKind r) n1 n2)
    (hb : alpha (rInMode r) * (addW (rWord r) + mulW (rWord r) * zw) <= (n1 : Rat) - 2) :
    2 <= n2 ∧ alpha (rOutMode r) * zw <= (n2 : Rat) - 2 := by
  cases r <;> refine survive_step_le _ _ _ _ _ _ zw hz (validKind_rat hv) hb ?_ <;>
    norm_num [rInMode, rWord, rKind, rOutMode, alpha, addW, mulW, n2Slope, n2Const]

lemma step_survive (m1 : Mode) (w : Word) (s2 : DState) (n1 : Nat) (zw : Rat)
    (hz : 0 <= zw) (hn1 : 2 <= n1) (hm1 : modeMatches m1 (dfaStep w s2) = true)
    (hb : alpha m1 * (addW w + mulW w * zw) <= (n1 : Rat) - 2) :
    ∃ (r : StepRule) (n2 : Nat),
      rInMode r = m1 ∧ rWord r = w ∧ dfaStep (rWord r) s2 = dfaStep w s2 ∧
      modeMatches (rOutMode r) s2 = true ∧ validKind (rKind r) n1 n2 ∧
      2 <= n2 ∧ alpha (rOutMode r) * zw <= (n2 : Rat) - 2 := by
  let r := pickRule m1 w s2 (n1 % 2)
  have hc := checkPickRule_all m1 w s2 (n1 % 2) (Nat.mod_two_eq_zero_or_one n1)
  unfold checkPickRule at hc
  rw [hm1] at hc
  simp only [ite_true, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨hin, hword⟩, hm2⟩, hpar⟩
  have hv : validKind (rKind r) n1 (evalKind (rKind r) n1) := validKind_eval hn1 hpar
  have hb' : alpha (rInMode r) * (addW (rWord r) + mulW (rWord r) * zw) <= (n1 : Rat) - 2 := by
    rw [hin, hword]; exact hb
  rcases stepRule_survive r n1 (evalKind (rKind r) n1) zw hz hv hb' with ⟨hn2, hb2⟩
  exact ⟨r, evalKind (rKind r) n1, hin, hword, by rw [hword], hm2, hv, hn2, hb2⟩

lemma Scan_survive (u : List Word) (s_end : DState) :
    ∀ (m1 : Mode) (n1 : Nat),
      2 <= n1 ->
      modeMatches m1 (dfaRun u s_end) = true ->
      alpha m1 * zW u <= (n1 : Rat) - 2 ->
      ∃ m2 n2 v g, Scan m1 (dfaRun u s_end) n1 u m2 s_end n2 v g := by
  induction u with
  | nil =>
    intro m1 n1 hn1 hm1 _
    exact ⟨m1, n1, [], 0, Scan.nil m1 s_end n1 hm1 hn1⟩
  | cons w u ih =>
    intro m1 n1 hn1 hm1 hb
    have hzw : 0 <= zW u := zW_nonneg u
    rw [zW_cons] at hb
    rcases step_survive m1 w (dfaRun u s_end) n1 (zW u) hzw hn1 hm1 hb
      with ⟨r, n2, rfl, rfl, _, hm2, hv, hn2, hb2⟩
    rcases ih (rOutMode r) n2 hn2 hm2 hb2 with ⟨m_end, n_end, v, g, hS⟩
    exact ⟨m_end, n_end, rEmit r ++ v, rG r + g, Scan.step rfl hm1 hv hS⟩

lemma zw_step_le (zWe z13e mOut cOut mIn aW muW cIn zw_u : Rat)
    (hc : z13e * mOut <= mIn * muW ∧ zWe + z13e * cOut <= mIn * aW + cIn)
    (hz : 0 <= zw_u) :
    zWe + z13e * (mOut * zw_u + cOut) <= mIn * (aW + muW * zw_u) + cIn := by
  rcases hc with ⟨hs, hb⟩
  have hm : 0 <= (mIn * muW - z13e * mOut) * zw_u := mul_nonneg (by linarith) hz
  linarith

def validParProp (k : NKinds) (n1 n2 : Nat) : Prop :=
  match k with
  | .dbl2 => n2 % 2 = 0
  | .dbl1 => n2 % 2 = 1
  | .keep => n2 % 2 = n1 % 2
  | .half0 => n1 % 2 = 0
  | .half1 => n1 % 2 = 1

lemma validKind_par {k : NKinds} {n1 n2 : Nat} (hv : validKind k n1 n2) :
    validParProp k n1 n2 := by
  cases k with
  | dbl2 | dbl1 => rcases hv with ⟨hn1, rfl⟩; dsimp [validParProp]; omega
  | keep => rcases hv with ⟨_, rfl⟩; rfl
  | half0 | half1 => exact hv.2.1

lemma stepRule_zW_contract (r : StepRule) (n1 n2 : Nat) (zw_u : Rat)
    (hzw : 0 <= zw_u) (hv : validKind (rKind r) n1 n2) :
    zW (rEmit r) + z13 (rEmit r) * (multZW (rOutMode r) * zw_u + cSt (rOutMode r) (n2 % 2)) <=
    multZW (rInMode r) * (addW (rWord r) + mulW (rWord r) * zw_u) + cSt (rInMode r) (n1 % 2) := by
  have hpar := validKind_par hv
  cases r <;> dsimp [rKind, validParProp] at hpar <;> rw [hpar] <;>
    (try (rcases Nat.mod_two_eq_zero_or_one n1 with hp | hp <;> rw [hp])) <;>
    (try (rcases Nat.mod_two_eq_zero_or_one n2 with hp | hp <;> rw [hp])) <;>
    (refine zw_step_le _ _ _ _ _ _ _ _ zw_u ?_ hzw;
      dsimp [rEmit, rOutMode, rInMode, rWord, cSt]; norm_num [zW, z13, multZW, addW, mulW])

lemma cSt_nonneg (m : Mode) (p : Nat) : 0 <= cSt m (p % 2) := by
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;> (rw [hp]; cases m <;> norm_num [cSt])

lemma Scan_zW_contract {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    zW v <= multZW m1 * zW u + cSt m1 (n1 % 2) := by
  induction h with
  | nil m _ n _ _ =>
    have hc := cSt_nonneg m n
    simp [zW]; linarith
  | @step r _ _ _ n1 n2 _ _ u v _ _ _ hv _ ih =>
    have hstep := stepRule_zW_contract r n1 n2 (zW u) (zW_nonneg u) hv
    have hm_ih := mul_le_mul_of_nonneg_left ih (le_of_lt (z13_pos (rEmit r)))
    rw [<- zW_cons (rWord r) u] at hstep
    rw [zW_append]
    linarith

def minPowS : DState -> Nat
  | .S2 => 1
  | .S3 | .S4 => 2
  | .S5 => 4

lemma minPowS_step2 (w1 w2 : Word) (s : DState) :
    minPowS (dfaStep w1 (dfaStep w2 s)) <= 4 := by
  cases w1 <;> cases w2 <;> cases s <;> decide

lemma dfaRun_KQ_min {A H : Nat} {ds : List Word} (h : zDg A H ds) :
    minPowS (dfaRun ds .S2) <= 2 ^ H := by
  cases h with
  | nil => decide
  | @zero _ H1 _ h1 =>
    cases h1 with
    | nil => decide
    | @zero _ H2 u2 _ =>
      have hp : 1 <= 2 ^ H2 := zPp H2
      have hm := minPowS_step2 K K (dfaRun u2 .S2)
      dsimp [dfaRun]; rw [zPow1, zPow1]; omega
    | @one _ H2 u2 _ =>
      have hp : 1 <= 2 ^ H2 := zPp H2
      have hm := minPowS_step2 K Q (dfaRun u2 .S2)
      dsimp [dfaRun]; rw [zPow1, zPow1]; omega
  | @one _ H1 _ h1 =>
    cases h1 with
    | nil => decide
    | @zero _ H2 u2 _ =>
      have hp : 1 <= 2 ^ H2 := zPp H2
      have hm := minPowS_step2 Q K (dfaRun u2 .S2)
      dsimp [dfaRun]; rw [zPow1, zPow1]; omega
    | @one _ H2 u2 _ =>
      have hp : 1 <= 2 ^ H2 := zPp H2
      have hm := minPowS_step2 Q Q (dfaRun u2 .S2)
      dsimp [dfaRun]; rw [zPow1, zPow1]; omega

lemma zDg_z13_zW {A H : Nat} {ds : List Word} (h : zDg A H ds) :
    z13 ds = ((2 ^ H : Nat) : Rat) ∧ zW ds <= ((2 ^ H : Nat) : Rat) - 1 := by
  induction h with
  | nil => simp [z13, zW]
  | @zero A H u _ ih =>
    rw [zPow1 H, Nat.cast_add]; dsimp [z13, zW]; constructor <;> linarith
  | @one A H u _ ih =>
    rw [zPow1 H, Nat.cast_add]; dsimp [z13, zW]; constructor <;> linarith

lemma kq_step_le (zWe z13e aOut cOut aIn cIn P0 P : Rat)
    (hc : z13e * aOut <= 2 * aIn ∧ zWe + z13e * (aOut * P0 + cOut) <= aIn * (2 * P0) + cIn)
    (hP : P0 <= P) :
    zWe + z13e * (aOut * P + cOut) <= aIn * (2 * P) + cIn := by
  rcases hc with ⟨hs, hb⟩
  have hm : 0 <= (2 * aIn - z13e * aOut) * (P - P0) := mul_nonneg (by linarith) (by linarith)
  linarith

lemma stepRule_KQ_zW (r : StepRule) (s2 : DState) (P : Rat)
    (hw : rWord r ≠ V)
    (hm1 : modeMatches (rInMode r) (dfaStep (rWord r) s2) = true)
    (hm2 : modeMatches (rOutMode r) s2 = true)
    (hP : (minPowS s2 : Rat) <= P) :
    zW (rEmit r) + z13 (rEmit r) * (kqA (rOutMode r) s2 * P + kqC (rOutMode r) s2) <=
    kqA (rInMode r) (dfaStep (rWord r) s2) * (2 * P) + kqC (rInMode r) (dfaStep (rWord r) s2) := by
  cases r <;> (try exact False.elim (hw rfl)) <;>
    cases s2 <;> (try contradiction) <;>
    (refine kq_step_le _ _ _ _ _ _ _ P ?_ hP;
      norm_num [rEmit, rOutMode, rInMode, rWord, dfaStep, zW, z13, kqA, kqC, minPowS])

lemma Scan_dfaRun {m1 : Mode} {s1 : DState} {n1 : Nat} {u : List Word}
    {m2 : Mode} {s2 : DState} {n2 : Nat} {v : List Word} {g : Nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) : s1 = dfaRun u s2 := by
  induction h with
  | nil _ _ _ _ _ => rfl
  | step hs _ _ _ ih => subst hs; subst ih; rfl

lemma Scan_KQ_zW {m1 : Mode} {s1 : DState} {n1 : Nat} {ds : List Word}
    {m2 : Mode} {n2 : Nat} {v : List Word} {g : Nat}
    (hS : Scan m1 s1 n1 ds m2 .S2 n2 v g) :
    ∀ {A H : Nat}, zDg A H ds ->
      zW v <= kqA m1 s1 * ((2 ^ H : Nat) : Rat) + kqC m1 s1 := by
  generalize hs_end : DState.S2 = s_end at hS
  induction hS with
  | nil m s _ hm _ =>
    intro A H hD
    subst hs_end
    cases hD
    cases m <;> simp [modeMatches] at hm <;> norm_num [zW, kqA, kqC]
  | @step r s1 s2 s3 _ _ _ _ ds' v _ hs hm1 _ hrest ih =>
    intro A H hD
    subst hs_end
    subst hs
    have hw_ne : rWord r ≠ V := by intro hv; rw [hv] at hD; cases hD
    have hD_tail : ∃ A' H', zDg A' H' ds' ∧ H = 1 + H' := by
      generalize hw_eq : rWord r = w0 at hD
      cases hD with
      | zero h' => exact ⟨_, _, h', rfl⟩
      | one h' => exact ⟨_, _, h', rfl⟩
    rcases hD_tail with ⟨A', H', hD', rfl⟩
    have hs2_eq : s2 = dfaRun ds' .S2 := Scan_dfaRun hrest
    have hm2 : modeMatches (rOutMode r) s2 = true := Scan_match_in hrest
    have hP : (minPowS s2 : Rat) <= ((2 ^ H' : Nat) : Rat) := by
      rw [hs2_eq]; exact_mod_cast (dfaRun_KQ_min hD')
    have hstep := stepRule_KQ_zW r s2 ((2 ^ H' : Nat) : Rat) hw_ne hm1 hm2 hP
    have ih' := ih rfl hD'
    have hm_ih := mul_le_mul_of_nonneg_left ih' (le_of_lt (z13_pos (rEmit r)))
    have hpow : ((2 ^ (1 + H') : Nat) : Rat) = 2 * ((2 ^ H' : Nat) : Rat) := by
      rw [zPow1 H', Nat.cast_add]; ring
    rw [zW_append, hpow]
    linarith

def zDen : List Word -> Nat
  | [] => 1
  | _ :: u => 8 * zDen u

def z13Num : List Word -> Nat
  | [] => 1
  | V :: u => 4 * z13Num u
  | K :: u => 16 * z13Num u
  | Q :: u => 16 * z13Num u

def zWNum : List Word -> Nat
  | [] => 0
  | V :: u => zDen u + 4 * zWNum u
  | K :: u => 8 * zDen u + 16 * zWNum u
  | Q :: u => 2 * zDen u + 16 * zWNum u

lemma zDen_pos (u : List Word) : 0 < zDen u := by
  induction u with
  | nil => decide
  | cons _ _ ih => unfold zDen; omega

lemma z13Num_eq (u : List Word) : (z13Num u : Rat) = z13 u * (zDen u : Rat) := by
  induction u with
  | nil => simp [z13Num, z13, zDen]
  | cons a u ih =>
    cases a <;> (dsimp [z13Num, z13, zDen]; push_cast; rw [ih]; ring)

lemma zWNum_eq (u : List Word) : (zWNum u : Rat) = zW u * (zDen u : Rat) := by
  induction u with
  | nil => simp [zWNum, zW, zDen]
  | cons a u ih =>
    cases a <;> (dsimp [zWNum, zW, zDen]; push_cast; rw [ih]; ring)

def checkZWLe (u : List Word) (p q : Nat) : Bool :=
  q * zWNum u <= p * zDen u

lemma checkZWLe_sound (u : List Word) (p q : Nat)
    (h : checkZWLe u p q = true) : (q : Rat) * zW u <= (p : Rat) := by
  unfold checkZWLe at h
  rw [decide_eq_true_eq] at h
  have hr : (q : Rat) * (zWNum u : Rat) <= (p : Rat) * (zDen u : Rat) := by exact_mod_cast h
  rw [zWNum_eq] at hr
  have hd : (0 : Rat) < (zDen u : Rat) := by exact_mod_cast (zDen_pos u)
  rcases le_or_gt ((q : Rat) * zW u) (p : Rat) with hle | hgt
  · exact hle
  · have hmul := mul_lt_mul_of_pos_right hgt hd
    linarith

def checkZ13Pow2 (u : List Word) (e p q : Nat) : Bool :=
  q * z13Num u * (2 ^ e) == p * zDen u

lemma checkZ13Pow2_sound (u : List Word) (e p q : Nat)
    (h : checkZ13Pow2 u e p q = true) :
    (q : Rat) * z13 u * ((2 ^ e : Nat) : Rat) = (p : Rat) := by
  unfold checkZ13Pow2 at h
  rw [beq_iff_eq] at h
  have hr : (q : Rat) * (z13Num u : Rat) * ((2 ^ e : Nat) : Rat) = (p : Rat) * (zDen u : Rat) := by
    exact_mod_cast h
  rw [z13Num_eq] at hr
  have hd : (0 : Rat) < (zDen u : Rat) := by exact_mod_cast (zDen_pos u)
  rcases lt_trichotomy ((q : Rat) * z13 u * ((2 ^ e : Nat) : Rat)) (p : Rat) with h1 | h1 | h1
  · have hmul := mul_lt_mul_of_pos_right h1 hd
    linarith
  · exact h1
  · have hmul := mul_lt_mul_of_pos_right h1 hd
    linarith

def kqA4096 : Mode -> DState -> Nat
  | .PA1, .S2 | .FA1, .S2 => 512
  | .KA1, .S5 => 64
  | .KHV, .S3 => 128
  | .PHV, .S4 => 128
  | .PHV, .S3 | .PHV, .S5 => 1024
  | .FH0, .S4 | .PH0, .S4 | .FH1, .S4 | .PH1, .S4 => 512
  | .PH0, .S3 | .PH0, .S5 | .PH1, .S3 | .PH1, .S5 => 4096
  | _, _ => 0

lemma kqA4096_eq (m : Mode) (s : DState) :
    4096 * kqA m s = (kqA4096 m s : Rat) := by
  cases m <;> cases s <;> norm_num [kqA, kqA4096]

def kqCPos4096 : Mode -> DState -> Nat
  | .KA1, .S5 => 2048
  | .KHV, .S3 => 2048
  | .PHV, .S4 => 256
  | .FH0, .S4 | .PH0, .S4 => 3072
  | _, _ => 0

lemma kqCPos4096_ge (m : Mode) (s : DState) :
    4096 * kqC m s <= (kqCPos4096 m s : Rat) := by
  cases m <;> cases s <;> norm_num [kqC, kqCPos4096]

-- Section 5: Fixed Segments (`head_w`, `s_full`, `top_base`) and Concrete Orbit `init -> u_0 -> u_10`
def head_w : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,K]
def v_head : List Word := [V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V]
abbrev b_head : Nat := 266862588

lemma Scan_head : Scan .PA1 .S2 3 head_w .FA1 .S2 b_head v_head 0 := by
  have h := evalAffineScan_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11] .PA1 .S2 0 3 head_w .FA1 0 b_head v_head 0 0 (by decide)
  have hd : dfaRun head_w .S2 = .S2 := by decide
  rw [hd] at h
  simpa using h

def top_base : List Word := [Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q]
def top_body : List Word := [Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q]
def v_top : List Word := [V,V,V,V,Q,V,V,V]
abbrev A_top : Nat := 65151

lemma zDg_top : zDg A_top 16 top_base :=
  checkDg_sound A_top top_base (by decide)

lemma Scan_top {m_top : Mode} (hm : m_top = .PA1 ∨ m_top = .FA1) (b_top : Nat) (hb : 2 <= b_top) :
    Scan m_top .S2 b_top top_body .PA1 .S2 (64 * (b_top - 2) + 41) v_top 21 := by
  have h_in : 1 * (b_top - 2) + 2 = b_top := by omega
  have hd : dfaRun top_body .S2 = .S2 := by decide
  rcases hm with rfl | rfl
  · have h := evalAffineScan_sound [.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19] .PA1 .S2 1 2 top_body .PA1 64 41 v_top 21 (b_top - 2) (by decide)
    rw [hd, h_in] at h; exact h
  · have h := evalAffineScan_sound [.R09,.R19,.R04,.R19,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19] .FA1 .S2 1 2 top_body .PA1 64 41 v_top 21 (b_top - 2) (by decide)
    rw [hd, h_in] at h; exact h

def bot_w : List Word := [Q,K,K,Q,K,Q]
abbrev A_bot : Nat := 41

lemma zDg_bot : zDg A_bot 6 bot_w :=
  checkDg_sound A_bot bot_w (by decide)

def s_base : List Word := [V,V,V,V,Q,V,V,V,V]
def s_full : List Word := s_base ++ bot_w

def sRuleTable : Mode -> DState -> Nat -> List StepRule
  | .PA1, .S2, 0 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 1 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 2 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 3 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 4 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 5 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 6 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 7 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 8 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 9 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 10 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 11 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 12 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 13 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 14 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S2, 15 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .PA1, .S3, 0 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 1 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 2 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 3 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 4 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 5 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 6 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 7 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 8 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 9 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 10 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 11 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 12 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 13 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 14 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S3, 15 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 0 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 1 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 2 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 3 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 4 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 5 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 6 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 7 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 8 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 9 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 10 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 11 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 12 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 13 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 14 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S4, 15 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 0 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 1 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 2 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 3 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 4 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 5 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 6 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 7 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 8 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 9 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 10 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 11 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 12 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 13 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 14 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .PA1, .S5, 15 => [.R00,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S2, 0 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 1 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 2 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 3 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 4 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 5 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 6 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 7 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 8 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 9 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 10 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 11 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 12 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 13 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 14 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S2, 15 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28]
  | .FA1, .S3, 0 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 1 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 2 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 3 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 4 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 5 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 6 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 7 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 8 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 9 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 10 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 11 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 12 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 13 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 14 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S3, 15 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 0 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 1 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 2 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 3 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 4 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 5 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 6 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 7 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 8 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 9 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 10 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 11 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 12 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 13 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 14 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S4, 15 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 0 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 1 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 2 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 3 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 4 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 5 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 6 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 7 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 8 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 9 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 10 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 11 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 12 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 13 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 14 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | .FA1, .S5, 15 => [.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04]
  | _, _, _ => []

def checkOneS (m_in : Mode) (s_ds : DState) (r16 : Nat) : Bool :=
  match evalAffineScan (sRuleTable m_in s_ds r16) m_in s_ds 16 (64 + r16) s_full with
  | some (m_ds, mb_s, cb_s, v_s, g_s) =>
    (6 <= g_s) && (2048 <= mb_s) && (7919 <= cb_s) &&
    checkZWLe v_s 43 128 &&
    (z13Num v_s * kqA4096 m_ds s_ds <= 4 * zDen v_s) &&
    (z13Num v_s * kqCPos4096 m_ds s_ds <= zDen v_s)
  | none => false

lemma checkOneS_all (m_in : Mode) (s_ds : DState) (r16 : Nat)
    (hm : m_in = .PA1 ∨ m_in = .FA1) (hr : r16 < 16) :
    checkOneS m_in s_ds r16 = true := by
  rcases hm with rfl | rfl <;> cases s_ds <;>
    (match r16 with
     | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
     | _ + 16 => omega)

lemma Scan_s_all {m_p : Mode} (hm_p : m_p = .PA1 ∨ m_p = .FA1) (s_ds : DState)
    {bp : Nat} (hbp : 64 <= bp) :
    ∃ m_ds b_ds v_s g_s,
      Scan m_p .S2 bp s_full m_ds s_ds b_ds v_s g_s ∧
      6 <= g_s ∧
      128 * bp <= b_ds + 2200 ∧
      zW v_s <= 43 / 128 ∧
      z13 v_s * kqA m_ds s_ds <= 1 / 1024 ∧
      z13 v_s * kqC m_ds s_ds <= 1 / 4096 := by
  let q := (bp - 64) / 16
  let r16 := (bp - 64) % 16
  have hr16_lt : r16 < 16 := Nat.mod_lt _ (by decide)
  have hc := checkOneS_all m_p s_ds r16 hm_p hr16_lt
  unfold checkOneS at hc
  cases hrec : evalAffineScan (sRuleTable m_p s_ds r16) m_p s_ds 16 (64 + r16) s_full with
  | none => rw [hrec] at hc; contradiction
  | some val =>
    rw [hrec] at hc
    rcases val with ⟨m_ds, mb_s, cb_s, v_s, g_s⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨⟨⟨hg_s, hmb_s⟩, hcb_s⟩, hzw_b⟩, hA_b⟩, hC_b⟩
    have hScan := evalAffineScan_sound (sRuleTable m_p s_ds r16) m_p s_ds 16 (64 + r16) s_full
      m_ds mb_s cb_s v_s g_s q hrec
    have hd_s : dfaRun s_full s_ds = .S2 := by
      change dfaStep V (dfaStep V _) = .S2
      exact dfaStep_VV _
    have hbp_eq : 16 * q + (64 + r16) = bp := by omega
    rw [hd_s, hbp_eq] at hScan
    have hb_ds : 128 * bp <= (mb_s * q + cb_s) + 2200 := by
      have hmq : 2048 * q <= mb_s * q := Nat.mul_le_mul_right q hmb_s
      omega
    have hzw_r : zW v_s <= 43 / 128 := by
      have h128 := checkZWLe_sound v_s 43 128 hzw_b
      norm_num at h128; linarith
    have hd_pos : (0 : Rat) < (zDen v_s : Rat) := by exact_mod_cast (zDen_pos v_s)
    have hA_r : z13 v_s * kqA m_ds s_ds <= 1 / 1024 := by
      have hr : (z13Num v_s : Rat) * (kqA4096 m_ds s_ds : Rat) <= 4 * (zDen v_s : Rat) := by
        exact_mod_cast hA_b
      rw [z13Num_eq, <- kqA4096_eq] at hr
      rcases le_or_gt (z13 v_s * kqA m_ds s_ds) (1 / 1024) with hle | hgt
      · exact hle
      · have hgt' : (4 : Rat) < 4096 * (z13 v_s * kqA m_ds s_ds) := by linarith
        have hm := mul_lt_mul_of_pos_right hgt' hd_pos
        linarith
    have hC_r : z13 v_s * kqC m_ds s_ds <= 1 / 4096 := by
      have hr : (z13Num v_s : Rat) * (kqCPos4096 m_ds s_ds : Rat) <= (zDen v_s : Rat) := by
        exact_mod_cast hC_b
      rw [z13Num_eq] at hr
      have hc_le := kqCPos4096_ge m_ds s_ds
      have hmul_c := mul_le_mul_of_nonneg_left hc_le (le_of_lt (z13_pos v_s))
      rcases le_or_gt (z13 v_s * kqC m_ds s_ds) (1 / 4096) with hle | hgt
      · exact hle
      · have hgt' : (1 : Rat) < (z13 v_s * (kqCPos4096 m_ds s_ds : Rat)) := by linarith
        have hm := mul_lt_mul_of_pos_right hgt' hd_pos
        linarith
    exact ⟨m_ds, mb_s * q + cb_s, v_s, g_s, hScan, hg_s, hb_ds, hzw_r, hA_r, hC_r⟩

def u_0 : List Word := [V, Q]

lemma init_to_u0 : (init []) [tm]⊢⁺ (zCf (zTs u_0 default)) := by
  dsimp only [init, u_0, zCf, zTs, V_u, Q_u]
  simp only [List.cons_append, List.nil_append, append_cons, append_nil, z00]
  execute

def u_1 : List Word := [V,V,V,K,K,Q]
lemma step_0 : Step u_0 u_1 := checkStep_sound [.R00] [V] [K,K,Q] u_1 (by decide)
def u_2 : List Word := [V,V,V,V,V,V,K,K,Q,K,Q]
lemma step_1 : Step u_1 u_2 := checkStep_sound [.R00,.R05,.R06,.R10,.R11] [V,V,V,K,K] [K,K,Q,K,Q] u_2 (by decide)
def u_3 : List Word := [V,V,V,V,V,V,V,V,V,V,K,Q,Q,K,K,K,K,K,Q]
lemma step_2 : Step u_2 u_3 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R06,.R10,.R11,.R09,.R18] [V,V,V,V,V,V,K,K,Q,K] [K,Q,Q,K,K,K,K,K,Q] u_3 (by decide)
def u_4 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,Q,V,Q,Q,Q,Q,V,K,K,Q,Q,Q]
lemma step_3 : Step u_3 u_4 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R14,.R23,.R04,.R17,.R31,.R31,.R31,.R32] [V,V,V,V,V,V,V,V,V,V,K,Q,Q,K,K,K,K,K] [K,K,Q,Q,Q] u_4 (by decide)
def u_5 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q]
lemma step_4 : Step u_4 u_5 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R21,.R00,.R09,.R19,.R04,.R19,.R01,.R10,.R11,.R09,.R19] [V,V,V,V,V,V,V,V,V,V,K,V,Q,V,Q,Q,Q,Q,V,K,K,Q,Q] [Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q] u_5 (by decide)
def u_6 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,K,K,Q,K,Q,Q,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q]
lemma step_5 : Step u_5 u_6 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R09,.R19,.R04,.R19,.R04,.R18,.R04,.R18,.R04,.R19,.R04,.R19,.R04,.R19] [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q] [Q,K,K,Q,K,Q,Q,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q] u_6 (by decide)
def u_7 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,K,V,Q,Q,Q,Q,Q,Q,Q,V,V,V,V,V,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q]
lemma step_6 : Step u_6 u_7 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R16,.R28,.R04,.R17,.R31,.R31,.R31,.R31,.R31,.R31,.R32,.R04,.R18,.R04,.R19,.R04,.R19,.R04,.R19] [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,K,K,Q,K,Q,Q,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q] [Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q] u_7 (by decide)
def u_8 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q]
lemma step_7 : Step u_7 u_8 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R14,.R22,.R11,.R07,.R21,.R04,.R19,.R04,.R19,.R04,.R19,.R00,.R05,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04,.R16,.R28,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19] [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,K,V,Q,Q,Q,Q,Q,Q,Q,V,V,V,V,V,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q] [Q,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q] u_8 (by decide)
def u_9 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q]
lemma step_8 : Step u_8 u_9 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R21,.R03,.R22,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04,.R19,.R04,.R18,.R04,.R19,.R04,.R18,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19] [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q] [Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q] u_9 (by decide)
def u_10 : List Word := [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,K,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,K,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q]
lemma step_9 : Step u_9 u_10 := checkStep_sound [.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R07,.R21,.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R20,.R11,.R07,.R20,.R11,.R05,.R05,.R05,.R07,.R20,.R11,.R05,.R05,.R05,.R07,.R20,.R11,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R05,.R05,.R05,.R07,.R21,.R00,.R05,.R05,.R05,.R09,.R16,.R27,.R04,.R18,.R04,.R19,.R04,.R19,.R04,.R18,.R04,.R16,.R27,.R04,.R16,.R27,.R04,.R19,.R04,.R18,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R18,.R04,.R18,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R19,.R04,.R17,.R32,.R04,.R19,.R04,.R19,.R04,.R19] [V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q] [Q,K,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,K,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q] u_10 (by decide)

lemma rounds_0_10 : Rounds u_0 u_10 := Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3 (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7 (Rounds.next step_8 (Rounds.next step_9 (Rounds.refl u_10))))))))))

-- Section 6: 5-Piece Invariant `Good u`, Unconditional Closure `Good_step`, and `is_does_not_halt`
def Good (u : List Word) : Prop :=
  ∃ p_w ds_core A_core m,
    u = head_w ++ p_w ++ s_full ++ ds_core ++ top_base ∧
    (∃ p_tail, p_w = V :: V :: p_tail) ∧
    8 <= m ∧
    zDg A_core m ds_core ∧
    z13 p_w * ((2 ^ m : Nat) : Rat) = 2048 ∧
    zW p_w <= 43

def p_init : List Word := [V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,K,V,V,V,V,Q,V,V,V,V,V,V,V,V,V]
def ds_core_init : List Word := [Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,K,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]

lemma good_u10 : Good u_10 := by
  refine ⟨p_init, ds_core_init, 4603791232746792399, 62, by decide, ⟨p_init.drop 2, by decide⟩,
    by decide, checkDg_sound 4603791232746792399 ds_core_init (by decide), ?_, ?_⟩
  · have h := checkZ13Pow2_sound p_init 62 2048 1 (by decide)
    norm_num at h; exact h
  · have h := checkZWLe_sound p_init 43 1 (by decide)
    norm_num at h; exact h

lemma bound_b_end_zDg {mid_all v_mid : List Word} {m_top : Mode} {b_top g_mid : Nat}
    (hm_top : m_top = .PA1 ∨ m_top = .FA1)
    (hb_top : 2 <= b_top)
    (hg_mid : 6 <= g_mid)
    (hS_mid : Scan .FA1 .S2 b_head mid_all m_top .S2 b_top v_mid g_mid)
    (hz13_vmid : z13 v_mid * ((2 ^ g_mid : Nat) : Rat) = 1024)
    (hzW_vmid : zW v_mid <= 43821 / 512) :
    ∃ A_core' ds_core',
      zDg A_core' (g_mid + 2) ds_core' ∧
      zDg (64 * (b_top - 2) + 41) (22 + g_mid + 2)
          (bot_w ++ ds_core' ++ top_base) := by
  rcases Scan_delta hS_mid with ⟨hd_lo, hd_hi⟩
  have hphi_top : phi m_top = 1 := by rcases hm_top with rfl | rfl <;> rfl
  rw [hphi_top] at hd_lo hd_hi
  dsimp [phi] at hd_lo hd_hi
  have h_pow_ge64 : 64 <= 2 ^ g_mid := by
    have hsub : g_mid = 6 + (g_mid - 6) := by omega
    have hp : 1 <= 2 ^ (g_mid - 6) := zPp (g_mid - 6)
    rw [hsub, Nat.pow_add]
    have h64 : 2 ^ 6 = 64 := by decide
    omega
  have h_pow_r : (64 : Rat) <= ((2 ^ g_mid : Nat) : Rat) := by exact_mod_cast h_pow_ge64
  have h_pow_pos : (0 : Rat) <= ((2 ^ g_mid : Nat) : Rat) := by linarith
  have hbt_lo : (266861218 : Rat) <= (b_top : Rat) * z13 v_mid := by
    norm_num [b_head] at hd_hi; linarith
  have hbt_hi : (b_top : Rat) * z13 v_mid <= (266862588 : Rat) := by
    norm_num [b_head] at hd_lo; linarith
  have hm1 := mul_le_mul_of_nonneg_right hbt_lo h_pow_pos
  have hm2 := mul_le_mul_of_nonneg_right hbt_hi h_pow_pos
  have h_assoc : ((b_top : Rat) * z13 v_mid) * ((2 ^ g_mid : Nat) : Rat) =
      1024 * (b_top : Rat) := by
    calc ((b_top : Rat) * z13 v_mid) * ((2 ^ g_mid : Nat) : Rat)
      _ = (b_top : Rat) * (z13 v_mid * ((2 ^ g_mid : Nat) : Rat)) := by ring
      _ = 1024 * (b_top : Rat) := by rw [hz13_vmid]; ring
  rw [h_assoc] at hm1 hm2
  let n_end := 64 * (b_top - 2) + 41
  have hn_end_r : 16 * (n_end : Rat) = 1024 * (b_top : Rat) - 1392 := by
    dsimp [n_end]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb_top]
    push_cast; ring
  have h_shift_r : ((2 ^ (8 + g_mid) : Nat) : Rat) = 256 * ((2 ^ g_mid : Nat) : Rat) := by
    have h8 : ((2 ^ 8 : Nat) : Rat) = 256 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h8]
  have h_nend_lo_r : (A_top : Rat) * ((2 ^ (8 + g_mid) : Nat) : Rat) < (n_end : Rat) := by
    rw [h_shift_r]; dsimp [A_top]; linarith
  have h_nend_hi_r : (n_end : Rat) < ((A_top : Rat) + 1) * ((2 ^ (8 + g_mid) : Nat) : Rat) := by
    rw [h_shift_r]; dsimp [A_top]; linarith
  have h_nend_lo : A_top * 2 ^ (8 + g_mid) < n_end := by exact_mod_cast h_nend_lo_r
  have h_nend_hi : n_end < (A_top + 1) * 2 ^ (8 + g_mid) := by exact_mod_cast h_nend_hi_r
  let A_core' := (b_top - 2) % (2 ^ (g_mid + 2))
  have h_Acore'_lt : A_core' < 2 ^ (g_mid + 2) := Nat.mod_lt _ (zPp (g_mid + 2))
  rcases zDg_exists (g_mid + 2) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_bot_mid := zDg_append zDg_bot hD_core'
  have h_all := zDg_append h_bot_mid zDg_top
  have h_pow_eq : 2 ^ (8 + g_mid) = 64 * 2 ^ (g_mid + 2) := by
    have h_e : 8 + g_mid = 6 + (g_mid + 2) := by omega
    have h6 : 2 ^ 6 = 64 := by decide
    rw [h_e, Nat.pow_add, h6]
  have h_div_top : n_end / (2 ^ (8 + g_mid)) = A_top := by
    have hp_pos : 0 < 2 ^ (8 + g_mid) := zPp (8 + g_mid)
    have h1 := (Nat.le_div_iff_mul_le hp_pos).mpr (le_of_lt h_nend_lo)
    have h2 := (Nat.div_lt_iff_lt_mul hp_pos).mpr h_nend_hi
    omega
  have h_div_bt : (b_top - 2) / (2 ^ (g_mid + 2)) = A_top := by
    have h_ndiv64 : n_end / 64 = b_top - 2 := by dsimp [n_end]; omega
    rw [<- h_ndiv64, Nat.div_div_eq_div_mul, <- h_pow_eq, h_div_top]
  have h_val_all : A_bot + A_core' * 2 ^ 6 + A_top * 2 ^ (6 + (g_mid + 2)) = n_end := by
    have h6 : 2 ^ 6 = 64 := by decide
    have h6g : 2 ^ (6 + (g_mid + 2)) = 64 * 2 ^ (g_mid + 2) := by rw [Nat.pow_add, h6]
    rw [h6, h6g]
    have h_assoc_top : A_top * (64 * 2 ^ (g_mid + 2)) = 64 * (A_top * 2 ^ (g_mid + 2)) := by ring
    rw [h_assoc_top]
    have hmod := Nat.div_add_mod (b_top - 2) (2 ^ (g_mid + 2))
    rw [h_div_bt, Nat.mul_comm (2 ^ (g_mid + 2)) A_top] at hmod
    dsimp [A_core', A_bot, n_end] at hmod ⊢
    omega
  have h_len_all : (6 + (g_mid + 2)) + 16 = 22 + g_mid + 2 := by omega
  rw [h_val_all, h_len_all] at h_all
  exact ⟨A_core', ds_core', hD_core', by simpa [List.append_assoc] using h_all⟩

lemma Scan_FA1_V_emit {m0 m2 : Mode} {s0 s2 : DState} {n1 n2 g : Nat} {u0 v : List Word}
    (h : Scan m0 s0 n1 u0 m2 s2 n2 v g)
    (hm0 : m0 = .FA1) (hu0 : ∃ p_rest, u0 = V :: p_rest) :
    ∃ v_tail, v = V :: v_tail := by
  rcases hu0 with ⟨p_rest, hu_eq⟩
  cases h with
  | nil _ _ _ _ _ => simp at hu_eq
  | @step r _ _ _ _ _ _ _ _ v_rest _ _ _ _ _ =>
    have hw : rWord r = V := (List.cons.inj hu_eq).1
    cases r <;> simp [rInMode] at hm0 <;> simp [rWord] at hw <;> exact ⟨v_rest, rfl⟩

lemma Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_w, ds_core, A_core, m, rfl, ⟨p_tail, hp_start⟩, hm, hD_core, hz13, hzW⟩
  have hdfa_p : dfaRun p_w .S2 = .S2 := by
    rw [hp_start]; exact dfaStep_VV _
  have hb_head_ok : alpha .FA1 * zW p_w <= (b_head : Rat) - 2 := by
    norm_num [alpha, b_head]; linarith
  have hm_fa1 : modeMatches .FA1 (dfaRun p_w .S2) = true := by rw [hdfa_p]; rfl
  rcases Scan_survive p_w .S2 .FA1 b_head (by decide) hm_fa1 hb_head_ok
    with ⟨m_p, bp, v_p, gp, hS_p⟩
  rw [hdfa_p] at hS_p
  have hm_p_match : modeMatches m_p .S2 = true := (Scan_exit_ge2 hS_p).2
  have hm_p : m_p = .PA1 ∨ m_p = .FA1 := by
    cases m_p <;> simp [modeMatches] at hm_p_match
    · left; rfl
    · right; rfl
  -- Bounds on `v_p` and `bp`
  have hz13_vp_eq : z13 v_p * ((2 ^ gp : Nat) : Rat) = z13 p_w := by
    have h := Scan_z13 hS_p
    have hpsi_p : psi m_p = 4 := by rcases hm_p with rfl | rfl <;> rfl
    rw [hpsi_p] at h; dsimp [psi] at h; linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ gp : Nat) : Rat) := by exact_mod_cast (zPp gp)
  have hz13_vp_le_pw : z13 v_p <= z13 p_w := by
    have hm1 := mul_le_mul_of_nonneg_left h_pow_gp_ge1 (le_of_lt (z13_pos v_p))
    linarith
  have h_pow_m_ge256 : 256 <= 2 ^ m := by
    have hsub : m = 8 + (m - 8) := by omega
    have hp : 1 <= 2 ^ (m - 8) := zPp (m - 8)
    rw [hsub, Nat.pow_add]
    have h8 : 2 ^ 8 = 256 := by decide
    omega
  have h_pow_m_r : (256 : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_pow_m_ge256
  have hz13_pw_le8 : z13 p_w <= 8 := by
    have hm1 := mul_le_mul_of_nonneg_left h_pow_m_r (le_of_lt (z13_pos p_w))
    linarith
  have hz13_vp_le8 : z13 v_p <= 8 := by linarith
  have hz13_vp_powm : z13 v_p * ((2 ^ m : Nat) : Rat) <= 2048 := by
    have hm1 := mul_le_mul_of_nonneg_right hz13_vp_le_pw (by linarith : (0 : Rat) <= ((2 ^ m : Nat) : Rat))
    linarith
  have hzw_vp : zW v_p <= 10355 / 128 := by
    have hc := Scan_zW_contract hS_p
    have hmod : b_head % 2 = 0 := by decide
    rw [hmod] at hc
    norm_num [multZW, cSt] at hc
    linarith
  have hbp_lb : 130303 * 2 ^ m <= bp := by
    rcases Scan_delta hS_p with ⟨_, hd_hi⟩
    have hphi_p : phi m_p = 1 := by rcases hm_p with rfl | rfl <;> rfl
    rw [hphi_p] at hd_hi; dsimp [phi] at hd_hi
    have h1 : (266861293 : Rat) <= (bp : Rat) * z13 v_p := by
      norm_num [b_head] at hd_hi; linarith
    have hm1 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : Rat) <= ((2 ^ m : Nat) : Rat))
    have hm2 := mul_le_mul_of_nonneg_left hz13_vp_powm (Nat.cast_nonneg bp)
    have h_assoc : ((bp : Rat) * z13 v_p) * ((2 ^ m : Nat) : Rat) =
        (bp : Rat) * (z13 v_p * ((2 ^ m : Nat) : Rat)) := by ring
    rw [h_assoc] at hm1
    have h_rat : (130303 : Rat) * ((2 ^ m : Nat) : Rat) <= (bp : Rat) := by linarith
    exact_mod_cast h_rat
  have hbp_ge64 : 64 <= bp := by omega
  -- Scan `s_full` into `s_ds := dfaRun ds_core .S2`
  let s_ds := dfaRun ds_core .S2
  rcases Scan_s_all hm_p s_ds hbp_ge64
    with ⟨m_ds, b_ds, v_s, g_s, hS_s, hg_s, hb_ds, hzw_vs, hkqA_vs, hkqC_vs⟩
  -- Survive `ds_core`
  rcases zDg_z13_zW hD_core with ⟨hz13_ds, hzW_ds⟩
  have hb_ds_ge2 : 2 <= b_ds := by omega
  have hm_ds_match : modeMatches m_ds (dfaRun ds_core .S2) = true := (Scan_exit_ge2 hS_s).2
  have hb_ds_ok : alpha m_ds * zW ds_core <= (b_ds : Rat) - 2 := by
    have ha_hi : alpha m_ds <= 96 := by cases m_ds <;> norm_num [alpha]
    have hzw_nn : 0 <= zW ds_core := zW_nonneg ds_core
    have hm1 := mul_le_mul_of_nonneg_right ha_hi hzw_nn
    have hm2 := mul_le_mul_of_nonneg_left hzW_ds (by norm_num : (0 : Rat) <= 96)
    have hbp_r : (130303 : Rat) * ((2 ^ m : Nat) : Rat) <= (bp : Rat) := by exact_mod_cast hbp_lb
    have hbds_r : (128 : Rat) * (bp : Rat) <= (b_ds : Rat) + 2200 := by exact_mod_cast hb_ds
    linarith
  rcases Scan_survive ds_core .S2 m_ds b_ds hb_ds_ge2 hm_ds_match hb_ds_ok
    with ⟨m_top, b_top, v_ds, g_ds, hS_ds⟩
  rcases Scan_exit_ge2 hS_ds with ⟨hb_top, hm_top_match⟩
  have hm_top : m_top = .PA1 ∨ m_top = .FA1 := by
    cases m_top <;> simp [modeMatches] at hm_top_match
    · left; rfl
    · right; rfl
  -- Combine `mid_all := p_w ++ s_full ++ ds_core`
  let mid_all := p_w ++ s_full ++ ds_core
  let v_mid := v_p ++ v_s ++ v_ds
  let g_mid := gp + g_s + g_ds
  have hg_mid : 6 <= g_mid := by dsimp [g_mid]; omega
  have hS_mid : Scan .FA1 .S2 b_head mid_all m_top .S2 b_top v_mid g_mid := by
    have h12 := Scan_append hS_p hS_s
    have h123 := Scan_append h12 hS_ds
    simpa [mid_all, v_mid, g_mid, List.append_assoc, Nat.add_assoc] using h123
  -- Bound `zW v_mid <= 43821 / 512`
  have hzW_vds : zW v_ds <= kqA m_ds s_ds * ((2 ^ m : Nat) : Rat) + kqC m_ds s_ds :=
    Scan_KQ_zW hS_ds hD_core
  have hzW_vmid : zW v_mid <= 43821 / 512 := by
    have hm_vds := mul_le_mul_of_nonneg_left hzW_vds (le_of_lt (z13_pos v_s))
    have hm_A := mul_le_mul_of_nonneg_right hkqA_vs (by linarith : (0 : Rat) <= ((2 ^ m : Nat) : Rat))
    have h_tail : zW (v_s ++ v_ds) <= 1377 / 4096 + (1 / 1024) * ((2 ^ m : Nat) : Rat) := by
      rw [zW_append]
      have h_lin : z13 v_s * (kqA m_ds s_ds * ((2 ^ m : Nat) : Rat) + kqC m_ds s_ds) =
          (z13 v_s * kqA m_ds s_ds) * ((2 ^ m : Nat) : Rat) + z13 v_s * kqC m_ds s_ds := by ring
      rw [h_lin] at hm_vds
      linarith
    have hm_tail := mul_le_mul_of_nonneg_left h_tail (le_of_lt (z13_pos v_p))
    have h_dist : z13 v_p * (1377 / 4096 + (1 / 1024) * ((2 ^ m : Nat) : Rat)) =
        (1377 / 4096) * z13 v_p + (1 / 1024) * (z13 v_p * ((2 ^ m : Nat) : Rat)) := by ring
    rw [h_dist] at hm_tail
    have h_vmid_eq : v_mid = v_p ++ (v_s ++ v_ds) := by simp [v_mid, List.append_assoc]
    rw [h_vmid_eq, zW_append]
    linarith
  -- Exact `z13 v_mid * 2^g_mid = 1024`
  have hz13_vmid : z13 v_mid * ((2 ^ g_mid : Nat) : Rat) = 1024 := by
    have h := Scan_z13 hS_mid
    have hpsi_top : psi m_top = 4 := by rcases hm_top with rfl | rfl <;> rfl
    rw [hpsi_top] at h; dsimp [psi] at h
    have hs_z13 : z13 s_full = 1 / 2 := by
      have hs := checkZ13Pow2_sound s_full 0 1 2 (by decide)
      norm_num at hs; linarith
    have hmid_z13 : z13 mid_all = 1024 := by
      dsimp [mid_all]
      rw [z13_append, z13_append, hs_z13, hz13_ds]
      linarith
    rw [hmid_z13] at h
    linarith
  -- Scan `top_body` and decompose `n_end := 64 * (b_top - 2) + 41`
  have hS_top := Scan_top hm_top b_top hb_top
  rcases bound_b_end_zDg hm_top hb_top hg_mid hS_mid hz13_vmid hzW_vmid
    with ⟨A_core', ds_core', hD_core', hD_end⟩
  let body := head_w ++ mid_all ++ top_body
  let v_body := v_head ++ v_mid ++ v_top
  let da := bot_w ++ ds_core' ++ top_base
  let u' := V :: (v_body ++ V :: da)
  have h_u_eq : head_w ++ p_w ++ s_full ++ ds_core ++ top_base = body ++ [Q] := by
    have ht : top_body ++ [Q] = top_base := by decide
    dsimp only [body, mid_all]
    simp only [List.append_assoc]
    rw [ht]
  have hS_body : Scan .PA1 .S2 3 body .PA1 .S2 (64 * (b_top - 2) + 41) v_body (0 + g_mid + 21) :=
    Scan_append (Scan_append Scan_head hS_mid) hS_top
  refine ⟨u', ⟨body, .PA1, 64 * (b_top - 2) + 41, v_body, da, 22 + g_mid + 2, 0 + g_mid + 21,
    h_u_eq, Or.inl rfl, hS_body, hD_end, rfl⟩, ?_⟩
  have hvp_start : ∃ vp_tail, v_p = V :: vp_tail :=
    Scan_FA1_V_emit hS_p rfl ⟨V :: p_tail, hp_start⟩
  rcases hvp_start with ⟨vp_tail, hvp_eq⟩
  let p_w' := V :: v_mid
  let m' := g_mid + 2
  refine ⟨p_w', ds_core', A_core', m', ?_, ⟨vp_tail ++ v_s ++ v_ds, by simp [p_w', v_mid, hvp_eq]⟩, by omega, hD_core', ?_, ?_⟩
  · have hv_h : V :: v_head = head_w ++ [V] := by decide
    have hs_eq : v_top ++ [V] ++ bot_w = s_full := by decide
    calc V :: ((v_head ++ v_mid ++ v_top) ++ V :: (bot_w ++ ds_core' ++ top_base))
      _ = (V :: v_head) ++ v_mid ++ (v_top ++ [V] ++ bot_w) ++ ds_core' ++ top_base := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
      _ = head_w ++ (V :: v_mid) ++ s_full ++ ds_core' ++ top_base := by
          rw [hv_h, hs_eq]
          simp only [List.cons_append, List.nil_append, List.append_assoc]
  · dsimp only [p_w', m', z13]
    have h4 : ((2 ^ 2 : Nat) : Rat) = 4 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h4]
    linarith
  · dsimp only [p_w', zW]
    linarith

lemma reach_N (m : Nat) :
    ∃ N, m <= N ∧ ∃ u,
      multiStep tm (init []) N = some (zCf (zTs u default)) ∧
      Good u := by
  induction m with
  | zero =>
    rcases init_to_u0 with ⟨k1, _, hk1⟩
    rcases Rounds_exec rounds_0_10 with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, u_10, zMt tm _ _ _ k1 k2 hk1 hk2, good_u10⟩
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

end BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH
