/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import BusyBeaver.BB6.NonHalt.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH

/-!
# Busy Beaver Machine `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-!
797:#789 / 778:#770 / 740:#732 / 663:#655 / 623:#615 / 608:#600
(E1 mirror sibling of 797:#239 `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---`).

Stage-1 pure-kernel non-halting proof via mirror-isomorphism transport (`isoCfg`: state swap
`A ↔ D` + tape reversal `L ↔ R`) to the E1 sibling `tm239`, combined with the symbolic
4-stage closed attractor (`InvM m z c k`: `k ≤ 5 ∧ 1 ≤ z ∧ 33 ≤ m ∧ 9 * m ≤ c ∧ 2100 ≤ c`),
entered from blank tape at symbolic macro step `t = 2638` (`m = 91, z = 1, c = 2200, k = 2`).
-/

open BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH
  (symRunBits symRunBits_sound_plus v5 evalSym reachesPlus_eq_both mCfg eval_mCfg_z1
   InvM invM_step cfgD symZero symOne symConst)

/-- Mirror sibling `1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---` (`A ↔ D`, `L ↔ R`). -/
private abbrev tm239 : Machine (Fin 2) (Fin 6) :=
  BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH.target_tm

private def permState : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 4
  | 5 => 5

private def mirrorTape (t : Tape (Fin 2)) : Tape (Fin 2) :=
  ⟨t.head, t.right, t.left⟩

def isoCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map permState, mirrorTape c.tape⟩

private theorem step_iso (c c' : Cfg (Fin 2) (Fin 6))
    (h : step tm239 c = some c') : step target_tm (isoCfg c) = some (isoCfg c') := by
  rcases c with ⟨st, ⟨hd, l, r⟩⟩
  rcases st with _ | ⟨qn, hqn⟩
  · cases h
  · rcases hd with ⟨hn, hhn⟩
    match qn, hn with
    | 0, 0 => cases h; rfl
    | 0, 1 => cases h; rfl
    | 1, 0 => cases h; rfl
    | 1, 1 => cases h; rfl
    | 2, 0 => cases h; rfl
    | 2, 1 => cases h; rfl
    | 3, 0 => cases h; rfl
    | 3, 1 => cases h; rfl
    | 4, 0 => cases h; rfl
    | 4, 1 => cases h; rfl
    | 5, 0 => cases h; rfl
    | 5, 1 => cases h
    | _ + 6, _ => omega
    | _, _ + 2 => omega

private theorem multiStep_iso : ∀ (n : ℕ) (c c' : Cfg (Fin 2) (Fin 6)),
    multiStep tm239 c n = some c' → multiStep target_tm (isoCfg c) n = some (isoCfg c')
  | 0, _, _, h => by
    cases h; rfl
  | n + 1, c, c', h => by
    rw [multiStep, Function.iterate_succ_apply'] at h ⊢
    change (multiStep tm239 c n).bind (step tm239) = some c' at h
    change (multiStep target_tm (isoCfg c) n).bind (step target_tm) = some (isoCfg c')
    rcases hm : multiStep tm239 c n with _ | cm
    · rw [hm] at h; cases h
    · rw [hm] at h
      rw [multiStep_iso n c cm hm]
      exact step_iso cm c' h

private theorem reachesStar_iso {c c' : Cfg (Fin 2) (Fin 6)}
    (h : ReachesStar tm239 c c') : ReachesStar target_tm (isoCfg c) (isoCfg c') := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, multiStep_iso n c c' hn⟩

private theorem reachesPlus_iso {c c' : Cfg (Fin 2) (Fin 6)}
    (h : ReachesPlus tm239 c c') : ReachesPlus target_tm (isoCfg c) (isoCfg c') := by
  rcases h with ⟨n, hpos, hn⟩
  exact ⟨n, hpos, multiStep_iso n c c' hn⟩


/-! #### Blank-Tape Entry & Main Theorem -/

private theorem isoCfg_cfgD_default :
    isoCfg (cfgD default default) = init [] := by
  rw [init_nil_eq_headRight]
  rfl

private theorem rfl_entry_789_0 :
    symRunBits [7, 6, 3] (.mD, [], []) =
      some (.mE, [.pair 0 0 (symZero), .pair 2 0 (symConst 14), .mid (symZero),
        .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_1 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .pair 2 0 (symConst 14), .mid (symZero),
      .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 1 0 (symZero)]) =
      some (.mA, [.pair 2 0 (symOne), .mid (symOne), .pair 1 1 (symZero), .pair 1 0 (symZero),
        .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symZero),
        .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 3), .mid (symZero),
        .pair 2 0 (symZero), .pair 1 1 (symOne), .pair 1 2 (symZero), .pair 1 1 (symConst 63),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_2 :
    symRunBits [7, 6, 3] (.mA, [.pair 2 0 (symOne), .mid (symOne), .pair 1 1 (symZero),
      .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
      .pair 1 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero), .pair 1 1 (symConst 3),
      .mid (symZero), .pair 2 0 (symZero), .pair 1 1 (symOne), .pair 1 2 (symZero),
      .pair 1 1 (symConst 63), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 2 0 (symConst 67), .pair 1 1 (symZero), .mid (symZero),
        .pair 2 0 (symConst 18), .mid (symConst 8), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 0 0 (symZero), .pair 1 1 (symZero)]) := rfl
private theorem rfl_entry_789_3 :
    symRunBits [7, 6, 3] (.mA, [.pair 2 0 (symConst 67), .pair 1 1 (symZero), .mid (symZero),
      .pair 2 0 (symConst 18), .mid (symConst 8), .pair 1 1 (symZero), .pair 1 0 (symZero)],
      [.pair 0 0 (symZero), .pair 1 1 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero), .pair 1 1 (symConst 9),
        .pair 1 2 (symZero), .pair 1 1 (symConst 157), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_4 :
    symRunBits [7, 6, 3] (.mA, [.pair 1 0 (symZero), .pair 1 1 (symZero), .pair 1 0 (symZero)],
      [.pair 0 0 (symZero), .pair 1 1 (symConst 22), .mid (symZero), .pair 1 1 (symConst 9),
      .pair 1 2 (symZero), .pair 1 1 (symConst 157), .pair 1 0 (symZero)]) =
      some (.mA, [.mid (symZero), .pair 2 0 (symConst 10), .pair 3 0 (symZero), .mid (symZero),
        .pair 2 0 (symConst 29), .mid (symConst 3), .pair 1 1 (symZero), .pair 2 0 (symZero)],
        [.pair 0 0 (symZero), .pair 2 1 (symZero), .pair 1 1 (symConst 150),
        .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_5 :
    symRunBits [7, 6, 3] (.mA, [.mid (symZero), .pair 2 0 (symConst 10), .pair 3 0 (symZero),
      .mid (symZero), .pair 2 0 (symConst 29), .mid (symConst 3), .pair 1 1 (symZero),
      .pair 2 0 (symZero)], [.pair 0 0 (symZero), .pair 2 1 (symZero), .pair 1 1 (symConst 150),
      .pair 1 0 (symZero)]) =
      some (.mA, [.pair 2 0 (symConst 409), .pair 2 1 (symZero), .pair 2 0 (symOne),
        .mid (symConst 13), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 0 0 (symZero),
        .pair 1 1 (symZero), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_6 :
    symRunBits [7, 6, 3] (.mA, [.pair 2 0 (symConst 409), .pair 2 1 (symZero), .pair 2 0 (symOne),
      .mid (symConst 13), .pair 1 1 (symZero), .pair 2 0 (symZero)], [.pair 0 0 (symZero),
      .pair 1 1 (symZero), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero)], [.pair 1 0 (symZero), .pair 2 0 (symOne),
        .mid (symConst 3), .pair 1 1 (symOne), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 27), .mid (symZero), .pair 1 1 (symConst 13), .pair 1 2 (symZero),
        .pair 1 1 (symConst 396), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_7 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero)], [.pair 1 0 (symZero), .pair 2 0 (symOne),
      .mid (symConst 3), .pair 1 1 (symOne), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (symConst 27), .mid (symZero), .pair 1 1 (symConst 13), .pair 1 2 (symZero),
      .pair 1 1 (symConst 396), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 0 (symZero)], [.pair 1 0 (symZero), .pair 2 0 (symZero), .mid (symConst 62),
        .pair 1 1 (symConst 48), .mid (symZero), .pair 1 1 (symConst 408), .pair 1 2 (symZero),
        .pair 1 1 (symOne), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_8 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 1 (symZero), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 0 (symZero)], [.pair 1 0 (symZero), .pair 2 0 (symZero), .mid (symConst 62),
      .pair 1 1 (symConst 48), .mid (symZero), .pair 1 1 (symConst 408), .pair 1 2 (symZero),
      .pair 1 1 (symOne), .pair 1 0 (symZero)]) =
      some (.mA, [.mid (symZero), .pair 2 0 (symConst 5), .mid (symZero), .pair 2 0 (symConst 15),
        .pair 1 0 (symZero), .mid (symConst 55), .pair 1 1 (symZero), .pair 2 0 (symZero),
        .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 2 1 (symZero),
        .pair 1 1 (symConst 877), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_9 :
    symRunBits [7, 6, 3] (.mA, [.mid (symZero), .pair 2 0 (symConst 5), .mid (symZero),
      .pair 2 0 (symConst 15), .pair 1 0 (symZero), .mid (symConst 55), .pair 1 1 (symZero),
      .pair 2 0 (symZero), .pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
      .pair 2 1 (symZero), .pair 1 1 (symConst 877), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
        .mid (symConst 2), .pair 1 1 (symOne), .pair 1 0 (symZero), .pair 2 0 (symZero),
        .pair 1 1 (symConst 189), .mid (symZero), .pair 1 1 (symConst 94), .pair 1 2 (symZero),
        .pair 1 1 (symConst 790), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_10 :
    symRunBits [7, 6, 3] (.mA, [.pair 3 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
      .mid (symConst 2), .pair 1 1 (symOne), .pair 1 0 (symZero), .pair 2 0 (symZero),
      .pair 1 1 (symConst 189), .mid (symZero), .pair 1 1 (symConst 94), .pair 1 2 (symZero),
      .pair 1 1 (symConst 790), .pair 1 0 (symZero)]) =
      some (.mE, [.pair 0 0 (symZero), .mid (symZero), .pair 2 0 (symConst 97),
        .pair 1 0 (symOne), .pair 2 0 (symConst 210), .mid (symConst 32), .pair 1 1 (symZero),
        .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 2 (symZero),
        .pair 1 1 (symConst 783), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_11 :
    symRunBits [7, 6, 3] (.mE, [.pair 0 0 (symZero), .mid (symZero), .pair 2 0 (symConst 97),
      .pair 1 0 (symOne), .pair 2 0 (symConst 210), .mid (symConst 32), .pair 1 1 (symZero),
      .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 1 2 (symZero),
      .pair 1 1 (symConst 783), .pair 1 0 (symZero)]) =
      some (.mA, [.mid (symZero), .pair 2 0 (symConst 488), .pair 1 0 (symOne),
        .pair 2 0 (symConst 601), .mid (symConst 98), .pair 1 1 (symZero), .pair 1 0 (symZero)],
        [.pair 0 0 (symZero), .pair 2 1 (symZero), .pair 1 1 (symOne), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_12 :
    symRunBits [7, 6, 3] (.mA, [.mid (symZero), .pair 2 0 (symConst 488), .pair 1 0 (symOne),
      .pair 2 0 (symConst 601), .mid (symConst 98), .pair 1 1 (symZero), .pair 1 0 (symZero)],
      [.pair 0 0 (symZero), .pair 2 1 (symZero), .pair 1 1 (symOne), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (symConst 91), .pair 1 1 (symZero),
        .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
        .pair 1 1 (symConst 10), .mid (symZero), .pair 1 1 (symConst 3), .pair 1 2 (symZero),
        .pair 1 1 (symConst 2202), .pair 1 0 (symZero)]) := rfl
private theorem rfl_entry_789_13 :
    symRunBits [5, 2, 1] (.mA, [.pair 1 0 (symZero), .mid (symConst 91), .pair 1 1 (symZero),
      .pair 1 0 (symConst 2), .pair 2 0 (symZero), .pair 1 0 (symZero)], [.pair 0 0 (symZero),
      .pair 1 1 (symConst 10), .mid (symZero), .pair 1 1 (symConst 3), .pair 1 2 (symZero),
      .pair 1 1 (symConst 2202), .pair 1 0 (symZero)]) =
      some (.mA, [.pair 1 0 (symZero), .mid (symConst 90), .pair 1 1 (symZero),
        .pair 1 0 (symZero)], [.pair 0 0 (symZero), .pair 1 1 (symConst 16), .mid (symZero),
        .pair 1 1 (symConst 6), .pair 1 2 (symZero), .pair 1 1 (symConst 2199),
        .pair 1 0 (symZero)]) := rfl

private theorem init_reaches_entry :
    ReachesStar target_tm (init []) (isoCfg (mCfg 91 1 2200 2)) := by
  have hinit : evalSym (v5 0 0 0 0 0) (.mD, [], []) = cfgD default default := rfl
  have h_e0 := symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_0
  have h_e1 := h_e0.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_1)
  have h_e2 := h_e1.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_2)
  have h_e3 := h_e2.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_3)
  have h_e4 := h_e3.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_4)
  have h_e5 := h_e4.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_5)
  have h_e6 := h_e5.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_6)
  have h_e7 := h_e6.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_7)
  have h_e8 := h_e7.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_8)
  have h_e9 := h_e8.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_9)
  have h_e10 := h_e9.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_10)
  have h_e11 := h_e10.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_11)
  have h_e12 := h_e11.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_12)
  have h_e13 := h_e12.trans (symRunBits_sound_plus (v5 0 0 0 0 0) rfl_entry_789_13)
  have hstep :=
    reachesPlus_eq_both h_e13 hinit (eval_mCfg_z1 (v5 0 0 0 0 0) (symConst 90) (symConst 16)
    (symConst 6) (symConst 2199) 91 2200 2 rfl rfl rfl rfl)
  have hstar := reachesStar_iso hstep.to_star
  rw [isoCfg_cfgD_default] at hstar
  exact hstar

def InAttractor (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m z c k, InvM m z c k ∧ cfg = isoCfg (mCfg m z c k)

private theorem attractor_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : InAttractor cfg) :
    ∃ cfg', ReachesPlus target_tm cfg cfg' ∧ InAttractor cfg' := by
  rcases h with ⟨m, z, c, k, hinv, rfl⟩
  obtain ⟨m', z', c', k', hm', hstep⟩ := invM_step hinv
  exact ⟨isoCfg (mCfg m' z' c' k'), reachesPlus_iso hstep, m', z', c', k', hm', rfl⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  IsNotHalt.of_reachesPlus_invariant
    init_reaches_entry
    ⟨91, 1, 2200, 2, ⟨by omega, by omega, by omega, by omega, by omega⟩, rfl⟩
    attractor_closed


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH
