/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Basic
import BusyBeaver.Calculi.Longitudinal
import BusyBeaver.Calculi.LongitudinalCascade

open Mathlib Relation Nat Turing BusyBeaver SixState
open BusyBeaver.Longitudinal
open BusyBeaver.LongitudinalCascade

namespace BusyBeaver.M_1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LAHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

def target_flip : Machine Sym Q
  | 0, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => none

theorem init_flip_raw :
    (init ([] : List Sym)) [target_flip]⊢*
    NatCfg.toCfg (K := 6) ⟨4, 0, 0, 19288074671834⟩ := by
  rw [← toCfg_zero (K := 6)]
  exact ⟨4293, stepsNat_sound target_flip 4293 ⟨0, 0, 0, 0⟩ ⟨4, 0, 0, 19288074671834⟩
    (by decide +kernel) (by decide)⟩

def statePerm : Q → Q
  | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5

theorem step_statePerm (c : Cfg Sym Q) :
    step target_flip (mapCfg statePerm c) = (step tm1 c).map (mapCfg statePerm) := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    (try rfl) <;>
    omega

theorem multiStep_statePerm (c : Cfg Sym Q) (n : Nat) :
    multiStep target_flip (mapCfg statePerm c) n = (multiStep tm1 c n).map (mapCfg statePerm) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [BusyBeaver.multiStep_succ', BusyBeaver.multiStep_succ', ih]
    rcases multiStep tm1 c n with _ | c'
    · rfl
    · exact step_statePerm c'

theorem nonHaltFrom_statePerm {c : Cfg Sym Q} (h : NonHaltFrom tm1 c) :
    NonHaltFrom target_flip (mapCfg statePerm c) := by
  intro c' ⟨n, hn⟩
  rw [multiStep_statePerm, Option.map_eq_some_iff] at hn
  rcases hn with ⟨d, hd, rfl⟩
  rw [step_statePerm, Option.isSome_map]
  exact h d ⟨n, hd⟩

theorem target_eq_flipTM : target = flipTM target_flip := by
  funext ⟨q, hq⟩ ⟨a, ha⟩
  rcases q with _ | _ | _ | _ | _ | _ | q <;> rcases a with _ | _ | a <;> (try rfl) <;> omega

theorem isNotHalt_flipTM {M : Machine Sym Q} (h : IsNotHalt M) :
    IsNotHalt (flipTM M) := by
  intro c ⟨n, hn⟩
  have h_init : (init ([] : List Sym) : Cfg Sym Q) =
      flipCfg (init ([] : List Sym) : Cfg Sym Q) := rfl
  rw [h_init, multiStep_flipTM, Option.map_eq_some_iff] at hn
  rcases hn with ⟨d, hd, rfl⟩
  rw [step_flipTM, Option.isSome_map]
  exact h d ⟨n, hd⟩

theorem toCfg_flip_eq :
    NatCfg.toCfg (K := 6) ⟨4, 0, 0, 19288074671834⟩ =
    mapCfg statePerm (cfg (prefix_word 3 +> (word 3 11 +> ([0, 0, 1, 0] +> default)))) := by
  have h1 : NatCfg.toCfg (K := 6) ⟨4, 0, 0, 19288074671834⟩ =
      Cfg.headRight E (decodeHalf 0) (decodeHalf (2 * 19288074671834)) :=
    toCfg_headRight (K := 6) E 0 (2 * 19288074671834)
  have h2 : decodeHalf (2 * 19288074671834) =
      ([0, 0, 1, 0] ++ prefix_word 3 ++ word 3 11 ++ [0, 0, 1, 0]) +>
        (default : ListBlank Sym) := by
    rw [← decodeHalf_zero, decodeHalf_encodeList]
    congr 1
  rw [h1, h2, decodeHalf_zero]
  simp only [cfg, mapCfg, statePerm, Option.map_some, Cfg.headRight, append_assoc]

public section

theorem is_not_halt : IsNotHalt target := by
  rw [target_eq_flipTM]
  apply isNotHalt_flipTM
  have h_reach : (init ([] : List Sym)) [target_flip]⊢*
      mapCfg statePerm (cfg (prefix_word 3 +> (word 3 11 +> ([0, 0, 1, 0] +> default)))) := by
    rw [← toCfg_flip_eq]
    exact init_flip_raw
  exact nonHaltFrom_of_stepStar h_reach
    (nonHaltFrom_statePerm (normal_nonhalt (Or.inl initial2_root)))

end

end BusyBeaver.M_1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LAHHH
