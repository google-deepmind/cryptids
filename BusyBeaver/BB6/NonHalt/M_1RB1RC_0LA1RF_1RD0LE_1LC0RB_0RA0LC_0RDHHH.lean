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

namespace BusyBeaver.M_1RB1RC_0LA1RF_1RD0LE_1LC0RB_0RA0LC_0RDHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_0LA1RF_1RD0LE_1LC0RB_0RA0LC_0RDHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

theorem init_raw :
    (init ([] : List Sym)) [target]⊢*
    NatCfg.toCfg (K := 6) ⟨4, 0, 0, 22414810863322⟩ := by
  rw [← toCfg_zero (K := 6)]
  exact ⟨4091, stepsNat_sound target 4091 ⟨0, 0, 0, 0⟩ ⟨4, 0, 0, 22414810863322⟩
    (by decide +kernel) (by decide)⟩

def statePerm : Q → Q
  | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5

theorem step_statePerm (c : Cfg Sym Q) :
    step target (mapCfg statePerm c) = (step tm1 c).map (mapCfg statePerm) := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    (try rfl) <;>
    omega

theorem multiStep_statePerm (c : Cfg Sym Q) (n : Nat) :
    multiStep target (mapCfg statePerm c) n = (multiStep tm1 c n).map (mapCfg statePerm) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [BusyBeaver.multiStep_succ', BusyBeaver.multiStep_succ', ih]
    rcases multiStep tm1 c n with _ | c'
    · rfl
    · exact step_statePerm c'

theorem nonHaltFrom_statePerm {c : Cfg Sym Q} (h : NonHaltFrom tm1 c) :
    NonHaltFrom target (mapCfg statePerm c) := by
  intro c' ⟨n, hn⟩
  rw [multiStep_statePerm, Option.map_eq_some_iff] at hn
  rcases hn with ⟨d, hd, rfl⟩
  rw [step_statePerm, Option.isSome_map]
  exact h d ⟨n, hd⟩

theorem toCfg_eq :
    NatCfg.toCfg (K := 6) ⟨4, 0, 0, 22414810863322⟩ =
    mapCfg statePerm (cfg (prefix_word 3 +> (word 2 5 +> ([0, 0, 1, 0, 1, 0] +> default)))) := by
  have h1 : NatCfg.toCfg (K := 6) ⟨4, 0, 0, 22414810863322⟩ =
      Cfg.headRight E (decodeHalf 0) (decodeHalf (2 * 22414810863322)) :=
    toCfg_headRight (K := 6) E 0 (2 * 22414810863322)
  have h2 : decodeHalf (2 * 22414810863322) =
      ([0, 0, 1, 0] ++ prefix_word 3 ++ word 2 5 ++ [0, 0, 1, 0, 1, 0]) +>
        (default : ListBlank Sym) := by
    rw [← decodeHalf_zero, decodeHalf_encodeList]
    congr 1
  rw [h1, h2, decodeHalf_zero]
  simp only [cfg, mapCfg, statePerm, Option.map_some, Cfg.headRight, append_assoc]

public section

theorem is_not_halt : IsNotHalt target := by
  have h_reach : (init ([] : List Sym)) [target]⊢*
      mapCfg statePerm (cfg (prefix_word 3 +> (word 2 5 +> ([0, 0, 1, 0, 1, 0] +> default)))) := by
    rw [← toCfg_eq]
    exact init_raw
  exact nonHaltFrom_of_stepStar h_reach
    (nonHaltFrom_statePerm (normal_nonhalt (Or.inl initial3_root)))

end

end BusyBeaver.M_1RB1RC_0LA1RF_1RD0LE_1LC0RB_0RA0LC_0RDHHH
