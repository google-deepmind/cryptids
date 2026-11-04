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

namespace BusyBeaver.M_1RB0LC_1LA0RE_0RD0LA_1RE1RA_0LD1RF_0RBHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LA0RE_0RD0LA_1RE1RA_0LD1RF_0RBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

theorem target_eq_tm1 : target = tm1 := by
  funext ⟨q, hq⟩ ⟨a, ha⟩
  rcases q with _ | _ | _ | _ | _ | _ | q <;> rcases a with _ | _ | a <;> (try rfl) <;> omega

theorem init_raw :
    (init ([] : List Sym)) [tm1]⊢*
    NatCfg.toCfg (K := 6) ⟨2, 0, 0, 733815953114⟩ := by
  rw [← toCfg_zero (K := 6)]
  exact ⟨2669, stepsNat_sound tm1 2669 ⟨0, 0, 0, 0⟩ ⟨2, 0, 0, 733815953114⟩
    (by decide +kernel) (by decide)⟩

theorem toCfg_eq :
    NatCfg.toCfg (K := 6) ⟨2, 0, 0, 733815953114⟩ =
    cfg (prefix_word 3 +> (t ^ 4 +> default)) := by
  have h1 : NatCfg.toCfg (K := 6) ⟨2, 0, 0, 733815953114⟩ =
      Cfg.headRight C (decodeHalf 0) (decodeHalf (2 * 733815953114)) :=
    toCfg_headRight (K := 6) C 0 (2 * 733815953114)
  have h2 : decodeHalf (2 * 733815953114) =
      ([0, 0, 1, 0] ++ prefix_word 3 ++ t ^ 4) +> (default : ListBlank Sym) := by
    rw [← decodeHalf_zero, decodeHalf_encodeList]
    congr 1
  rw [h1, h2, decodeHalf_zero]
  simp only [cfg, Cfg.headRight, append_assoc]

public section

theorem is_not_halt : IsNotHalt target := by
  rw [target_eq_tm1]
  have h_reach : (init ([] : List Sym)) [tm1]⊢*
      cfg (prefix_word 3 +> (t ^ 4 +> default)) := by
    rw [← toCfg_eq]
    exact init_raw
  exact nonHaltFrom_of_stepStar h_reach (normal_nonhalt (Or.inl initial_root))

end

end BusyBeaver.M_1RB0LC_1LA0RE_0RD0LA_1RE1RA_0LD1RF_0RBHHH
