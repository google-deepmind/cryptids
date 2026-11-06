/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB0RE_1LC1RF_HHH0LD_0LE1LB_1LF1LD_1RD0RA


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1RF_HHH0LD_0LE1LB_1LF1LD_1RD0RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


open BusyBeaver.Counter
open TM311Donor

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

def σ_EFDBAC : Fin 6 → Fin 6
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 2

theorem tableIso_311_128 : ∀ (q : Fin 6) (a : Fin 2),
    target_tm (σ_EFDBAC q) a = (donor311_tm q a).map (conjOut σ_EFDBAC true)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 3, 0 => rfl
  | 3, 1 => rfl
  | 4, 0 => rfl
  | 4, 1 => rfl
  | 5, 0 => rfl
  | 5, 1 => rfl

theorem init_reaches_conj_inv_128 :
    (init []) [target_tm]⊢⁺ conjCfg σ_EFDBAC true (cfg_modeC (encL 7 []) default) := by
  refine run_local_plus_eq (tm := target_tm) (n := 177)
    (s1 := ⟨[(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2),
        (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)],
      [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2),
        (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2),
        (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 0, .right⟩)
    (s2 := ⟨[(0 : Fin 2), (0 : Fin 2)],
      [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
        (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
        (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
        (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 3, .left⟩)
    default default rfl ?_ ?_
  · simp only [cfg_of, init, Tape.mk₁, append_cons, append_nil,
      zero_cons_default, default_head, default_tail]; rfl
  · simp only [cfg_of, cfg_modeC, conjCfg, mirrorTape, σ_EFDBAC,
      encL, encL_tail, prepend10, append_cons, append_nil,
      zero_cons_default, default_head, default_tail, Option.map]; rfl



theorem is_does_not_halt : IsNotHalt target_tm :=
  does_not_halt_of_conj_invariant tableIso_311_128 Inv
    ⟨cfg_modeC (encL 7 []) default, stepPlus_stepStar init_reaches_conj_inv_128,
      ⟨7, [], rfl, Or.inl ⟨rfl, by omega⟩⟩⟩
    inv_step

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RE_1LC1RF_HHH0LD_0LE1LB_1LF1LD_1RD0RA
