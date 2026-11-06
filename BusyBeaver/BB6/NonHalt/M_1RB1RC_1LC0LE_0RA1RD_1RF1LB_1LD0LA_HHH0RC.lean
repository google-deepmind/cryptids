/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


open BusyBeaver.Counter
open TM311Donor

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

theorem init_reaches_inv :
    ∃ c, ((init []) [donor311_tm]⊢⁺ c) ∧ Inv c := by
  -- init [] -> (0, []) -> (3, []) -> (2, [3])
  have h0 : (init []) [donor311_tm]⊢⁺ cfg_modeC (encL 0 []) default := init_reaches_modeC
  have h1 : (cfg_modeC (encL 0 []) default) [donor311_tm]⊢⁺ cfg_modeC (encL 3 []) default := by
    have ha := step_modeC_nil (encL 0 [])
    have hb : (cfg_modeE0_first (encL 0 [])) [donor311_tm]⊢⁺ cfg_modeC (encL 0 []) (prepend01 3
        default) :=
      step_modeE0_first_base
    have hc := modeC_prepend01_star 3 0 [] default
    rw [Nat.zero_add] at hc
    exact stepPlus_stepPlus_stepPlus ha (stepPlus_stepStar_stepPlus hb hc)
  have h2 : (cfg_modeC (encL 3 []) default) [donor311_tm]⊢⁺ cfg_modeC (encL 2 [3]) default := by
    have ha := step_modeC_nil (encL 3 [])
    have hb := step_modeE0_first_b10 (encL 2 [])
    have hc : (cfg_modeE0_loop (encL 2 []) default) [donor311_tm]⊢⁺
        cfg_modeE0_loop (encL 0 []) (prepend11_01 1 default) :=
      step_modeE0_loop_b10_b10 (encL 0 []) default
    have hd := step_modeE0_loop_base (prepend11_01 1 default)
    have he := step_modeC_b01 (encL 0 [0]) (prepend11_01 1 default)
    have hf := modeC_consume_11_01_nonempty 1 1 [0] default (by simp) trivial
    simp only [add_last, Nat.zero_add, Nat.mul_one] at hf
    exact stepPlus_stepPlus_stepPlus ha
      (stepPlus_stepPlus_stepPlus hb
        (stepPlus_stepPlus_stepPlus hc
          (stepPlus_stepPlus_stepPlus hd
            (stepPlus_stepStar_stepPlus he hf))))
  have h_inv : InvNil 2 [3] := Or.inr ⟨by simp, by simp [GoodKS]⟩
  exact ⟨cfg_modeC (encL 2 [3]) default,
    stepPlus_stepPlus_stepPlus h0 (stepPlus_stepPlus_stepPlus h1 h2),
    ⟨2, [3], rfl, h_inv⟩⟩

theorem donor311_nonhalt :
    IsDoesNotHalt donor311_tm := by
  rcases init_reaches_inv with ⟨c, h_plus, h_inv⟩
  exact does_not_halt_of_invariant Inv ⟨c, stepPlus_stepStar h_plus, h_inv⟩ inv_step



theorem is_does_not_halt : IsNotHalt target_tm := by
  exact donor311_nonhalt

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC
