/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LBHHH

open Mathlib Relation Nat Turing BusyBeaver SixState
open BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LBHHH

namespace BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

abbrev fCR_1rehhh_b : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCR true B A -- CR config for 1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

abbrev fCL_1rehhh_b : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCL true C -- CL config for 1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

set_option maxHeartbeats 2000000 in
-- Justification: Symbolic execution of the 15 elementary SegRules for
-- 1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH.
theorem segRules_1rehhh_b : SegRules (callStep target fCR_1rehhh_b fCL_1rehhh_b) := by
  unfold fCR_1rehhh_b fCL_1rehhh_b
  prove_seg_rules

theorem step_ca_1rehhh_b (r : HalfTape) :
    (fCL_1rehhh_b lh r) [target]⊢⁺ (fCR_1rehhh_b ([1] +> default) .ca r) := by
  unfold fCL_1rehhh_b fCR_1rehhh_b cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ca for 1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

theorem step_ch_1rehhh_b (r : HalfTape) :
    (fCL_1rehhh_b ([1] +> default) r) [target]⊢⁺ (fCR_1rehhh_b lh .ch r) := by
  unfold fCL_1rehhh_b fCR_1rehhh_b cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ch for 1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

theorem step_init_1rehhh_b :
    (init []) [target]⊢⁺ fCL_1rehhh_b lh (initTape .kindB) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold fCL_1rehhh_b initTape cfgCL lh t d1 d0
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_init for 1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

end

@[expose] public section

theorem is_not_halt : IsNotHalt target :=
  does_not_halt_of_seg_rules segRules_1rehhh_b step_ca_1rehhh_b step_ch_1rehhh_b .kindB
      step_init_1rehhh_b

end

end BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH
