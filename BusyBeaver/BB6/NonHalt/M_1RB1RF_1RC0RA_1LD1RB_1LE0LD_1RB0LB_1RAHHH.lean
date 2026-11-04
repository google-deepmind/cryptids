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

namespace BusyBeaver.M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

abbrev fCR_1rahhh : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCR true C B -- CR config for 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH

abbrev fCL_1rahhh : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCL true D -- CL config for 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH

set_option maxHeartbeats 2000000 in
-- Justification: Symbolic execution of the 15 elementary SegRules for
-- 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH.
theorem segRules_1rahhh : SegRules (callStep target fCR_1rahhh fCL_1rahhh) := by
  unfold fCR_1rahhh fCL_1rahhh
  prove_seg_rules

theorem step_ca_1rahhh (r : HalfTape) :
    (fCL_1rahhh lh r) [target]⊢⁺ (fCR_1rahhh ([1] +> default) .ca r) := by
  unfold fCL_1rahhh fCR_1rahhh cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ca for 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH

theorem step_ch_1rahhh (r : HalfTape) :
    (fCL_1rahhh ([1] +> default) r) [target]⊢⁺ (fCR_1rahhh lh .ch r) := by
  unfold fCL_1rahhh fCR_1rahhh cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ch for 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH

theorem step_init_1rahhh :
    (init []) [target]⊢⁺ fCL_1rahhh lh (initTape .kindC) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold fCL_1rahhh initTape cfgCL lh t d1 d0
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_init for 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH

end

@[expose] public section

theorem is_not_halt : IsNotHalt target :=
  does_not_halt_of_seg_rules segRules_1rahhh step_ca_1rahhh step_ch_1rahhh .kindC step_init_1rahhh

end

end BusyBeaver.M_1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH
