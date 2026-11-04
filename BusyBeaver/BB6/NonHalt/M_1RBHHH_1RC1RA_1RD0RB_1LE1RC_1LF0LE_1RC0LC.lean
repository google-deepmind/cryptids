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

namespace BusyBeaver.M_1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

abbrev fCR_1rc0lc : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCR true D C -- CR config for 1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC

abbrev fCL_1rc0lc : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCL true E -- CL config for 1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC

set_option maxHeartbeats 2000000 in
-- Justification: Symbolic execution of the 15 elementary SegRules for
-- 1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC.
theorem segRules_1rc0lc : SegRules (callStep target fCR_1rc0lc fCL_1rc0lc) := by
  unfold fCR_1rc0lc fCL_1rc0lc
  prove_seg_rules

theorem step_ca_1rc0lc (r : HalfTape) :
    (fCL_1rc0lc lh r) [target]⊢⁺ (fCR_1rc0lc ([1] +> default) .ca r) := by
  unfold fCL_1rc0lc fCR_1rc0lc cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ca for 1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC

theorem step_ch_1rc0lc (r : HalfTape) :
    (fCL_1rc0lc ([1] +> default) r) [target]⊢⁺ (fCR_1rc0lc lh .ch r) := by
  unfold fCL_1rc0lc fCR_1rc0lc cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ch for 1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC

theorem step_init_1rc0lc :
    (init []) [target]⊢⁺ fCL_1rc0lc lh (initTape .kindD) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold fCL_1rc0lc initTape cfgCL lh t d1 d0
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_init for 1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC

end

@[expose] public section

theorem is_not_halt : IsNotHalt target :=
  does_not_halt_of_seg_rules segRules_1rc0lc step_ca_1rc0lc step_ch_1rc0lc .kindD step_init_1rc0lc

end

end BusyBeaver.M_1RBHHH_1RC1RA_1RD0RB_1LE1RC_1LF0LE_1RC0LC
