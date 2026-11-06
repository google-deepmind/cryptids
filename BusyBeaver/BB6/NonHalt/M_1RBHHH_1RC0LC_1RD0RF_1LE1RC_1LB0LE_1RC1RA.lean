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

namespace BusyBeaver.M_1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA



@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


section

abbrev fCR_1rc1ra : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCR true D C -- CR config for 1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA

abbrev fCL_1rc1ra : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCL true E -- CL config for 1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA

set_option maxHeartbeats 2000000 in
-- Justification: Symbolic execution of the 15 elementary SegRules for
-- 1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA.
theorem segRules_1rc1ra : SegRules (callStep target fCR_1rc1ra fCL_1rc1ra) := by
  unfold fCR_1rc1ra fCL_1rc1ra
  prove_seg_rules

theorem step_ca_1rc1ra (r : HalfTape) :
    (fCL_1rc1ra lh r) [target]⊢⁺ (fCR_1rc1ra ([1] +> default) .ca r) := by
  unfold fCL_1rc1ra fCR_1rc1ra cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ca for 1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA

theorem step_ch_1rc1ra (r : HalfTape) :
    (fCL_1rc1ra ([1] +> default) r) [target]⊢⁺ (fCR_1rc1ra lh .ch r) := by
  unfold fCL_1rc1ra fCR_1rc1ra cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ch for 1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA

theorem step_init_1rc1ra :
    (init []) [target]⊢⁺ fCL_1rc1ra lh (initTape .kindD) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold fCL_1rc1ra initTape cfgCL lh t d1 d0
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_init for 1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA

end

public section

theorem is_not_halt : IsNotHalt target :=
  does_not_halt_of_seg_rules segRules_1rc1ra step_ca_1rc1ra step_ch_1rc1ra .kindD step_init_1rc1ra

end

end BusyBeaver.M_1RBHHH_1RC0LC_1RD0RF_1LE1RC_1LB0LE_1RC1RA
