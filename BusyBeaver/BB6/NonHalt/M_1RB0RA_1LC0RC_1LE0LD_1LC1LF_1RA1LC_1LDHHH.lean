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

namespace BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

abbrev fCR_1ldhhh : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCR false E C -- CR config for 1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH

abbrev fCL_1ldhhh : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6) :=
  cfgCL false A -- CL config for 1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH

set_option maxHeartbeats 2000000 in
-- Justification: Symbolic execution of the 15 elementary SegRules for
-- 1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH.
theorem segRules_1ldhhh : SegRules (callStep target fCR_1ldhhh fCL_1ldhhh) := by
  unfold fCR_1ldhhh fCL_1ldhhh
  prove_seg_rules

theorem step_ca_1ldhhh (r : HalfTape) :
    (fCL_1ldhhh lh r) [target]⊢⁺ (fCR_1ldhhh ([1] +> default) .ca r) := by
  unfold fCL_1ldhhh fCR_1ldhhh cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ca for 1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH

theorem step_ch_1ldhhh (r : HalfTape) :
    (fCL_1ldhhh ([1] +> default) r) [target]⊢⁺ (fCR_1ldhhh lh .ch r) := by
  unfold fCL_1ldhhh fCR_1ldhhh cfgCL cfgCR callState callWord lh
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_ch for 1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH

theorem step_init_1ldhhh :
    (init []) [target]⊢⁺ fCL_1ldhhh lh (initTape .kindA) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold fCL_1ldhhh initTape cfgCL lh t d1 d0
  simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
  execute -- step_init for 1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH

end

@[expose] public section

theorem is_not_halt : IsNotHalt target :=
  does_not_halt_of_seg_rules segRules_1ldhhh step_ca_1ldhhh step_ch_1ldhhh .kindA step_init_1ldhhh

end

end BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LDHHH
