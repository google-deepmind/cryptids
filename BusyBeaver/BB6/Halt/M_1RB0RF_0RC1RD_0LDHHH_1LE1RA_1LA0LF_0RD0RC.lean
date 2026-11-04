/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RF_0RC1RD_0LDHHH_1LE1RA_1LA0LF_0RD0RC

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_0RC1RD_0LDHHH_1LE1RA_1LA0LF_0RD0RC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

namespace Solution

open Counter BusyBeaver.BufferChainEngine

abbrev tm_0RF : Machine (Fin 2) (Fin 6) := target

set_option maxHeartbeats 1000000 in
-- 25- to 41-step symbolic reductions require slightly more heartbeats.
theorem spec_0RF : Spec tm_0RF F A where
  w0_1 xs_rf r_rf := ⟨19, by buf_run_steps 19⟩
  w10 xs_rf r_rf := ⟨31, by buf_run_steps 31⟩
  w11_1 xs_rf r_rf := ⟨12, by buf_run_steps 12⟩
  rw0 xs_rf r_rf := ⟨3, by buf_run_steps 3⟩
  rw11 xs_rf' r_rf := ⟨20, by buf_run_steps 20⟩
  turn x := ⟨27, by buf_run_steps 27⟩
  lov_nil r := ⟨41, by buf_run_steps 41⟩
  lov_w0 u_rf r_rf := ⟨3, by buf_run_steps 3⟩
  lov_w11_0 x_rf r_rf := ⟨20, by buf_run_steps 20⟩
  lov_w11_1_start z_rf r_rf := ⟨12, by buf_run_steps 12⟩
  lov_w11_1_end z_rf' r_rf := ⟨9, by buf_run_steps 9⟩
  lov_finish y := ⟨12, by buf_run_steps 12⟩

set_option maxRecDepth 200000 in
-- Kernel reflection of the 865-step initial transition trace requires deeper recursion.
theorem init_to_x0_0RF : (init []) [tm_0RF]⊢* (cfgL F (Lmp x0) (RC 1)) :=
  init_to_x0_of_cmultiStep (k := 865) (by decide)

def c_msb_start_0RF : CCfg (Fin 2) (Fin 6) :=
  ⟨F, 1, (encWords encWord msb_17 ++ [1, 1, 1, 1, 1, 1]).tail, [0, 1, 0, 1, 0]⟩

def c_msb_halt_0RF : CCfg (Fin 2) (Fin 6) :=
  (cmultiStep tm_0RF 1356 c_msb_start_0RF).getD c_msb_start_0RF

set_option maxRecDepth 200000 in
-- Kernel reflection of the 1356-step MSB-17 terminal trace requires deeper recursion.
theorem msb_17_halt_0RF (r : ListBlank (Fin 2)) :
    ∃ cfg, ((cfgL F (Lmp msb_17) ([1, 0] +> r)) [tm_0RF]⊢* cfg) ∧
      (step tm_0RF cfg).isNone := by
  have h_start : cfgL F (Lmp msb_17) ([1, 0] +> r) = evalCCfg r c_msb_start_0RF := rfl
  have h_msb : cmultiStep tm_0RF 1356 c_msb_start_0RF = some c_msb_halt_0RF := by decide
  have h_q : c_msb_halt_0RF.q = C := by decide
  have h_cur : c_msb_halt_0RF.cur = 1 := by decide
  refine ⟨evalCCfg r c_msb_halt_0RF, ?_, ?_⟩
  · rw [h_start]
    exact ⟨1356, cmultiStep_sound 1356 c_msb_start_0RF c_msb_halt_0RF r h_msb⟩
  · simp [step, h_q, h_cur, C, tm_0RF]; rfl

end Solution

public section

open Solution BusyBeaver.BufferChainEngine in
theorem is_halt : IsHalt target :=
  is_halt_of_msb17_10 spec_0RF init_to_x0_0RF msb_17_halt_0RF

end

end BusyBeaver.M_1RB0RF_0RC1RD_0LDHHH_1LE1RA_1LA0LF_0RD0RC
