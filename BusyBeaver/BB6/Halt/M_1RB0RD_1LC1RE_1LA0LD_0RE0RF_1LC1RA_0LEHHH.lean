/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LEHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LEHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

namespace Solution

open Counter BusyBeaver.BufferChainEngine

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

set_option maxHeartbeats 1000000 in
-- 25- to 41-step symbolic reductions require slightly more heartbeats.
theorem spec : Spec target_tm D A where
  w0_1 xs r := ⟨19, by buf_run_steps 19⟩
  w10 xs r := ⟨31, by buf_run_steps 31⟩
  w11_1 xs r := ⟨12, by buf_run_steps 12⟩
  rw0 xs r := ⟨3, by buf_run_steps 3⟩
  rw11 xs' r := ⟨20, by buf_run_steps 20⟩
  turn x := ⟨25, by buf_run_steps 25⟩
  lov_nil r := ⟨41, by buf_run_steps 41⟩
  lov_w0 u r := ⟨3, by buf_run_steps 3⟩
  lov_w11_0 x r := ⟨20, by buf_run_steps 20⟩
  lov_w11_1_start z r := ⟨12, by buf_run_steps 12⟩
  lov_w11_1_end z' r := ⟨9, by buf_run_steps 9⟩
  lov_finish y := ⟨12, by buf_run_steps 12⟩

set_option maxRecDepth 200000 in
-- Kernel reflection of the 847-step initial transition trace requires deeper recursion.
theorem init_to_x0 : (init []) [target_tm]⊢* (cfgL D (Lmp x0) (RC 1)) :=
  init_to_x0_of_cmultiStep (k := 847) (by decide)

def c_msb_start : CCfg (Fin 2) (Fin 6) :=
  ⟨D, 1, (encWords encWord msb_17 ++ [1, 1, 1, 1, 1, 1]).tail, [0, 1, 0, 1, 0]⟩

def c_msb_halt : CCfg (Fin 2) (Fin 6) :=
  (cmultiStep target_tm 1356 c_msb_start).getD c_msb_start

set_option maxRecDepth 200000 in
-- Kernel reflection of the 1356-step MSB-17 terminal trace requires deeper recursion.
theorem msb_17_halt (r : ListBlank (Fin 2)) :
    ∃ cfg, ((cfgL D (Lmp msb_17) ([1, 0] +> r)) [target_tm]⊢* cfg) ∧
      (step target_tm cfg).isNone := by
  have h_start : cfgL D (Lmp msb_17) ([1, 0] +> r) = evalCCfg r c_msb_start := rfl
  have h_msb : cmultiStep target_tm 1356 c_msb_start = some c_msb_halt := by decide
  have h_q : c_msb_halt.q = F := by decide
  have h_cur : c_msb_halt.cur = 1 := by decide
  refine ⟨evalCCfg r c_msb_halt, ?_, ?_⟩
  · rw [h_start]
    exact ⟨1356, cmultiStep_sound 1356 c_msb_start c_msb_halt r h_msb⟩
  · simp [step, h_q, h_cur, F, target_tm]; rfl

end Solution

public section

open Solution BusyBeaver.BufferChainEngine in
theorem is_halt : IsHalt target :=
  is_halt_of_msb17_10 spec init_to_x0 msb_17_halt

end

end BusyBeaver.M_1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LEHHH
