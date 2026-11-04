/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Basic
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.CertTree
import BusyBeaver.Calculi.CertTreeDataA
import BusyBeaver.Calculi.CertTreeDataB

open Mathlib Relation Nat Turing BusyBeaver SixState
open BusyBeaver.CertTreeEngine

namespace BusyBeaver.M_1RB1RA_1LC0RE_1LD1LB_1RA0LE_1RA0LF_0LBHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1LC0RE_1LD1LB_1RA0LE_1RA0LF_0LBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := cert_tm true

theorem target_eq : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl


namespace Solution


set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_0 : run_tree target_tm 0x103c3 0x102c3 st_0 fc_0 = .inl fc_1 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_1 : run_tree target_tm 0x103c3 0x102c3 st_1 fc_1 = .inl fc_2 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_2 : run_tree target_tm 0x103c3 0x102c3 st_2 fc_2 = .inl fc_3 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_3 : run_tree target_tm 0x103c3 0x102c3 st_3 fc_3 = .inl fc_4 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_4 : run_tree target_tm 0x103c3 0x102c3 st_4 fc_4 = .inl fc_5 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_5 : run_tree target_tm 0x103c3 0x102c3 st_5 fc_5 = .inl fc_6 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_6 : run_tree target_tm 0x103c3 0x102c3 st_6 fc_6 = .inl fc_7 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_7 : run_tree target_tm 0x103c3 0x102c3 st_7 fc_7 = .inl fc_8 := rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Certificate tree evaluation requires elevated recursion depth and heartbeats.
theorem step_8 : run_tree target_tm 0x103c3 0x102c3 st_8 fc_8 = .inr true := rfl

theorem full_halt : HaltsFrom target_tm (init []) :=
  full_halt_of_steps target_tm 0x103c3 0x102c3
    step_0 step_1 step_2 step_3 step_4 step_5 step_6 step_7 step_8

end Solution

public section

theorem is_halt : IsHalt target := by
  rw [target_eq]
  exact (isHalt_iff_haltsFrom_init target_tm).mpr Solution.full_halt

end

end BusyBeaver.M_1RB1RA_1LC0RE_1LD1LB_1RA0LE_1RA0LF_0LBHHH
