/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
/-!
Halting trace certificate.

Decider `direct_simulation_halt`: Halted after 10 steps (evaluated steps:
10, certificate size: 10).  The
simulator counts the undefined transition as a step, so the halting
configuration is reached after 9 `step`s.  `haltsAt` re-runs the
machine inside the kernel (`decide +kernel`, no `native_decide`).
-/

/-- `true` iff `M` reaches, after exactly `n` steps, a configuration without a
successor. -/
def haltsAt (M : Machine (Fin 2) (Fin 6)) (n : ℕ) : Bool :=
  match multiStep M (init []) n with
  | some cfg => (step M cfg).isNone
  | none => false

theorem is_halt_of_haltsAt (M : Machine (Fin 2) (Fin 6)) (n : ℕ)
    (h : haltsAt M n = true) : IsHalt M := by
  unfold haltsAt at h
  cases hm : multiStep M (init []) n with
  | none =>
    rw [hm] at h
    exact absurd h Bool.false_ne_true
  | some cfg =>
    rw [hm] at h
    exact ⟨cfg, ⟨n, hm⟩, h⟩

def solution_steps : ℕ := 9



theorem is_halt : IsHalt target := by
  -- Terminal halting configuration reached after 9 steps (kernel replay).
  exact is_halt_of_haltsAt target_tm 9 (by decide +kernel)

end BusyBeaver.M_1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA
