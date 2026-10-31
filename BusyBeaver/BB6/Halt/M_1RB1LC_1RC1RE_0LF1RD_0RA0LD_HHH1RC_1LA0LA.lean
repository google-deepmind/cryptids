/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LC_1RC1RE_0LF1RD_0RA0LD_---1RC_1LA0LA` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LC_1RC1RE_0LF1RD_0RA0LD_---1RC_1LA0LA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LC_1RC1RE_0LF1RD_0RA0LD_---1RC_1LA0LA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 5, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

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

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  -- Terminal halting configuration reached after 9 steps (kernel replay).
  exact is_halt_of_haltsAt target_tm 9 (by decide +kernel)

end BusyBeaver.M_1RB1LC_1RC1RE_0LF1RD_0RA0LD_HHH1RC_1LA0LA
