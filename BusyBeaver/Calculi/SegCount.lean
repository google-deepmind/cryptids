/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Calculi.Longitudinal

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.SegCount

open BusyBeaver.Longitudinal

@[expose] public section

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def runSteps (M : Machine Γ Λ) : ℕ → BoundedConfig.BCfg Γ Λ → BoundedConfig.BCfg Γ Λ
  | 0, x => x
  | n + 1, x =>
    match BoundedConfig.step M x with
    | none => x
    | some x' => runSteps M n x'

theorem runSteps_spec (M : Machine Γ Λ) (n : ℕ) (x y : BoundedConfig.BCfg Γ Λ)
    (h : runSteps M n x = y) (l₀ r₀ : ListBlank Γ) :
    (BoundedConfig.toCfg x l₀ r₀) [M]⊢* (BoundedConfig.toCfg y l₀ r₀) := by
  subst h
  induction n generalizing x with
  | zero => exact stepStar_refl M _
  | succ n ih =>
    dsimp [runSteps]
    rcases hstep : BoundedConfig.step M x with _ | x'
    · exact stepStar_refl M _
    · exact stepStar_trans ⟨1, BoundedConfig.step_spec M x hstep l₀ r₀⟩ (ih x')

end

end BusyBeaver.SegCount
