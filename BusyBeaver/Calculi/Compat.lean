/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
import Mathlib.Computability.TuringMachine.Tape

/-!
# Compatibility Layer for `BusyBeaver` (`BusyBeaver.Compat`)

Legacy aliases, macros, and transitional shims:

- Legacy reachability shorthands (`zSm`, `z01`..`z06`, `zMa`, `zMt`, `zPs`, `zPt`, `zSt`)
- Normalization macros (`normalize`, `normalize_at`, `walk`)
- Re-exported state labels (`SixState (A B C D E F)`)
-/

@[expose] public section

namespace BusyBeaver

open Turing

export SixState (A B C D E F)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-! ## Legacy / Shorthand Reachability Aliases -/

theorem zSm (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ :=
  ⟨1, h⟩

theorem z01 (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ :=
  ⟨1, by decide, h⟩

theorem z02 {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ h₂

theorem z03 {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  step_stepStar_stepPlus h₁ h₂

theorem z04 {tm : Machine Γ Λ} (c : Cfg Γ Λ) : c [tm]⊢* c :=
  ⟨0, rfl⟩

theorem z05 (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ :=
  ⟨1, h⟩

theorem z06 {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ :=
  stepStar_trans h₁ h₂

theorem zMa {tm : Machine Γ Λ} (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) :=
  multiStep_add tm c₁ n m

theorem zMt (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) : c₁ [tm]⊢^{n + m} c₃ :=
  multiStep_trans h₁ h₂

theorem zPs {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ :=
  stepPlus_stepStar h

theorem zPt {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_trans h₁ h₂

theorem zSt {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ :=
  stepStar_trans h₁ h₂

/-! ## Normalization and Reachability Macros -/

/-- Normalizes tape cons and append constructors, powers, and default blanks. -/
macro "normalize" : tactic =>
  `(tactic| (
    try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
      pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
      zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero, Nat.mul_add,
      Nat.mul_one]))

/-- Normalizes tape cons and append constructors, powers, and default blanks in a hypothesis. -/
macro "normalize_at" h:ident : tactic =>
  `(tactic| (
    try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
      pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
      zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero, Nat.mul_add,
      Nat.mul_one] at $h:ident))

/-- Chains a reachability transition step into a `ReachesStar` or `ReachesPlus` goal. -/
macro "walk" t:term : tactic =>
  `(tactic| (
    (first | refine stepStar_trans $t ?_ | refine stepStar_stepPlus_stepPlus $t ?_)
    try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, default_head, default_tail, zero_cons_default, pow_zero_list,
      pow_succ_list, nil_append_list, cons_append_list, ones_append_cons_one,
      zeros_append_cons_zero, pow_append_pow, zeros_append_default, Nat.mul_zero, Nat.mul_add,
      Nat.mul_one]))

end BusyBeaver
