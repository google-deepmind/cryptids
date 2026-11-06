/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs.Core

/-!
# Mixed-Radix Odometer Systems (`BusyBeaver.Defs.Odometer`)

Mixed-radix odometer-word hub systems:

- `OdomSide` — odometer stack tape orientation.
- `evalOdomR`, `evalOdomL` — outward-facing and inward-facing configuration evaluators.
- `HasOdometerReduction` — mixed-radix odometer reduction.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Tape orientation for a mixed-radix odometer-word system (`HasOdometerReduction`). -/
inductive OdomSide where
  /-- Odometer stack on the left half-tape and active word on the right half-tape. -/
  | leftOdom
  /-- Odometer stack on the right half-tape and active word on the left half-tape. -/
  | rightOdom

/-- Evaluate the outward-facing hub configuration (head at `q_R` facing the active word `w` across
fixed boundary prefix `pfx_R`). -/
@[reducible, simp]
def evalOdomR {Γ Λ : Type*} [Inhabited Γ]
    (side : OdomSide) (q_R : Λ) (pfx_R : List Γ)
    (encOdom : ListBlank Γ) (w : ListBlank Γ) : Cfg Γ Λ :=
  match side with
  | .leftOdom => Cfg.headRight q_R (ListBlank.append pfx_R encOdom) w
  | .rightOdom => Cfg.headLeft q_R w (ListBlank.append pfx_R encOdom)

/-- Evaluate the inward-facing odometer entry configuration (head at `q_L` facing the odometer
stack `encOdom` across fixed boundary prefix `pfx_L`). -/
@[reducible, simp]
def evalOdomL {Γ Λ : Type*} [Inhabited Γ]
    (side : OdomSide) (q_L : Λ) (pfx_L : List Γ)
    (encOdom : ListBlank Γ) (w : ListBlank Γ) : Cfg Γ Λ :=
  match side with
  | .leftOdom => Cfg.headLeft q_L encOdom (ListBlank.append pfx_L w)
  | .rightOdom => Cfg.headRight q_L (ListBlank.append pfx_L w) encOdom

/-- The blank-tape trajectory of `M` enters a closed outward-facing odometer-word hub coupled with
a non-surjective multi-bit mixed-radix odometer stack (`OdomTok`, `cap`, `dec`, `drain`) supporting
odd-doubling (`2c + 1`), even-doubling (`2c`), and base-`b` division (`c / b`, `b ≥ 2`) frames,
universal capacity decrement (`cap stk ≥ 1`) and full-stack drain (`cap stk = 0`), active `0`-bit
reflection, and push/reflect/halt closure under `ReachesPlus`. -/
def HasOdometerReduction {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (OdomTok : Type)
    (side : OdomSide)
    (q_R : List OdomTok → Λ)
    (q_L : Λ)
    (pfx_R pfx_L odomBase : List (Fin (k + 2)))
    (odomWord : OdomTok → List (Fin (k + 2)))
    (encOdom : List OdomTok → ListBlank (Fin (k + 2)))
    (cap : List OdomTok → ℕ)
    (dec : List OdomTok → List OdomTok)
    (decPfx : List OdomTok → List (Fin (k + 2)))
    (drain : List OdomTok → List (Fin (k + 2)))
    (IsInOdomSystem : Cfg (Fin (k + 2)) Λ → Prop),
    (∃ toks : List OdomTok, 2 ≤ toks.length ∧ toks.length ≤ 6 ∧ ∀ t : OdomTok, t ∈ toks) ∧
    odomBase ≠ [] ∧
    (∀ t : OdomTok, 2 ≤ (odomWord t).length) ∧
    encOdom [] = ListBlank.append odomBase default ∧
    (∀ t stk, encOdom (t :: stk) = ListBlank.append (odomWord t) (encOdom stk)) ∧
    (∃ t : ListBlank (Fin (k + 2)), ∀ stk : List OdomTok, encOdom stk ≠ t) ∧
    cap [] = 0 ∧
    (∃ (t_inc t_even t_div : OdomTok) (b : ℕ) (blk_inc blk_div : List (Fin (k + 2))),
      2 ≤ b ∧ 2 ≤ blk_inc.length ∧ 2 ≤ blk_div.length ∧
      (∀ stk, cap (t_inc :: stk) = 2 * cap stk + 1) ∧
      (∀ stk, cap (t_even :: stk) = 2 * cap stk) ∧
      (∀ stk, cap (t_div :: stk) = cap stk / b) ∧
      (∀ stk w,
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) (ListBlank.append blk_inc w))
          (evalOdomR side (q_R (t_inc :: stk)) pfx_R (encOdom (t_inc :: stk)) w)) ∧
      (∀ stk w,
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) (ListBlank.append blk_div w))
          (evalOdomR side (q_R (t_div :: stk)) pfx_R (encOdom (t_div :: stk)) w))) ∧
    (∀ stk, (dec stk).length = stk.length) ∧
    (∀ stk, cap stk ≥ 1 → cap (dec stk) = cap stk - 1) ∧
    (∀ stk w, cap stk ≥ 1 →
      ReachesPlus M
        (evalOdomL side q_L pfx_L (encOdom stk) w)
        (evalOdomR side (q_R (dec stk)) pfx_R (encOdom (dec stk))
          (ListBlank.append (decPfx stk) w))) ∧
    (∀ stk, cap stk = 0 → drain stk ≠ []) ∧
    (∀ stk w, cap stk = 0 →
      ReachesPlus M
        (evalOdomL side q_L pfx_L (encOdom stk) w)
        (evalOdomR side (q_R []) pfx_R (encOdom []) (ListBlank.append (drain stk) w))) ∧
    (∀ stk w,
      ReachesPlus M
        (evalOdomR side (q_R stk) pfx_R (encOdom stk) (ListBlank.cons (0 : Fin (k + 2)) w))
        (evalOdomL side q_L pfx_L (encOdom stk) (ListBlank.cons (1 : Fin (k + 2)) w))) ∧
    (∀ stk w,
      (∃ t w',
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) w)
          (evalOdomR side (q_R (t :: stk)) pfx_R (encOdom (t :: stk)) w')) ∨
      (∃ w',
        ReachesPlus M
          (evalOdomR side (q_R stk) pfx_R (encOdom stk) w)
          (evalOdomL side q_L pfx_L (encOdom stk) w')) ∨
      (∃ cfg',
        ReachesPlus M (evalOdomR side (q_R stk) pfx_R (encOdom stk) w) cfg' ∧
          (step M cfg').isNone)) ∧
    (∀ cfg, IsInOdomSystem cfg ↔
      ∃ stk w, cfg = evalOdomR side (q_R stk) pfx_R (encOdom stk) w) ∧
    (∃ (stk₀ : List OdomTok) (w₀ : ListBlank (Fin (k + 2))),
      ReachesPlus M (init []) (evalOdomR side (q_R stk₀) pfx_R (encOdom stk₀) w₀) ∧
      2 ≤ stk₀.length ∧ 1 ≤ cap stk₀) ∧
    (∀ stk w,
      ∃ cfg', ReachesPlus M (evalOdomR side (q_R stk) pfx_R (encOdom stk) w) cfg' ∧
        (IsInOdomSystem cfg' ∨ (step M cfg').isNone))

end BusyBeaver
