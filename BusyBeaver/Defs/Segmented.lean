/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import BusyBeaver.Defs.Core
public import BusyBeaver.Defs.Stack
public import BusyBeaver.Defs.WordRun

/-!
# Segmented Tape Definitions (`BusyBeaver.Defs.Segmented`)

Segmented schema (`IsSegmentedCryptid`) and supporting definitions for partitioned half-tapes
composed of register, word-run, finite-word, and gadget regions.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

universe u v

/-- Segmented Half-Tape Region Descriptor (`SegRegionKind`). -/
inductive SegRegionKind (Γ : Type u) where
  | reg (blk : List Γ) (val : ℕ)
  | wordRun (frames : List (List Γ × ℕ))
  | finWord (words : List (List Γ))
  | gadget (w : List Γ)

/-- Evaluates a single `SegRegionKind Γ` into its `List Γ` bit-segment. -/
def evalSegRegion {Γ : Type u} : SegRegionKind Γ → List Γ
  | .reg blk v => blk ^ v
  | .wordRun [] => []
  | .wordRun ((w, m) :: rest) => (w ^ m) ++ evalSegRegion (.wordRun rest)
  | .finWord [] => []
  | .finWord (w :: ws) => w ++ evalSegRegion (.finWord ws)
  | .gadget w => w

/-- Evaluates a `≤ 3`-region segmented half-tape `List (SegRegionKind Γ)` onto `default`. -/
def evalSegmentedHalf {Γ : Type u} [Inhabited Γ] : List (SegRegionKind Γ) → ListBlank Γ
  | [] => default
  | reg :: rest => ListBlank.append (evalSegRegion reg) (evalSegmentedHalf rest)

/-- Structural well-formedness for a `SegRegionKind`: non-empty periodic/word blocks, bounded
    `.gadget` literals (`w.length ≤ 16`), and no full single-symbol raw alphabet wrapping inside
    `.wordRun` / `.finWord`. -/
def SegRegionKind.WellFormed {Γ : Type u} : SegRegionKind Γ → Prop
  | .reg blk _ => blk ≠ []
  | .wordRun frames =>
      (∀ p ∈ frames, p.1 ≠ []) ∧ ¬ ∀ b : Γ, ∃ p ∈ frames, p.1 = [b]
  | .finWord words =>
      (∀ w ∈ words, w ≠ []) ∧ ¬ ∀ b : Γ, [b] ∈ words
  | .gadget w => w.length ≤ 16

/-- `IsNowhereDenseFamily` for the evaluated segmented half-tapes `evalSegmentedHalf (segs s)`. -/
def IsNowhereDenseHalf {Γ : Type u} {S : Type v} [Inhabited Γ]
    (Valid : S → Prop) (segs : S → List (SegRegionKind Γ)) : Prop :=
  IsNowhereDenseFamily Valid (fun s => evalSegmentedHalf (segs s))

/-- Closed `≤ 3`-region segmented transition system on an explicit `(SegState, Mode)` carrier. -/
def IsClosedSegmentedSystem {k : ℕ} {Λ : Type u} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ)
    {SegState Mode : Type}
    (modes : List Mode)
    (ValidSeg : SegState → Prop)
    (modeOf : SegState → Mode)
    (segsL segsR : SegState → List (SegRegionKind (Fin (k + 2))))
    (evalCfg : SegState → Cfg (Fin (k + 2)) Λ) : Prop :=
  1 ≤ modes.length ∧ modes.length ≤ 8 ∧ (∀ m : Mode, m ∈ modes) ∧
  (∀ s, ValidSeg s →
    (segsL s).length ≤ 3 ∧ (segsR s).length ≤ 3 ∧
    (∀ r ∈ segsL s, r.WellFormed) ∧ (∀ r ∈ segsR s, r.WellFormed)) ∧
  (∀ m : Mode, ∃ (q : Λ) (vL vR : HalfTapeView (Fin (k + 2))),
    viewPrefixLen vL ≤ 8 ∧ viewPrefixLen vR ≤ 8 ∧
    ∀ s, ValidSeg s → modeOf s = m →
      (evalCfg s = ⟨some q, ⟨(0 : Fin (k + 2)),
        applyView vL (evalSegmentedHalf (segsL s)),
        applyView vR (evalSegmentedHalf (segsR s))⟩⟩) ∨
      (evalCfg s = Cfg.headLeft q (applyView vL (evalSegmentedHalf (segsL s)))
        (applyView vR (evalSegmentedHalf (segsR s)))) ∨
      (evalCfg s = Cfg.headRight q (applyView vL (evalSegmentedHalf (segsL s)))
        (applyView vR (evalSegmentedHalf (segsR s))))) ∧
  (IsNowhereDenseHalf ValidSeg segsL ∨ IsNowhereDenseHalf ValidSeg segsR) ∧
  (IsNowhereDenseHalf ValidSeg segsL ∨
    (∀ s, ValidSeg s → ∃ (q : Λ) (vR : ListBlank (Fin (k + 2))),
      (evalCfg s = ⟨some q, ⟨(0 : Fin (k + 2)), evalSegmentedHalf (segsL s), vR⟩⟩) ∨
      (evalCfg s = Cfg.headLeft q (evalSegmentedHalf (segsL s)) vR) ∨
      (evalCfg s = Cfg.headRight q (evalSegmentedHalf (segsL s)) vR))) ∧
  (IsNowhereDenseHalf ValidSeg segsR ∨
    (∀ s, ValidSeg s → ∃ (q : Λ) (vL : ListBlank (Fin (k + 2))),
      (evalCfg s = ⟨some q, ⟨(0 : Fin (k + 2)), vL, evalSegmentedHalf (segsR s)⟩⟩) ∨
      (evalCfg s = Cfg.headLeft q vL (evalSegmentedHalf (segsR s))) ∨
      (evalCfg s = Cfg.headRight q vL (evalSegmentedHalf (segsR s))))) ∧
  (∃ s₀, ValidSeg s₀ ∧ ReachesPlus M (init []) (evalCfg s₀)) ∧
  (∀ s, ValidSeg s →
    ∃ cfg', ReachesPlus M (evalCfg s) cfg' ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step M cfg').isNone))

/-- Unifying `≤ 3`-Region Segmented Schema (`IsSegmentedCryptid`). At least one half-tape must
    be `IsNowhereDenseHalf`; a half-tape that is not must be boundary-aligned (no hidden view
    prefix), and all regions must be `SegRegionKind.WellFormed`. -/
def IsSegmentedCryptid {k : ℕ} {Λ : Type u} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (SegState Mode : Type)
    (modes : List Mode)
    (ValidSeg : SegState → Prop)
    (modeOf : SegState → Mode)
    (segsL segsR : SegState → List (SegRegionKind (Fin (k + 2))))
    (evalCfg : SegState → Cfg (Fin (k + 2)) Λ),
    IsClosedSegmentedSystem M modes ValidSeg modeOf segsL segsR evalCfg

end BusyBeaver
