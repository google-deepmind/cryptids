/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Machine `1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA`

Formal `HasTransducerReduction` proof for the 6-state, 2-symbol Busy Beaver machine
`1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA` (macro-equivalent holdout corresponding to
`1RB0LE_0RC---_1LC0RD_0RB1RA_1LF1LE_0LA1LF` on `Bell_eats_counter`):
- <https://wiki.bbchallenge.org/wiki/Bell_eats_counter>

The tape evolves as a 4-mode strict-sub-Kraft word-stack transducer (`hR`, `hR1`, `hR11`, `hL`)
between left alphabet `TokL = {T1, T000, T100}` (`kraftSum = 6 < 8`) and right alphabet
`TokR = {U100, U1001, U10011, U10001}` (`kraftSum = 8 < 32`).
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA

open Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Word-Stack Alphabets, Views, and Macro-Transducer -/

private inductive TransducerMode where
  | hR
  | hR1
  | hR11
  | hL
  deriving DecidableEq, Repr

private inductive TokL where
  | T1
  | T000
  | T100
  deriving DecidableEq, Repr

private inductive TokR where
  | U100
  | U1001
  | U10011
  | U10001
  deriving DecidableEq, Repr

@[simp] private def baseL : List (Fin 2) := []
@[simp] private def baseR : List (Fin 2) := [1]

@[simp]
private def wordL : TokL → List (Fin 2)
  | .T1 => [1]
  | .T000 => [0, 0, 0]
  | .T100 => [1, 0, 0]

@[simp]
private def wordR : TokR → List (Fin 2)
  | .U100 => [0, 0, 1]
  | .U1001 => [1, 0, 0, 1]
  | .U10011 => [1, 1, 0, 0, 1]
  | .U10001 => [1, 0, 0, 0, 1]

@[simp]
private def encLeft : List TokL → ListBlank (Fin 2)
  | [] => baseL +> default
  | t :: L => wordL t +> encLeft L

@[simp]
private def encRight : List TokR → ListBlank (Fin 2)
  | [] => baseR +> default
  | t :: R => wordR t +> encRight R

private theorem encLeft_non_surjective :
    ∃ t : ListBlank (Fin 2), ∀ L : List TokL, encLeft L ≠ t := by
  refine ⟨(0 : Fin 2) >> (1 : Fin 2) >> default, fun L h => ?_⟩
  cases L with
  | nil =>
    have h1 : (encLeft []).tail.head = ((0 : Fin 2) >> (1 : Fin 2) >> default).tail.head :=
      congrArg (fun x => x.tail.head) h
    simp only [encLeft, baseL, ListBlank.append, ListBlank.tail_cons, ListBlank.head_cons,
      ListBlank.tail_default, ListBlank.head_default_fin] at h1
    revert h1; decide
  | cons t tl =>
    cases t with
    | T1 =>
      have h1 : (encLeft (.T1 :: tl)).head = ((0 : Fin 2) >> (1 : Fin 2) >> default).head :=
        congrArg ListBlank.head h
      simp only [encLeft, wordL, ListBlank.append, ListBlank.head_cons] at h1
      revert h1; decide
    | T000 =>
      have h1 : (encLeft (.T000 :: tl)).tail.head =
          ((0 : Fin 2) >> (1 : Fin 2) >> default).tail.head :=
        congrArg (fun x => x.tail.head) h
      simp only [encLeft, wordL, ListBlank.append, ListBlank.tail_cons, ListBlank.head_cons] at h1
      revert h1; decide
    | T100 =>
      have h1 : (encLeft (.T100 :: tl)).head = ((0 : Fin 2) >> (1 : Fin 2) >> default).head :=
        congrArg ListBlank.head h
      simp only [encLeft, wordL, ListBlank.append, ListBlank.head_cons] at h1
      revert h1; decide

private theorem encRight_non_surjective :
    ∃ t : ListBlank (Fin 2), ∀ R : List TokR, encRight R ≠ t := by
  refine ⟨default, fun R h => ?_⟩
  cases R with
  | nil =>
    have h1 : (encRight []).head = (default : ListBlank (Fin 2)).head :=
      congrArg ListBlank.head h
    simp only [encRight, baseR, ListBlank.append, ListBlank.head_cons,
      ListBlank.head_default_fin] at h1
    revert h1; decide
  | cons t tl =>
    cases t with
    | U100 =>
      have h1 : (encRight (.U100 :: tl)).tail.tail.head =
          (default : ListBlank (Fin 2)).tail.tail.head :=
        congrArg (fun x => x.tail.tail.head) h
      simp only [encRight, wordR, ListBlank.append, ListBlank.tail_cons, ListBlank.head_cons,
        ListBlank.tail_default, ListBlank.head_default_fin] at h1
      revert h1; decide
    | U1001 =>
      have h1 : (encRight (.U1001 :: tl)).head = (default : ListBlank (Fin 2)).head :=
        congrArg ListBlank.head h
      simp only [encRight, wordR, ListBlank.append, ListBlank.head_cons,
        ListBlank.head_default_fin] at h1
      revert h1; decide
    | U10011 =>
      have h1 : (encRight (.U10011 :: tl)).head = (default : ListBlank (Fin 2)).head :=
        congrArg ListBlank.head h
      simp only [encRight, wordR, ListBlank.append, ListBlank.head_cons,
        ListBlank.head_default_fin] at h1
      revert h1; decide
    | U10001 =>
      have h1 : (encRight (.U10001 :: tl)).head = (default : ListBlank (Fin 2)).head :=
        congrArg ListBlank.head h
      simp only [encRight, wordR, ListBlank.append, ListBlank.head_cons,
        ListBlank.head_default_fin] at h1
      revert h1; decide

@[simp]
private def evalTransducerCfg : TransducerMode → List TokL → List TokR → Cfg (Fin 2) (Fin 6)
  | .hR, L, R => (applyView (.id []) (encLeft L)) <{{0}} (applyView (.id [0, 1]) (encRight R))
  | .hR1, L, R => (applyView (.id []) (encLeft L)) <{{3}} (applyView (.id [0, 0, 1]) (encRight R))
  | .hR11, L, R =>
      (applyView (.id []) (encLeft L)) <{{3}} (applyView (.id [1, 0, 0, 1]) (encRight R))
  | .hL, L, R => (applyView (.id [0, 0]) (encLeft L)) {{5}}> (applyView (.id []) (encRight R))

private def IsInTransducerSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalTransducerCfg m L R

private theorem valid_transducer_modes :
    IsValidTransducerModes encLeft encRight evalTransducerCfg := by
  intro m
  cases m with
  | hR => exact ⟨0, .id [], .id [0, 1], by decide, by decide, Or.inr (Or.inl (fun _ _ => rfl))⟩
  | hR1 => exact ⟨3, .id [], .id [0, 0, 1], by decide, by decide, Or.inr (Or.inl (fun _ _ => rfl))⟩
  | hR11 =>
    exact ⟨3, .id [], .id [1, 0, 0, 1], by decide, by decide, Or.inr (Or.inl (fun _ _ => rfl))⟩
  | hL => exact ⟨5, .id [0, 0], .id [], by decide, by decide, Or.inr (Or.inr (fun _ _ => rfl))⟩

@[simp]
private def stepMacro :
    TransducerMode → List TokL → List TokR → Option (TransducerMode × List TokL × List TokR)
  | .hR, [], R => some (.hL, [.T100], R)
  | .hR, .T1 :: L, R => some (.hR1, L, R)
  | .hR, .T000 :: L, R => some (.hL, .T100 :: L, R)
  | .hR, .T100 :: L, R => some (.hR, L, .U100 :: R)
  | .hR1, [], R => some (.hL, [.T000, .T1], R)
  | .hR1, .T1 :: L, R => some (.hR11, L, R)
  | .hR1, .T000 :: L, R => some (.hL, .T000 :: .T1 :: L, R)
  | .hR1, .T100 :: L, R => some (.hR, L, .U1001 :: R)
  | .hR11, [], R => some (.hL, [.T1, .T100, .T1], R)
  | .hR11, [.T1], R => some (.hR, [], .U10011 :: R)
  | .hR11, .T1 :: .T000 :: L, R => some (.hR1, L, .U10001 :: R)
  | .hR11, .T1 :: .T1 :: _, _ => none
  | .hR11, .T1 :: .T100 :: _, _ => none
  | .hR11, .T000 :: L, R => some (.hL, .T1 :: .T100 :: .T1 :: L, R)
  | .hR11, .T100 :: L, R => some (.hR, L, .U10011 :: R)
  | .hL, L, [] => some (.hR1, L, [])
  | .hL, L, .U100 :: R => some (.hL, .T000 :: L, R)
  | .hL, L, .U1001 :: R => some (.hL, .T1 :: .T100 :: L, R)
  | .hL, L, .U10011 :: R => some (.hR, L, .U10001 :: R)
  | .hL, L, .U10001 :: R => some (.hR1, L, .U1001 :: R)

private theorem stepMacro_none_iff (m : TransducerMode) (L : List TokL) (R : List TokR) :
    stepMacro m L R = none ↔
      (m = .hR11 ∧ ∃ t₂ L'', t₂ ∈ ([.T1, .T100] : List TokL) ∧ L = .T1 :: t₂ :: L'') := by
  cases m with
  | hL => cases R with | nil => simp [stepMacro] | cons rt _ => cases rt <;> simp [stepMacro]
  | _ =>
    cases L with
    | nil => simp [stepMacro]
    | cons t₁ L₁ =>
      cases t₁ <;> cases L₁ with
      | nil => simp [stepMacro]
      | cons t₂ L₂ => cases t₂ <;> simp [stepMacro]

/-! ## Local Macro-Step Soundness and Bidirectional Sweeps -/

private theorem init_reaches_transducer_system :
    (init []) [target]⊢⁺ evalTransducerCfg .hL [.T100] [] := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, baseL, baseR, wordL,
    ListBlank.append, ListBlank.cons_zero_default]
  bb_steps

private theorem step_hR_nil (R : List TokR) :
    (evalTransducerCfg .hR [] R) [target]⊢⁺ evalTransducerCfg .hL [.T100] R := by
  simp only [evalTransducerCfg, applyView, encLeft, baseL, wordL, ListBlank.append,
    ListBlank.cons_zero_default]
  bb_steps

private theorem step_hR_T1 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR (.T1 :: L) R) [target]⊢⁺ evalTransducerCfg .hR1 L R := by
  simp only [evalTransducerCfg, applyView, encLeft, wordL, ListBlank.append]
  bb_steps

private theorem step_hR_T000 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR (.T000 :: L) R) [target]⊢⁺ evalTransducerCfg .hL (.T100 :: L) R := by
  simp only [evalTransducerCfg, applyView, encLeft, wordL, ListBlank.append]
  bb_steps

private theorem step_hR_T100 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR (.T100 :: L) R) [target]⊢⁺ evalTransducerCfg .hR L (.U100 :: R) := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, wordL, wordR, ListBlank.append]
  bb_steps

private theorem step_hR1_nil (R : List TokR) :
    (evalTransducerCfg .hR1 [] R) [target]⊢⁺ evalTransducerCfg .hL [.T000, .T1] R := by
  simp only [evalTransducerCfg, applyView, encLeft, baseL, wordL, ListBlank.append]
  bb_steps

private theorem step_hR1_T1 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR1 (.T1 :: L) R) [target]⊢⁺ evalTransducerCfg .hR11 L R := by
  simp only [evalTransducerCfg, applyView, encLeft, wordL, ListBlank.append]
  bb_steps

private theorem step_hR1_T000 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR1 (.T000 :: L) R) [target]⊢⁺
      evalTransducerCfg .hL (.T000 :: .T1 :: L) R := by
  simp only [evalTransducerCfg, applyView, encLeft, wordL, ListBlank.append]
  bb_steps

private theorem step_hR1_T100 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR1 (.T100 :: L) R) [target]⊢⁺ evalTransducerCfg .hR L (.U1001 :: R) := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, wordL, wordR, ListBlank.append]
  bb_steps

private theorem step_hR11_nil (R : List TokR) :
    (evalTransducerCfg .hR11 [] R) [target]⊢⁺ evalTransducerCfg .hL [.T1, .T100, .T1] R := by
  simp only [evalTransducerCfg, applyView, encLeft, baseL, wordL, ListBlank.append]
  bb_steps

private theorem step_hR11_T000 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR11 (.T000 :: L) R) [target]⊢⁺
      evalTransducerCfg .hL (.T1 :: .T100 :: .T1 :: L) R := by
  simp only [evalTransducerCfg, applyView, encLeft, wordL, ListBlank.append]
  bb_steps

private theorem step_hR11_T100 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR11 (.T100 :: L) R) [target]⊢⁺
      evalTransducerCfg .hR L (.U10011 :: R) := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, wordL, wordR, ListBlank.append]
  bb_steps

private theorem step_hR11_T1_singleton (R : List TokR) :
    (evalTransducerCfg .hR11 [.T1] R) [target]⊢⁺ evalTransducerCfg .hR [] (.U10011 :: R) := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, baseL, wordL, wordR,
    ListBlank.append]
  bb_steps

private theorem step_hR11_T1_T000 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR11 (.T1 :: .T000 :: L) R) [target]⊢⁺
      evalTransducerCfg .hR1 L (.U10001 :: R) := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, wordL, wordR, ListBlank.append]
  bb_steps

private theorem step_hL_nil (L : List TokL) :
    (evalTransducerCfg .hL L []) [target]⊢⁺ evalTransducerCfg .hR1 L [] := by
  simp only [evalTransducerCfg, applyView, encRight, baseR, ListBlank.append]
  bb_steps

private theorem step_hL_U100 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hL L (.U100 :: R)) [target]⊢⁺ evalTransducerCfg .hL (.T000 :: L) R := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, wordL, wordR, ListBlank.append]
  bb_steps

private theorem step_hL_U1001 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hL L (.U1001 :: R)) [target]⊢⁺
      evalTransducerCfg .hL (.T1 :: .T100 :: L) R := by
  simp only [evalTransducerCfg, applyView, encLeft, encRight, wordL, wordR, ListBlank.append]
  bb_steps

private theorem step_hL_U10011 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hL L (.U10011 :: R)) [target]⊢⁺
      evalTransducerCfg .hR L (.U10001 :: R) := by
  simp only [evalTransducerCfg, applyView, encRight, wordR, ListBlank.append]
  bb_steps

private theorem step_hL_U10001 (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hL L (.U10001 :: R)) [target]⊢⁺
      evalTransducerCfg .hR1 L (.U1001 :: R) := by
  simp only [evalTransducerCfg, applyView, encRight, wordR, ListBlank.append]
  bb_steps

private theorem step_hR11_T1_T1_nil_halts (R : List TokR) :
    ∃ cfg_h,
      ((evalTransducerCfg .hR11 [.T1, .T1] R) [target]⊢⁺ cfg_h) ∧
      (step target cfg_h).isNone := by
  refine ⟨(((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) {{1}}>
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encRight R)), ?_, ?_⟩
  · simp only [evalTransducerCfg, applyView, encLeft, baseL, wordL, ListBlank.append]
    bb_steps
  · bb_halt

private theorem step_hR11_T1_T100_nil_halts (R : List TokR) :
    ∃ cfg_h,
      ((evalTransducerCfg .hR11 [.T1, .T100] R) [target]⊢⁺ cfg_h) ∧
      (step target cfg_h).isNone := by
  refine ⟨(((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) {{1}}>
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encRight R)), ?_, ?_⟩
  · simp only [evalTransducerCfg, applyView, encLeft, baseL, wordL, ListBlank.append]
    bb_steps
  · bb_halt

private theorem step_hR11_T1_T1_sfx_halts (L'' : List TokL) (R : List TokR) :
    ∃ cfg_h,
      ((evalTransducerCfg .hR11 (.T1 :: .T1 :: ([.T000, .T000] ++ L'')) R) [target]⊢⁺ cfg_h) ∧
      (step target cfg_h).isNone := by
  refine ⟨(((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encLeft L'') {{1}}>
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encRight R)), ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, evalTransducerCfg, applyView, encLeft, wordL,
      ListBlank.append]
    bb_steps
  · bb_halt

private theorem step_hR11_T1_T100_sfx_halts (L'' : List TokL) (R : List TokR) :
    ∃ cfg_h,
      ((evalTransducerCfg .hR11 (.T1 :: .T100 :: ([.T000, .T000] ++ L'')) R) [target]⊢⁺ cfg_h) ∧
      (step target cfg_h).isNone := by
  refine ⟨(((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encLeft L'') {{1}}>
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encRight R)), ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, evalTransducerCfg, applyView, encLeft, wordL,
      ListBlank.append]
    bb_steps
  · bb_halt

private theorem transducer_step_sound (m : TransducerMode) (L : List TokL) (R : List TokR)
    (m' : TransducerMode) (L' : List TokL) (R' : List TokR)
    (h : stepMacro m L R = some (m', L', R')) :
    (evalTransducerCfg m L R) [target]⊢⁺ evalTransducerCfg m' L' R' := by
  cases m with
  | hR =>
    cases L with
    | nil => cases h; exact step_hR_nil R
    | cons lt ls =>
      cases lt with
      | T1 => cases h; exact step_hR_T1 L' R
      | T000 => cases h; exact step_hR_T000 ls R
      | T100 => cases h; exact step_hR_T100 L' R
  | hR1 =>
    cases L with
    | nil => cases h; exact step_hR1_nil R
    | cons lt ls =>
      cases lt with
      | T1 => cases h; exact step_hR1_T1 L' R
      | T000 => cases h; exact step_hR1_T000 ls R
      | T100 => cases h; exact step_hR1_T100 L' R
  | hR11 =>
    cases L with
    | nil => cases h; exact step_hR11_nil R
    | cons lt ls =>
      cases lt with
      | T1 =>
        cases ls with
        | nil => cases h; exact step_hR11_T1_singleton R
        | cons lt₂ ls₂ =>
          cases lt₂ with
          | T1 => cases h
          | T000 => cases h; exact step_hR11_T1_T000 L' R
          | T100 => cases h
      | T000 => cases h; exact step_hR11_T000 ls R
      | T100 => cases h; exact step_hR11_T100 L' R
  | hL =>
    cases R with
    | nil => cases h; exact step_hL_nil L
    | cons rt rs =>
      cases rt with
      | U100 => cases h; exact step_hL_U100 L R'
      | U1001 => cases h; exact step_hL_U1001 L R'
      | U10011 => cases h; exact step_hL_U10011 L rs
      | U10001 => cases h; exact step_hL_U10001 L rs

private theorem replicate_append_cons {α : Type*} (k : ℕ) (x : α) (xs : List α) :
    List.replicate k x ++ (x :: xs) = List.replicate (k + 1) x ++ xs := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem sweep_left_to_right (n : ℕ) (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hR (List.replicate (1 * (n + 1)) .T100 ++ L) R) [target]⊢⁺
      evalTransducerCfg .hR L (List.replicate (1 * (n + 1)) .U100 ++ R) := by
  induction n generalizing L R with
  | zero => exact step_hR_T100 L R
  | succ n ih =>
    have h1 := step_hR_T100 (List.replicate (1 * (n + 1)) .T100 ++ L) R
    have h2 := ih L (.U100 :: R)
    rw [replicate_append_cons (1 * (n + 1)) .U100 R] at h2
    exact h1.trans h2

private theorem sweep_right_to_left (n : ℕ) (L : List TokL) (R : List TokR) :
    (evalTransducerCfg .hL L (List.replicate (1 * (n + 1)) .U100 ++ R)) [target]⊢⁺
      evalTransducerCfg .hL (List.replicate (1 * (n + 1)) .T000 ++ L) R := by
  induction n generalizing L R with
  | zero => exact step_hL_U100 L R
  | succ n ih =>
    have h1 := step_hL_U100 L (List.replicate (1 * (n + 1)) .U100 ++ R)
    have h2 := ih (.T000 :: L) R
    rw [replicate_append_cons (1 * (n + 1)) .T000 L] at h2
    exact h1.trans h2

private theorem iterTransducerMacro_add {M L R : Type}
    (stepF : M → List L → List R → Option (M × List L × List R))
    (a b : ℕ) (cfg cfg₁ : M × List L × List R)
    (ha : iterTransducerMacro stepF a cfg = some cfg₁) :
    iterTransducerMacro stepF (a + b) cfg = iterTransducerMacro stepF b cfg₁ := by
  induction a generalizing cfg with
  | zero =>
    simp only [iterTransducerMacro, Option.some.injEq] at ha
    subst ha
    simp
  | succ a ih =>
    simp only [iterTransducerMacro] at ha
    cases hstep : stepF cfg.1 cfg.2.1 cfg.2.2 with
    | none => simp [hstep] at ha
    | some cfg' =>
      simp only [hstep] at ha
      rw [Nat.succ_add]
      simp only [iterTransducerMacro, hstep]
      exact ih cfg' ha

private def growL : List TokL :=
  [.T100, .T1, .T1, .T100, .T1, .T100, .T1, .T100, .T1, .T100, .T1, .T100, .T1, .T100,
   .T000, .T000, .T000, .T100]

private def growR : List TokR := [.U1001, .U10001]

private theorem iter_stepMacro_512 :
    iterTransducerMacro stepMacro 512 (.hL, [.T100], []) = some (.hR, growL, growR) := by
  have h1 : iterTransducerMacro stepMacro 128 (.hL, [.T100], []) =
      some (.hR1, [.T000, .T1, .T100, .T1, .T100, .T000, .T000, .T100], [.U1001, .U1001]) := rfl
  have h2 : iterTransducerMacro stepMacro 128
      (.hR1, [.T000, .T1, .T100, .T1, .T100, .T000, .T000, .T100], [.U1001, .U1001]) =
      some (.hL, [.T000, .T1, .T1, .T100, .T1, .T100, .T1, .T100, .T100, .T000, .T1, .T100],
        [.U1001, .U1001]) := rfl
  have h3 : iterTransducerMacro stepMacro 128
      (.hL, [.T000, .T1, .T1, .T100, .T1, .T100, .T1, .T100, .T100, .T000, .T1, .T100],
        [.U1001, .U1001]) =
      some (.hL, [.T1, .T100, .T1, .T100, .T000, .T1, .T100, .T100, .T100],
        [.U1001, .U10011, .U100, .U1001, .U10001]) := rfl
  have h4 : iterTransducerMacro stepMacro 128
      (.hL, [.T1, .T100, .T1, .T100, .T000, .T1, .T100, .T100, .T100],
        [.U1001, .U10011, .U100, .U1001, .U10001]) =
      some (.hR, growL, growR) := rfl
  change iterTransducerMacro stepMacro (128 + (128 + (128 + 128))) (.hL, [.T100], []) =
    some (.hR, growL, growR)
  rw [iterTransducerMacro_add _ 128 _ _ _ h1,
      iterTransducerMacro_add _ 128 _ _ _ h2,
      iterTransducerMacro_add _ 128 _ _ _ h3]
  exact h4

/-- `target` satisfies `HasTransducerReduction`. -/
theorem has_transducer_reduction : HasTransducerReduction target := by
  exact ⟨TransducerMode, TokL, TokR, baseL, baseR, wordL, wordR,
    encLeft, encRight, evalTransducerCfg, stepMacro, IsInTransducerSystem,
    ⟨[.hR, .hR1, .hR11, .hL], by decide, by decide, fun m => by cases m <;> simp⟩,
    ⟨[.T1, .T000, .T100], 3, by decide, by decide, by decide, by decide, by decide,
     fun t => by cases t <;> simp, fun t => by cases t <;> decide, by decide⟩,
    ⟨[.U100, .U1001, .U10011, .U10001], 5, by decide, by decide, by decide, by decide, by decide,
     fun t => by cases t <;> simp, fun t => by cases t <;> decide, by decide⟩,
    by decide, by decide,
    Or.inr (fun t => by cases t <;> decide),
    ⟨.T100, by decide, (1 : Fin 2), by decide, by decide⟩,
    ⟨.U100, by decide, (1 : Fin 2), by decide, by decide⟩,
    rfl,
    fun _ _ => rfl,
    rfl,
    fun _ _ => rfl,
    encLeft_non_surjective,
    encRight_non_surjective,
    valid_transducer_modes,
    fun _ => Iff.rfl,
    transducer_step_sound,
    .hL, [.T100], [],
    by decide,
    init_reaches_transducer_system,
    ⟨512, .hR, growL, growR, by decide, by decide, iter_stepMacro_512, by decide⟩,
    (fun m => match m with
      | .hL => ⟨0, _, _, by decide, rfl⟩
      | .hR1 => ⟨1, _, _, by decide, rfl⟩
      | .hR => ⟨2, _, _, by decide, rfl⟩
      | .hR11 => ⟨6, _, _, by decide, rfl⟩),
    (fun t => match t with
      | .T100 => ⟨0, _, _, _, by decide, rfl, by decide⟩
      | .T1 => ⟨4, _, _, _, by decide, rfl, by decide⟩
      | .T000 => ⟨10, _, _, _, by decide, rfl, by decide⟩),
    (fun t => match t with
      | .U1001 => ⟨2, _, _, _, by decide, rfl, by decide⟩
      | .U10011 => ⟨7, _, _, _, by decide, rfl, by decide⟩
      | .U100 => ⟨8, _, _, _, by decide, rfl, by decide⟩
      | .U10001 => ⟨11, _, _, _, by decide, rfl, by decide⟩),
    Or.inl ⟨.hR11, .T1, [.T1, .T100], by decide, by decide,
      fun _ => rfl,
      stepMacro_none_iff,
      (fun t₂ ht₂ R => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht₂
        rcases ht₂ with rfl | rfl
        · exact step_hR11_T1_T1_nil_halts R
        · exact step_hR11_T1_T100_nil_halts R),
      (fun t₂ ht₂ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht₂
        rcases ht₂ with rfl | rfl
        · exact ⟨[.T000, .T000], by decide, step_hR11_T1_T1_sfx_halts⟩
        · exact ⟨[.T000, .T000], by decide, step_hR11_T1_T100_sfx_halts⟩)⟩,
    ⟨.hR, .hL, .T100, .T000, .U100, .U100, 1, 1, 1, 1,
     by decide, by decide, by decide, by decide,
     by decide, by decide, by decide, by decide,
     by decide, by decide, by decide, by decide,
     Or.inr (by decide),
     Or.inl (by decide),
     ⟨29, _, _, by decide, rfl, rfl⟩,
     ⟨32, _, _, by decide, rfl, rfl⟩,
     sweep_left_to_right, sweep_right_to_left⟩⟩

end BusyBeaver.M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA
