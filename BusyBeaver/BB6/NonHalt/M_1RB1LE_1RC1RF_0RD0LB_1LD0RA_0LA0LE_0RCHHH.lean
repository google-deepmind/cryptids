/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import BusyBeaver.Stack
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.RunWin
import BusyBeaver.Calculi.Excursion
import BusyBeaver.Calculi.Longitudinal

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => none


namespace CollarBox
open Turing BusyBeaver BusyBeaver.RunWin BusyBeaver.Excursion BusyBeaver.Longitudinal

/-- Decision tree for symbolic execution of one block or hub transition across `0, 1, 2, ...`
sequential sub-box calls. -/
private inductive BoxProg (I : ℕ) (Leaf : Type) where
  | finish (steps : ℕ) (leaf : Leaf)
  | callSubBox (steps : ℕ) (subIn : Fin I) (branches : List (BoxProg I Leaf))

/-- Certificate for a finite-collar block-monoid turnaround transducer. -/
private structure CollarBoxCert (B I C H : ℕ) where
  mirrorTape : Bool := false
  lenPreserving : Bool := true
  maxTreeDepth  : ℕ
  qIn           : Fin 6
  qOut          : Fin 6
  blockBits     : Fin B → List (Fin 2)
  endBits       : List (Fin 2)
  inCollar      : Fin I → List (Fin 2)
  retCollar     : Fin I → Fin C → List (Fin 2)
  endProg       : Fin I → ℕ × Fin C × List (Fin B)
  boxProg       : Fin I → Fin B → BoxProg I (Fin C × List (Fin B))
  hubState      : Fin H → Fin 6
  hubLeft       : Fin H → List (Fin 2)
  hubRight      : Fin H → List (Fin 2)
  hubProg       : Fin H → BoxProg I (Fin H × List (Fin B))
  initHub       : Fin H
  initBlocks    : List (Fin B)
  entrySteps    : ℕ

/-- Flatten a list of block indices into raw tape bits. -/
private def encBlocks {B : ℕ} (blockBits : Fin B → List (Fin 2)) : List (Fin B) → List (Fin 2)
  | [] => []
  | b :: xs => blockBits b ++ encBlocks blockBits xs

/-- Encode a block list `xs` followed by `endBits` onto a blank half-tape. -/
private def enc {B : ℕ} (blockBits : Fin B → List (Fin 2)) (endBits : List (Fin 2)) :
    List (Fin B) → ListBlank (Fin 2)
  | [] => endBits +> default
  | b :: xs => blockBits b +> enc blockBits endBits xs

private theorem encBlocks_append_enc {B : ℕ} (blockBits : Fin B → List (Fin 2))
    (endBits : List (Fin 2)) (emitted ys : List (Fin B)) :
    encBlocks blockBits emitted +> enc blockBits endBits ys =
      enc blockBits endBits (emitted ++ ys) := by
  induction emitted with
  | nil => rfl
  | cons b bs ih =>
    simp only [encBlocks, List.cons_append, enc, BusyBeaver.PairStack.listblank_append_right_assoc,
        ih]

/-- Trim trailing `0` symbols from a finite bit list (matching `consSym true`). -/
private def trimZeros : List (Fin 2) → List (Fin 2)
  | [] => []
  | a :: xs =>
    match trimZeros xs with
    | [] => if a == 0 then [] else [a]
    | ys => a :: ys

private theorem trimZeros_append_default (xs : List (Fin 2)) :
    trimZeros xs +> (default : ListBlank (Fin 2)) = xs +> default := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [trimZeros]
    rcases h : trimZeros rest with _ | ⟨y, ys⟩
    · have hrest : rest +> (default : ListBlank (Fin 2)) = default := by
        rw [← ih, h]
        rfl
      by_cases ha : a = 0
      · subst ha
        simp only [beq_self_eq_true, ↓reduceIte, listblank_append_nil, listblank_append_cons,
          hrest, zero_cons_default]
      · have hbeq : (a == 0) = false := beq_false_of_ne ha
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, listblank_append_cons,
          listblank_append_nil, hrest]
    · simp only [listblank_append_cons]
      rw [← listblank_append_cons, ← h, ih]

/-- Resume symbolic cursor at `(pushed +> Lt) <{{qOut}} (rc +> Rt)`. -/
private def resumeSymCfg (qOut : Fin 6) (pushed rc : List (Fin 2)) : SymCfg (Fin 2) (Fin 6) :=
  match pushed with
  | [] => ⟨some qOut, .leftHead rc⟩
  | ph :: pt => ⟨some qOut, .mid pt ph rc⟩

private theorem resumeSymCfg_eval (qOut : Fin 6) (pushed rc : List (Fin 2))
    (Lt Rt : ListBlank (Fin 2)) :
    (resumeSymCfg qOut pushed rc).eval Lt Rt = ((pushed +> Lt) <{{qOut}} (rc +> Rt)) := by
  cases pushed with
  | nil => rfl
  | cons ph pt =>
    simp only [resumeSymCfg, SymCfg.eval, SymCursor.eval, listblank_append_cons,
      eval_headLeft_cons]

/-- Universal positive-step box contract across arbitrary outer left tape `l`. -/
private def BoxStep (M : Machine (Fin 2) (Fin 6)) {I C : ℕ}
    (inCollar : Fin I → List (Fin 2)) (retCollar : Fin I → Fin C → List (Fin 2))
    (qIn qOut : Fin 6)
    (i : Fin I) (u : ListBlank (Fin 2)) (c : Fin C) (v : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2),
    ((inCollar i +> l) {{qIn}}> u) [M]⊢⁺ (l <{{qOut}} (retCollar i c +> v))

/-- Top-level turnaround hub configuration. -/
private def cfgHub {B I C H : ℕ} (cert : CollarBoxCert B I C H) (h : Fin H) (xs : List (Fin B)) :
    Cfg (Fin 2) (Fin 6) :=
  ((cert.hubLeft h +> default) {{cert.hubState h}}>
    (cert.hubRight h +> enc cert.blockBits cert.endBits xs))

/-- Check a `BoxProg` for one `(i : Fin I, b : Fin B)` block transition. -/
private def checkBlockProg {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
    (cert : CollarBoxCert B I C H) (i : Fin I) (allowSub : Bool) :
    ℕ → SymCfg (Fin 2) (Fin 6) → BoxProg I (Fin C × List (Fin B)) → Bool
  | 0, _, _ => false
  | _ + 1, s, .finish steps (cOut, emitted) =>
    let lenOk := if cert.lenPreserving then emitted.length == 1 else true
    lenOk &&
    match steps with
    | 0 => false
    | k + 1 =>
      match symRun false false M s (k + 1) with
      | some ⟨some q', .leftHead outBits⟩ =>
        (q' == cert.qOut) &&
        (outBits == cert.retCollar i cOut ++ encBlocks cert.blockBits emitted)
      | _ => false
  | fuel + 1, s, .callSubBox steps subIn branches =>
    allowSub &&
    match steps with
    | 0 => false
    | k + 1 =>
      match symRun false false M s (k + 1) with
      | some ⟨some q', .rightHead revL⟩ =>
        let ic := cert.inCollar subIn
        (q' == cert.qIn) &&
        (revL.take ic.length == ic) &&
        let pushed := revL.drop ic.length
        let nextAllow := cert.lenPreserving
        checkBlockBranches M cert i nextAllow fuel pushed subIn branches 0
      | _ => false
where
  checkBlockBranches {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
      (cert : CollarBoxCert B I C H) (i : Fin I) (allowSub : Bool)
      (fuel : ℕ) (pushed : List (Fin 2)) (subIn : Fin I) :
      List (BoxProg I (Fin C × List (Fin B))) → ℕ → Bool
    | [], idx => idx == C
    | br :: brs, idx =>
      if h : idx < C then
        let rc := cert.retCollar subIn ⟨idx, h⟩
        checkBlockProg M cert i allowSub fuel (resumeSymCfg cert.qOut pushed rc) br &&
        checkBlockBranches M cert i allowSub fuel pushed subIn brs (idx + 1)
      else
        false

/-- Check a `BoxProg` for one top-level hub `h : Fin H` (`blankL = true, blankR = false`). -/
private def checkHubProg {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
    (cert : CollarBoxCert B I C H) :
    ℕ → SymCfg (Fin 2) (Fin 6) → BoxProg I (Fin H × List (Fin B)) → Bool
  | 0, _, _ => false
  | _ + 1, s, .finish steps (nextHub, emitted) =>
    match steps with
    | 0 => false
    | k + 1 =>
      match symRun true false M s (k + 1) with
      | some ⟨some q', .mid outL outH outR⟩ =>
        (q' == cert.hubState nextHub) &&
        (trimZeros outL == trimZeros (cert.hubLeft nextHub)) &&
        ((outH :: outR) == cert.hubRight nextHub ++ encBlocks cert.blockBits emitted)
      | _ => false
  | fuel + 1, s, .callSubBox steps subIn branches =>
    match steps with
    | 0 => false
    | k + 1 =>
      match symRun true false M s (k + 1) with
      | some ⟨some q', .rightHead revL⟩ =>
        let ic := cert.inCollar subIn
        (q' == cert.qIn) &&
        (revL.take ic.length == ic) &&
        let pushed := revL.drop ic.length
        checkHubBranches M cert fuel pushed subIn branches 0
      | _ => false
where
  checkHubBranches {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
      (cert : CollarBoxCert B I C H) (fuel : ℕ) (pushed : List (Fin 2)) (subIn : Fin I) :
      List (BoxProg I (Fin H × List (Fin B))) → ℕ → Bool
    | [], idx => idx == C
    | br :: brs, idx =>
      if h : idx < C then
        let rc := cert.retCollar subIn ⟨idx, h⟩
        checkHubProg M cert fuel (resumeSymCfg cert.qOut pushed rc) br &&
        checkHubBranches M cert fuel pushed subIn brs (idx + 1)
      else
        false

/-- Check `endBits` base case for collar `i : Fin I` (`blankL = false, blankR = true`). -/
private def checkEndOne {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
    (cert : CollarBoxCert B I C H) (i : Fin I) : Bool :=
  let (steps, cOut, emitted) := cert.endProg i
  let lenOk := if cert.lenPreserving then emitted.isEmpty else true
  lenOk &&
  match cert.endBits, steps with
  | eh :: ert, k + 1 =>
    let s₀ : SymCfg (Fin 2) (Fin 6) := ⟨some cert.qIn, .mid (cert.inCollar i) eh ert⟩
    match symRun false true M s₀ (k + 1) with
    | some ⟨some q', .leftHead outBits⟩ =>
      (q' == cert.qOut) &&
      (trimZeros outBits ==
        trimZeros (cert.retCollar i cOut ++ encBlocks cert.blockBits emitted ++ cert.endBits))
    | _ => false
  | _, _ => false

/-- Check one `(i : Fin I, b : Fin B)` block tree from its entry `SymCfg`. -/
private def checkBlockOne {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
    (cert : CollarBoxCert B I C H) (i : Fin I) (b : Fin B) : Bool :=
  match cert.blockBits b with
  | bh :: brt =>
    let s₀ : SymCfg (Fin 2) (Fin 6) := ⟨some cert.qIn, .mid (cert.inCollar i) bh brt⟩
    checkBlockProg M cert i true cert.maxTreeDepth s₀ (cert.boxProg i b)
  | [] => false

/-- Check one hub `h : Fin H` from its entry `SymCfg`. -/
private def checkHubOne {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
    (cert : CollarBoxCert B I C H) (h : Fin H) : Bool :=
  match cert.hubRight h with
  | hh :: hrt =>
    let s₀ : SymCfg (Fin 2) (Fin 6) := ⟨some (cert.hubState h), .mid (cert.hubLeft h) hh hrt⟩
    checkHubProg M cert cert.maxTreeDepth s₀ (cert.hubProg h)
  | [] => false

/-- Helper checking `f ⟨idx, _⟩ == true` for all `idx < N`. -/
private def allFin : (N : ℕ) → (Fin N → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ && allFin n (fun i => f ⟨i.val + 1,
      Nat.succ_lt_succ i.isLt⟩)

private theorem allFin_iff {N : ℕ} {f : Fin N → Bool} (h : allFin N f = true) (i : Fin N) :
    f i = true := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    dsimp only [allFin] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h0, hrest⟩
    rcases i with ⟨_ | k, hk⟩
    · exact h0
    · exact ih hrest ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Top-level kernel-reducible checker for `CollarBoxCert`. -/
private def checkCollarBoxCert {B I C H : ℕ} (M : Machine (Fin 2) (Fin 6))
    (cert : CollarBoxCert B I C H) : Bool :=
  let M' := if cert.mirrorTape then flipTM M else M
  (0 < I) && (0 < C) && (0 < H) &&
  allFin I (checkEndOne M' cert) &&
  allFin I (fun i => allFin B (checkBlockOne M' cert i)) &&
  allFin H (checkHubOne M' cert) &&
  let initSym : SymCfg (Fin 2) (Fin 6) := ⟨some 0, .mid [] 0 []⟩
  match symRun true true M' initSym cert.entrySteps with
  | some ⟨some q', .mid outL outH outR⟩ =>
    (q' == cert.hubState cert.initHub) &&
    (trimZeros outL == trimZeros (cert.hubLeft cert.initHub)) &&
    (trimZeros (outH :: outR) ==
      trimZeros (cert.hubRight cert.initHub ++
        encBlocks cert.blockBits cert.initBlocks ++ cert.endBits))
  | _ => false

/-! ## Soundness Proof -/

private theorem isNotHalt_of_flipTM {M : Machine (Fin 2) (Fin 6)}
    (h : IsNotHalt (flipTM M)) : IsNotHalt M := by
  intro cfg hreach
  have hinit_flip : flipCfg (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = init [] := by
    simp [init, flipCfg, flipTape, Tape.mk₁, Tape.mk₂, Tape.mk',
      ListBlank.mk_nil, ListBlank.head_default, ListBlank.tail_default]
  have hreach_flip : (init []) [flipTM M]⊢* (flipCfg cfg) := by
    rw [← hinit_flip]
    exact stepStar_flipTM hreach
  have hsome := h (flipCfg cfg) hreach_flip
  rw [step_flipTM] at hsome
  rcases hstep : step M cfg with _ | _
  · rw [hstep] at hsome
    simp at hsome
  · rfl

private theorem branch_lookup {I C : ℕ}
    {M : Machine (Fin 2) (Fin 6)} {B H : ℕ} {cert : CollarBoxCert B I C H}
    {i : Fin I} {allowSub : Bool} {fuel : ℕ} {pushed : List (Fin 2)} {subIn : Fin I}
    {branches : List (BoxProg I (Fin C × List (Fin B)))} {idx : ℕ}
    (hok : checkBlockProg.checkBlockBranches M cert i allowSub fuel pushed subIn branches idx =
        true)
    (c : Fin C) (hc : idx ≤ c.val) :
    ∃ br, checkBlockProg M cert i allowSub fuel
      (resumeSymCfg cert.qOut pushed (cert.retCollar subIn c)) br = true := by
  induction branches generalizing idx with
  | nil =>
    simp only [checkBlockProg.checkBlockBranches, beq_iff_eq] at hok
    omega
  | cons br brs ih =>
    dsimp only [checkBlockProg.checkBlockBranches] at hok
    split at hok
    · rename_i hlt
      rcases Bool.and_eq_true_iff.mp hok with ⟨hbr, hbrs⟩
      rcases Nat.eq_or_lt_of_le hc with heq | hgt
      · have hfin : (⟨idx, hlt⟩ : Fin C) = c := Fin.ext heq
        rw [hfin] at hbr
        exact ⟨br, hbr⟩
      · exact ih hbrs hgt
    · simp at hok

private theorem hub_branch_lookup {B I C H : ℕ}
    {M : Machine (Fin 2) (Fin 6)} {cert : CollarBoxCert B I C H}
    {fuel : ℕ} {pushed : List (Fin 2)} {subIn : Fin I}
    {branches : List (BoxProg I (Fin H × List (Fin B)))} {idx : ℕ}
    (hok : checkHubProg.checkHubBranches M cert fuel pushed subIn branches idx = true)
    (c : Fin C) (hc : idx ≤ c.val) :
    ∃ br, checkHubProg M cert fuel
      (resumeSymCfg cert.qOut pushed (cert.retCollar subIn c)) br = true := by
  induction branches generalizing idx with
  | nil =>
    simp only [checkHubProg.checkHubBranches, beq_iff_eq] at hok
    omega
  | cons br brs ih =>
    dsimp only [checkHubProg.checkHubBranches] at hok
    split at hok
    · rename_i hlt
      rcases Bool.and_eq_true_iff.mp hok with ⟨hbr, hbrs⟩
      rcases Nat.eq_or_lt_of_le hc with heq | hgt
      · have hfin : (⟨idx, hlt⟩ : Fin C) = c := Fin.ext heq
        rw [hfin] at hbr
        exact ⟨br, hbr⟩
      · exact ih hbrs hgt
    · simp at hok

private theorem checkEndOne_sound {B I C H : ℕ} {M : Machine (Fin 2) (Fin 6)}
    {cert : CollarBoxCert B I C H} {i : Fin I}
    (hok : checkEndOne M cert i = true) :
    ∃ (c : Fin C) (ys : List (Fin B)),
      (cert.lenPreserving = true → ys.length = 0) ∧
      BoxStep M cert.inCollar cert.retCollar cert.qIn cert.qOut i
        (enc cert.blockBits cert.endBits []) c (enc cert.blockBits cert.endBits ys) := by
  unfold checkEndOne at hok
  rcases hend : cert.endProg i with ⟨steps, cOut, emitted⟩
  rw [hend] at hok
  rcases Bool.and_eq_true_iff.mp hok with ⟨hlenOk, hrun⟩
  cases heb : cert.endBits with
  | nil => rw [heb] at hrun; simp at hrun
  | cons eh ert =>
    rw [heb] at hrun
    cases steps with
    | zero => simp at hrun
    | succ k =>
      dsimp only at hrun
      rcases hsr : symRun false true M ⟨some cert.qIn, .mid (cert.inCollar i) eh ert⟩ (k + 1) with
        _ | ⟨_ | q', _ | outBits | _⟩
      all_goals (rw [hsr] at hrun; try (simp at hrun; done))
      simp only [Bool.and_eq_true] at hrun
      rcases hrun with ⟨hq, hbits⟩
      have hq_eq : q' = cert.qOut := beq_iff_eq.mp hq
      subst hq_eq
      have htrim : trimZeros outBits =
          trimZeros (cert.retCollar i cOut ++ encBlocks cert.blockBits emitted ++ (eh :: ert)) :=
        beq_iff_eq.mp hbits
      refine ⟨cOut, emitted, ?_, ?_⟩
      · intro hlp
        rw [hlp] at hlenOk
        simp only [↓reduceIte, List.isEmpty_iff] at hlenOk
        simp [hlenOk]
      · intro l
        have hp := symRun_blankR_plus l M ⟨some cert.qIn, .mid (cert.inCollar i) eh ert⟩
          ⟨some cert.qOut, .leftHead outBits⟩ k hsr
        have h1 : (SymCfg.mk (some cert.qIn) (.mid (cert.inCollar i) eh ert)).eval l default =
            ((cert.inCollar i +> l) {{cert.qIn}}> enc cert.blockBits cert.endBits []) := by
          simp only [enc, heb, listblank_append_cons, eval_headRight_cons, SymCfg.eval,
            SymCursor.eval]
        have h2 : (SymCfg.mk (some cert.qOut) (.leftHead outBits)).eval l default =
            (l <{{cert.qOut}} (cert.retCollar i cOut +> enc cert.blockBits cert.endBits emitted)) :=
                by
          simp only [SymCfg.eval, SymCursor.eval]
          have hout : outBits +> (default : ListBlank (Fin 2)) =
              (cert.retCollar i cOut ++ encBlocks cert.blockBits emitted ++
                  cert.endBits) +> default := by
            rw [← trimZeros_append_default outBits, htrim, ← heb, trimZeros_append_default]
          have henc : (cert.retCollar i cOut ++ encBlocks cert.blockBits emitted ++ cert.endBits) +>
              (default : ListBlank (Fin 2)) =
              cert.retCollar i cOut +> enc cert.blockBits cert.endBits emitted := by
            rw [List.append_assoc, BusyBeaver.PairStack.listblank_append_right_assoc,
                BusyBeaver.PairStack.listblank_append_right_assoc]
            have he : cert.endBits +> (default : ListBlank (Fin 2)) =
                enc cert.blockBits cert.endBits [] := rfl
            rw [he, encBlocks_append_enc, List.append_nil]
          rw [hout, henc]
        rw [h1, h2, heb] at hp
        exact hp

private theorem blockProg_lenPreserving_sound {B I C H : ℕ}
    {M : Machine (Fin 2) (Fin 6)} {cert : CollarBoxCert B I C H}
    (hlp : cert.lenPreserving = true)
    {i : Fin I} {allowSub : Bool} {n : ℕ}
    (ih : ∀ ws : List (Fin B), ws.length = n → ∀ sub : Fin I,
      ∃ (c : Fin C) (ys : List (Fin B)), ys.length = n ∧
        BoxStep M cert.inCollar cert.retCollar cert.qIn cert.qOut sub
          (enc cert.blockBits cert.endBits ws) c (enc cert.blockBits cert.endBits ys)) :
    ∀ (fuel : ℕ) (s : SymCfg (Fin 2) (Fin 6)) (prog : BoxProg I (Fin C × List (Fin B)))
      (xs : List (Fin B)),
      xs.length = n →
      checkBlockProg M cert i allowSub fuel s prog = true →
      ∃ (cOut : Fin C) (zs : List (Fin B)),
        zs.length = n + 1 ∧
        ∀ l : ListBlank (Fin 2),
          (s.eval l (enc cert.blockBits cert.endBits xs)) [M]⊢⁺
            (l <{{cert.qOut}} (cert.retCollar i cOut +> enc cert.blockBits cert.endBits zs)) := by
  intro fuel
  induction fuel generalizing allowSub with
  | zero => intros _ _ _ _ h; simp [checkBlockProg] at h
  | succ fuel ihF =>
    intro s prog xs hlen hok
    cases prog with
    | finish steps leaf =>
      rcases leaf with ⟨cOut, emitted⟩
      dsimp only [checkBlockProg] at hok
      rw [hlp] at hok
      rcases Bool.and_eq_true_iff.mp hok with ⟨hemlen, hrun⟩
      simp only [↓reduceIte, beq_iff_eq] at hemlen
      cases steps with
      | zero => simp at hrun
      | succ k =>
        dsimp only at hrun
        rcases hsr : symRun false false M s (k + 1) with _ | ⟨_ | q', _ | outBits | _⟩
        all_goals (rw [hsr] at hrun; try (simp at hrun; done))
        simp only [Bool.and_eq_true] at hrun
        rcases hrun with ⟨hq, hbits⟩
        have hq_eq : q' = cert.qOut := beq_iff_eq.mp hq
        subst hq_eq
        have hout_eq : outBits = cert.retCollar i cOut ++ encBlocks cert.blockBits emitted :=
          beq_iff_eq.mp hbits
        refine ⟨cOut, emitted ++ xs, by simp [hemlen, hlen, Nat.add_comm], fun l => ?_⟩
        have hp := symRun_open_plus l (enc cert.blockBits cert.endBits xs) M s
          ⟨some cert.qOut, .leftHead outBits⟩ k hsr
        have hev : (SymCfg.mk (some cert.qOut) (.leftHead outBits)).eval
            l (enc cert.blockBits cert.endBits xs) =
            (l <{{cert.qOut}}
              (cert.retCollar i cOut +> enc cert.blockBits cert.endBits (emitted ++ xs))) := by
          simp only [SymCfg.eval, SymCursor.eval, hout_eq,
              BusyBeaver.PairStack.listblank_append_right_assoc,
            encBlocks_append_enc]
        rwa [hev] at hp
    | callSubBox steps subIn branches =>
      dsimp only [checkBlockProg] at hok
      rcases Bool.and_eq_true_iff.mp hok with ⟨_, hrun⟩
      cases steps with
      | zero => simp at hrun
      | succ k =>
        dsimp only at hrun
        rcases hsr : symRun false false M s (k + 1) with _ | ⟨_ | q', _ | _ | revL⟩
        all_goals (rw [hsr] at hrun; try (simp at hrun; done))
        simp only [Bool.and_eq_true] at hrun
        rcases hrun with ⟨⟨hq, htake⟩, hbrs⟩
        have hq_eq : q' = cert.qIn := beq_iff_eq.mp hq
        subst hq_eq
        have htake_eq : revL.take (cert.inCollar subIn).length = cert.inCollar subIn :=
          beq_iff_eq.mp htake
        set pushed := revL.drop (cert.inCollar subIn).length
        have hrev : cert.inCollar subIn ++ pushed = revL := by
          rw [← htake_eq]
          exact List.take_append_drop _ revL
        rcases ih xs hlen subIn with ⟨c₁, ys₁, hlen₁, hsub⟩
        rcases branch_lookup hbrs c₁ (Nat.zero_le _) with ⟨br, hbr⟩
        rcases ihF (allowSub := cert.lenPreserving)
          (resumeSymCfg cert.qOut pushed (cert.retCollar subIn c₁)) br ys₁ hlen₁ hbr with
          ⟨cOut, zs, hzs_len, hrest⟩
        refine ⟨cOut, zs, hzs_len, fun l => ?_⟩
        have hp₁ := symRun_open_plus l (enc cert.blockBits cert.endBits xs) M s
          ⟨some cert.qIn, .rightHead revL⟩ k hsr
        have hev₁ : (SymCfg.mk (some cert.qIn) (.rightHead revL)).eval
            l (enc cert.blockBits cert.endBits xs) =
            ((cert.inCollar subIn +> (pushed +> l)) {{cert.qIn}}>
              enc cert.blockBits cert.endBits xs) := by
          simp only [SymCfg.eval, SymCursor.eval, ← hrev,
              BusyBeaver.PairStack.listblank_append_right_assoc]
        rw [hev₁] at hp₁
        have hp₂ := hsub (pushed +> l)
        have hp₃ := hrest l
        rw [resumeSymCfg_eval] at hp₃
        exact BusyBeaver.stepPlus_trans hp₁ (BusyBeaver.stepPlus_trans hp₂ hp₃)

private theorem blockProg_oneCall_sound {B I C H : ℕ}
    {M : Machine (Fin 2) (Fin 6)} {cert : CollarBoxCert B I C H}
    (hnlp : cert.lenPreserving = false)
    {i : Fin I} {xs : List (Fin B)}
    (ih : ∀ sub : Fin I,
      ∃ (c : Fin C) (ys : List (Fin B)),
        BoxStep M cert.inCollar cert.retCollar cert.qIn cert.qOut sub
          (enc cert.blockBits cert.endBits xs) c (enc cert.blockBits cert.endBits ys)) :
    ∀ (fuel : ℕ) (allowSub : Bool) (s : SymCfg (Fin 2) (Fin 6))
      (prog : BoxProg I (Fin C × List (Fin B))) (curXs : List (Fin B)),
      (allowSub = true → curXs = xs) →
      checkBlockProg M cert i allowSub fuel s prog = true →
      ∃ (cOut : Fin C) (zs : List (Fin B)),
        ∀ l : ListBlank (Fin 2),
          (s.eval l (enc cert.blockBits cert.endBits curXs)) [M]⊢⁺
            (l <{{cert.qOut}} (cert.retCollar i cOut +> enc cert.blockBits cert.endBits zs)) := by
  intro fuel
  induction fuel with
  | zero => intros _ _ _ _ _ h; simp [checkBlockProg] at h
  | succ fuel ihF =>
    intro allowSub s prog curXs hcur hok
    cases prog with
    | finish steps leaf =>
      rcases leaf with ⟨cOut, emitted⟩
      dsimp only [checkBlockProg] at hok
      rw [hnlp] at hok
      rcases Bool.and_eq_true_iff.mp hok with ⟨_, hrun⟩
      cases steps with
      | zero => simp at hrun
      | succ k =>
        dsimp only at hrun
        rcases hsr : symRun false false M s (k + 1) with _ | ⟨_ | q', _ | outBits | _⟩
        all_goals (rw [hsr] at hrun; try (simp at hrun; done))
        simp only [Bool.and_eq_true] at hrun
        rcases hrun with ⟨hq, hbits⟩
        have hq_eq : q' = cert.qOut := beq_iff_eq.mp hq
        subst hq_eq
        have hout_eq : outBits = cert.retCollar i cOut ++ encBlocks cert.blockBits emitted :=
          beq_iff_eq.mp hbits
        refine ⟨cOut, emitted ++ curXs, fun l => ?_⟩
        have hp := symRun_open_plus l (enc cert.blockBits cert.endBits curXs) M s
          ⟨some cert.qOut, .leftHead outBits⟩ k hsr
        have hev : (SymCfg.mk (some cert.qOut) (.leftHead outBits)).eval
            l (enc cert.blockBits cert.endBits curXs) =
            (l <{{cert.qOut}}
              (cert.retCollar i cOut +> enc cert.blockBits cert.endBits (emitted ++ curXs))) := by
          simp only [SymCfg.eval, SymCursor.eval, hout_eq,
              BusyBeaver.PairStack.listblank_append_right_assoc,
            encBlocks_append_enc]
        rwa [hev] at hp
    | callSubBox steps subIn branches =>
      dsimp only [checkBlockProg] at hok
      rcases Bool.and_eq_true_iff.mp hok with ⟨hallow, hrun⟩
      have hxs_eq : curXs = xs := hcur hallow
      subst hxs_eq
      cases steps with
      | zero => simp at hrun
      | succ k =>
        dsimp only at hrun
        rcases hsr : symRun false false M s (k + 1) with _ | ⟨_ | q', _ | _ | revL⟩
        all_goals (rw [hsr] at hrun; try (simp at hrun; done))
        simp only [Bool.and_eq_true] at hrun
        rcases hrun with ⟨⟨hq, htake⟩, hbrs⟩
        have hq_eq : q' = cert.qIn := beq_iff_eq.mp hq
        subst hq_eq
        have htake_eq : revL.take (cert.inCollar subIn).length = cert.inCollar subIn :=
          beq_iff_eq.mp htake
        set pushed := revL.drop (cert.inCollar subIn).length
        have hrev : cert.inCollar subIn ++ pushed = revL := by
          rw [← htake_eq]
          exact List.take_append_drop _ revL
        rcases ih subIn with ⟨c₁, ys₁, hsub⟩
        rcases branch_lookup hbrs c₁ (Nat.zero_le _) with ⟨br, hbr⟩
        rw [hnlp] at hbr
        rcases ihF false (resumeSymCfg cert.qOut pushed (cert.retCollar subIn c₁)) br ys₁
          (fun h => absurd h Bool.false_ne_true) hbr with ⟨cOut, zs, hrest⟩
        refine ⟨cOut, zs, fun l => ?_⟩
        have hp₁ := symRun_open_plus l (enc cert.blockBits cert.endBits curXs) M s
          ⟨some cert.qIn, .rightHead revL⟩ k hsr
        have hev₁ : (SymCfg.mk (some cert.qIn) (.rightHead revL)).eval
            l (enc cert.blockBits cert.endBits curXs) =
            ((cert.inCollar subIn +> (pushed +> l)) {{cert.qIn}}>
              enc cert.blockBits cert.endBits curXs) := by
          simp only [SymCfg.eval, SymCursor.eval, ← hrev,
              BusyBeaver.PairStack.listblank_append_right_assoc]
        rw [hev₁] at hp₁
        have hp₂ := hsub (pushed +> l)
        have hp₃ := hrest l
        rw [resumeSymCfg_eval] at hp₃
        exact BusyBeaver.stepPlus_trans hp₁ (BusyBeaver.stepPlus_trans hp₂ hp₃)

private theorem box_all_sound {B I C H : ℕ} {M : Machine (Fin 2) (Fin 6)}
    {cert : CollarBoxCert B I C H}
    (hend : ∀ i : Fin I, checkEndOne M cert i = true)
    (hblk : ∀ (i : Fin I) (b : Fin B), checkBlockOne M cert i b = true) :
    ∀ (xs : List (Fin B)) (i : Fin I),
      ∃ (c : Fin C) (ys : List (Fin B)),
        BoxStep M cert.inCollar cert.retCollar cert.qIn cert.qOut i
          (enc cert.blockBits cert.endBits xs) c (enc cert.blockBits cert.endBits ys) := by
  cases hlp : cert.lenPreserving with
  | true =>
    suffices hlen_ind : ∀ (n : ℕ) (xs : List (Fin B)), xs.length = n → ∀ i : Fin I,
        ∃ (c : Fin C) (ys : List (Fin B)), ys.length = n ∧
          BoxStep M cert.inCollar cert.retCollar cert.qIn cert.qOut i
            (enc cert.blockBits cert.endBits xs) c (enc cert.blockBits cert.endBits ys) by
      intro xs i
      rcases hlen_ind xs.length xs rfl i with ⟨c, ys, _, hbox⟩
      exact ⟨c, ys, hbox⟩
    intro n
    induction n with
    | zero =>
      intro xs hlen i
      cases xs with
      | nil =>
        rcases checkEndOne_sound (hend i) with ⟨c, ys, hys_len, hbox⟩
        exact ⟨c, ys, hys_len hlp, hbox⟩
      | cons _ _ => simp at hlen
    | succ n ih =>
      intro xs hlen i
      cases xs with
      | nil => simp at hlen
      | cons b xs' =>
        have hlen' : xs'.length = n := Nat.succ.inj hlen
        have hb := hblk i b
        dsimp only [checkBlockOne] at hb
        cases hbb : cert.blockBits b with
        | nil => rw [hbb] at hb; simp at hb
        | cons bh brt =>
          rw [hbb] at hb
          rcases blockProg_lenPreserving_sound hlp ih cert.maxTreeDepth
            ⟨some cert.qIn, .mid (cert.inCollar i) bh brt⟩ (cert.boxProg i b) xs' hlen' hb with
            ⟨cOut, zs, hzs_len, hreach⟩
          refine ⟨cOut, zs, hzs_len, fun l => ?_⟩
          have hev : (SymCfg.mk (some cert.qIn) (.mid (cert.inCollar i) bh brt)).eval
              l (enc cert.blockBits cert.endBits xs') =
              ((cert.inCollar i +> l) {{cert.qIn}}> enc cert.blockBits cert.endBits (b :: xs')) :=
                  by
            simp only [enc, hbb, listblank_append_cons, eval_headRight_cons, SymCfg.eval,
              SymCursor.eval]
          rw [← hev]
          exact hreach l
  | false =>
    intro xs
    induction xs with
    | nil =>
      intro i
      rcases checkEndOne_sound (hend i) with ⟨c, ys, _, hbox⟩
      exact ⟨c, ys, hbox⟩
    | cons b xs' ih =>
      intro i
      have hb := hblk i b
      dsimp only [checkBlockOne] at hb
      cases hbb : cert.blockBits b with
      | nil => rw [hbb] at hb; simp at hb
      | cons bh brt =>
        rw [hbb] at hb
        rcases blockProg_oneCall_sound hlp ih cert.maxTreeDepth true
          ⟨some cert.qIn, .mid (cert.inCollar i) bh brt⟩ (cert.boxProg i b) xs'
          (fun _ => rfl) hb with ⟨cOut, zs, hreach⟩
        refine ⟨cOut, zs, fun l => ?_⟩
        have hev : (SymCfg.mk (some cert.qIn) (.mid (cert.inCollar i) bh brt)).eval
            l (enc cert.blockBits cert.endBits xs') =
            ((cert.inCollar i +> l) {{cert.qIn}}> enc cert.blockBits cert.endBits (b :: xs')) := by
          simp only [enc, hbb, listblank_append_cons, eval_headRight_cons, SymCfg.eval,
            SymCursor.eval]
        rw [← hev]
        exact hreach l

private theorem hubProg_sound {B I C H : ℕ} {M : Machine (Fin 2) (Fin 6)}
    {cert : CollarBoxCert B I C H}
    (hbox : ∀ (xs : List (Fin B)) (i : Fin I),
      ∃ (c : Fin C) (ys : List (Fin B)),
        BoxStep M cert.inCollar cert.retCollar cert.qIn cert.qOut i
          (enc cert.blockBits cert.endBits xs) c (enc cert.blockBits cert.endBits ys)) :
    ∀ (fuel : ℕ) (s : SymCfg (Fin 2) (Fin 6)) (prog : BoxProg I (Fin H × List (Fin B)))
      (xs : List (Fin B)),
      checkHubProg M cert fuel s prog = true →
      ∃ (nextHub : Fin H) (zs : List (Fin B)),
        (s.eval default (enc cert.blockBits cert.endBits xs)) [M]⊢⁺ cfgHub cert nextHub zs := by
  intro fuel
  induction fuel with
  | zero => intros _ _ _ h; simp [checkHubProg] at h
  | succ fuel ih =>
    intro s prog xs hok
    cases prog with
    | finish steps leaf =>
      rcases leaf with ⟨nextHub, emitted⟩
      dsimp only [checkHubProg] at hok
      cases steps with
      | zero => simp at hok
      | succ k =>
        dsimp only at hok
        rcases hsr : symRun true false M s (k + 1) with _ | ⟨_ | q', ⟨outL, outH, outR⟩ | _ | _⟩
        all_goals (rw [hsr] at hok; try (simp at hok; done))
        simp only [Bool.and_eq_true] at hok
        rcases hok with ⟨⟨hq, hL⟩, hR⟩
        have hq_eq : q' = cert.hubState nextHub := beq_iff_eq.mp hq
        subst hq_eq
        have hL_eq : trimZeros outL = trimZeros (cert.hubLeft nextHub) := beq_iff_eq.mp hL
        have hR_eq : (outH :: outR) = cert.hubRight nextHub ++ encBlocks cert.blockBits emitted :=
          beq_iff_eq.mp hR
        refine ⟨nextHub, emitted ++ xs, ?_⟩
        have hp := symRun_blankL_plus (enc cert.blockBits cert.endBits xs) M s
          ⟨some (cert.hubState nextHub), .mid outL outH outR⟩ k hsr
        have hev : (SymCfg.mk (some (cert.hubState nextHub)) (.mid outL outH outR)).eval
            default (enc cert.blockBits cert.endBits xs) =
            cfgHub cert nextHub (emitted ++ xs) := by
          have houtL : outL +> (default : ListBlank (Fin 2)) = cert.hubLeft nextHub +> default := by
            rw [← trimZeros_append_default outL, hL_eq, trimZeros_append_default]
          have houtR : (outH :: outR) +> enc cert.blockBits cert.endBits xs =
              cert.hubRight nextHub +> enc cert.blockBits cert.endBits (emitted ++ xs) := by
            rw [hR_eq, BusyBeaver.PairStack.listblank_append_right_assoc, encBlocks_append_enc]
          simp only [cfgHub, SymCfg.eval, SymCursor.eval, houtL, ← houtR,
            listblank_append_cons, eval_headRight_cons]
        rwa [hev] at hp
    | callSubBox steps subIn branches =>
      dsimp only [checkHubProg] at hok
      cases steps with
      | zero => simp at hok
      | succ k =>
        dsimp only at hok
        rcases hsr : symRun true false M s (k + 1) with _ | ⟨_ | q', _ | _ | revL⟩
        all_goals (rw [hsr] at hok; try (simp at hok; done))
        simp only [Bool.and_eq_true] at hok
        rcases hok with ⟨⟨hq, htake⟩, hbrs⟩
        have hq_eq : q' = cert.qIn := beq_iff_eq.mp hq
        subst hq_eq
        have htake_eq : revL.take (cert.inCollar subIn).length = cert.inCollar subIn :=
          beq_iff_eq.mp htake
        set pushed := revL.drop (cert.inCollar subIn).length
        have hrev : cert.inCollar subIn ++ pushed = revL := by
          rw [← htake_eq]
          exact List.take_append_drop _ revL
        rcases hbox xs subIn with ⟨c₁, ys₁, hsub⟩
        rcases hub_branch_lookup hbrs c₁ (Nat.zero_le _) with ⟨br, hbr⟩
        rcases ih (resumeSymCfg cert.qOut pushed (cert.retCollar subIn c₁)) br ys₁ hbr with
          ⟨nextHub, zs, hrest⟩
        refine ⟨nextHub, zs, ?_⟩
        have hp₁ := symRun_blankL_plus (enc cert.blockBits cert.endBits xs) M s
          ⟨some cert.qIn, .rightHead revL⟩ k hsr
        have hev₁ : (SymCfg.mk (some cert.qIn) (.rightHead revL)).eval
            default (enc cert.blockBits cert.endBits xs) =
            ((cert.inCollar subIn +> (pushed +> default)) {{cert.qIn}}>
              enc cert.blockBits cert.endBits xs) := by
          simp only [SymCfg.eval, SymCursor.eval, ← hrev,
              BusyBeaver.PairStack.listblank_append_right_assoc]
        rw [hev₁] at hp₁
        have hp₂ := hsub (pushed +> default)
        rw [resumeSymCfg_eval] at hrest
        exact BusyBeaver.stepPlus_trans hp₁ (BusyBeaver.stepPlus_trans hp₂ hrest)

/-- Main soundness theorem: if `checkCollarBoxCert M cert = true`, then `IsNotHalt M`. -/
private theorem collarBoxCert_sound {B I C H : ℕ}
    {M : Machine (Fin 2) (Fin 6)} {cert : CollarBoxCert B I C H}
    (hok : checkCollarBoxCert M cert = true) :
    IsNotHalt M := by
  dsimp only [checkCollarBoxCert] at hok
  set M' : Machine (Fin 2) (Fin 6) := if cert.mirrorTape then flipTM M else M
  rcases Bool.and_eq_true_iff.mp hok with ⟨hrest0, hinitRun⟩
  rcases Bool.and_eq_true_iff.mp hrest0 with ⟨hrest1, hhubs⟩
  rcases Bool.and_eq_true_iff.mp hrest1 with ⟨hrest2, hblks⟩
  rcases Bool.and_eq_true_iff.mp hrest2 with ⟨_, hends⟩
  have hend_all : ∀ i : Fin I, checkEndOne M' cert i = true := allFin_iff hends
  have hblk_all : ∀ (i : Fin I) (b : Fin B), checkBlockOne M' cert i b = true :=
    fun i b => allFin_iff (allFin_iff hblks i) b
  have hhub_all : ∀ h : Fin H, checkHubOne M' cert h = true := allFin_iff hhubs
  have hbox := box_all_sound hend_all hblk_all
  have hhub_step : ∀ (h : Fin H) (xs : List (Fin B)),
      ∃ (h' : Fin H) (zs : List (Fin B)), (cfgHub cert h xs) [M']⊢⁺ (cfgHub cert h' zs) := by
    intro h xs
    have hh := hhub_all h
    dsimp only [checkHubOne] at hh
    cases hhr : cert.hubRight h with
    | nil => rw [hhr] at hh; simp at hh
    | cons hh0 hrt =>
      rw [hhr] at hh
      rcases hubProg_sound hbox cert.maxTreeDepth
        ⟨some (cert.hubState h), .mid (cert.hubLeft h) hh0 hrt⟩ (cert.hubProg h) xs hh with
        ⟨h', zs, hp⟩
      refine ⟨h', zs, ?_⟩
      have hev : (SymCfg.mk (some (cert.hubState h)) (.mid (cert.hubLeft h) hh0 hrt)).eval
          default (enc cert.blockBits cert.endBits xs) = cfgHub cert h xs := by
        simp only [cfgHub, hhr, listblank_append_cons, eval_headRight_cons, SymCfg.eval,
          SymCursor.eval]
      rwa [hev] at hp
  rcases hsr : symRun true true M' ⟨some 0, .mid [] 0 []⟩ cert.entrySteps with
    _ | ⟨_ | q', ⟨outL, outH, outR⟩ | _ | _⟩
  all_goals (rw [hsr] at hinitRun; try (simp at hinitRun; done))
  simp only [Bool.and_eq_true] at hinitRun
  rcases hinitRun with ⟨⟨hq, hL⟩, hR⟩
  have hq_eq : q' = cert.hubState cert.initHub := beq_iff_eq.mp hq
  subst hq_eq
  have hL_eq : trimZeros outL = trimZeros (cert.hubLeft cert.initHub) := beq_iff_eq.mp hL
  have hR_eq : trimZeros (outH :: outR) =
      trimZeros (cert.hubRight cert.initHub ++
        encBlocks cert.blockBits cert.initBlocks ++ cert.endBits) := beq_iff_eq.mp hR
  have hinit_star : (init ([] : List (Fin 2))) [M']⊢* cfgHub cert cert.initHub cert.initBlocks := by
    have hs := symRun_blank_star M' ⟨some 0, .mid [] 0 []⟩
      ⟨some (cert.hubState cert.initHub), .mid outL outH outR⟩ cert.entrySteps hsr
    have hinit0 : (SymCfg.mk (some (0 : Fin 6)) (.mid [] (0 : Fin 2) [])).eval
        default default = init [] := rfl
    rw [hinit0] at hs
    have hev : (SymCfg.mk (some (cert.hubState cert.initHub)) (.mid outL outH outR)).eval
        default default = cfgHub cert cert.initHub cert.initBlocks := by
      have houtL : outL +> (default : ListBlank (Fin 2)) =
          cert.hubLeft cert.initHub +> default := by
        rw [← trimZeros_append_default outL, hL_eq, trimZeros_append_default]
      have houtR : (outH :: outR) +> (default : ListBlank (Fin 2)) =
          cert.hubRight cert.initHub +> enc cert.blockBits cert.endBits cert.initBlocks := by
        rw [← trimZeros_append_default (outH :: outR), hR_eq, trimZeros_append_default,
          List.append_assoc, BusyBeaver.PairStack.listblank_append_right_assoc,
              BusyBeaver.PairStack.listblank_append_right_assoc]
        have he : cert.endBits +> (default : ListBlank (Fin 2)) =
            enc cert.blockBits cert.endBits [] := rfl
        rw [he, encBlocks_append_enc, List.append_nil]
      simp only [cfgHub, SymCfg.eval, SymCursor.eval, houtL, ← houtR,
        listblank_append_cons, eval_headRight_cons]
    rwa [hev] at hs
  have hM'_nh : IsNotHalt M' := by
    refine does_not_halt_of_advances
      (P := fun c => ∃ (h : Fin H) (xs : List (Fin B)), c = cfgHub cert h xs)
      hinit_star
      ⟨cert.initHub, cert.initBlocks, rfl⟩
      ?_
    rintro _ ⟨h, xs, rfl⟩
    rcases hhub_step h xs with ⟨h', zs, hp⟩
    exact Advances.of_stepPlus hp ⟨h', zs, rfl⟩
  cases hmir : cert.mirrorTape with
  | false =>
    dsimp only [M'] at hM'_nh
    rw [hmir] at hM'_nh
    simpa using hM'_nh
  | true =>
    dsimp only [M'] at hM'_nh
    rw [hmir] at hM'_nh
    exact isNotHalt_of_flipTM (by simpa using hM'_nh)

end CollarBox


open CollarBox

/-- 16-block prefix-free turnaround transducer certificate for
    `1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---`. -/
private def cert403 : CollarBoxCert 16 1 2 1 where
  mirrorTape := false
  lenPreserving := true
  maxTreeDepth := 4
  qIn := 0
  qOut := 4
  blockBits := fun b =>
    match b.val with
    | 0  => [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1]
    | 1  => [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    | 2  => [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1]
    | 3  => [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1]
    | 4  => [0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1]
    | 5  => [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1]
    | 6  => [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
    | 7  => [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
    | 8  => [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]
    | 9  => [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
    | 10 => [0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1]
    | 11 => [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1]
    | 12 => [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
    | 13 => [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
    | 14 => [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]
    | _  => [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]
  endBits := [0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1]
  inCollar := fun _ => [0, 0]
  retCollar := fun _ c =>
    match c.val with
    | 0 => [0, 0, 0, 1]
    | _ => [0, 1]
  endProg := fun _ => (103, 0, [])
  boxProg := fun _ b =>
    match b.val with
    | 0  => .callSubBox 64 0 [.finish 12 (1, [7]), .finish 12 (1, [1])]
    | 1  => .callSubBox 52 0 [.finish 12 (1, [5]), .finish 12 (1, [0])]
    | 2  => .callSubBox 48 0 [.finish 22 (1, [11]), .finish 22 (1, [3])]
    | 3  => .finish 37 (1, [4])
    | 4  => .callSubBox 50 0
        [.finish 86 (0, [2]), .callSubBox 69 0 [.finish 14 (0, [5]), .finish 14 (0, [0])]]
    | 5  => .finish 79 (1, [8])
    | 6  => .finish 41 (1, [9])
    | 7  => .finish 67 (1, [2])
    | 8  => .callSubBox 42 0
        [.finish 60 (1, [14]), .callSubBox 43 0 [.finish 14 (1, [12]), .finish 14 (1, [6])]]
    | 9  => .callSubBox 42 0
        [.finish 98 (0, [8]), .callSubBox 81 0 [.finish 14 (0, [7]), .finish 14 (0, [1])]]
    | 10 => .callSubBox 112 0
        [.finish 62 (0, [14]), .callSubBox 43 0 [.finish 16 (0, [12]), .finish 16 (0, [6])]]
    | 11 => .finish 37 (1, [10])
    | 12 => .finish 41 (1, [13])
    | 13 => .callSubBox 110 0 [.finish 24 (0, [11]), .finish 24 (0, [3])]
    | 14 => .finish 41 (1, [15])
    | _  => .callSubBox 32 0
        [.finish 108 (0, [15]), .callSubBox 43 0 [.finish 62 (0, [13]), .finish 62 (0, [9])]]
  hubState := fun _ => 1
  hubLeft  := fun _ => [1]
  hubRight := fun _ => [0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1]
  hubProg  := fun _ =>
    .callSubBox 91 0
      [ .callSubBox 193 0 [.finish 42 (0, [11]), .finish 42 (0, [3])]
      , .callSubBox 69 0
          [ .finish 172 (0, [8])
          , .callSubBox 137 0 [.finish 32 (0, [7]), .finish 32 (0, [1])] ] ]
  initHub := 0
  initBlocks := [15]
  entrySteps := 843


private theorem is_does_not_halt : IsNotHalt target_tm :=
  collarBoxCert_sound (cert := cert403) (by decide +kernel)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH
