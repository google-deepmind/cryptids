/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1LC0RA_0RA0LD_1LEHHH_1RF0LF_0LC0RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => none
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
-- ============================================================================
-- Section 2: Turing Machine Infrastructure & Notations
-- ============================================================================


/- A Turing machine statement writing a symbol and moving in direction `dir`. -/
-- ============================================================================
-- Section 5: Specific Turing Machine: holdout_0504
-- ============================================================================
/- Transition function for holdout_0504: `1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA` -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

lemma multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma stepStar_refl {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} (c : Cfg Γ Λ) : c [tm]⊢* c := ⟨0, rfl⟩

lemma stepStar_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (stepPlus_stepStar h₂)

lemma step_stepStar_stepPlus {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

/-- Universal non-halting principle from a state invariant with `⊢⁺` progress. -/
theorem nonhalt_of_inv {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (P : Cfg Γ Λ → Prop)
    (h0 : ∃ c₀, P c₀ ∧ (init []) [M]⊢* c₀)
    (hstep : ∀ c, P c → ∃ c', P c' ∧ (c [M]⊢⁺ c')) :
    IsDoesNotHalt M := by
  have hreach : ∀ k, ∃ c, P c ∧ ∃ m ≥ k, multiStep M (init []) m = some c := by
    intro k
    induction k with
    | zero =>
      obtain ⟨c₀, hc₀, m, hm⟩ := h0
      exact ⟨c₀, hc₀, m, Nat.zero_le m, hm⟩
    | succ k ih =>
      obtain ⟨c, hc, m, hge, hm⟩ := ih
      obtain ⟨c', hc', d, hd_pos, hd⟩ := hstep c hc
      exact ⟨c', hc', m + d, by omega, multiStep_trans M (init []) c c' m d hm hd⟩
  intro cfg ⟨n, hn⟩
  rw [Option.isSome_iff_ne_none]
  intro hnone
  obtain ⟨c, _, m, hge, hm⟩ := hreach (n + 1)
  have hm_eq : m = n + (1 + (m - n - 1)) := by omega
  rw [hm_eq, multiStep_add M (init []) n (1 + (m - n - 1)), hn] at hm
  simp only [Option.bind] at hm
  rw [multiStep_add M cfg 1 (m - n - 1), multiStep_one, hnone] at hm
  simp only [Option.bind] at hm
  cases hm

-- ============================================================================
-- Section 6: Mode Configurations & 16 Micro-Step Transition Lemmas for TM31
-- ============================================================================

def cfg_h01B (w s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  w <{{E}} ((1 : Fin 2) >> (0 : Fin 2) >> s)

def cfg_modeB (w s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (0 : Fin 2) >> w) {{B}}> s

def cfg_modeF (w s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> (0 : Fin 2) >> w) {{F}}> s

lemma step_init_to_h01B :
    (init []) [target_tm]⊢⁺ cfg_h01B default ((1 : Fin 2) >> default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold cfg_h01B A E
  execute

-- h01B rules (8)
lemma step_h01B_nil (s : ListBlank (Fin 2)) :
    (cfg_h01B default s) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default) s := by
  unfold cfg_h01B cfg_modeB E B; simp only [zero_cons_default]; execute

lemma step_h01B_010 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_h01B cfg_modeB E B; execute

lemma step_h01B_0010 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_h01B cfg_modeB E B; execute

lemma step_h01B_0110 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_h01B cfg_modeB E B; execute

lemma step_h01B_110 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_h01B cfg_modeB E B; execute

lemma step_h01B_1110 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_h01B cfg_modeB E B; execute

lemma step_h01B_100 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_h01B w ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s) := by
  unfold cfg_h01B E; execute

lemma step_h01B_1010 (w s : ListBlank (Fin 2)) :
    (cfg_h01B ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s) [target_tm]⊢⁺
      cfg_h01B w ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s) := by
  unfold cfg_h01B E; execute

-- modeB rules (4)
lemma step_modeB_base (w : ListBlank (Fin 2)) :
    (cfg_modeB w ((1 : Fin 2) >> default)) [target_tm]⊢⁺
      cfg_h01B ((1 : Fin 2) >> (0 : Fin 2) >> w) ((1 : Fin 2) >> default) := by
  unfold cfg_modeB cfg_h01B B E; execute

lemma step_modeB_0100 (w s : ListBlank (Fin 2)) :
    (cfg_modeB w ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s)) [target_tm]⊢⁺
      cfg_h01B w ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s) := by
  unfold cfg_modeB cfg_h01B B E; execute

lemma step_modeB_0101 (w s : ListBlank (Fin 2)) :
    (cfg_modeB w ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s)) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_modeB B; execute

lemma step_modeB_011 (w s : ListBlank (Fin 2)) :
    (cfg_modeB w ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s)) [target_tm]⊢⁺
      cfg_modeF ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_modeB cfg_modeF B F; execute

-- modeF rules (3)
lemma step_modeF_0100 (w s : ListBlank (Fin 2)) :
    (cfg_modeF w ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s)) [target_tm]⊢⁺
      cfg_h01B w ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s) := by
  unfold cfg_modeF cfg_h01B F E; execute

lemma step_modeF_0101 (w s : ListBlank (Fin 2)) :
    (cfg_modeF w ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s)) [target_tm]⊢⁺
      cfg_modeB ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_modeF cfg_modeB F B; execute

lemma step_modeF_011 (w s : ListBlank (Fin 2)) :
    (cfg_modeF w ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> s)) [target_tm]⊢⁺
      cfg_modeF ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> w) s := by
  unfold cfg_modeF F; execute

-- ============================================================================
-- Section 7: Symbolic Token Lists (`WTok`, `STok`) & Shift Algebra
-- ============================================================================

inductive WTok
  | W010
  | W0010
  | W0110
  | W100
  | W110
  | W1010
  | W1110
deriving DecidableEq, Repr

inductive STok
  | T0100
  | T0101
  | T011
deriving DecidableEq, Repr

def evalW : List WTok → ListBlank (Fin 2)
  | [] => default
  | .W010 :: L => (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW L
  | .W0010 :: L => (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW L
  | .W0110 :: L => (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW L
  | .W100 :: L => (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> evalW L
  | .W110 :: L => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW L
  | .W1010 :: L => (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW L
  | .W1110 :: L => (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW L

def evalS : List STok → ListBlank (Fin 2)
  | [] => (1 : Fin 2) >> default
  | .T0100 :: S => (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalS S
  | .T0101 :: S => (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalS S
  | .T011 :: S => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalS S

-- Symbolic transitions on `(evalW L)` and `(evalS S)`
lemma sym_h01B_nil (S : List STok) :
    (cfg_h01B (evalW []) (evalS S)) [target_tm]⊢⁺
      cfg_modeB (evalW [.W100]) (evalS S) :=
  step_h01B_nil (evalS S)

lemma sym_h01B_010 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W010 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_modeB (evalW (.W110 :: L)) (evalS S) :=
  step_h01B_010 (evalW L) (evalS S)

lemma sym_h01B_0010 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W0010 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_modeB (evalW (.W1010 :: L)) (evalS S) :=
  step_h01B_0010 (evalW L) (evalS S)

lemma sym_h01B_0110 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W0110 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_modeB (evalW (.W1110 :: L)) (evalS S) :=
  step_h01B_0110 (evalW L) (evalS S)

lemma sym_h01B_110 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W110 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_modeB (evalW (.W100 :: L)) (evalS S) :=
  step_h01B_110 (evalW L) (evalS S)

lemma sym_h01B_1110 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W1110 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_modeB (evalW (.W1010 :: L)) (evalS S) :=
  step_h01B_1110 (evalW L) (evalS S)

lemma sym_h01B_100 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W100 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_h01B (evalW L) (evalS (.T011 :: S)) :=
  step_h01B_100 (evalW L) (evalS S)

lemma sym_h01B_1010 (L : List WTok) (S : List STok) :
    (cfg_h01B (evalW (.W1010 :: L)) (evalS S)) [target_tm]⊢⁺
      cfg_h01B (evalW L) (evalS (.T0100 :: S)) :=
  step_h01B_1010 (evalW L) (evalS S)

lemma sym_modeB_0100 (L : List WTok) (S : List STok) :
    (cfg_modeB (evalW L) (evalS (.T0100 :: S))) [target_tm]⊢⁺
      cfg_h01B (evalW L) (evalS (.T0101 :: S)) :=
  step_modeB_0100 (evalW L) (evalS S)

lemma sym_modeB_0101 (L : List WTok) (S : List STok) :
    (cfg_modeB (evalW L) (evalS (.T0101 :: S))) [target_tm]⊢⁺
      cfg_modeB (evalW (.W1010 :: L)) (evalS S) :=
  step_modeB_0101 (evalW L) (evalS S)

lemma sym_modeB_011 (L : List WTok) (S : List STok) :
    (cfg_modeB (evalW L) (evalS (.T011 :: S))) [target_tm]⊢⁺
      cfg_modeF (evalW (.W010 :: L)) (evalS S) :=
  step_modeB_011 (evalW L) (evalS S)

lemma sym_modeF_0100 (L : List WTok) (S : List STok) :
    (cfg_modeF (evalW L) (evalS (.T0100 :: S))) [target_tm]⊢⁺
      cfg_h01B (evalW L) (evalS (.T0100 :: S)) :=
  step_modeF_0100 (evalW L) (evalS S)

lemma sym_modeF_0101 (L : List WTok) (S : List STok) :
    (cfg_modeF (evalW L) (evalS (.T0101 :: S))) [target_tm]⊢⁺
      cfg_modeB (evalW (.W1010 :: L)) (evalS S) :=
  step_modeF_0101 (evalW L) (evalS S)

lemma sym_modeF_011 (L : List WTok) (S : List STok) :
    (cfg_modeF (evalW L) (evalS (.T011 :: S))) [target_tm]⊢⁺
      cfg_modeF (evalW (.W010 :: L)) (evalS S) :=
  step_modeF_011 (evalW L) (evalS S)

-- ============================================================================
-- Section 8: Shift Algebra, Demand/Potential Bounds & Non-Halting Theorem
-- ============================================================================

def shift : Bool → List WTok → List WTok
  | true,  [] => [.W100]
  | true,  .W0010 :: m => .W100 :: .W010 :: m
  | true,  .W0110 :: m => .W100 :: .W110 :: m
  | true,  .W010 :: m => .W100 :: shift true m
  | true,  .W1010 :: m => .W1010 :: shift true m
  | true,  .W100 :: m => .W1010 :: shift false m
  | true,  .W110 :: m => .W110 :: m
  | true,  .W1110 :: m => .W1110 :: m
  | false, [] => []
  | false, .W010 :: m => .W0010 :: m
  | false, .W110 :: m => .W0110 :: m
  | false, .W100 :: m => .W010 :: shift false m
  | false, .W1010 :: m => .W010 :: shift true m
  | false, .W0010 :: m => .W0010 :: m
  | false, .W0110 :: m => .W0110 :: m
  | false, .W1110 :: m => .W1110 :: m

def isHigh : List WTok → Bool
  | .W1010 :: _ | .W0010 :: _ | .W1110 :: _ | .W0110 :: _ => true
  | _ => false

def dem : Bool → List WTok → Nat
  | false, [] => 0
  | true,  [] => 3
  | _, .W1010 :: m => (dem true m + 1) / 2
  | _, .W0010 :: m | _, .W1110 :: m => (dem true m + 1) / 2 + 1
  | _, .W0110 :: m => (dem true m + 1) / 2 + 2
  | true, .W100 :: m => 2 * dem false m
  | true, .W010 :: m => 2 * dem false m + 1
  | true, .W110 :: m => max 3 (2 * dem false m + 2)
  | false, .W010 :: m => 3 * dem false m
  | false, .W110 :: m => 3 * dem false m - 1
  | false, .W100 :: m => 3 * dem false m - 2

def potF : Bool → List WTok → Nat
  | false, [] => 2
  | true,  [] => 4
  | _, .W1010 :: m | _, .W0010 :: m | _, .W1110 :: m | _, .W0110 :: m =>
    (potF true m + 4) / 2
  | true, .W010 :: m => 2 * potF false m + 1
  | true, .W100 :: m => 2 * potF false m + 2
  | true, .W110 :: m => 2 * potF false m + 3
  | false, .W010 :: m => max 3 (3 * potF false m - 5)
  | false, .W110 :: m => max 3 (3 * potF false m - 4)
  | false, .W100 :: m => 3 * potF false m - 3

theorem evalW_shift : ∀ (b : Bool) (u : List WTok),
    dem b u = 0 →
    evalW (shift b u) =
      (if b then (1 : Fin 2) >> (0 : Fin 2) >> evalW u else (0 : Fin 2) >> evalW u)
  | true,  [], h => nomatch h
  | false, [], _ => by simp only [shift, evalW, zero_cons_default]; rfl
  | true,  .W0010 :: m, _ => rfl
  | true,  .W0110 :: m, _ => rfl
  | true,  .W010 :: m, h => by simp only [dem] at h; omega
  | true,  .W110 :: m, h => by simp only [dem] at h; omega
  | true,  .W1110 :: m, h => by simp only [dem] at h; omega
  | true,  .W1010 :: m, h => by
    have hm : dem true m = 0 := by simp only [dem] at h; omega
    change (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW (shift true m) = _
    rw [evalW_shift true m hm]; rfl
  | true,  .W100 :: m, h => by
    have hm : dem false m = 0 := by simp only [dem] at h; omega
    change (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW (shift false m) = _
    rw [evalW_shift false m hm]; rfl
  | false, .W010 :: m, _ => rfl
  | false, .W110 :: m, _ => rfl
  | false, .W0010 :: m, h => by simp only [dem] at h; omega
  | false, .W0110 :: m, h => by simp only [dem] at h; omega
  | false, .W1110 :: m, h => by simp only [dem] at h; omega
  | false, .W1010 :: m, h => by
    have hm : dem true m = 0 := by simp only [dem] at h; omega
    change (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW (shift true m) = _
    rw [evalW_shift true m hm]; rfl
  | false, .W100 :: m, h => by
    have hm : dem false m = 0 := by simp only [dem] at h; omega
    change (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalW (shift false m) = _
    rw [evalW_shift false m hm]; rfl

theorem potF_ge : ∀ (u : List WTok), potF false u ≥ 2 ∧ potF true u ≥ 4
  | [] => ⟨by decide, by decide⟩
  | t :: m => by
    have ⟨ihF, ihT⟩ := potF_ge m
    cases t <;> simp only [potF] <;> exact ⟨by omega, by omega⟩

theorem potF_true_le : ∀ (u : List WTok), potF true u ≤ 2 * potF false u + 3
  | [] => by decide
  | t :: m => by
    have ⟨hpF, hpT⟩ := potF_ge m
    cases t <;> simp only [potF] <;> omega

theorem dem_true_of_dem_false_zero : ∀ {u : List WTok}, dem false u = 0 → dem true u ≤ 3
  | [], _ => by decide
  | t :: m, h => by
    cases t <;> simp only [dem] at h ⊢ <;> omega

theorem isHigh_shift_true : ∀ {u : List WTok}, dem true u = 0 → isHigh (shift true u) = true
  | [], h => nomatch h
  | t :: m, h => by
    cases t <;> simp only [dem, shift, isHigh] at h ⊢ <;> omega

theorem shift_false_true_le {m : List WTok} (hm : dem false m = 0)
    (ihF2 : potF false (shift false m) ≤ 3 * potF false m - 4) :
    3 * dem true (shift false m) ≤ 2 * dem false (shift false m) + 9 ∧
    potF true (shift false m) ≤ 2 * potF false m + 2 := by
  cases m with
  | nil => decide
  | cons t n =>
    have ⟨hpF, hpT⟩ := potF_ge n
    have hptle := potF_true_le n
    cases t with
    | W010 | W110 =>
      have hn : dem false n = 0 := by simp only [dem] at hm; omega
      have hdt := dem_true_of_dem_false_zero hn
      simp only [shift, dem, potF]
      exact ⟨by omega, by omega⟩
    | W0010 | W0110 | W1110 =>
      simp only [dem] at hm; omega
    | W100 =>
      simp only [shift] at ihF2 ⊢
      generalize shift false n = s at ihF2 ⊢
      simp only [dem, potF] at ihF2 ⊢
      exact ⟨by omega, by omega⟩
    | W1010 =>
      simp only [shift] at ihF2 ⊢
      generalize shift true n = s at ihF2 ⊢
      simp only [dem, potF] at ihF2 ⊢
      exact ⟨by omega, by omega⟩

theorem shift_true_false_eq {m : List WTok} (h : dem true m = 0) :
    dem false (shift true m) = dem true (shift true m) ∧
    potF false (shift true m) = potF true (shift true m) := by
  cases m with
  | nil => nomatch h
  | cons t n =>
    cases t with
    | W010 | W110 | W0010 | W0110 | W1110 =>
      simp only [dem] at h; omega
    | W100 | W1010 =>
      exact ⟨rfl, rfl⟩

theorem shift_bounds : ∀ (u : List WTok),
    (dem false u = 0 →
      2 * dem false (shift false u) ≤ 6 * potF false u - 9 ∧
      potF false (shift false u) ≤ 3 * potF false u - 4) ∧
    (dem true u = 0 →
      2 * dem true (shift true u) ≤ potF true u - 2 ∧
      potF true (shift true u) ≤ (potF true u + 4) / 2)
  | [] => ⟨fun _ => by decide, fun h => nomatch h⟩
  | t :: m => by
    have ⟨ihF, ihT⟩ := shift_bounds m
    have ⟨hpF, hpT⟩ := potF_ge m
    have hptle := potF_true_le m
    cases t with
    | W010 =>
      refine ⟨fun h => ?_, fun h => by simp only [dem] at h; omega⟩
      have hm : dem false m = 0 := by simp only [dem] at h; omega
      have hdt := dem_true_of_dem_false_zero hm
      simp only [shift, dem, potF]
      exact ⟨by omega, by omega⟩
    | W110 =>
      refine ⟨fun h => ?_, fun h => by simp only [dem] at h; omega⟩
      have hm : dem false m = 0 := by simp only [dem] at h; omega
      have hdt := dem_true_of_dem_false_zero hm
      simp only [shift, dem, potF]
      exact ⟨by omega, by omega⟩
    | W0010 =>
      exact ⟨fun h => by simp only [dem] at h; omega, fun h => by simp only [dem] at h; omega⟩
    | W0110 =>
      exact ⟨fun h => by simp only [dem] at h; omega, fun h => by simp only [dem] at h; omega⟩
    | W1110 =>
      exact ⟨fun h => by simp only [dem] at h; omega, fun h => by simp only [dem] at h; omega⟩
    | W100 =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hm : dem false m = 0 := by simp only [dem] at h; omega
        have ⟨ihF1, ihF2⟩ := ihF hm
        simp only [shift, dem, potF]
        exact ⟨by omega, by omega⟩
      · have hm : dem false m = 0 := by simp only [dem] at h; omega
        have ⟨ihF1, ihF2⟩ := ihF hm
        have ⟨hsf1, hsf2⟩ := shift_false_true_le hm ihF2
        simp only [shift, dem, potF]
        exact ⟨by omega, by omega⟩
    | W1010 =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hm : dem true m = 0 := by simp only [dem] at h; omega
        have ⟨ihT1, ihT2⟩ := ihT hm
        have ⟨hst1, hst2⟩ := shift_true_false_eq hm
        simp only [shift, dem, potF]
        exact ⟨by omega, by omega⟩
      · have hm : dem true m = 0 := by simp only [dem] at h; omega
        have ⟨ihT1, ihT2⟩ := ihT hm
        simp only [shift, dem, potF]
        exact ⟨by omega, by omega⟩

-- ============================================================================
-- Section 9: Fuel-Indexed Multi-Pass Transducer (`TreeW`) with `StepOK`
-- ============================================================================

def ExitAt (S : List STok) (isB : Bool) (L' : List WTok) : Cfg (Fin 2) (Fin 6) :=
  if isB then cfg_modeB (evalW L') (evalS S) else cfg_modeF (evalW (.W010 :: L')) (evalS S)

def StepOK (L : List WTok) (isB : Bool) (next : List WTok) : Prop :=
  match L with
  | [] => isB = true ∧ next = [.W100]
  | .W010 :: R => isB = true ∧ next = .W110 :: R
  | .W110 :: R => isB = true ∧ next = .W100 :: R
  | .W100 :: R =>
    isB = false ∧
    dem false next ≤ dem false R - 1 ∧
    potF false next ≤ potF false R + 1
  | _ =>
    isB = true ∧
    isHigh next = true ∧
    dem false next ≤ dem false L - 1 ∧
    potF false next ≤ potF false L + 1

theorem stepOK_of_isHigh {w next : List WTok} {isB : Bool}
    (hw : isHigh w = true) (hok : StepOK w isB next) :
    isB = true ∧ isHigh next = true ∧
    dem false next ≤ dem false w - 1 ∧
    potF false next ≤ potF false w + 1 := by
  cases w with
  | nil => nomatch hw
  | cons t R =>
    cases t with
    | W010 | W110 | W100 => nomatch hw
    | W0010 | W0110 | W1010 | W1110 => exact hok

theorem dem_potF_of_isHigh {w : List WTok} (hw : isHigh w = true) :
    dem true w = dem false w ∧ potF true w = potF false w := by
  cases w with
  | nil => nomatch hw
  | cons t R =>
    cases t with
    | W010 | W110 | W100 => nomatch hw
    | W0010 | W0110 | W1010 | W1110 => exact ⟨rfl, rfl⟩

theorem stepOK_W100_true {M next : List WTok} (hok : StepOK M true next) :
    StepOK (.W100 :: M) false next := by
  cases M with
  | nil =>
    rcases hok with ⟨_, rfl⟩
    exact ⟨rfl, by decide, by decide⟩
  | cons t R =>
    cases t with
    | W010 =>
      rcases hok with ⟨_, rfl⟩
      dsimp only [StepOK, dem, potF]
      exact ⟨rfl, by omega, by omega⟩
    | W110 =>
      rcases hok with ⟨_, rfl⟩
      dsimp only [StepOK, dem, potF]
      exact ⟨rfl, by omega, by omega⟩
    | W100 => nomatch hok.1
    | W0010 | W0110 | W1010 | W1110 =>
      rcases hok with ⟨_, _, hd1, hp⟩
      exact ⟨rfl, hd1, hp⟩

theorem stepOK_W100_false {M K : List WTok} (hok : StepOK M false K) :
    StepOK (.W100 :: M) false (.W010 :: K) := by
  cases M with
  | nil => nomatch hok.1
  | cons t R =>
    cases t with
    | W010 | W110 | W0010 | W0110 | W1010 | W1110 => nomatch hok.1
    | W100 =>
      rcases hok with ⟨_, hd1, hp⟩
      have ⟨hpR, _⟩ := potF_ge R
      dsimp only [StepOK, dem, potF]
      exact ⟨rfl, by omega, by omega⟩

theorem stepOK_W1010_TT {M M₁ M₂ : List WTok}
    (hok₁ : StepOK M true M₁) (hok₂ : StepOK M₁ true M₂) :
    StepOK (.W1010 :: M) true (.W1010 :: M₂) := by
  cases M with
  | nil =>
    rcases hok₁ with ⟨_, rfl⟩
    nomatch hok₂.1
  | cons t R =>
    cases t with
    | W100 => nomatch hok₁.1
    | W110 =>
      rcases hok₁ with ⟨_, rfl⟩
      nomatch hok₂.1
    | W010 =>
      rcases hok₁ with ⟨_, rfl⟩
      rcases hok₂ with ⟨_, rfl⟩
      dsimp only [StepOK, isHigh, dem, potF]
      exact ⟨rfl, rfl, by omega, by omega⟩
    | W0010 | W0110 | W1010 | W1110 =>
      rcases hok₁ with ⟨_, hm1, hd1, hp1⟩
      rcases stepOK_of_isHigh hm1 hok₂ with ⟨_, hm2, hd2, hp2⟩
      have ⟨hdt2, hpt2⟩ := dem_potF_of_isHigh hm2
      dsimp only [StepOK, isHigh, dem, potF] at hd1 hp1 ⊢
      exact ⟨rfl, rfl, by omega, by omega⟩

theorem stepOK_W1010_TF {M M₁ M₂ : List WTok}
    (hok₁ : StepOK M true M₁) (hok₂ : StepOK M₁ false M₂) :
    StepOK (.W1010 :: M) true (.W1010 :: .W010 :: M₂) := by
  cases M with
  | nil =>
    rcases hok₁ with ⟨_, rfl⟩
    rcases hok₂ with ⟨_, hd2, hp2⟩
    dsimp only [StepOK, isHigh, dem, potF] at hd2 hp2 ⊢
    exact ⟨rfl, rfl, by omega, by omega⟩
  | cons t R =>
    cases t with
    | W100 => nomatch hok₁.1
    | W010 =>
      rcases hok₁ with ⟨_, rfl⟩
      nomatch hok₂.1
    | W110 =>
      rcases hok₁ with ⟨_, rfl⟩
      rcases hok₂ with ⟨_, hd2, hp2⟩
      dsimp only [StepOK, isHigh, dem, potF] at hd2 hp2 ⊢
      exact ⟨rfl, rfl, by omega, by omega⟩
    | W0010 | W0110 | W1010 | W1110 =>
      rcases hok₁ with ⟨_, hm1, _, _⟩
      nomatch (stepOK_of_isHigh hm1 hok₂).1

theorem stepOK_W1010_F {M M₁ : List WTok}
    (hok₁ : StepOK M false M₁) :
    StepOK (.W1010 :: M) true (.W1010 :: .W100 :: M₁) := by
  cases M with
  | nil => nomatch hok₁.1
  | cons t R =>
    cases t with
    | W010 | W110 | W0010 | W0110 | W1010 | W1110 => nomatch hok₁.1
    | W100 =>
      rcases hok₁ with ⟨_, hd1, hp1⟩
      dsimp only [StepOK, isHigh, dem, potF] at hd1 hp1 ⊢
      exact ⟨rfl, rfl, by omega, by omega⟩

-- Symbolic pass combinators
lemma pass_W100_B {M M' : List WTok}
    (h : ∀ S : List STok, (cfg_h01B (evalW M) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW M') (evalS S))
    (S : List STok) :
    (cfg_h01B (evalW (.W100 :: M)) (evalS S)) [target_tm]⊢⁺ cfg_modeF (evalW (.W010 :: M')) (evalS S) :=
  stepPlus_trans (sym_h01B_100 M S) (stepPlus_trans (h (.T011 :: S)) (sym_modeB_011 M' S))

lemma pass_W100_F {M M' : List WTok}
    (h : ∀ S : List STok, (cfg_h01B (evalW M) (evalS S)) [target_tm]⊢⁺ cfg_modeF (evalW M') (evalS S))
    (S : List STok) :
    (cfg_h01B (evalW (.W100 :: M)) (evalS S)) [target_tm]⊢⁺ cfg_modeF (evalW (.W010 :: M')) (evalS S) :=
  stepPlus_trans (sym_h01B_100 M S) (stepPlus_trans (h (.T011 :: S)) (sym_modeF_011 M' S))

lemma pass_W1010_BB {M M₁ M₂ : List WTok}
    (h₁ : ∀ S : List STok, (cfg_h01B (evalW M) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW M₁) (evalS S))
    (h₂ : ∀ S : List STok, (cfg_h01B (evalW M₁) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW M₂) (evalS S))
    (S : List STok) :
    (cfg_h01B (evalW (.W1010 :: M)) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW (.W1010 :: M₂)) (evalS S) :=
  stepPlus_trans (sym_h01B_1010 M S)
    (stepPlus_trans (h₁ (.T0100 :: S))
      (stepPlus_trans (sym_modeB_0100 M₁ S)
        (stepPlus_trans (h₂ (.T0101 :: S))
          (sym_modeB_0101 M₂ S))))

lemma pass_W1010_BF {M M₁ M₂ : List WTok}
    (h₁ : ∀ S : List STok, (cfg_h01B (evalW M) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW M₁) (evalS S))
    (h₂ : ∀ S : List STok, (cfg_h01B (evalW M₁) (evalS S)) [target_tm]⊢⁺ cfg_modeF (evalW M₂) (evalS S))
    (S : List STok) :
    (cfg_h01B (evalW (.W1010 :: M)) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW (.W1010 :: M₂)) (evalS S) :=
  stepPlus_trans (sym_h01B_1010 M S)
    (stepPlus_trans (h₁ (.T0100 :: S))
      (stepPlus_trans (sym_modeB_0100 M₁ S)
        (stepPlus_trans (h₂ (.T0101 :: S))
          (sym_modeF_0101 M₂ S))))

lemma pass_W1010_F {M M₁ : List WTok}
    (h₁ : ∀ S : List STok, (cfg_h01B (evalW M) (evalS S)) [target_tm]⊢⁺ cfg_modeF (evalW (.W010 :: M₁)) (evalS S))
    (S : List STok) :
    (cfg_h01B (evalW (.W1010 :: M)) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW (.W1010 :: .W100 :: M₁)) (evalS S) :=
  stepPlus_trans (sym_h01B_1010 M S)
    (stepPlus_trans (h₁ (.T0100 :: S))
      (stepPlus_trans (sym_modeF_0100 (.W010 :: M₁) S)
        (stepPlus_trans (sym_h01B_010 M₁ (.T0100 :: S))
          (stepPlus_trans (sym_modeB_0100 (.W110 :: M₁) S)
            (stepPlus_trans (sym_h01B_110 M₁ (.T0101 :: S))
              (sym_modeB_0101 (.W100 :: M₁) S))))))

def TreeW : Nat → List WTok → Prop
  | 0, _ => True
  | n + 1, L =>
    ∃ (isB : Bool) (next : List WTok),
      StepOK L isB next ∧
      (∀ S : List STok, (cfg_h01B (evalW L) (evalS S)) [target_tm]⊢⁺ ExitAt S isB next) ∧
      TreeW n next

theorem treeW_succ : ∀ {n : Nat} {L : List WTok}, TreeW (n + 1) L → TreeW n L
  | 0, _, _ => trivial
  | _ + 1, _, ⟨isB, next, hok, hstep, sub⟩ => ⟨isB, next, hok, hstep, treeW_succ sub⟩

theorem treeW_triple : ∀ (n : Nat),
    (∀ {M : List WTok}, TreeW n M → TreeW n (.W100 :: M)) ∧
    (∀ {M : List WTok}, TreeW n M → TreeW n (.W110 :: M)) ∧
    (∀ {M : List WTok}, TreeW n M → TreeW n (.W010 :: M))
  | 0 => ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩
  | n + 1 =>
    let ⟨ih100, ih110, ih010⟩ := treeW_triple n
    ⟨fun {M} h => match h with
      | ⟨true, next, hok, hstep, sub⟩ =>
        ⟨false, next, stepOK_W100_true hok, pass_W100_B hstep, sub⟩
      | ⟨false, K, hok, hstep, sub⟩ =>
        ⟨false, .W010 :: K, stepOK_W100_false hok, pass_W100_F hstep, ih010 sub⟩,
     fun {M} t => ⟨true, .W100 :: M, ⟨rfl, rfl⟩, sym_h01B_110 M, ih100 (treeW_succ t)⟩,
     fun {M} t => ⟨true, .W110 :: M, ⟨rfl, rfl⟩, sym_h01B_010 M, ih110 (treeW_succ t)⟩⟩

theorem treeW_W100 {n : Nat} {M : List WTok} (h : TreeW n M) : TreeW n (.W100 :: M) :=
  (treeW_triple n).1 h

theorem treeW_W110 {n : Nat} {M : List WTok} (h : TreeW n M) : TreeW n (.W110 :: M) :=
  (treeW_triple n).2.1 h

theorem treeW_W010 {n : Nat} {M : List WTok} (h : TreeW n M) : TreeW n (.W010 :: M) :=
  (treeW_triple n).2.2 h

theorem treeW_nil : ∀ (n : Nat), TreeW n []
  | 0 => trivial
  | n + 1 => ⟨true, [.W100], ⟨rfl, rfl⟩, sym_h01B_nil, treeW_W100 (treeW_nil n)⟩

theorem treeW_W1010_step {n : Nat} {M : List WTok} (t : TreeW (n + 2) M) :
    ∃ (next : List WTok),
      StepOK (.W1010 :: M) true (.W1010 :: next) ∧
      (∀ S : List STok, (cfg_h01B (evalW (.W1010 :: M)) (evalS S)) [target_tm]⊢⁺ cfg_modeB (evalW (.W1010 :: next)) (evalS S)) ∧
      TreeW n next := by
  obtain ⟨isB₁, M₁, hok₁, hstep₁, sub₁⟩ := t
  cases isB₁ with
  | true =>
    obtain ⟨isB₂, M₂, hok₂, hstep₂, sub₂⟩ := sub₁
    cases isB₂ with
    | true =>
      exact ⟨M₂, stepOK_W1010_TT hok₁ hok₂, pass_W1010_BB hstep₁ hstep₂, sub₂⟩
    | false =>
      exact ⟨.W010 :: M₂, stepOK_W1010_TF hok₁ hok₂, pass_W1010_BF hstep₁ hstep₂, treeW_W010 sub₂⟩
  | false =>
    exact ⟨.W100 :: M₁, stepOK_W1010_F hok₁, pass_W1010_F hstep₁, treeW_W100 (treeW_succ sub₁)⟩

theorem treeW_W1010 : ∀ (n : Nat) {M : List WTok}, TreeW (2 * n) M → TreeW n (.W1010 :: M)
  | 0, _, _ => trivial
  | n + 1, M, t => by
    have heq : 2 * (n + 1) = 2 * n + 2 := rfl
    rw [heq] at t
    obtain ⟨next, hok, hstep, sub⟩ := treeW_W1010_step t
    exact ⟨true, .W1010 :: next, hok, hstep, treeW_W1010 n sub⟩

theorem treeW_W0010 : ∀ {n : Nat} {M : List WTok}, TreeW (2 * n) M → TreeW n (.W0010 :: M)
  | 0, _, _ => trivial
  | n + 1, M, t => by
    have heq : 2 * (n + 1) = 2 * n + 2 := rfl
    rw [heq] at t
    exact ⟨true, .W1010 :: M,
      ⟨rfl, rfl, by simp only [dem]; omega, by simp only [potF]; omega⟩,
      sym_h01B_0010 M, treeW_W1010 n (treeW_succ (treeW_succ t))⟩

theorem treeW_W1110 : ∀ {n : Nat} {M : List WTok}, TreeW (2 * n) M → TreeW n (.W1110 :: M)
  | 0, _, _ => trivial
  | n + 1, M, t => by
    have heq : 2 * (n + 1) = 2 * n + 2 := rfl
    rw [heq] at t
    exact ⟨true, .W1010 :: M,
      ⟨rfl, rfl, by simp only [dem]; omega, by simp only [potF]; omega⟩,
      sym_h01B_1110 M, treeW_W1010 n (treeW_succ (treeW_succ t))⟩

theorem treeW_W0110 : ∀ {n : Nat} {M : List WTok}, TreeW (2 * n) M → TreeW n (.W0110 :: M)
  | 0, _, _ => trivial
  | n + 1, M, t => by
    have heq : 2 * (n + 1) = 2 * n + 2 := rfl
    rw [heq] at t
    exact ⟨true, .W1110 :: M,
      ⟨rfl, rfl, by simp only [dem]; omega, by simp only [potF]; omega⟩,
      sym_h01B_0110 M, treeW_W1110 (treeW_succ (treeW_succ t))⟩

theorem buildTreeW : ∀ (L : List WTok) (n : Nat), TreeW n L
  | [], n => treeW_nil n
  | .W010 :: M, n => treeW_W010 (buildTreeW M n)
  | .W0010 :: M, n => treeW_W0010 (buildTreeW M (2 * n))
  | .W0110 :: M, n => treeW_W0110 (buildTreeW M (2 * n))
  | .W100 :: M, n => treeW_W100 (buildTreeW M n)
  | .W110 :: M, n => treeW_W110 (buildTreeW M n)
  | .W1010 :: M, n => treeW_W1010 n (buildTreeW M (2 * n))
  | .W1110 :: M, n => treeW_W1110 (buildTreeW M (2 * n))

-- ============================================================================
-- Section 10: Initial Reachability (`step_init_to_w4`) & `holdout_0504_nonhalt`
-- ============================================================================

lemma step_modeB_reparse {u w : List WTok}
    (heq : (1 : Fin 2) >> (0 : Fin 2) >> evalW u = evalW w) :
    (cfg_modeB (evalW u) (evalS [])) [target_tm]⊢⁺
      cfg_h01B (evalW w) (evalS []) := by
  rw [← heq]
  exact step_modeB_base (evalW u)

lemma step_init_to_w4 :
    (init []) [target_tm]⊢⁺
      cfg_h01B (evalW [.W1010, .W1010, .W1010, .W0010, .W1010, .W010, .W100]) (evalS []) := by
  have h_w1 := pass_W1010_BF sym_h01B_nil (pass_W100_B sym_h01B_nil)
  have h_w2 := pass_W1010_F (pass_W100_B h_w1)
  have h_w3_a := pass_W1010_BB (sym_h01B_010 [.W100, .W1010]) (sym_h01B_110 [.W100, .W1010])
  have h_w3_b := pass_W1010_F (pass_W100_F (pass_W100_B h_w1))
  have h_w3 := pass_W1010_BB h_w3_a h_w3_b
  have hp0 : (init []) [target_tm]⊢⁺ cfg_h01B (evalW [.W1010]) (evalS []) :=
    stepPlus_trans step_init_to_h01B
      (stepPlus_trans (sym_h01B_nil [])
        (step_modeB_reparse (by simp only [evalW, zero_cons_default])))
  have hp1 : (cfg_h01B (evalW [.W1010]) (evalS [])) [target_tm]⊢⁺
      cfg_h01B (evalW [.W1010, .W100, .W1010]) (evalS []) :=
    stepPlus_trans (h_w1 []) (step_modeB_reparse (by simp only [evalW, zero_cons_default]))
  have hp2 : (cfg_h01B (evalW [.W1010, .W100, .W1010]) (evalS [])) [target_tm]⊢⁺
      cfg_h01B (evalW [.W1010, .W1010, .W010, .W100, .W1010]) (evalS []) :=
    stepPlus_trans (h_w2 []) (step_modeB_reparse (by simp only [evalW, zero_cons_default]))
  have hp3 : (cfg_h01B (evalW [.W1010, .W1010, .W010, .W100, .W1010]) (evalS [])) [target_tm]⊢⁺
      cfg_h01B (evalW [.W1010, .W1010, .W1010, .W0010, .W1010, .W010, .W100]) (evalS []) :=
    stepPlus_trans (h_w3 []) (step_modeB_reparse (by simp only [evalW, zero_cons_default]))
  exact stepPlus_trans hp0 (stepPlus_trans hp1 (stepPlus_trans hp2 hp3))

def Inv0504 (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ w : List WTok,
    isHigh w = true ∧
    dem false w ≤ 1 ∧
    potF false w ≤ 4 ∧
    c = cfg_h01B (evalW w) (evalS [])

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  refine nonhalt_of_inv target_tm Inv0504 ?_ ?_
  · refine ⟨_, ⟨[.W1010, .W1010, .W1010, .W0010, .W1010, .W010, .W100], rfl, by decide, by decide, rfl⟩, ?_⟩
    exact stepPlus_stepStar step_init_to_w4
  · rintro _ ⟨w, hw, hd, hp, rfl⟩
    obtain ⟨isB, u, hok, hstep, _⟩ := buildTreeW w 1
    obtain ⟨rfl, hu_high, hu_dem1, hu_pot⟩ := stepOK_of_isHigh hw hok
    have ⟨hdu_eq, hpu_eq⟩ := dem_potF_of_isHigh hu_high
    have hdu : dem true u = 0 := by omega
    have hpu : potF true u ≤ 5 := by omega
    have hw'_high : isHigh (shift true u) = true := isHigh_shift_true hdu
    have ⟨hdw'_eq, hpw'_eq⟩ := dem_potF_of_isHigh hw'_high
    have ⟨hb_dem, hb_pot⟩ := (shift_bounds u).2 hdu
    refine ⟨cfg_h01B (evalW (shift true u)) (evalS []),
      ⟨shift true u, hw'_high, by omega, by omega, rfl⟩, ?_⟩
    exact stepPlus_trans (hstep []) (step_modeB_reparse (evalW_shift true u hdu).symm)

end BusyBeaver.M_1RB0RE_1LC0RA_0RA0LD_1LEHHH_1RF0LF_0LC0RA
