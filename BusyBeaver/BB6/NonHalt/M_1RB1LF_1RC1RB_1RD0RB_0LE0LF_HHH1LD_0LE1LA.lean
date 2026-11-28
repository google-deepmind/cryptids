/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat

/-!
# Busy Beaver Machine `1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

abbrev sweep_tm : Machine (Fin 2) (Fin 6) := target_tm

abbrev qRe : Fin 6 := 0
abbrev qSw : Fin 6 := 1
abbrev qEr : Fin 6 := 3
abbrev qPr : Fin 6 := 5

def Sweep (q : Fin 6) (r u : ListBlank (Fin 2)) : Prop :=
  ∀ L : ListBlank (Fin 2), (L {{qSw}}> r) [sweep_tm]⊢⁺ (L <{{q}} u)

def eraCfg (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> default) {{qSw}}> r)

/-! ### 1. Micro-Step Window Lemmas -/

theorem win_B_000 (L r : ListBlank (Fin 2)) :
    (L {{qSw}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) [sweep_tm]⊢⁺
      (L <{{qPr}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_B_001 (L r : ListBlank (Fin 2)) :
    (L {{qSw}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [sweep_tm]⊢⁺
      (L <{{qPr}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_B_1 (L r : ListBlank (Fin 2)) :
    (L {{qSw}}> ((1 : Fin 2) >> r)) [sweep_tm]⊢⁺
      (((1 : Fin 2) >> L) {{qSw}}> r) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_B_01 (L r : ListBlank (Fin 2)) :
    (L {{qSw}}> ((0 : Fin 2) >> (1 : Fin 2) >> r)) [sweep_tm]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> L) {{qSw}}> r) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_1_F (L r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> L) <{{qPr}} r) [sweep_tm]⊢⁺ (L <{{qRe}} ((1 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_1_D (L r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> L) <{{qEr}} r) [sweep_tm]⊢⁺ (L <{{qPr}} ((0 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_1_A (L r : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> L) <{{qRe}} r) [sweep_tm]⊢⁺ (L <{{qPr}} ((1 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_10_F (L r : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> L) <{{qPr}} r) [sweep_tm]⊢⁺
      (L <{{qEr}} ((1 : Fin 2) >> (0 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_10_D (L r : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> L) <{{qEr}} r) [sweep_tm]⊢⁺
      (L <{{qEr}} ((1 : Fin 2) >> (0 : Fin 2) >> r)) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_10_A (L r : ListBlank (Fin 2)) :
    (((0 : Fin 2) >> (1 : Fin 2) >> L) <{{qRe}} r) [sweep_tm]⊢⁺
      (((1 : Fin 2) >> (1 : Fin 2) >> L) {{qSw}}> r) := by
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem win_era_bounce (u : ListBlank (Fin 2)) :
    (((1 : Fin 2) >> (1 : Fin 2) >> default) <{{qEr}} u) [sweep_tm]⊢⁺
      (eraCfg ((0 : Fin 2) >> u)) := by
  unfold eraCfg
  have hz : (((1 : Fin 2) >> (1 : Fin 2) >> default) : ListBlank (Fin 2)) =
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) := by
    simp only [ListBlank.cons_zero_default]
  rw [hz]
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem init_to_era0 :
    (init []) [sweep_tm]⊢* (eraCfg ([(0 : Fin 2), 1] +> default)) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) =
      (default {{0}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default)) := by
    simp only [ListBlank.cons_zero_default]
    rfl
  rw [h0]
  unfold eraCfg
  dsimp [ListBlank.append]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem era_step {r u : ListBlank (Fin 2)} (h : Sweep qEr r u) :
    (eraCfg r) [sweep_tm]⊢⁺ (eraCfg ((0 : Fin 2) >> u)) :=
  ReachesPlus.trans (h _) (win_era_bounce u)

/-! ### 2. Compositional `Sweep` Combinators -/

theorem sweep_000 (r : ListBlank (Fin 2)) :
    Sweep qPr ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r) ((0 : Fin 2) >> (1 : Fin 2) >> (0 :
      Fin 2) >> r) :=
  fun L => win_B_000 L r

theorem sweep_001 (r : ListBlank (Fin 2)) :
    Sweep qPr ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r) ((1 : Fin 2) >> (1 : Fin 2) >> (0 :
      Fin 2) >> r) :=
  fun L => win_B_001 L r

theorem sweep_default :
    Sweep qPr default ((0 : Fin 2) >> (1 : Fin 2) >> default) := by
  intro L
  have h := win_B_000 L default
  simpa only [ListBlank.cons_zero_default] using h

theorem sweep_1_F {r u : ListBlank (Fin 2)} (h : Sweep qPr r u) :
    Sweep qRe ((1 : Fin 2) >> r) ((1 : Fin 2) >> u) :=
  fun L => ReachesPlus.trans (win_B_1 L r) (ReachesPlus.trans (h _) (win_1_F L u))

theorem sweep_1_D {r u : ListBlank (Fin 2)} (h : Sweep qEr r u) :
    Sweep qPr ((1 : Fin 2) >> r) ((0 : Fin 2) >> u) :=
  fun L => ReachesPlus.trans (win_B_1 L r) (ReachesPlus.trans (h _) (win_1_D L u))

theorem sweep_1_A {r u : ListBlank (Fin 2)} (h : Sweep qRe r u) :
    Sweep qPr ((1 : Fin 2) >> r) ((1 : Fin 2) >> u) :=
  fun L => ReachesPlus.trans (win_B_1 L r) (ReachesPlus.trans (h _) (win_1_A L u))

theorem sweep_01_F {r u : ListBlank (Fin 2)} (h : Sweep qPr r u) :
    Sweep qEr ((0 : Fin 2) >> (1 : Fin 2) >> r) ((1 : Fin 2) >> (0 : Fin 2) >> u) :=
  fun L => ReachesPlus.trans (win_B_01 L r) (ReachesPlus.trans (h _) (win_10_F L u))

theorem sweep_01_D {r u : ListBlank (Fin 2)} (h : Sweep qEr r u) :
    Sweep qEr ((0 : Fin 2) >> (1 : Fin 2) >> r) ((1 : Fin 2) >> (0 : Fin 2) >> u) :=
  fun L => ReachesPlus.trans (win_B_01 L r) (ReachesPlus.trans (h _) (win_10_D L u))

theorem sweep_01_A_F {r u v : ListBlank (Fin 2)} (h1 : Sweep qRe r u) (h2 : Sweep qPr u v) :
    Sweep qPr ((0 : Fin 2) >> (1 : Fin 2) >> r) ((1 : Fin 2) >> (1 : Fin 2) >> v) :=
  fun L => ReachesPlus.trans (win_B_01 L r)
    (ReachesPlus.trans (h1 _)
      (ReachesPlus.trans (win_10_A L u)
        (ReachesPlus.trans (h2 _)
          (ReachesPlus.trans (win_1_F _ v) (win_1_A L _)))))

theorem sweep_01_A_D {r u v : ListBlank (Fin 2)} (h1 : Sweep qRe r u) (h2 : Sweep qEr u v) :
    Sweep qRe ((0 : Fin 2) >> (1 : Fin 2) >> r) ((1 : Fin 2) >> (0 : Fin 2) >> v) :=
  fun L => ReachesPlus.trans (win_B_01 L r)
    (ReachesPlus.trans (h1 _)
      (ReachesPlus.trans (win_10_A L u)
        (ReachesPlus.trans (h2 _)
          (ReachesPlus.trans (win_1_D _ v) (win_1_F L _)))))

theorem sweep_01_A_A {r u v : ListBlank (Fin 2)} (h1 : Sweep qRe r u) (h2 : Sweep qRe u v) :
    Sweep qRe ((0 : Fin 2) >> (1 : Fin 2) >> r) ((1 : Fin 2) >> (1 : Fin 2) >> v) :=
  fun L => ReachesPlus.trans (win_B_01 L r)
    (ReachesPlus.trans (h1 _)
      (ReachesPlus.trans (win_10_A L u)
        (ReachesPlus.trans (h2 _)
          (ReachesPlus.trans (win_1_A _ v) (win_1_F L _)))))

theorem sweep_11_pow_F (m : Nat) {r u : ListBlank (Fin 2)} (h : Sweep qPr r u) :
    Sweep qPr ((([1, 1] : List (Fin 2)) ^ m) +> r) ((([1, 1] : List (Fin 2)) ^ m) +> u) := by
  induction m with
  | zero => simpa [list_pow_zero, ListBlank.append_nil] using h
  | succ m ih =>
    simp only [ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]
    exact sweep_1_A (sweep_1_F ih)

theorem sweep_11_pow_A (m : Nat) {r u : ListBlank (Fin 2)} (h : Sweep qRe r u) :
    Sweep qRe ((([1, 1] : List (Fin 2)) ^ m) +> r) ((([1, 1] : List (Fin 2)) ^ m) +> u) := by
  induction m with
  | zero => simpa [list_pow_zero, ListBlank.append_nil] using h
  | succ m ih =>
    simp only [ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]
    exact sweep_1_F (sweep_1_A ih)

/-! ### 3. 8-Constructor `Tree`, `Payload`, `RVal`, and Tape Evaluation -/

inductive Tree where
  | endZero (c : Nat)
  | endStop (c : Nat)
  | endOne (c : Nat)
  | oneEnd (c : Nat)
  | stopOne (c : Nat)
  | stop (c : Nat) (d : Tree)
  | od (c m : Nat) (d : Tree)
  | sh (c m : Nat) (u : Tree)
  deriving DecidableEq

def tree_c : Tree → Nat
  | .endZero c | .endStop c | .endOne c | .oneEnd c | .stopOne c
  | .stop c _ | .od c _ _ | .sh c _ _ => c

def set_c (nc : Nat) : Tree → Tree
  | .endZero _ => .endZero nc
  | .endStop _ => .endStop nc
  | .endOne _ => .endOne nc
  | .oneEnd _ => .oneEnd nc
  | .stopOne _ => .stopOne nc
  | .stop _ d => .stop nc d
  | .od _ m d => .od nc m d
  | .sh _ m u => .sh nc m u

def add_c (dc : Nat) (t : Tree) : Tree := set_c (tree_c t + dc) t
def sub_c (dc : Nat) (t : Tree) : Tree := set_c (tree_c t - dc) t

def mk_stop (c : Nat) (d : Tree) : Tree :=
  if d = .endZero 0 then .endStop c
  else if d = .endOne 1 then .stopOne c
  else .stop c d

def mk_sh (c m : Nat) (u : Tree) : Tree :=
  if m = 0 ∧ u = .endStop 1 then .oneEnd c
  else .sh c m u

def evalCore : Tree → ListBlank (Fin 2)
  | .endZero _ => default
  | .endStop _ => [(0 : Fin 2), 0, 1] +> default
  | .endOne _ => [(1 : Fin 2)] +> default
  | .oneEnd _ => [(1 : Fin 2), 0, 1, 0, 0, 1] +> default
  | .stopOne _ => [(0 : Fin 2), 0, 1, 0, 1, 1] +> default
  | .stop _ d => [(0 : Fin 2), 0, 1] +> (([0, 1] : List (Fin 2)) ^ tree_c d +> evalCore d)
  | .od _ m d => (([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> (([0,
    1] : List (Fin 2)) ^ tree_c d +> evalCore d))
  | .sh _ m u => (([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (([0,
    1] : List (Fin 2)) ^ tree_c u +> evalCore u))

def evalT (t : Tree) : ListBlank (Fin 2) :=
  (([0, 1] : List (Fin 2)) ^ tree_c t) +> evalCore t

def tailT (t : Tree) : ListBlank (Fin 2) :=
  (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (tree_c t - 1)) +> evalCore t)

theorem tree_c_set_c (nc : Nat) (t : Tree) : tree_c (set_c nc t) = nc := by
  cases t <;> rfl

theorem evalCore_set_c (nc : Nat) (t : Tree) : evalCore (set_c nc t) = evalCore t := by
  cases t <;> rfl

theorem evalT_stop (c : Nat) (d : Tree) :
    evalT (.stop c d) = (([0, 1] : List (Fin 2)) ^ c) +> ([(0 : Fin 2), 0, 1] +> evalT d) := rfl

theorem evalT_od (c m : Nat) (d : Tree) :
    evalT (.od c m d) =
      (([0, 1] : List (Fin 2)) ^ c) +> ((([1,
        1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d)) := rfl

theorem evalT_sh (c m : Nat) (u : Tree) :
    evalT (.sh c m u) =
      (([0, 1] : List (Fin 2)) ^ c) +> ((([1,
        1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> evalT u)) := rfl

theorem cons_zero_tailT {t : Tree} (hc : tree_c t ≥ 1) :
    ((0 : Fin 2) >> tailT t) = evalT t := by
  unfold tailT evalT
  obtain ⟨k, hk⟩ : ∃ k, tree_c t = k + 1 := ⟨tree_c t - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, ListBlank.append_pow_succ]
  rfl

theorem evalT_add_c_one {t : Tree} :
    evalT (add_c 1 t) = ((0 : Fin 2) >> (1 : Fin 2) >> evalT t) := by
  unfold add_c evalT
  rw [tree_c_set_c, evalCore_set_c, Nat.add_comm (tree_c t) 1, list_pow_add, list_pow_one,
    ListBlank.append_assoc]
  rfl

theorem tailT_add_c_one {t : Tree} (hc : tree_c t ≥ 1) :
    tailT (add_c 1 t) = ((1 : Fin 2) >> (0 : Fin 2) >> tailT t) := by
  unfold add_c tailT
  rw [tree_c_set_c, evalCore_set_c, show tree_c t + 1 - 1 = tree_c t by omega]
  have hpow : (([0, 1] : List (Fin 2)) ^ tree_c t) +> evalCore t =
      ((0 : Fin 2) >> (1 : Fin 2) >> ((([0,
        1] : List (Fin 2)) ^ (tree_c t - 1)) +> evalCore t)) := by
    conv_lhs => rw [show tree_c t = (tree_c t - 1) + 1 by omega]
    rw [ListBlank.append_pow_succ]
    rfl
  rw [hpow]

theorem evalT_mk_stop (c : Nat) (d : Tree) :
    evalT (mk_stop c d) = (([0, 1] : List (Fin 2)) ^ c) +> ([(0 : Fin 2), 0, 1] +> evalT d) := by
  unfold mk_stop
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rfl
  · rfl

theorem tailT_mk_stop (c : Nat) (hc : c ≥ 1) (d : Tree) :
    tailT (mk_stop c d) =
      (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (c - 1)) +> ([(0 : Fin 2), 0, 1] +> evalT d)) := by
  unfold mk_stop
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rfl
  · rfl

theorem tailT_mk_sh (c m : Nat) (hc : c ≥ 1) (u : Tree) :
    tailT (mk_sh c m u) =
      (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (c - 1)) +>
        ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> evalT u))) := by
  unfold mk_sh
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩
    simp [tailT, evalT, tree_c, evalCore, list_pow_zero, ListBlank.append_nil, list_pow_one]
  · rfl

inductive Payload where
  | P_tree (t : Tree)
  | P_od (d : Tree)
  deriving DecidableEq

def evalP : Payload → ListBlank (Fin 2)
  | .P_tree t => evalT t
  | .P_od d => (0 : Fin 2) >> evalT d

inductive RVal where
  | R_D (p : Payload)
  | R_F (m : Nat) (p : Payload)
  | R_A (m : Nat) (p : Payload)
  deriving DecidableEq

def SweepRV (r : ListBlank (Fin 2)) : RVal → Prop
  | .R_D (.P_tree t) => Sweep qEr r (tailT t)
  | .R_D (.P_od _) => False
  | .R_F m p => Sweep qPr r ((([1, 1] : List (Fin 2)) ^ m) +> evalP p)
  | .R_A m p => Sweep qRe r ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> evalP p))

def app_1_odd (m : Nat) : RVal → RVal
  | .R_F m0 p => .R_A (m + m0) p
  | .R_A m0 p => .R_F (m + m0 + 1) p
  | .R_D p => .R_F m p

def app_1_even (m : Nat) (rv : RVal) : RVal :=
  if m = 0 then rv
  else match rv with
    | .R_F m0 p => .R_F (m + m0) p
    | .R_A m0 p => .R_A (m + m0) p
    | .R_D p => .R_A (m - 1) p

def bump_ra : RVal → RVal
  | .R_F m p => .R_F (m + 1) p
  | .R_D p => .R_A 0 p
  | .R_A m p => .R_A (m + 1) p

/-! ### 4. Structural Well-Formedness, Weights `W0`/`Wd`/`W_rv`, Shield `S_rv`, and Measures -/

mutual
def WF_u : Tree → Prop
  | .endZero c | .endStop c | .stopOne c => c ≥ 1
  | .endOne c | .oneEnd c => c ≥ 2
  | .stop c d => c ≥ 1 ∧ d ≠ .endZero 0 ∧ d ≠ .endOne 1 ∧ WF_d d
  | .od c _ d => c ≥ 2 ∧ WF_d d
  | .sh c m u => c ≥ 2 ∧ ¬(m = 0 ∧ u = .endStop 1) ∧ WF_u u

def WF_d : Tree → Prop
  | .endZero _ | .endStop _ | .endOne _ | .oneEnd _ | .stopOne _ => True
  | .stop _ d => d ≠ .endZero 0 ∧ d ≠ .endOne 1 ∧ WF_d d
  | .od _ _ d => WF_d d
  | .sh _ m u => ¬(m = 0 ∧ u = .endStop 1) ∧ WF_u u
end

mutual
def W0 : Tree → Nat
  | .endZero c => 2 * c + 11
  | .endStop c => if c ≤ 1 then 11 else 2 * c + 10
  | .endOne c => 2 * c + 9
  | .oneEnd c => 2 * c + 11
  | .stopOne c => 2 * c + 13
  | .stop c d => 2 * c + 4 + Wd d
  | .od c m d => 2 * c + 2 * m + 4 + Wd d
  | .sh c m u => 2 * c + 2 * m + 2 + W0 u

def Wd : Tree → Nat
  | .endZero c => if c = 0 then 10 else if c = 1 then 13 else 2 * c + 12
  | .endStop c => if c = 0 then 11 else 2 * c + 12
  | .endOne c => if c ≤ 1 then 9 else 2 * c + 10
  | .oneEnd c => if c = 0 then 12 else 2 * c + 11
  | .stopOne c => if c = 0 then 14 else 2 * c + 13
  | .stop c d => 2 * c + 4 + Wd d
  | .od c m d => 2 * c + 2 * m + 4 + Wd d
  | .sh c m u => 2 * c + 2 * m + 2 + W0 u
end

def isLeaf : Tree → Bool
  | .endZero _ | .endStop _ | .endOne _ | .oneEnd _ | .stopOne _ => true
  | _ => false

def stopOnePosBonus : Tree → Nat
  | .stopOne c => if c ≥ 1 then 2 else 0
  | _ => 0

def BadRoot : Tree → Prop
  | .stop c (.stopOne cd) => (cd ≥ 1 ∧ c = cd + 1) ∨ (cd = 0 ∧ c = 2)
  | .sh c m (.oneEnd k) => m = 0 ∧ k ≥ 2 ∧ c = k
  | .sh c m (.endOne k) => m = 1 ∧ k ≥ 3 ∧ c + 1 = k
  | .od c m (.stopOne cd) => c = 3 ∧ m = 0 ∧ cd = 0
  | .od c m (.oneEnd cd) => c = 2 ∧ m = 0 ∧ cd = 1
  | .od c m (.stop cd (.endOne ce)) => c = 2 ∧ m = 0 ∧ cd = 0 ∧ ce = 0
  | _ => False

def WF_r_core (t : Tree) : Prop :=
  WF_u t ∧ match t with
    | .endZero _ | .endStop _ | .endOne _ | .oneEnd _ => True
    | .stopOne c => c ≥ 2
    | .stop c d => c ≥ 2 ∧ 2 * c + 11 ≥ Wd d
    | .od c _ d => (if d = .endZero 1 then c ≥ 3 else c ≥ 2) ∧ 2 * c + 9 ≥ Wd d + stopOnePosBonus d
    | .sh c _ u => 2 * c + 11 ≥ W0 u

def WF_r (t : Tree) : Prop := WF_r_core t ∧ ¬ BadRoot t

def W0_lin (t : Tree) : Nat :=
  if t = .endStop 1 then 12 else W0 t

def S_tree : Tree → Nat
  | .stopOne c => 24 - 2 * c
  | .endZero _ | .endStop _ | .endOne _ | .oneEnd _ => 0
  | .stop c d => max (24 - 2 * c) (Wd d + 9 - 2 * c)
  | .od c _ d => max (if d = .endZero 1 then 26 - 2 * c else 0) (Wd d + 11 + stopOnePosBonus d - 2
    * c)
  | .sh c _ u => W0 u + 9 - 2 * c

def W_ra_tree (m : Nat) (w : Tree) : Nat :=
  match w with
  | .endZero c => if c ≤ 1 then 2 * m + 15 else 2 * m + 2 * c + 13
  | .endStop c => 2 * m + 2 * c + 13
  | _ => 2 * m + 4 + W0 w

def W_ra_od (m : Nat) (d : Tree) : Nat :=
  match d with
  | .endZero cd => if cd ≤ 1 then 2 * m + 2 * cd + 15 else 2 * m + 2 * cd + 16
  | .endOne cd => 2 * m + 2 * cd + 14
  | .endStop cd => 2 * m + 2 * cd + 17
  | .oneEnd cd => 2 * m + 2 * cd + 17
  | .stopOne cd => 2 * m + 2 * cd + 19
  | _ => 2 * m + 6 + Wd d

def W_rv : RVal → Nat
  | .R_D (.P_tree t) => W0_lin t
  | .R_D (.P_od _) => 0
  | .R_F 0 (.P_tree u) =>
      if u = .endZero 1 then 13
      else if u = .endOne 2 then 14
      else W0_lin (mk_stop 1 (sub_c 1 u)) - 2
  | .R_F 0 (.P_od _) => 0
  | .R_F (m + 1) (.P_tree u) =>
      if m = 0 ∧ u = .endStop 1 then 15
      else W0_lin (mk_sh 2 m u) - 2
  | .R_F (m + 1) (.P_od d) =>
      if d = .endOne 1 then 2 * (m + 1) + 15
      else 2 * (m + 1) + 4 + Wd d
  | .R_A m (.P_tree w) => W_ra_tree m w
  | .R_A m (.P_od d) => W_ra_od m d

def evenCeil (x : Nat) : Nat := ((x + 1) / 2) * 2

def S_ra_tree (_m : Nat) (w : Tree) : Nat :=
  match w with
  | .endZero c | .endStop c => max 24 (2 * c + 20)
  | _ => max 24 (evenCeil (W0 w + 9) + 2)

def S_ra_od (d : Tree) : Nat :=
  match d with
  | .endZero cd | .endStop cd => 2 * cd + 26
  | .endOne cd | .oneEnd cd => 2 * cd + 24
  | .stopOne cd => 2 * cd + 28
  | .stop cd _ => 2 * cd + max 26 (evenCeil (Wd (set_c 0 d) + 13) + 2)
  | _ => 2 * tree_c d + max 26 (evenCeil (Wd (set_c 0 d) + 11) + 2)

def S_rv : RVal → Nat
  | .R_D (.P_tree t) => S_tree t
  | .R_D (.P_od _) => 0
  | .R_F 0 (.P_tree u) => max 22 (S_tree (mk_stop 1 (sub_c 1 u)) + 2)
  | .R_F 0 (.P_od _) => 22
  | .R_F (m + 1) (.P_tree u) => max 22 (S_tree (mk_sh 2 m u) + 2)
  | .R_F (m + 1) (.P_od d) => max 22 (S_tree (.od 2 m d) + 2)
  | .R_A m (.P_tree w) => S_ra_tree m w
  | .R_A _ (.P_od d) => S_ra_od d

def WF_rv : RVal → Prop
  | .R_D (.P_tree u) => WF_u u
  | .R_D (.P_od _) => False
  | .R_F 0 (.P_tree u) => WF_u u
  | .R_F 0 (.P_od _) => False
  | .R_F (_ + 1) (.P_tree u) => WF_u u
  | .R_F (_ + 1) (.P_od d) => WF_d d
  | .R_A _ (.P_tree u) => WF_u u
  | .R_A _ (.P_od d) => WF_d d

def NotBadRD (rv : RVal) : Prop :=
  rv ≠ .R_D (.P_tree (.endZero 1)) ∧ rv ≠ .R_D (.P_tree (.endOne 2))

def GoodRV : RVal → Prop
  | .R_D (.P_tree (.endZero _)) => False
  | .R_D (.P_tree (.endStop _)) => False
  | .R_D (.P_tree (.endOne _)) => False
  | .R_F 0 (.P_tree (.endZero 1)) => False
  | _ => True

def W_safe : RVal → Nat
  | .R_D (.P_tree (.endOne c)) => 2 * c + 10
  | .R_D (.P_tree (.oneEnd c)) => 2 * c + 13
  | .R_D (.P_tree (.stopOne c)) => if c ≤ 1 then 18 else 2 * c + 15
  | .R_F m (.P_tree (.endStop c)) =>
      if m = 1 ∧ c = 1 then 17 else W_rv (.R_F m (.P_tree (.endStop c)))
  | .R_F m (.P_tree (.endOne c)) =>
      if m = 0 ∧ c = 2 then 16 else W_rv (.R_F m (.P_tree (.endOne c)))
  | .R_A m (.P_od (.endOne cd)) =>
      if m = 0 then 2 * cd + 15 else W_rv (.R_A m (.P_od (.endOne cd)))
  | rv => W_rv rv

def BadRV (rem : Nat) (rv : RVal) : Prop :=
  if rem = 0 then
    match rv with
    | .R_D (.P_tree t) => BadRoot t
    | _ => False
  else
    match rv with
    | .R_D (.P_tree t) => BadRoot (add_c rem t)
    | .R_F 0 (.P_tree u) => BadRoot (mk_stop rem (sub_c 1 u))
    | .R_F (m + 1) (.P_tree u) => BadRoot (mk_sh (rem + 1) m u)
    | .R_F (m + 1) (.P_od d) => BadRoot (.od (rem + 1) m d)
    | .R_A m (.P_tree (.endStop k)) => m = 1 ∧ k ≥ 2 ∧ rem = k
    | .R_A m (.P_tree (.endOne k)) => m = 0 ∧ k ≥ 2 ∧ rem = k
    | .R_A m (.P_od (.oneEnd cd)) => (cd = 0 ∧ m = 1 ∧ rem = 2) ∨ (cd = 1 ∧ m = 0 ∧ rem = 3)
    | _ => False

def M_u : Tree → Nat
  | .od c m d => W0 (.od c m d) + 3
  | .sh c m u => W0 (.sh c m u) + 3
  | _ => 0

def M_d0 : Tree → Nat
  | .od c m d => Wd (.od c m d) + 7
  | .sh c m u => Wd (.sh c m u) + 7
  | _ => 0

def M_rv (rv : RVal) : Nat := W_rv rv + 2

/-! ### 5. Basic Bounds & `SweepRV` Combinators -/

theorem tree_c_pos_of_WF_u {u : Tree} (h : WF_u u) : tree_c u ≥ 1 := by
  cases u <;> simp only [WF_u, tree_c] at h ⊢ ; all_goals (try omega)

theorem WF_d_of_WF_u {u : Tree} (h : WF_u u) : WF_d u := by
  cases u <;> simp [WF_u, WF_d] at h ⊢ <;> tauto

theorem WF_d_set_c (nc : Nat) {d : Tree} (h : WF_d d) : WF_d (set_c nc d) := by
  cases d <;> simp only [WF_d, set_c] at h ⊢ <;> exact h

theorem WF_u_add_c (k : Nat) {u : Tree} (h : WF_u u) : WF_u (add_c k u) := by
  cases u with
  | stop c d =>
      rcases h with ⟨hc, rest⟩
      dsimp only [WF_u, add_c, set_c, tree_c]
      exact ⟨by omega, rest⟩
  | od c m d =>
      rcases h with ⟨hc, rest⟩
      dsimp only [WF_u, add_c, set_c, tree_c]
      exact ⟨by omega, rest⟩
  | sh c m u2 =>
      rcases h with ⟨hc, rest⟩
      dsimp only [WF_u, add_c, set_c, tree_c]
      exact ⟨by omega, rest⟩
  | _ => simp only [WF_u, add_c, set_c, tree_c] at h ⊢; (try omega)

theorem WF_u_mk_stop (c : Nat) (hc : c ≥ 1) {d : Tree} (hd : WF_d d) :
    WF_u (mk_stop c d) := by
  unfold mk_stop
  split_ifs with h1 h2
  · simp only [WF_u]; (try omega)
  · simp only [WF_u]; (try omega)
  · simp only [WF_u]; exact ⟨hc, h1, h2, hd⟩

theorem WF_u_mk_sh (c m : Nat) (hc : c ≥ 2) {u : Tree} (hu : WF_u u) :
    WF_u (mk_sh c m u) := by
  unfold mk_sh
  split_ifs with h1
  · simp only [WF_u]; (try omega)
  · simp only [WF_u]; exact ⟨hc, h1, hu⟩

mutual
theorem W0_ge_11 (t : Tree) : W0 t ≥ 2 * tree_c t + 9 := by
  cases t with
  | endZero c => simp [W0, tree_c]
  | endStop c =>
      simp only [W0, tree_c]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endOne c => simp [W0, tree_c]
  | oneEnd c => simp [W0, tree_c]
  | stopOne c => simp [W0, tree_c]
  | stop c d => have := Wd_ge_9 d; simp only [W0, tree_c]; (try omega)
  | od c m d => have := Wd_ge_9 d; simp only [W0, tree_c]; (try omega)
  | sh c m u => have := W0_ge_11 u; simp only [W0, tree_c]; (try omega)

theorem Wd_ge_9 (d : Tree) : Wd d ≥ 9 := by
  cases d with
  | endZero c =>
      simp only [Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endStop c =>
      simp only [Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endOne c =>
      simp only [Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | oneEnd c =>
      simp only [Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stopOne c =>
      simp only [Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stop c d2 => have := Wd_ge_9 d2; simp only [Wd]; (try omega)
  | od c m d2 => have := Wd_ge_9 d2; simp only [Wd]; (try omega)
  | sh c m u2 => have := W0_ge_11 u2; simp only [Wd]; (try omega)
end

theorem Wd_ge_2c_9 (d : Tree) : d = .endOne 1 ∨ Wd d ≥ 2 * tree_c d + 9 := by
  cases d with
  | endOne c =>
    by_cases h1 : c = 1
    · left; subst h1; rfl
    · right
      simp only [Wd, tree_c]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endZero c =>
      right
      simp only [Wd, tree_c]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endStop c =>
      right
      simp only [Wd, tree_c]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | oneEnd c =>
      right
      simp only [Wd, tree_c]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stopOne c =>
      right
      simp only [Wd, tree_c]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stop c d2 => have := Wd_ge_9 d2; right; simp only [Wd, tree_c]; (try omega)
  | od c m d2 => have := Wd_ge_9 d2; right; simp only [Wd, tree_c]; (try omega)
  | sh c m u2 => have := W0_ge_11 u2; right; simp only [Wd, tree_c]; (try omega)

theorem S_tree_iff_WF_r_core (k : Nat) {u : Tree} (hu : WF_u u) :
    WF_r_core (add_c k u) ↔ 2 * k + 20 ≥ S_tree u := by
  have huk := WF_u_add_c k hu
  simp only [WF_r_core, huk, true_and]
  cases u with
  | endZero c => simp [S_tree, add_c, set_c]
  | endStop c => simp [S_tree, add_c, set_c]
  | endOne c => simp [S_tree, add_c, set_c]
  | oneEnd c => simp [S_tree, add_c, set_c]
  | stopOne c =>
    simp [WF_u] at hu
    simp [S_tree, add_c, set_c, tree_c]
    omega
  | stop c d =>
    simp [WF_u] at hu
    simp [S_tree, add_c, set_c, tree_c]
    omega
  | od c m d =>
    simp only [WF_u] at hu
    simp only [S_tree, add_c, set_c, tree_c]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  | sh c m u2 =>
    simp [WF_u] at hu
    have hw := W0_ge_11 u2
    simp [S_tree, add_c, set_c, tree_c]
    omega

theorem sweepRV_app_1_odd (m : Nat) {r : ListBlank (Fin 2)} {rv : RVal}
    (hwf : WF_rv rv) (h : SweepRV r rv) :
    SweepRV ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> r)) (app_1_odd m rv) := by
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree u =>
      simp only [SweepRV, app_1_odd, evalP] at h ⊢
      have hc := tree_c_pos_of_WF_u hwf
      have h1 : Sweep qPr ((1 : Fin 2) >> r) (evalT u) := by
        rw [← cons_zero_tailT hc]; exact sweep_1_D h
      exact sweep_11_pow_F m h1
  | R_F m0 p =>
    simp only [SweepRV, app_1_odd] at h ⊢
    have h1 := sweep_1_F h
    have hsw := swap_1_11_pow m0 (evalP p)
    simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
    rw [← hsw] at h1
    have h2 := sweep_11_pow_A m h1
    simpa only [ListBlank.append_pow_add] using h2
  | R_A m0 p =>
    simp only [SweepRV, app_1_odd] at h ⊢
    have h1 := sweep_1_A h
    have h2 := sweep_11_pow_F m h1
    have heq : ((([1, 1] : List (Fin 2)) ^ (m + m0 + 1)) +> evalP p) =
        ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> ((([1,
          1] : List (Fin 2)) ^ m0) +> ((1 : Fin 2) >> evalP p)))) := by
      rw [show m + m0 + 1 = m + (m0 + 1) by omega, ListBlank.append_pow_add,
        ListBlank.append_pow_succ]
      simp only [ListBlank.append_cons, ListBlank.append_nil]
      have hsw := swap_1_11_pow m0 (evalP p)
      simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
      rw [hsw]
    rw [heq]
    exact h2

theorem WF_rv_app_1_odd (m : Nat) {rv : RVal} (hwf : WF_rv rv) :
    WF_rv (app_1_odd m rv) := by
  cases rv with
  | R_D p => cases p <;> cases m <;> simpa [app_1_odd, WF_rv] using hwf
  | R_F m0 p => cases m0 <;> cases p <;> simpa [app_1_odd, WF_rv] using hwf
  | R_A m0 p => cases p <;> simpa [app_1_odd, WF_rv] using hwf

theorem sweepRV_app_1_even (m : Nat) {r : ListBlank (Fin 2)} {rv : RVal}
    (hwf : WF_rv rv) (h : SweepRV r rv) :
    SweepRV ((([1, 1] : List (Fin 2)) ^ m) +> r) (app_1_even m rv) := by
  cases m with
  | zero => simpa [app_1_even, list_pow_zero, ListBlank.append_nil] using h
  | succ m =>
    cases rv with
    | R_D p =>
      cases p with
      | P_od d => cases hwf
      | P_tree u =>
        simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, SweepRV,
          evalP] at h ⊢
        have hc := tree_c_pos_of_WF_u hwf
        have h1 : Sweep qPr ((1 : Fin 2) >> r) (evalT u) := by
          rw [← cons_zero_tailT hc]; exact sweep_1_D h
        have h2 := sweep_1_F h1
        have h3 := sweep_11_pow_A m h2
        have hcomm : ((([1, 1] : List (Fin 2)) ^ (m + 1)) +> r) =
            ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by
          rw [list_pow_succ', ListBlank.append_assoc]
          rfl
        rw [hcomm]
        exact h3
    | R_F m0 p =>
      simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte, SweepRV] at h ⊢
      have h1 := sweep_11_pow_F (m + 1) h
      simpa only [ListBlank.append_pow_add] using h1
    | R_A m0 p =>
      simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte, SweepRV] at h ⊢
      have h1 := sweep_11_pow_A (m + 1) h
      simpa only [ListBlank.append_pow_add] using h1

theorem WF_rv_app_1_even (m : Nat) {rv : RVal} (hwf : WF_rv rv) :
    WF_rv (app_1_even m rv) := by
  cases m with
  | zero => simpa [app_1_even] using hwf
  | succ m =>
    cases rv with
    | R_D p => cases p <;> simpa [app_1_even, WF_rv] using hwf
    | R_F m0 p =>
      cases m0 <;> cases p <;> simp only [app_1_even, WF_rv] at hwf ⊢ <;> exact hwf
    | R_A m0 p => cases p <;> simpa [app_1_even, WF_rv] using hwf

/-! ### 6. Base-Case `Sweep` & `SweepRV` Lemmas for Leaves and `stop` -/

theorem sweep_01_pow_from_F_aux (k : Nat) {r u : ListBlank (Fin 2)}
    (h : Sweep qPr r u) :
    Sweep qEr ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> r)
      ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> u))) := by
  induction k with
  | zero =>
    simpa [list_pow_one, list_pow_zero, ListBlank.append_cons, ListBlank.append_nil] using
      sweep_01_F h
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    simp only [ListBlank.append_cons, ListBlank.append_nil]
    have h2 := sweep_01_D ih
    conv_rhs => rw [ListBlank.append_pow_succ]
    simpa only [ListBlank.append_cons, ListBlank.append_nil] using h2

theorem sweep_01_pow_from_F (c : Nat) (hc : c ≥ 1) {r u : ListBlank (Fin 2)}
    (h : Sweep qPr r u) :
    Sweep qEr ((([0, 1] : List (Fin 2)) ^ c) +> r)
      ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ (c - 1)) +> ((0 : Fin 2) >> u))) := by
  have h1 := sweep_01_pow_from_F_aux (c - 1) h
  rwa [show c - 1 + 1 = c by omega] at h1

theorem sweep_01_pow_from_D (k : Nat) {r u : ListBlank (Fin 2)}
    (h : Sweep qEr r ((1 : Fin 2) >> u)) :
    Sweep qEr ((([0, 1] : List (Fin 2)) ^ k) +> r)
      ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> u)) := by
  induction k with
  | zero => simpa [list_pow_zero, ListBlank.append_nil] using h
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    conv_rhs => rw [ListBlank.append_pow_succ]
    simpa only [ListBlank.append_cons, ListBlank.append_nil] using sweep_01_D ih

theorem sweep_u_endZero (c : Nat) (hc : c ≥ 1) :
    SweepRV (evalT (.endZero c)) (.R_D (.P_tree (.endStop c))) := by
  simp only [SweepRV, evalT, tailT, tree_c, evalCore]
  have h := sweep_01_pow_from_F c hc sweep_default
  simpa [ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_u_stop_raw (c : Nat) (hc : c ≥ 1) (r : ListBlank (Fin 2)) :
    Sweep qEr ((([0, 1] : List (Fin 2)) ^ c) +> ([(0 : Fin 2), 0, 1] +> r))
      ((1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ c) +> ((1 : Fin 2) >> (0 : Fin 2) >> r))) := by
  have h0 : Sweep qPr ([(0 : Fin 2), 0,
    1] +> r) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r) := by
    simpa [ListBlank.append_cons, ListBlank.append_nil] using sweep_001 r
  have h1 := sweep_01_pow_from_F c hc h0
  have heq : ((([0,
    1] : List (Fin 2)) ^ (c - 1)) +>
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> r)) =
      ((([0, 1] : List (Fin 2)) ^ c) +> ((1 : Fin 2) >> (0 : Fin 2) >> r)) := by
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    conv_rhs => rw [list_pow_succ', ListBlank.append_assoc]
    rfl
  rw [heq] at h1
  exact h1

theorem sweep_u_endStop (c : Nat) (hc : c ≥ 1) :
    SweepRV (evalT (.endStop c)) (.R_D (.P_tree (.endOne (c + 1)))) := by
  simp only [SweepRV, evalT, tailT, tree_c, evalCore, Nat.add_sub_cancel]
  have h := sweep_u_stop_raw c hc default
  simpa [ListBlank.cons_zero_default, ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_u_stopOne (c : Nat) (hc : c ≥ 1) :
    SweepRV (evalT (.stopOne c)) (.R_D (.P_tree (.od (c + 1) 0 (.endOne 1)))) := by
  simp only [SweepRV, evalT, tailT, tree_c, evalCore, Nat.add_sub_cancel, list_pow_zero,
    list_pow_one, ListBlank.append_nil]
  have h := sweep_u_stop_raw c hc ([(0 : Fin 2), 1, 1] +> default)
  simpa [ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_u_stop (c : Nat) (hc : c ≥ 1) (d : Tree) :
    SweepRV (evalT (.stop c d)) (.R_D (.P_tree (.od (c + 1) 0 d))) := by
  simp only [SweepRV, evalT_stop, tailT, tree_c, evalCore, Nat.add_sub_cancel, list_pow_zero,
    ListBlank.append_nil]
  exact sweep_u_stop_raw c hc (evalT d)

theorem win_endOne_c1 :
    Sweep qPr ([(0 : Fin 2), 1, 1] +> default) ([(1 : Fin 2), 1, 0, 1, 0, 0, 1] +> default) := by
  intro L
  have hz : ([(0 : Fin 2), 1, 1] +> (default : ListBlank (Fin 2))) =
      ([(0 : Fin 2), 1, 1, 0, 0, 0, 0, 0] +> default) := by
    simp only [ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default]
  rw [hz]
  dsimp [ListBlank.append]
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem sweep_u_endOne (c : Nat) (hc : c ≥ 2) :
    SweepRV (evalT (.endOne c)) (.R_D (.P_tree (.oneEnd c))) := by
  simp only [SweepRV, evalT, tailT, tree_c, evalCore]
  have h1 := sweep_01_pow_from_F (c - 1) (by omega) win_endOne_c1
  have h_in : ((([0, 1] : List (Fin 2)) ^ (c - 1)) +> ([(0 : Fin 2), 1, 1] +> default)) =
      ((([0, 1] : List (Fin 2)) ^ c) +> ([(1 : Fin 2)] +> default)) := by
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega, show k + 2 = (k + 1) + 1 by omega]
    conv_rhs => rw [list_pow_succ', ListBlank.append_assoc]
    rfl
  have h_out : ((([0, 1] : List (Fin 2)) ^ (c - 1 - 1)) +>
      ((0 : Fin 2) >> [(1 : Fin 2), 1, 0, 1, 0, 0, 1] +> default)) =
      ((([0, 1] : List (Fin 2)) ^ (c - 1)) +> ([(1 : Fin 2), 0, 1, 0, 0, 1] +> default)) := by
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    conv_rhs => rw [list_pow_succ', ListBlank.append_assoc]
    rfl
  rw [h_in, h_out] at h1
  exact h1

theorem win_oneEnd_c1 :
    Sweep qEr ([(0 : Fin 2), 1, 1, 0, 1, 0, 0, 1] +> default)
      ((1 : Fin 2) >> ([(0 : Fin 2), 0, 1, 0, 1, 1] +> default)) := by
  intro L
  have hz : ([(0 : Fin 2), 1, 1, 0, 1, 0, 0, 1] +> (default : ListBlank (Fin 2))) =
      ([(0 : Fin 2), 1, 1, 0, 1, 0, 0, 1, 0] +> default) := by
    simp only [ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default]
  rw [hz]
  dsimp [ListBlank.append]
  refine ReachesPlus.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  refine ReachesStar.head (by (try simp only [Turing.ListBlank.head_cons,
    ListBlank.head_default_fin]); rfl) ?_
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]
  exact ReachesStar.refl _ _

theorem sweep_u_oneEnd (c : Nat) (hc : c ≥ 2) :
    SweepRV (evalT (.oneEnd c)) (.R_D (.P_tree (.stopOne c))) := by
  simp only [SweepRV, evalT, tailT, tree_c, evalCore]
  have h1 := sweep_01_pow_from_D (c - 1) win_oneEnd_c1
  have h_in : ((([0, 1] : List (Fin 2)) ^ (c - 1)) +>
      ([(0 : Fin 2), 1, 1, 0, 1, 0, 0, 1] +> default)) =
      ((([0, 1] : List (Fin 2)) ^ c) +> ([(1 : Fin 2), 0, 1, 0, 0, 1] +> default)) := by
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega, show k + 2 = (k + 1) + 1 by omega]
    conv_rhs => rw [list_pow_succ', ListBlank.append_assoc]
    rfl
  rw [h_in] at h1
  exact h1

theorem sweep_d0_endZero :
    SweepRV ((0 : Fin 2) >> evalT (.endZero 0)) (.R_F 0 (.P_tree (.endZero 1))) := by
  simp only [SweepRV, evalP, evalT, tree_c, evalCore, list_pow_zero, list_pow_one,
    ListBlank.append_nil, ListBlank.append_cons, ListBlank.cons_zero_default]
  exact sweep_default

theorem sweep_d0_endStop :
    SweepRV ((0 : Fin 2) >> evalT (.endStop 0)) (.R_F 0 (.P_tree (.endZero 2))) := by
  simp only [SweepRV, evalP, evalT, tree_c, evalCore, list_pow_zero, ListBlank.append_nil]
  have h := sweep_000 ((1 : Fin 2) >> default)
  simpa [list_pow_succ, list_pow_zero, ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_d0_endOne :
    SweepRV ((0 : Fin 2) >> evalT (.endOne 0)) (.R_D (.P_tree (.endStop 1))) := by
  have heq : ((0 : Fin 2) >> evalT (.endOne 0)) = evalT (.endZero 1) := by
    simp [evalT, tree_c, evalCore, list_pow_zero, list_pow_one, ListBlank.append_cons,
      ListBlank.append_nil]
  rw [heq]
  exact sweep_u_endZero 1 (by omega)

theorem sweep_d0_oneEnd :
    SweepRV ((0 : Fin 2) >> evalT (.oneEnd 0)) (.R_D (.P_tree (.endOne 3))) := by
  have heq : ((0 : Fin 2) >> evalT (.oneEnd 0)) = evalT (.endStop 2) := by
    simp [evalT, tree_c, evalCore, list_pow_zero, list_pow_succ, ListBlank.append_cons,
      ListBlank.append_nil]
  rw [heq]
  exact sweep_u_endStop 2 (by omega)

theorem sweep_d0_stopOne :
    SweepRV ((0 : Fin 2) >> evalT (.stopOne 0)) (.R_F 0 (.P_tree (.endOne 3))) := by
  simp only [SweepRV, evalP, evalT, tree_c, evalCore, list_pow_zero, ListBlank.append_nil]
  have h := sweep_000 ([(1 : Fin 2), 0, 1, 1] +> default)
  simpa [list_pow_succ, list_pow_zero, ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_d0_stop {d : Tree} (hc0 : tree_c d = 0) :
    SweepRV ((0 : Fin 2) >> evalT (.stop 0 d)) (.R_F 0 (.P_tree (add_c 2 d))) := by
  simp only [SweepRV, evalP, evalT_stop, list_pow_zero, ListBlank.append_nil]
  have h := sweep_000 ((1 : Fin 2) >> evalT d)
  have heq : evalT (add_c 2 d) = ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    evalT d) := by
    unfold add_c evalT
    rw [tree_c_set_c, evalCore_set_c, hc0]
    simp [list_pow_succ, list_pow_zero, ListBlank.append_cons, ListBlank.append_nil]
  rw [heq]
  simpa [ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_d0_stop_any (d : Tree) :
    SweepRV ((0 : Fin 2) >> evalT (.stop 0 d)) (.R_F 0 (.P_tree (add_c 2 d))) := by
  simp only [SweepRV, evalP, evalT_stop, list_pow_zero, ListBlank.append_nil]
  have h := sweep_000 ((1 : Fin 2) >> evalT d)
  have h2 : add_c 2 d = add_c 1 (add_c 1 d) := by
    cases d <;> simp [add_c, set_c, tree_c] ; all_goals (try omega)
  have heq : evalT (add_c 2 d) = ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    evalT d) := by
    rw [h2, evalT_add_c_one, evalT_add_c_one]
  rw [heq]
  simpa [ListBlank.append_cons, ListBlank.append_nil] using h

theorem sweep_d0_od_pos (m2 : Nat) {d2 : Tree} (hpos : tree_c d2 ≥ 1) :
    SweepRV ((0 : Fin 2) >> evalT (.od 0 m2 d2)) (.R_D (.P_tree (.od 2 m2 (sub_c 1 d2)))) := by
  simp only [SweepRV, evalT_od, list_pow_zero, ListBlank.append_nil]
  have hd2 : evalT d2 = ((0 : Fin 2) >> (1 : Fin 2) >> evalT (sub_c 1 d2)) := by
    have h := @evalT_add_c_one (sub_c 1 d2)
    have hrestore : add_c 1 (sub_c 1 d2) = d2 := by
      cases d2 <;> simp only [add_c, sub_c, set_c, tree_c, Tree.endZero.injEq, Tree.endStop.injEq,
        Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq, Tree.stop.injEq, and_true,
        true_and, Tree.od.injEq, Tree.sh.injEq] at hpos ⊢ ; all_goals (try omega)
    rw [hrestore] at h; exact h
  rw [hd2]
  have hin : ((0 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ m2) +>
      ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> evalT (sub_c 1 d2)))) =
      ((0 : Fin 2) >> (1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ m2) +>
        ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> evalT (sub_c 1 d2)))) := by
    have hsw := swap_1_11_pow m2 ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> evalT (sub_c 1 d2))
    simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
    rw [hsw]
  rw [hin]
  have h1 := sweep_001 (evalT (sub_c 1 d2))
  have h2 := sweep_11_pow_F m2 h1
  have h3 := sweep_01_F h2
  have hout : ((1 : Fin 2) >> (0 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ m2) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> evalT (sub_c 1 d2)))) =
      tailT (.od 2 m2 (sub_c 1 d2)) := by
    unfold tailT evalCore
    simp only [tree_c, show 2 - 1 = 1 by rfl, list_pow_one, ListBlank.append_cons,
      ListBlank.append_nil]
    have hsw := swap_1_11_pow m2 ((1 : Fin 2) >> (0 : Fin 2) >> evalT (sub_c 1 d2))
    simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
    rw [hsw]
    rfl
  rw [← hout]
  exact h3

theorem sweep_P_od_pos {d : Tree} (hpos : tree_c d ≥ 1) :
    SweepRV (evalP (.P_od d)) (.R_F 1 (.P_od (sub_c 1 d))) := by
  simp only [SweepRV, evalP, list_pow_one]
  have hd : evalT d = ((0 : Fin 2) >> (1 : Fin 2) >> evalT (sub_c 1 d)) := by
    have h := @evalT_add_c_one (sub_c 1 d)
    have hrestore : add_c 1 (sub_c 1 d) = d := by
      cases d <;> simp only [add_c, sub_c, set_c, tree_c, Tree.endZero.injEq, Tree.endStop.injEq,
        Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq, Tree.stop.injEq, and_true,
        true_and, Tree.od.injEq, Tree.sh.injEq] at hpos ⊢ ; all_goals (try omega)
    rw [hrestore] at h; exact h
  rw [hd]
  simpa [ListBlank.append_cons, ListBlank.append_nil] using sweep_001 (evalT (sub_c 1 d))

/-! ### 7. Single-Step `01` on `RVal` (`sweepRV_01_*` and `bump_ra`) -/

theorem sweepRV_01_RD {t : Tree} {r : ListBlank (Fin 2)} (ht : WF_u t)
    (h : SweepRV r (.R_D (.P_tree t))) :
    SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) (.R_D (.P_tree (add_c 1 t))) := by
  simp only [SweepRV] at h ⊢
  rw [tailT_add_c_one (tree_c_pos_of_WF_u ht)]
  exact sweep_01_D h

theorem sweepRV_01_RF0 {u : Tree} {r : ListBlank (Fin 2)} (hu : WF_u u)
    (h : SweepRV r (.R_F 0 (.P_tree u))) :
    SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) (.R_D (.P_tree (mk_stop 1 (sub_c 1 u)))) := by
  simp only [SweepRV, evalP, list_pow_zero, ListBlank.append_nil] at h ⊢
  have hc := tree_c_pos_of_WF_u hu
  have hu_eq : evalT u = ((0 : Fin 2) >> (1 : Fin 2) >> evalT (sub_c 1 u)) := by
    have h1 := @evalT_add_c_one (sub_c 1 u)
    have hr : add_c 1 (sub_c 1 u) = u := by
      cases u <;> simp only [add_c, sub_c, set_c, tree_c, Tree.endZero.injEq, Tree.endStop.injEq,
        Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq, Tree.stop.injEq, and_true,
        true_and, Tree.od.injEq, Tree.sh.injEq] at hc ⊢ ; all_goals (try omega)
    rw [hr] at h1; exact h1
  rw [hu_eq] at h
  have hs := sweep_01_F h
  rw [tailT_mk_stop 1 (by omega) (sub_c 1 u)]
  simpa [list_pow_zero, ListBlank.append_cons, ListBlank.append_nil] using hs

theorem sweepRV_01_RF_tree (m : Nat) {u : Tree} {r : ListBlank (Fin 2)}
    (h : SweepRV r (.R_F (m + 1) (.P_tree u))) :
    SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) (.R_D (.P_tree (mk_sh 2 m u))) := by
  simp only [SweepRV, evalP] at h ⊢
  have hs := sweep_01_F h
  rw [tailT_mk_sh 2 m (by omega) u]
  simp only [show 2 - 1 = 1 by rfl, list_pow_one, ListBlank.append_cons, ListBlank.append_nil]
  have heq : ((([1, 1] : List (Fin 2)) ^ (m + 1)) +> evalT u) =
      ((1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> evalT u))) := by
    rw [ListBlank.append_pow_succ]
    simp only [ListBlank.append_cons, ListBlank.append_nil]
    have hsw := swap_1_11_pow m (evalT u)
    simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
    rw [hsw]
  rw [heq] at hs
  exact hs

theorem sweepRV_01_RF_od (m : Nat) {d : Tree} {r : ListBlank (Fin 2)}
    (h : SweepRV r (.R_F (m + 1) (.P_od d))) :
    SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) (.R_D (.P_tree (.od 2 m d))) := by
  simp only [SweepRV, evalP] at h ⊢
  have hs := sweep_01_F h
  unfold tailT evalCore
  simp only [tree_c, show 2 - 1 = 1 by rfl, list_pow_one, ListBlank.append_cons,
    ListBlank.append_nil]
  have heq : ((([1, 1] : List (Fin 2)) ^ (m + 1)) +> ((0 : Fin 2) >> evalT d)) =
      ((1 : Fin 2) >> ((([1,
        1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d))) := by
    rw [ListBlank.append_pow_succ]
    simp only [ListBlank.append_cons, ListBlank.append_nil]
    have hsw := swap_1_11_pow m ((0 : Fin 2) >> evalT d)
    simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
    rw [hsw]
  rw [heq] at hs
  exact hs

theorem sweepRV_01_RA (m : Nat) {p : Payload} {rv0 : RVal} {r : ListBlank (Fin 2)}
    (hwf0 : WF_rv rv0) (h1 : SweepRV r (.R_A m p)) (h0 : SweepRV (evalP p) rv0) :
    SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) (bump_ra (app_1_odd m rv0)) := by
  simp only [SweepRV] at h1
  have h2 := sweepRV_app_1_odd m hwf0 h0
  cases hrv2 : app_1_odd m rv0 with
  | R_D p2 =>
    cases rv0 <;> simp [app_1_odd] at hrv2
  | R_F m2 p2 =>
    rw [hrv2] at h2
    simp only [SweepRV] at h2
    simp only [bump_ra, SweepRV]
    have hs := sweep_01_A_F h1 h2
    simpa only [ListBlank.append_pow_succ, ListBlank.append_cons,
      ListBlank.append_nil] using hs
  | R_A m2 p2 =>
    rw [hrv2] at h2
    simp only [SweepRV] at h2
    simp only [bump_ra, SweepRV]
    have hs := sweep_01_A_A h1 h2
    simpa only [ListBlank.append_pow_succ, ListBlank.append_cons,
      ListBlank.append_nil] using hs

theorem WF_rv_bump_ra {rv2 : RVal} (hwf2 : WF_rv rv2)
    (hnotD : ∀ p, rv2 ≠ .R_D p) : WF_rv (bump_ra rv2) := by
  cases rv2 with
  | R_D p => exact absurd rfl (hnotD p)
  | R_F m p =>
    cases m <;> cases p <;> simp only [bump_ra, WF_rv] at hwf2 ⊢ <;> exact hwf2
  | R_A m p =>
    cases p <;> simpa [bump_ra, WF_rv] using hwf2

theorem app_1_odd_ne_RD (m : Nat) (rv : RVal) (p : Payload) :
    app_1_odd m rv ≠ .R_D p := by
  cases rv <;> simp [app_1_odd]

/-! ### 8. Universal Arithmetic Sub-Lemmas for `W_rv` and `S_rv` -/

theorem W0_lin_eq (t : Tree) :
    (t = .endStop 1 ∧ W0_lin t = 12 ∧ W0 t = 11) ∨ (t ≠ .endStop 1 ∧ W0_lin t = W0 t) := by
  unfold W0_lin
  split_ifs with h
  · left; subst h; exact ⟨rfl, rfl, rfl⟩
  · right; exact ⟨h, rfl⟩

theorem W0_lin_add_c_one {u : Tree} (hu : WF_u u) :
    W0_lin (add_c 1 u) = W0_lin u + 2 := by
  cases u with
  | endZero c => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)
  | endStop c =>
    simp [WF_u] at hu
    simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
      Tree.endStop.injEq, Nat.reduceEqDiff, Nat.reduceLeDiff]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  | endOne c => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)
  | oneEnd c => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)
  | stopOne c => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)
  | stop c d => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)
  | od c m d => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)
  | sh c m u2 => simp [WF_u] at hu; simp only [W0_lin, W0, add_c, set_c, tree_c, reduceCtorEq,
    ↓reduceIte, ite_true, ite_false]; (try omega)

theorem S_tree_add_c_one {u : Tree} (hu : WF_u u) :
    S_tree (add_c 1 u) = S_tree u - 2 := by
  cases u with
  | endZero c | endStop c | endOne c | oneEnd c =>
    simp [S_tree, add_c, set_c]
  | stopOne c =>
    simp only [S_tree, add_c, set_c, tree_c]; (try omega)
  | stop c d =>
    simp only [S_tree, add_c, set_c, tree_c]; (try omega)
  | od c m d =>
    simp only [S_tree, add_c, set_c, tree_c]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  | sh c m u2 =>
    simp only [S_tree, add_c, set_c, tree_c]; (try omega)

theorem Wd_sub_c_one_le {u : Tree} (hu : WF_u u) :
    Wd (sub_c 1 u) ≤ W0 u + 2 := by
  cases u with
  | endZero c =>
      simp [WF_u] at hu
      simp only [sub_c, set_c, tree_c, Wd, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endStop c =>
      simp [WF_u] at hu
      simp only [sub_c, set_c, tree_c, Wd, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endOne c =>
      simp [WF_u] at hu
      simp only [sub_c, set_c, tree_c, Wd, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | oneEnd c =>
      simp [WF_u] at hu
      simp only [sub_c, set_c, tree_c, Wd, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stopOne c =>
      simp [WF_u] at hu
      simp only [sub_c, set_c, tree_c, Wd, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stop c d => simp [WF_u] at hu; simp only [sub_c, set_c, tree_c, Wd, W0]; (try omega)
  | od c m d => simp [WF_u] at hu; simp only [sub_c, set_c, tree_c, Wd, W0]; (try omega)
  | sh c m u2 => simp [WF_u] at hu; simp only [sub_c, set_c, tree_c, Wd, W0]; (try omega)

theorem W_rv_RF0_spec {u : Tree} (hu : WF_u u) :
    W0_lin (mk_stop 1 (sub_c 1 u)) ≤ W_rv (.R_F 0 (.P_tree u)) + 2 := by
  simp only [W_rv]
  split_ifs with h1 h2
  · subst h1; simp [mk_stop, sub_c, set_c, tree_c, W0_lin]
  · subst h2; simp [mk_stop, sub_c, set_c, tree_c, W0_lin, W0]
  · have hge := W0_ge_11 (mk_stop 1 (sub_c 1 u))
    rcases W0_lin_eq (mk_stop 1 (sub_c 1 u)) with ⟨_, hl, _⟩ | ⟨_, hl⟩ ; all_goals (try omega)

theorem W_rv_RF_pos_tree_spec (m : Nat) {u : Tree} (hu : WF_u u) :
    W0_lin (mk_sh 2 m u) ≤ W_rv (.R_F (m + 1) (.P_tree u)) + 2 := by
  simp only [W_rv]
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩; simp [mk_sh, W0_lin, W0]
  · have hge := W0_ge_11 (mk_sh 2 m u)
    rcases W0_lin_eq (mk_sh 2 m u) with ⟨_, hl, _⟩ | ⟨_, hl⟩ ; all_goals (try omega)

theorem W_rv_app_1_even_le (m : Nat) {rv : RVal} (hwf : WF_rv rv) :
    W_rv (app_1_even m rv) ≤ 2 * m + 2 + W_rv rv := by
  cases m with
  | zero => simp [app_1_even]
  | succ m =>
    cases rv with
    | R_D p =>
      cases p with
      | P_od d => cases hwf
      | P_tree u =>
        simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, W_rv]
        cases u <;> simp only [WF_rv, WF_u, W_ra_tree, W0_lin, W0, Tree.endStop.injEq,
          Nat.reduceLeDiff] at hwf ⊢
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    | R_F m0 p =>
      cases m0 with
      | zero =>
        cases p with
        | P_od d => cases hwf
        | P_tree u =>
          simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte]
          have hsub := Wd_sub_c_one_le hwf
          cases u <;> simp only [WF_rv, WF_u, W_rv, mk_stop, mk_sh, sub_c, set_c, tree_c, W0_lin,
            W0,
            Wd, Tree.endZero.injEq, Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq,
              ↓reduceIte, ite_true, ite_false, and_false, false_and, not_false_eq_true,
              not_true_eq_false, ne_eq, eq_self, Nat.reduceEqDiff, Nat.reduceLeDiff] at hwf hsub ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
      | succ m0 =>
        cases p with
        | P_tree u =>
          simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte,
            show m + 1 + (m0 + 1) = (m + m0 + 1) + 1 by omega]
          have hw := W0_ge_11 u
          cases u <;> simp only [W_rv, mk_sh, W0_lin, W0, Tree.endStop.injEq, and_false, false_and,
            not_false_eq_true, not_true_eq_false, eq_self, Nat.reduceLeDiff, reduceCtorEq,
              ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
              Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
              Nat.reduceSub] at hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | P_od d =>
          simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte,
            show m + 1 + (m0 + 1) = (m + m0 + 1) + 1 by omega]
          simp only [W_rv]
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
    | R_A m0 p =>
      cases p with
      | P_tree w =>
        simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte, W_rv]
        cases w <;> simp only [W_ra_tree]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | P_od d =>
        simp only [app_1_even, Nat.succ_ne_zero, ↓reduceIte, W_rv]
        cases d <;> simp only [W_ra_od]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)

theorem W_rv_app_1_odd_le_4 (M : Nat) {rv : RVal} (hwf : WF_rv rv) :
    W_rv (app_1_odd M rv) ≤ 2 * M + 4 + W_rv rv := by
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree u =>
      cases M with
      | zero =>
        have hsub := Wd_sub_c_one_le hwf
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, mk_stop, sub_c, set_c, tree_c, W0_lin,
          W0,
          Wd, Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
            not_false_eq_true, not_true_eq_false, Nat.reduceEqDiff, Nat.reduceLeDiff, zero_add,
            add_zero] at hwf hsub ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | succ M =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, mk_sh, W0_lin, W0, Tree.endStop.injEq,
          not_false_eq_true, not_true_eq_false, Nat.reduceLeDiff] at hwf hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_F m0 p =>
    cases m0 with
    | zero =>
      cases p with
      | P_od d => cases hwf
      | P_tree u =>
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_stop, sub_c, set_c,
          tree_c,
          W0_lin, W0, Wd, Tree.endZero.injEq, Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq,
            ↓reduceIte, ite_true, ite_false, not_false_eq_true, not_true_eq_false, eq_self,
            Nat.reduceLeDiff, zero_add, add_zero] at hwf ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    | succ m0 =>
      cases p with
      | P_tree u =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0,
          Tree.endStop.injEq, and_false, false_and, ne_eq, eq_self, Nat.reduceLeDiff, reduceCtorEq,
            ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
            not_false_eq_true, not_true_eq_false, Nat.add_one_ne_zero, Nat.succ_ne_zero,
            Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at hwf hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | P_od d =>
        cases d <;> simp only [WF_rv, app_1_odd, W_rv, W_ra_od, Wd, Tree.endOne.injEq,
          Nat.reduceLeDiff] at hwf ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0] at hwf hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      cases d <;> simp only [WF_rv, app_1_odd, W_rv, W_ra_od, Wd] at hwf ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem S_rv_app_1_odd_le (M : Nat) {rv : RVal} (hwf : WF_rv rv) :
    S_rv (app_1_odd M rv) ≤ max 24 (evenCeil (W_rv rv + 9)) := by
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree u =>
      cases M with
      | zero =>
        have hsub := Wd_sub_c_one_le hwf
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, W_rv, mk_stop, sub_c, set_c, tree_c,
          S_tree, W0_lin, W0, Wd, evenCeil, Tree.endStop.injEq, Tree.endOne.injEq, ↓reduceIte,
            ite_true, ite_false, not_false_eq_true, not_true_eq_false, Nat.reduceEqDiff,
            Nat.reduceLeDiff] at hwf hsub hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | succ M =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, W_rv, mk_sh, S_tree, W0_lin, W0,
          evenCeil, Tree.endStop.injEq] at hwf hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_F m0 p =>
    cases m0 with
    | zero =>
      cases p with
      | P_od d => cases hwf
      | P_tree u =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, S_ra_tree, W_rv, mk_stop, sub_c, set_c,
          tree_c, W0_lin, W0, Wd, evenCeil, Tree.endZero.injEq, Tree.endStop.injEq,
            Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, not_false_eq_true,
            not_true_eq_false, eq_self, Nat.reduceLeDiff] at hwf hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    | succ m0 =>
      cases p with
      | P_tree u =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, S_ra_tree, W_rv, mk_sh, W0_lin, W0,
          evenCeil, Tree.endStop.injEq, and_false, false_and, ne_eq, eq_self, reduceCtorEq,
            ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
            not_false_eq_true, not_true_eq_false, Nat.add_one_ne_zero, Nat.succ_ne_zero,
            Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub] at hwf hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | P_od d =>
        cases d with
        | stop cd d2 =>
          have h2 := Wd_ge_9 d2
          simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil] at hwf h2 ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | od cd m2 d2 =>
          have h2 := Wd_ge_9 d2
          simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil] at hwf h2 ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | sh cd m2 u2 =>
          have h2 := W0_ge_11 u2
          simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil] at hwf h2 ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | _ =>
          simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil,
            Tree.endOne.injEq] at hwf ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, W_rv, W_ra_tree, mk_sh, S_tree, W0,
        evenCeil] at hwf hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      have hd := Wd_ge_9 d
      cases d <;> simp only [WF_rv, app_1_odd, S_rv, W_rv, W_ra_od, S_tree, Wd,
        evenCeil] at hwf hd ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

set_option maxHeartbeats 8000000 in
-- Large case-splitting `simp`/`omega` proof over `RVal` constructors requires extra heartbeats.
theorem bump_ra_bounds {rv2 : RVal} (hwf2 : WF_rv rv2)
    (hnotD : ∀ p, rv2 ≠ .R_D p)
    (hnotBad : rv2 ≠ .R_F 0 (.P_tree (.endZero 1)) ∧ rv2 ≠ .R_F 0 (.P_tree (.endOne 2))) :
    NotBadRD (bump_ra rv2) ∧
    W_rv (bump_ra rv2) ≤ W_rv rv2 + 2 ∧
    S_rv (bump_ra rv2) ≤ S_rv rv2 ∧
    (∀ M, W_rv (app_1_odd M (bump_ra rv2)) ≤ 2 * M + 4 + W_rv rv2 ∧
          S_rv (app_1_odd M (bump_ra rv2)) ≤ max 24 (evenCeil (W_rv rv2 + 9))) := by
  cases rv2 with
  | R_D p => exact absurd rfl (hnotD p)
  | R_F m p =>
    cases m with
    | zero =>
      cases p with
      | P_od d => cases hwf2
      | P_tree u =>
        rcases hnotBad with ⟨hnez, hneo⟩
        have hw := W0_ge_11 u
        refine ⟨by simp [bump_ra, NotBadRD], ?_, ?_, ?_⟩
        · cases u <;> simp only [WF_rv, WF_u, bump_ra, W_rv, mk_stop, mk_sh, sub_c, set_c, tree_c,
          W0_lin, W0, Wd, Tree.endZero.injEq, Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq,
            ↓reduceIte, ite_true, ite_false, and_false, false_and, and_true, true_and,
            not_false_eq_true, not_true_eq_false, ne_eq, eq_self, Nat.reduceEqDiff,
            Nat.reduceLeDiff, zero_add, add_zero, RVal.R_F.injEq, Payload.P_tree.injEq, or_false,
              false_or, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff,
              Nat.reduceSub] at hwf2 hnez hneo hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · cases u <;> simp only [WF_rv, WF_u, bump_ra, S_rv, mk_stop, mk_sh, sub_c, set_c, tree_c,
          S_tree, W0, Wd, Tree.endZero.injEq, Tree.endOne.injEq, ↓reduceIte, ite_true, ite_false,
            and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false, ne_eq,
            zero_add, add_zero] at hwf2 hnez hneo hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · intro M
          constructor
          · cases u <;> simp only [WF_rv, WF_u, bump_ra, app_1_odd, W_rv, W_ra_tree, mk_stop, sub_c,
            set_c, tree_c, W0_lin, W0, Wd, Tree.endZero.injEq, Tree.endStop.injEq,
              Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, not_false_eq_true,
              not_true_eq_false, ne_eq, eq_self, Nat.reduceLeDiff, zero_add,
              add_zero, RVal.R_F.injEq, Payload.P_tree.injEq, and_false, false_and, and_true,
                true_and, or_false, false_or, Nat.add_one_ne_zero, Nat.succ_ne_zero,
                Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at hwf2 hnez hneo hw ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
          · cases u <;> simp only [WF_rv, WF_u, bump_ra, app_1_odd, S_rv, S_ra_tree, W_rv, mk_stop,
            sub_c, set_c, tree_c, W0_lin, W0, Wd, evenCeil, Tree.endZero.injEq, Tree.endStop.injEq,
              Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, not_false_eq_true,
              not_true_eq_false, ne_eq, eq_self, Nat.reduceLeDiff] at hwf2 hnez hneo hw ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
    | succ m =>
      cases p with
      | P_tree u =>
        have hw := W0_ge_11 u
        refine ⟨by simp [bump_ra, NotBadRD], ?_, ?_, ?_⟩
        · cases u <;> simp only [WF_rv, WF_u, bump_ra, W_rv, mk_sh, W0_lin, W0, Tree.endStop.injEq,
          and_false, false_and, not_false_eq_true, not_true_eq_false, ne_eq,
          Nat.reduceLeDiff, reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_true, true_and,
            or_false, false_or, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
            Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at hwf2 hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · cases u <;> simp only [WF_rv, WF_u, bump_ra, S_rv, mk_sh, S_tree, W0, Tree.endStop.injEq,
          and_false, false_and, ne_eq, zero_add, add_zero, reduceCtorEq, ↓reduceIte, ite_true,
            ite_false, and_true, true_and, or_false, false_or, not_false_eq_true,
            not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff,
            Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub] at hwf2 hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · intro M
          constructor
          · cases u <;> simp only [WF_rv, WF_u, bump_ra, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin,
            W0, Tree.endStop.injEq, and_false, false_and, ne_eq, Nat.reduceLeDiff, reduceCtorEq,
              ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
              not_false_eq_true, not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
              Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at hwf2 hw ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
          · cases u <;> simp only [WF_rv, WF_u, bump_ra, app_1_odd, S_rv, S_ra_tree, W_rv, mk_sh,
            W0_lin, W0, evenCeil, Tree.endStop.injEq, and_false, false_and, ne_eq, reduceCtorEq,
              ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
              not_false_eq_true, not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
              Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub] at hwf2 hw ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
      | P_od d =>
        have hd := Wd_ge_9 d
        refine ⟨by simp [bump_ra, NotBadRD], ?_, ?_, ?_⟩
        · simp only [bump_ra, W_rv]
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · simp [bump_ra, S_rv, S_tree]
        · intro M
          constructor
          · cases d <;> simp only [WF_rv, bump_ra, app_1_odd, W_rv, W_ra_od, Wd, Tree.endOne.injEq,
            ne_eq, Nat.reduceLeDiff] at hwf2 hd ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
          · cases d with
            | stop cd d2 =>
              have h2 := Wd_ge_9 d2
              simp only [WF_rv, bump_ra, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd,
                evenCeil] at hwf2 h2 ⊢
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0, Wd] at *)
              all_goals (try split_ifs)
              all_goals (try exact not_false)
              all_goals (try omega)
            | od cd m2 d2 =>
              have h2 := Wd_ge_9 d2
              simp only [WF_rv, bump_ra, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd,
                evenCeil] at hwf2 h2 ⊢
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0, Wd] at *)
              all_goals (try split_ifs)
              all_goals (try exact not_false)
              all_goals (try omega)
            | sh cd m2 u2 =>
              have h2 := W0_ge_11 u2
              simp only [WF_rv, bump_ra, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd,
                evenCeil] at hwf2 h2 ⊢
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0, Wd] at *)
              all_goals (try split_ifs)
              all_goals (try exact not_false)
              all_goals (try omega)
            | _ =>
              simp only [WF_rv, bump_ra, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd,
                evenCeil, Tree.endOne.injEq, ne_eq] at hwf2 ⊢
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
              all_goals (try split_ifs at * )
              all_goals (try dsimp only [W0, Wd] at *)
              all_goals (try split_ifs)
              all_goals (try exact not_false)
              all_goals (try omega)
  | R_A m p =>
    cases p with
    | P_tree w =>
      have hw := W0_ge_11 w
      refine ⟨by simp [bump_ra, NotBadRD], ?_, ?_, ?_⟩
      · cases w <;> simp only [bump_ra, W_rv, W_ra_tree]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      · simp [bump_ra, S_rv, S_ra_tree]
      · intro M
        constructor
        · cases w <;> simp only [WF_rv, WF_u, bump_ra, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin,
          W0] at hwf2 hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · cases w <;> simp only [WF_rv, WF_u, bump_ra, app_1_odd, S_rv, W_rv, W_ra_tree, mk_sh,
          S_tree,
          W0, evenCeil] at hwf2 hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
    | P_od d =>
      have hd := Wd_ge_9 d
      refine ⟨by simp [bump_ra, NotBadRD], ?_, ?_, ?_⟩
      · cases d <;> simp only [bump_ra, W_rv, W_ra_od]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      · simp [bump_ra, S_rv]
      · intro M
        constructor
        · cases d <;> simp only [WF_rv, bump_ra, app_1_odd, W_rv, W_ra_od, Wd, Tree.endOne.injEq,
          ne_eq, Nat.reduceLeDiff] at hwf2 hd ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · cases d <;> simp only [WF_rv, bump_ra, app_1_odd, S_rv, W_rv, W_ra_od, S_tree, Wd,
          evenCeil] at hwf2 hd ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)

theorem bump_ra_app_1_odd (m : Nat) (rv0 : RVal) :
    bump_ra (app_1_odd m rv0) = app_1_odd (m + 1) rv0 := by
  cases rv0 <;> simp only [app_1_odd, bump_ra, RVal.R_A.injEq, true_and, and_true, ne_eq,
    RVal.R_F.injEq] ; all_goals (try omega)

theorem evenCeil_mono {x y : Nat} (h : x ≤ y) : evenCeil x ≤ evenCeil y := by
  unfold evenCeil; (try omega)

theorem evenCeil_ge (x : Nat) : evenCeil x ≥ x := by
  unfold evenCeil; (try omega)

theorem goodRV_of_odd (m : Nat) {rv0 : RVal}
    (hnb : m = 0 → rv0 ≠ .R_D (.P_tree (.endZero 1))) :
    GoodRV (app_1_odd m rv0) := by
  cases rv0 with
  | R_D p =>
    cases m with
    | zero =>
      cases p with
      | P_od d => simp [app_1_odd, GoodRV]
      | P_tree t =>
        cases t with
        | endZero c =>
          by_cases hc : c = 1
          · subst hc; exact absurd rfl (hnb rfl)
          · simp [app_1_odd, GoodRV, hc]
        | _ => simp [app_1_odd, GoodRV]
    | succ m => simp [app_1_odd, GoodRV]
  | R_F m0 p => simp [app_1_odd, GoodRV]
  | R_A m0 p => simp [app_1_odd, GoodRV]

theorem notBadRD_app_1_odd (m : Nat) (rv0 : RVal) : NotBadRD (app_1_odd m rv0) := by
  cases rv0 <;> simp [app_1_odd, NotBadRD]

theorem odd_of_app_1_odd_pos (M m : Nat) {rv0 : RVal} (hwf0 : WF_rv rv0) :
    W_rv (app_1_odd M (app_1_odd (m + 1) rv0)) ≤ 2 * M + 2 + W_rv (app_1_odd (m + 1) rv0) ∧
    (∀ p_od, rv0 ≠ .R_D (.P_od p_od) →
      (∀ d, rv0 = .R_A 0 (.P_od d) → False) →
      True) := by
  refine ⟨?_, fun _ _ _ => trivial⟩
  cases rv0 with
  | R_D p =>
    cases p with
    | P_od d => cases hwf0
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0,
        Tree.endStop.injEq, and_false, false_and, ne_eq, Nat.reduceLeDiff, reduceCtorEq,
          ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
          not_false_eq_true, not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
          Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at hwf0 hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | R_F m0 p =>
    cases m0 with
    | zero =>
      cases p with
      | P_od d => cases hwf0
      | P_tree u =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin,
          W0] at hwf0 hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    | succ m0 =>
      cases p with
      | P_tree u =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin,
          W0] at hwf0 hw ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | P_od d =>
        cases d <;> simp only [WF_rv, app_1_odd, W_rv, W_ra_od, Wd, Tree.endOne.injEq,
          Nat.reduceLeDiff] at hwf0 ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin,
        W0] at hwf0 hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      cases d <;> simp only [WF_rv, app_1_odd, W_rv, W_ra_od, Wd, Tree.endOne.injEq,
        Nat.reduceLeDiff] at hwf0 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem notBad_of_odd (m : Nat) {rv0 : RVal}
    (hnb : m = 0 → NotBadRD rv0) :
    app_1_odd m rv0 ≠ .R_F 0 (.P_tree (.endZero 1)) ∧
    app_1_odd m rv0 ≠ .R_F 0 (.P_tree (.endOne 2)) := by
  cases rv0 with
  | R_D p =>
    cases m with
    | zero =>
      rcases hnb rfl with ⟨h1, h2⟩
      simp only [app_1_odd, RVal.R_D.injEq, true_and, and_true, ne_eq, RVal.R_F.injEq, eq_self,
        Nat.reduceEqDiff]
      exact ⟨fun he => h1 (by rw [he]), fun he => h2 (by rw [he])⟩
    | succ m => simp [app_1_odd]
  | R_F m0 p => simp [app_1_odd]
  | R_A m0 p => simp [app_1_odd]

theorem W_safe_ge_W_rv {rv : RVal} : W_rv rv ≤ W_safe rv := by
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => rfl
    | P_tree t =>
        cases t <;> simp only [W_safe, W_rv, W0_lin, W0]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_F m p =>
    cases p with
    | P_od d => rfl
    | P_tree t =>
      cases m <;> cases t <;> simp only [W_safe, W_rv, mk_stop, mk_sh, sub_c, set_c, tree_c,
        W0_lin, W0, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_false,
        false_and, and_true, true_and, not_false_eq_true, not_true_eq_false, Nat.reduceLeDiff]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | R_A m p =>
    cases p with
    | P_tree t => rfl
    | P_od d =>
        cases d <;> simp only [W_safe, W_rv, W_ra_od]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)

theorem W_safe_app_1_even_pos (m : Nat) {rv : RVal} (hwf : WF_rv rv) :
    W_safe (app_1_even (m + 1) rv) ≤ 2 * (m + 1) + 2 + W_rv rv := by
  have he := W_rv_app_1_even_le (m + 1) hwf
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree u =>
      cases u <;> simp only [app_1_even, W_safe, W_rv, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.reduceEqDiff,
        Nat.succ_eq_add_one] at he ⊢ ; all_goals (try omega)
  | R_F m0 p =>
    cases m0 with
    | zero =>
      cases p with
      | P_od d => cases hwf
      | P_tree u =>
        have hsub := Wd_sub_c_one_le hwf
        cases u <;> simp only [WF_rv, WF_u, app_1_even, W_safe, W_rv, mk_stop, mk_sh, sub_c, set_c,
          tree_c, W0_lin, W0, Wd, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
            and_false, false_and, not_false_eq_true, not_true_eq_false,
            Nat.reduceLeDiff] at hwf hsub he ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    | succ m0 =>
      cases p with
      | P_tree u =>
        cases u <;> simp only [app_1_even, show m + 1 + (m0 + 1) = m + m0 + 2 by omega, W_safe,
          and_false, false_and, not_false_eq_true, not_true_eq_false, Nat.reduceLeDiff,
            reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
            eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
            Nat.reduceSub] at he ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | P_od d =>
        simp only [app_1_even, show m + 1 + (m0 + 1) = m + m0 + 2 by omega, W_safe, ↓reduceIte,
          ite_true, ite_false, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.reduceEqDiff,
          Nat.succ_eq_add_one] at he ⊢; (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree w => simp only [app_1_even, W_safe, ↓reduceIte, ite_true, ite_false,
      Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.reduceEqDiff,
      Nat.succ_eq_add_one] at he ⊢; (try omega)
    | P_od d =>
      cases d <;> simp only [app_1_even, show m + 1 + m0 = (m + m0) + 1 by omega, W_safe,
        ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero, Nat.succ_ne_zero,
        Nat.reduceEqDiff] at he ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem W_safe_app_1_odd_le_4 (M : Nat) {rv : RVal} (hwf : WF_rv rv)
    (hnf0 : ∀ p, rv ≠ .R_F 0 p) (hne2 : rv ≠ .R_D (.P_tree (.endOne 2))) :
    W_safe (app_1_odd M rv) ≤ 2 * M + 4 + W_rv rv := by
  have ho := W_rv_app_1_odd_le_4 M hwf
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree u =>
      cases M with
      | zero =>
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_safe, W_rv, W0_lin, W0,
          Tree.endStop.injEq, and_false, false_and, not_false_eq_true, not_true_eq_false, ne_eq,
          Nat.reduceLeDiff, zero_add, add_zero, RVal.R_D.injEq, Payload.P_tree.injEq,
            Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_true, true_and,
            or_false, false_or, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
            Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at hwf hne2 ho ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | succ M =>
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_safe, W_rv, W0_lin, W0] at hwf ho ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_F m0 p =>
    cases m0 with
    | zero => exact absurd rfl (hnf0 p)
    | succ m0 =>
      cases p with
      | P_tree u => simp only [app_1_odd, W_safe] at ho ⊢; (try omega)
      | P_od d =>
        cases d <;> simp only [app_1_odd, show M + (m0 + 1) = (M + m0) + 1 by omega, W_safe] at ho ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u =>
      cases u <;> simp only [app_1_odd, W_safe, W_rv, W_ra_tree, W0] at ho ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      simp only [app_1_odd, W_safe] at ho ⊢; (try omega)

theorem odd_wsafe_of_app_1_odd_pos (M m : Nat) {rv0 : RVal} (hwf0 : WF_rv rv0) :
    W_safe (app_1_odd M (app_1_odd (m + 1) rv0)) ≤ 2 * M + 2 + W_rv (app_1_odd (m + 1) rv0) := by
  have ho := (odd_of_app_1_odd_pos M m hwf0).1
  cases rv0 with
  | R_D p =>
    cases p with
    | P_od d => cases hwf0
    | P_tree u =>
      cases u <;> simp only [app_1_odd, W_safe] at ho ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | R_F m0 p =>
    cases p with
    | P_tree u =>
      cases u <;> simp only [app_1_odd, W_safe, and_false, false_and, Nat.reduceLeDiff,
        reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
        not_false_eq_true, not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceSub] at ho ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      simp only [app_1_odd, W_safe] at ho ⊢; (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u => simp only [app_1_odd, W_safe] at ho ⊢; (try omega)
    | P_od d =>
      cases d <;> simp only [app_1_odd, W_safe] at ho ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem W_safe_bump_ra_odd (m : Nat) {rv0 : RVal} (hwf0 : WF_rv rv0)
    (hnb0 : m = 0 → NotBadRD rv0) :
    W_safe (bump_ra (app_1_odd m rv0)) ≤ W_rv (app_1_odd m rv0) + 2 := by
  have hwf2 := WF_rv_app_1_odd m hwf0
  have hnd2 := app_1_odd_ne_RD m rv0
  have hnb2 := notBad_of_odd m hnb0
  have hb := (bump_ra_bounds hwf2 hnd2 hnb2).2.1
  rw [bump_ra_app_1_odd] at hb ⊢
  cases rv0 with
  | R_D p =>
    cases p with
    | P_od d => cases hwf0
    | P_tree u =>
      cases m with
      | zero =>
        rcases hnb0 rfl with ⟨h1, h2⟩
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, W_safe, W_rv, mk_stop, sub_c, set_c, tree_c,
          W0_lin, W0, Wd, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
            and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false, ne_eq,
            eq_self, Nat.reduceEqDiff] at hwf0 h1 h2 hw hb ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | succ m =>
        cases u <;> simp only [app_1_odd, W_safe, and_false, false_and, ne_eq, reduceCtorEq,
          ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or,
          not_false_eq_true, not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero,
          Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub] at hb ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_F m0 p =>
    cases p with
    | P_tree u => simp only [app_1_odd, W_safe] at hb ⊢; (try omega)
    | P_od d =>
      cases d <;> simp only [app_1_odd, W_safe] at hb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u =>
      cases u <;> simp only [app_1_odd, W_safe, and_false, false_and, ne_eq, reduceCtorEq,
        ↓reduceIte, ite_true, ite_false, and_true, true_and, or_false, false_or, not_false_eq_true,
        not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff,
        Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub] at hb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      simp only [app_1_odd, W_safe] at hb ⊢; (try omega)

theorem not_badRV_of_W_safe_le (rem M : Nat) {rv : RVal} (hwf : WF_rv rv)
    (hnf0 : ∀ p, rv ≠ .R_F 0 p) (hrem : rem ≥ 1) (hsafe : W_safe rv ≤ 2 * rem + 13) :
    ¬ BadRV rem (app_1_odd M rv) := by
  have hrem0 : rem ≠ 0 := by omega
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree u =>
      have hw := W0_ge_11 u
      cases M with
      | zero =>
        cases u with
        | stop c d2 =>
          have hd9 := Wd_ge_9 d2
          cases d2 <;> simp [WF_rv, WF_u, app_1_odd, BadRV, hrem0, BadRoot, mk_stop, sub_c, set_c,
            tree_c, W_safe, W_rv, W0_lin, W0] at hwf hw hd9 hsafe ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | od c m2 d2 =>
          have hd9 := Wd_ge_9 d2
          simp [WF_rv, WF_u, app_1_odd, BadRV, hrem0, BadRoot, mk_stop, sub_c, set_c, tree_c,
            W_safe, W_rv, W0_lin, W0] at hwf hw hd9 hsafe ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | sh c m2 u2 =>
          have hu11 := W0_ge_11 u2
          simp [WF_rv, WF_u, app_1_odd, BadRV, hrem0, BadRoot, mk_stop, sub_c, set_c, tree_c,
            W_safe, W_rv, W0_lin, W0] at hwf hw hu11 hsafe ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | _ =>
          simp only [WF_rv, WF_u, app_1_odd, BadRV, hrem0, BadRoot, mk_stop, sub_c, set_c, tree_c,
            W_safe, W_rv, W0_lin, W0, Tree.endOne.injEq, ↓reduceIte, ite_true, ite_false,
              not_false_eq_true, not_true_eq_false, ne_eq, Nat.reduceLeDiff] at hwf hsafe ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
      | succ M =>
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, BadRV, hrem0, BadRoot, mk_sh, W_safe, W_rv,
          W0_lin, W0] at hwf hw hsafe ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_F m0 p =>
    cases m0 with
    | zero => exact absurd rfl (hnf0 p)
    | succ m0 =>
      cases p with
      | P_tree u =>
        have hw := W0_ge_11 u
        cases u <;> simp only [WF_rv, WF_u, app_1_odd, BadRV, hrem0, mk_sh, W_safe, W_rv, W0_lin,
          W0, Tree.endStop.injEq, and_false, false_and, not_false_eq_true, not_true_eq_false,
            ne_eq, eq_self, Nat.reduceEqDiff, Nat.reduceLeDiff, reduceCtorEq, ↓reduceIte, ite_true,
              ite_false, and_true, true_and, or_false, false_or, Nat.add_one_ne_zero,
              Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceSub] at hwf hw hsafe ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | P_od d =>
        have hd9 := Wd_ge_9 d
        cases d <;> simp only [WF_rv, app_1_odd, BadRV, hrem0, W_safe, W_rv, Wd, and_false,
          false_and, not_false_eq_true, not_true_eq_false, ne_eq, reduceCtorEq, ↓reduceIte,
            ite_true, ite_false, and_true, true_and, or_false, false_or, eq_self,
            Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
            Nat.reduceLeDiff, Nat.reduceSub] at hwf hd9 hsafe ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, BadRV, hrem0, BadRoot, mk_sh, W_safe, W_rv,
        W_ra_tree, W0] at hwf hw hsafe ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      have hd9 := Wd_ge_9 d
      cases d with
      | stop cd d2 =>
        have h2 := Wd_ge_9 d2
        cases d2 <;> simp only [WF_rv, app_1_odd, BadRV, hrem0, BadRoot, W_safe, W_rv, W_ra_od,
          Wd] at hwf hd9 h2 hsafe ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | _ =>
        simp only [WF_rv, app_1_odd, BadRV, hrem0, BadRoot, W_safe, W_rv, W_ra_od,
          Wd] at hwf hd9 hsafe ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)

/-! ### 9. Inductive Predicates `PostU`, `PostD0`, `PostRV` and Iteration Lemmas -/

def PostRV (rv rvn : RVal) : Prop :=
  (∀ r, SweepRV r rv → SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) rvn) ∧
  WF_rv rvn ∧
  NotBadRD rvn ∧
  (∀ p, rvn ≠ .R_F 0 p) ∧
  W_rv rvn ≤ W_rv rv + 2 ∧
  W_safe rvn ≤ W_safe rv + 2 ∧
  S_rv rvn ≤ S_rv rv - 2 ∧
  (∀ rem, S_rv rv ≤ 20 + 2 * (rem + 1) → ¬ BadRV (rem + 1) rv → ¬ BadRV rem rvn) ∧
  (GoodRV rv → GoodRV rvn) ∧
  (GoodRV rv → ∀ M,
    W_rv (app_1_odd M rvn) ≤ 2 * M + 4 + W_rv rv ∧
    W_safe (app_1_odd M rvn) ≤ 2 * M + 4 + W_rv rv ∧
    S_rv (app_1_odd M rvn) ≤ max 24 (evenCeil (W_rv rv + 9)))

def PostU (u : Tree) : Prop :=
  ∃ rv, SweepRV (evalT u) rv ∧
    WF_rv rv ∧
    (u ≠ .endStop 1 → NotBadRD rv) ∧
    (∀ p, rv ≠ .R_F 0 p) ∧
    W_rv rv ≤ W0 u + 2 ∧
    W_safe rv ≤ (if isLeaf u then W0 u + 4 else W0 u + 2) ∧
    (∀ m, ¬(m = 0 ∧ u = .endStop 1) →
      W_rv (app_1_odd m rv) ≤ 2 * m + 4 + W0 u ∧
      W_safe (app_1_odd m rv) ≤ 2 * m + 4 + W0 u ∧
      S_rv (app_1_odd m rv) ≤ max 24 (evenCeil (W0 u + 9))) ∧
    (∀ c m, (if isLeaf u then c ≥ 2 else c ≥ 1) → ¬(m = 0 ∧ u = .endStop 1) →
      W0 u ≤ 2 * c + 11 → ¬ BadRoot (.sh c m u) → ¬ BadRV c (app_1_odd m rv)) ∧
    (WF_r u → ∃ tn, rv = .R_D (.P_tree tn) ∧ WF_r tn)

def PostD0 (d0 : Tree) : Prop :=
  ∃ rv, SweepRV ((0 : Fin 2) >> evalT d0) rv ∧
    WF_rv rv ∧
    NotBadRD rv ∧
    (d0 ≠ .endStop 0 → W_rv rv ≤ Wd d0 + 4 ∧ W_safe rv ≤ Wd d0 + 6) ∧
    (∀ m2, W_rv (app_1_even m2 rv) ≤ 2 * m2 + 6 + Wd d0 ∧
           W_safe (app_1_even m2 rv) ≤ 2 * m2 + 6 + Wd d0) ∧
    (∀ cd m, let df := set_c cd d0
      W_rv (app_1_odd (m + 2 * cd) rv) ≤ 2 * m + 2 * cd + 6 + Wd df ∧
      W_safe (app_1_odd (m + 2 * cd) rv) ≤ 2 * m + 2 * cd + 6 + Wd df ∧
      S_rv (app_1_odd (m + 2 * cd) rv) ≤
        max (if df = .endZero 1 then 26 - 2 * cd else max 20 (24 - 2 * cd))
            (evenCeil (Wd df + 11 + stopOnePosBonus df - 2 * cd)) ∧
      (∀ rem, rem ≥ 1 → cd + rem ≥ 2 →
        Wd df + stopOnePosBonus df ≤ 2 * (cd + rem) + 9 →
        ¬ BadRoot (.od (cd + rem) m df) → ¬ BadRV rem (app_1_odd (m + 2 * cd) rv)))

theorem S_rv_RD_of_le_20 {rv : RVal} (hwf : WF_rv rv) (hs : S_rv rv ≤ 20) (hnb0 : ¬ BadRV 0 rv) :
    ∃ tn, rv = .R_D (.P_tree tn) ∧ WF_r tn := by
  cases rv with
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree tn =>
      refine ⟨tn, rfl, ⟨?_, by simpa [BadRV] using hnb0⟩⟩
      have h0 := S_tree_iff_WF_r_core 0 hwf
      have had : add_c 0 tn = tn := by cases tn <;> simp [add_c, set_c, tree_c]
      rw [had] at h0
      exact h0.mpr (by simpa [S_rv] using hs)
  | R_F m p =>
    cases m <;> cases p <;> simp [S_rv] at hs
  | R_A m p =>
    cases p with
    | P_tree w =>
      cases w <;> simp [S_rv, S_ra_tree] at hs ; all_goals (try omega)
    | P_od d =>
      cases d <;> simp [S_rv, S_ra_od] at hs ; all_goals (try omega)

theorem iter_app_01_pos (k B : Nat)
    (ih_step : ∀ rv', WF_rv rv' → W_rv rv' ≤ B → ∃ rvn, PostRV rv' rvn)
    {r : ListBlank (Fin 2)} {rv : RVal}
    (hsw : SweepRV r rv) (hwf : WF_rv rv) (hgood : GoodRV rv)
    (hw : W_rv rv + 2 * k ≤ B) :
    ∃ rvf, SweepRV ((([0, 1] : List (Fin 2)) ^ (k + 1)) +> r) rvf ∧
      WF_rv rvf ∧ NotBadRD rvf ∧ (∀ p, rvf ≠ .R_F 0 p) ∧ GoodRV rvf ∧
      W_rv rvf ≤ W_rv rv + 2 * (k + 1) ∧
      W_safe rvf ≤ W_safe rv + 2 * (k + 1) ∧
      S_rv rvf ≤ S_rv rv - 2 * (k + 1) ∧
      (S_rv rv ≤ 20 + 2 * (k + 1) → ¬ BadRV (k + 1) rv → ¬ BadRV 0 rvf) ∧
      (∀ M, W_rv (app_1_odd M rvf) ≤ 2 * M + 4 + W_rv rv + 2 * k ∧
            W_safe (app_1_odd M rvf) ≤ 2 * M + 4 + W_rv rv + 2 * k ∧
            S_rv (app_1_odd M rvf) ≤ max 24 (evenCeil (W_rv rv + 2 * k + 9))) := by
  induction k generalizing r rv with
  | zero =>
    obtain ⟨rv1, hstep1, hwf1, hnb1, hnf1, hw1, hws1, hs1, hbad1, hgood1, hodd1⟩ :=
      ih_step rv hwf (by omega)
    refine ⟨rv1, ?_, hwf1, hnb1, hnf1, hgood1 hgood, by omega, by omega, by omega,
      fun hs hnb => hbad1 0 (by omega) hnb, ?_⟩
    · simpa [list_pow_one, ListBlank.append_cons, ListBlank.append_nil] using hstep1 r hsw
    · intro M
      obtain ⟨how, hows, hos⟩ := hodd1 hgood M
      exact ⟨by omega, by omega, by simpa using hos⟩
  | succ k ih =>
    obtain ⟨rv1, hstep1, hwf1, _, _, hw1, hws1, hs1, hbad1, hgood1, _⟩ :=
      ih_step rv hwf (by omega)
    have hsw1 := hstep1 r hsw
    obtain ⟨rvf, hswf, hwff, hnbf, hnff, hgoodf, hwf_w, hwf_ws, hwf_s, hbad_f, hodd_f⟩ :=
      ih hsw1 hwf1 (hgood1 hgood) (by omega)
    refine ⟨rvf, ?_, hwff, hnbf, hnff, hgoodf, by omega, by omega, by omega, ?_, ?_⟩
    · rw [list_pow_succ', ListBlank.append_assoc]
      simpa [ListBlank.append_cons, ListBlank.append_nil] using hswf
    · intro hs hnb
      exact hbad_f (by omega) (hbad1 (k + 1) (by omega) hnb)
    · intro M
      obtain ⟨how, hows, hos⟩ := hodd_f M
      refine ⟨by omega, by omega, ?_⟩
      exact le_trans hos (max_le (le_max_left _ _) (le_trans (evenCeil_mono (by omega))
        (le_max_right _ _)))

/-! ### 10. Base Leaf / `stop` Proofs of `PostU` and `PostD0` -/

theorem postU_endZero (c : Nat) (hc : c ≥ 1) : PostU (.endZero c) := by
  refine ⟨.R_D (.P_tree (.endStop c)), sweep_u_endZero c hc, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WF_rv, WF_u]; (try omega)
  · intro _; simp [NotBadRD]
  · simp only [W_rv, W0_lin, W0]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · simp only [isLeaf, W_safe, W_rv, W0_lin, W0]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · intro m _
    cases m with
    | zero =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, W0_lin, W0,
        Wd,
        evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_sh, S_tree, W0_lin, W0, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' m hc' _ hw0 hnbr
    simp only [isLeaf, Bool.false_eq_true, ↓reduceIte] at hc'
    cases m with
    | zero =>
      simp [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_stop, sub_c, set_c, tree_c,
        W0] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_sh, W0] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro _
    exact ⟨.endStop c, rfl, ⟨by
      simp only [WF_r_core, WF_u, and_true, true_and]; (try omega), by simp [BadRoot]⟩⟩

theorem postU_endStop (c : Nat) (hc : c ≥ 1) : PostU (.endStop c) := by
  refine ⟨.R_D (.P_tree (.endOne (c + 1))), sweep_u_endStop c hc, ?_, ?_, by simp, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp only [WF_rv, WF_u, and_true, true_and]; (try omega)
  · intro hne
    have hc2 : c ≥ 2 := by
      by_contra hlt; apply hne; congr; (try omega)
    simp only [NotBadRD, ne_eq, RVal.R_D.injEq, Payload.P_tree.injEq, Tree.endOne.injEq,
      reduceCtorEq, not_false_eq_true, true_and]; (try omega)
  · simp only [W_rv, W0_lin, W0, ne_eq]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · simp only [isLeaf, W_safe, W0]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · intro m hm
    cases m with
    | zero =>
      have hc2 : c ≥ 2 := by
        by_contra hlt; apply hm; exact ⟨rfl, by congr; (try omega)⟩
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, W0_lin, W0,
        Wd,
        evenCeil, Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true,
          ite_false, and_true, true_and, not_false_eq_true, not_true_eq_false, eq_self,
          Nat.reduceEqDiff, Nat.reduceLeDiff, zero_add, add_zero]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_sh, S_tree, W0_lin, W0, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' m hc' hm hw0 hnbr
    simp only [isLeaf, Bool.false_eq_true, ↓reduceIte] at hc'
    cases m with
    | zero =>
      have hc2 : c ≥ 2 := by
        by_contra hlt; apply hm; exact ⟨rfl, by congr; (try omega)⟩
      simp only [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_stop, sub_c, set_c, tree_c,
        W0, Tree.endStop.injEq, Tree.endOne.injEq, ↓reduceIte, ite_true, ite_false,
          not_false_eq_true, not_true_eq_false, eq_self, Nat.reduceEqDiff] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_sh, W0] at hw0 hnbr ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro _
    exact ⟨.endOne (c + 1), rfl, ⟨by simp only [WF_r_core, WF_u, and_true, true_and]; (try omega),
      by simp [BadRoot]⟩⟩

theorem postU_endOne (c : Nat) (hc : c ≥ 2) : PostU (.endOne c) := by
  refine ⟨.R_D (.P_tree (.oneEnd c)), sweep_u_endOne c hc, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WF_rv, WF_u, and_true, true_and]; (try omega)
  · intro _; simp [NotBadRD]
  · simp [W_rv, W0_lin, W0]; (try omega)
  · simp [isLeaf, W_safe, W0]; (try omega)
  · intro m _
    cases m with
    | zero =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, W0_lin, W0,
        Wd,
        evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_sh, S_tree, W0_lin, W0, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' m hc' _ hw0 hnbr
    simp only [isLeaf, Bool.false_eq_true, ↓reduceIte] at hc'
    cases m with
    | zero =>
      simp [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_stop, sub_c, set_c, tree_c,
        W0] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_sh, W0, reduceCtorEq,
        ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero, Nat.succ_ne_zero, and_false,
        false_and, eq_self, Nat.reduceEqDiff, Nat.reduceLeDiff] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro _
    exact ⟨.oneEnd c, rfl, ⟨by
      simp only [WF_r_core, WF_u, and_true, true_and]; (try omega), by simp [BadRoot]⟩⟩

theorem postU_oneEnd (c : Nat) (hc : c ≥ 2) : PostU (.oneEnd c) := by
  refine ⟨.R_D (.P_tree (.stopOne c)), sweep_u_oneEnd c hc, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WF_rv, WF_u, and_true, true_and]; (try omega)
  · intro _; simp [NotBadRD]
  · simp [W_rv, W0_lin, W0]; (try omega)
  · simp only [isLeaf, W_safe, W0]
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · intro m _
    cases m with
    | zero =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, W0_lin, W0,
        Wd,
        evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_sh, S_tree, W0_lin, W0, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' m hc' _ hw0 hnbr
    simp only [isLeaf, Bool.false_eq_true, ↓reduceIte] at hc'
    cases m with
    | zero =>
      simp only [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_stop, sub_c, set_c, tree_c,
        W0, reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_true, true_and, not_false_eq_true,
          not_true_eq_false, eq_self, Nat.reduceEqDiff, Nat.reduceLeDiff] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp [app_1_odd, BadRV, show c' ≠ 0 by omega, BadRoot, mk_sh, W0] at hw0 hnbr ⊢
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro _; exact ⟨.stopOne c, rfl, ⟨by simp only [WF_r_core, WF_u]; (try omega),
    by simp [BadRoot]⟩⟩

theorem postU_stopOne (c : Nat) (hc : c ≥ 1) : PostU (.stopOne c) := by
  refine ⟨.R_D (.P_tree (.od (c + 1) 0 (.endOne 1))), sweep_u_stopOne c hc, ?_, ?_, by simp, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp only [WF_rv, WF_u, WF_d, and_true, true_and]; (try omega)
  · intro _; simp [NotBadRD]
  · simp only [W_rv, W0_lin, W0, Wd, and_true, true_and, reduceCtorEq, ↓reduceIte, ite_true,
    ite_false, Nat.reduceLeDiff, zero_add, add_zero]; (try omega)
  · simp only [isLeaf, W_safe, W_rv, W0_lin, W0, Wd, and_true, true_and, reduceCtorEq, ↓reduceIte,
    ite_true, ite_false, Nat.reduceLeDiff, zero_add, add_zero]; (try omega)
  · intro m _
    cases m with
    | zero =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, W0_lin, W0,
        Wd,
        stopOnePosBonus, evenCeil, reduceCtorEq, ↓reduceIte, ite_true, ite_false, Nat.reduceLeDiff,
          zero_add, add_zero]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_sh, S_tree, W0_lin, W0, Wd, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' m hc' _ hw0 hnbr
    simp [isLeaf] at hc'
    exact not_badRV_of_W_safe_le c' m
      (by
        simp only [WF_rv, WF_u, WF_d, reduceCtorEq, and_true, true_and]; (try omega)) (by simp)
      (by omega) (by simp only [W_safe, W_rv, W0_lin, W0, Wd, reduceCtorEq, and_true, true_and,
        ↓reduceIte, ite_true, ite_false, Nat.reduceLeDiff, zero_add,
        add_zero] at hw0 ⊢; (try omega))
  · intro hr
    rcases hr with ⟨hrc, _⟩
    refine ⟨.od (c + 1) 0 (.endOne 1), rfl, ⟨?_, by simp [BadRoot]⟩⟩
    simp only [WF_r_core, WF_u, WF_d, Wd, stopOnePosBonus, reduceCtorEq, and_true, true_and,
      ↓reduceIte, ite_true, ite_false, Nat.reduceLeDiff, zero_add, add_zero,
      eq_self] at hrc ⊢; (try omega)

theorem postU_stop (c : Nat) (d : Tree) (hwf : WF_u (.stop c d)) : PostU (.stop c d) := by
  rcases hwf with ⟨hc, hd0, hd1, hd⟩
  have hwd := Wd_ge_9 d
  have hwf_rv : WF_rv (.R_D (.P_tree (.od (c + 1) 0 d))) := ⟨by omega, hd⟩
  have hws_le : W_safe (.R_D (.P_tree (.od (c + 1) 0 d))) ≤ W0 (.stop c d) + 2 := by
    simp only [W_safe, W_rv, W0_lin, W0, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq,
      zero_add, add_zero]; (try omega)
  refine ⟨.R_D (.P_tree (.od (c + 1) 0 d)), sweep_u_stop c hc d, hwf_rv, ?_, by simp, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro _; simp [NotBadRD]
  · simp only [W_rv, W0_lin, W0, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq, zero_add,
    add_zero]; (try omega)
  · simpa [isLeaf] using hws_le
  · intro m _
    cases m with
    | zero =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, W0_lin, W0,
        Wd,
        stopOnePosBonus, evenCeil, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq, zero_add,
          add_zero]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | succ m =>
      simp only [app_1_odd, W_safe, W_rv, S_rv, mk_sh, S_tree, W0_lin, W0, Wd, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' m hc' _ hw0 _
    simp only [isLeaf] at hc'
    exact not_badRV_of_W_safe_le c' m hwf_rv (by simp) hc' (by omega)
  · intro hr
    rcases hr with ⟨⟨_, hc2, hwd_le⟩, hnbr⟩
    refine ⟨.od (c + 1) 0 d, rfl, ⟨⟨⟨by omega, hd⟩, ?_, ?_⟩, ?_⟩⟩
    · all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d <;> simp only [BadRoot, stopOnePosBonus, Wd] at hwd_le hnbr ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d with
      | stop cd d2 =>
        cases d2 <;> simp only [BadRoot] at hnbr ⊢ ; all_goals (try omega)
      | _ =>
        simp only [BadRoot] at hnbr ⊢; (try omega)

theorem postD0_endZero : PostD0 (.endZero 0) := by
  refine ⟨.R_F 0 (.P_tree (.endZero 1)), sweep_d0_endZero, ?_, ?_, ?_, ?_, ?_⟩
  · simp [WF_rv, WF_u]
  · simp [NotBadRD]
  · intro _; simp [W_safe, W_rv, Wd]
  · intro m2
    cases m2 <;> simp only [app_1_even, W_safe, W_rv, mk_sh, W0_lin, W0, Wd, Tree.endStop.injEq,
      reduceCtorEq, ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero, Nat.succ_ne_zero,
      Nat.reduceEqDiff, zero_add, add_zero, Nat.succ_eq_add_one, and_false, false_and, and_true,
        true_and, or_false, false_or, not_false_eq_true, not_true_eq_false, eq_self,
        Nat.add_eq_zero_iff, Nat.reduceLeDiff, Nat.reduceSub] ; all_goals (try omega)
  · intro cd m
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [set_c, app_1_odd, W_rv, W_ra_tree, Wd, Tree.endStop.injEq, reduceCtorEq,
      ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.reduceEqDiff,
      zero_add, add_zero, Nat.succ_eq_add_one]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [set_c, app_1_odd, W_safe, W_rv, W_ra_tree, Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [set_c, app_1_odd, S_rv, S_ra_tree, Wd, stopOnePosBonus, evenCeil,
      Tree.endZero.injEq, ↓reduceIte, ite_true, ite_false, zero_add, add_zero]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem _ _ _
      simp [app_1_odd, BadRV, show rem ≠ 0 by omega]

theorem postD0_endStop : PostD0 (.endStop 0) := by
  refine ⟨.R_F 0 (.P_tree (.endZero 2)), sweep_d0_endStop, ?_, ?_, ?_, ?_, ?_⟩
  · simp [WF_rv, WF_u]
  · simp [NotBadRD]
  · intro h; exact absurd rfl h
  · intro m2
    cases m2 <;> simp only [app_1_even, W_safe, W_rv, mk_stop, mk_sh, sub_c, set_c, tree_c, W0_lin,
      W0,
      Wd, Tree.endStop.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero,
        Nat.succ_ne_zero, Nat.reduceEqDiff, zero_add, add_zero, Nat.succ_eq_add_one,
          Tree.endZero.injEq, and_false, false_and, and_true, true_and, or_false, false_or,
          not_false_eq_true, not_true_eq_false, eq_self, Nat.add_eq_zero_iff, Nat.reduceLeDiff,
          Nat.reduceSub]
    all_goals (try omega)
  · intro cd m
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [set_c, app_1_odd, W_rv, W_ra_tree, Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [set_c, app_1_odd, W_safe, W_rv, W_ra_tree, Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [set_c, app_1_odd, S_rv, S_ra_tree, Wd, stopOnePosBonus, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem _ _ _
      simp [app_1_odd, BadRV, show rem ≠ 0 by omega]

theorem postD0_endOne : PostD0 (.endOne 0) := by
  refine ⟨.R_D (.P_tree (.endStop 1)), sweep_d0_endOne, ?_, ?_, ?_, ?_, ?_⟩
  · simp [WF_rv, WF_u]
  · simp [NotBadRD]
  · intro _; simp [W_safe, W_rv, W0_lin, Wd]
  · intro m2
    cases m2 <;> simp [app_1_even, W_safe, W_rv, W_ra_tree, W0_lin, Wd] ; all_goals (try omega)
  · intro cd m
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, W_rv, mk_stop, sub_c, tree_c, W0_lin, W0, Wd]
      | succ M =>
        simp only [set_c, app_1_odd, W_rv, mk_sh, W0_lin, W0, Wd]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, W_safe, W_rv, mk_stop, sub_c, tree_c, W0_lin, W0, Wd]
      | succ M =>
        simp only [set_c, app_1_odd, W_safe, W_rv, mk_sh, W0_lin, W0, Wd]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, S_rv, mk_stop, sub_c, tree_c, S_tree, Wd, stopOnePosBonus, evenCeil]
      | succ M =>
        simp only [set_c, app_1_odd, S_rv, mk_sh, S_tree, W0, Wd, stopOnePosBonus, evenCeil]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · intro rem hrem _ _ _
      cases hM : m + 2 * cd with
      | zero =>
        simp [app_1_odd, BadRV, show rem ≠ 0 by omega, mk_stop, sub_c, set_c, tree_c, BadRoot]
      | succ M =>
        simp [app_1_odd, BadRV, show rem ≠ 0 by omega, mk_sh, BadRoot]; split_ifs <;> simp [BadRoot]

theorem postD0_oneEnd : PostD0 (.oneEnd 0) := by
  refine ⟨.R_D (.P_tree (.endOne 3)), sweep_d0_oneEnd, ?_, ?_, ?_, ?_, ?_⟩
  · simp [WF_rv, WF_u]
  · simp [NotBadRD]
  · intro _; simp [W_safe, W_rv, W0_lin, W0, Wd]
  · intro m2
    cases m2 <;> simp [app_1_even, W_safe, W_rv, W_ra_tree, W0_lin, W0, Wd] ; all_goals (try omega)
  · intro cd m
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, W_rv, mk_stop, sub_c, tree_c, W0_lin, W0, Wd]
      | succ M =>
        simp only [set_c, app_1_odd, W_rv, mk_sh, W0_lin, W0, Wd]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, W_safe, W_rv, mk_stop, sub_c, tree_c, W0_lin, W0, Wd]
      | succ M =>
        simp only [set_c, app_1_odd, W_safe, W_rv, mk_sh, W0_lin, W0, Wd]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, S_rv, mk_stop, sub_c, tree_c, S_tree, Wd, stopOnePosBonus, evenCeil]
      | succ M =>
        simp only [set_c, app_1_odd, S_rv, mk_sh, S_tree, W0, Wd, stopOnePosBonus, evenCeil]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · intro rem hrem hcd2 hwd hnbr
      cases hM : m + 2 * cd with
      | zero =>
        simp [app_1_odd, BadRV, show rem ≠ 0 by omega, mk_stop, sub_c, set_c, tree_c, BadRoot]
      | succ M =>
        simp only [set_c, Wd, stopOnePosBonus, BadRoot] at hwd hnbr
        simp only [app_1_odd, BadRV, show rem ≠ 0 by omega, mk_sh, BadRoot]
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)

theorem postD0_stopOne : PostD0 (.stopOne 0) := by
  refine ⟨.R_F 0 (.P_tree (.endOne 3)), sweep_d0_stopOne, ?_, ?_, ?_, ?_, ?_⟩
  · simp [WF_rv, WF_u]
  · simp [NotBadRD]
  · intro _; simp [W_safe, W_rv, mk_stop, sub_c, set_c, tree_c, W0_lin, W0, Wd]
  · intro m2
    cases m2 <;> simp only [app_1_even, W_safe, W_rv, mk_stop, mk_sh, sub_c, set_c, tree_c, W0_lin,
      W0,
      Wd, Tree.endStop.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero,
        Nat.succ_ne_zero, Nat.reduceEqDiff, zero_add, add_zero, Nat.succ_eq_add_one,
          Tree.endOne.injEq, and_false, false_and, and_true, true_and, or_false, false_or,
          not_false_eq_true, not_true_eq_false, eq_self, Nat.add_eq_zero_iff, Nat.reduceLeDiff,
          Nat.reduceSub]
    all_goals (try omega)
  · intro cd m
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [set_c, app_1_odd, W_rv, W_ra_tree, W0, Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [set_c, app_1_odd, W_safe, W_rv, W_ra_tree, W0, Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [set_c, app_1_odd, S_rv, S_ra_tree, W0, Wd, stopOnePosBonus, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hcd2 hwd hnbr
      simp only [set_c, Wd, stopOnePosBonus, BadRoot] at hwd hnbr
      simp only [app_1_odd, BadRV, show rem ≠ 0 by omega]
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem postD0_stop {d : Tree} (hwf : WF_d (.stop 0 d)) : PostD0 (.stop 0 d) := by
  rcases hwf with ⟨hd0, hd1, hd⟩
  have hu2 : WF_u (add_c 2 d) := by
    cases d <;> simp [WF_d, WF_u, add_c, set_c, tree_c] at hd ⊢ <;> tauto
  have hwd := Wd_ge_9 d
  have hw2 : W0 (add_c 2 d) ≤ Wd d + 5 := by
    cases d <;> simp only [add_c, set_c, tree_c, W0, Wd, ne_eq, Nat.reduceLeDiff,
      Tree.endZero.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
      and_false, false_and, and_true, true_and, or_false, false_or, not_false_eq_true,
      not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff,
      Nat.reduceEqDiff, Nat.reduceSub] at hd0 hd1 ⊢
    all_goals (try split_ifs at * )
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs at * )
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  have hsub2 : sub_c 1 (add_c 2 d) = add_c 1 d := by
    cases d <;> simp [sub_c, add_c, set_c, tree_c] ; all_goals (try omega)
  have hwd1 : Wd (add_c 1 d) ≤ Wd d + 3 := by
    cases d <;> simp only [add_c, set_c, tree_c, Wd, ne_eq, Nat.reduceLeDiff, Tree.endZero.injEq,
      Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, and_false, false_and,
      and_true, true_and, or_false, false_or, not_false_eq_true, not_true_eq_false, eq_self,
      Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
      Nat.reduceSub] at hd0 hd1 ⊢
    all_goals (try split_ifs at * )
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs at * )
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  have hrf0 : W_rv (.R_F 0 (.P_tree (add_c 2 d))) ≤ Wd d + 7 := by
    have hneqz : add_c 2 d ≠ .endZero 1 := by cases d <;> simp [add_c, set_c, tree_c]
                                              all_goals (try omega)
    by_cases hneo : add_c 2 d = .endOne 2
    · simp only [W_rv, hneqz, hneo, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq,
      eq_self]; (try omega)
    · simp only [W_rv, hneqz, hneo, ↓reduceIte, hsub2]
      have hmk : W0_lin (mk_stop 1 (add_c 1 d)) ≤ Wd d + 9 := by
        unfold mk_stop
        split_ifs with ha hb
        · cases d <;> simp [add_c, set_c, tree_c] at ha
        · simp only [W0_lin, W0, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq,
          eq_self]; (try omega)
        · simp only [W0_lin, W0, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq,
          eq_self]; (try omega)
      omega
  have hrf0_safe : W_safe (.R_F 0 (.P_tree (add_c 2 d))) ≤ Wd d + 9 := by
    cases d <;> simp only [add_c, set_c, tree_c, W_safe] at hrf0 ⊢
    all_goals (try split_ifs)
    all_goals (try simp only [Wd, reduceCtorEq, ↓reduceIte, ite_true, ite_false, ne_eq] at hrf0 ⊢)
    all_goals (try split_ifs at hrf0 ⊢)
    all_goals omega
  refine ⟨.R_F 0 (.P_tree (add_c 2 d)), sweep_d0_stop_any d, hu2, ?_, ?_, ?_, ?_⟩
  · simp [NotBadRD]
  · intro _; simp only [Wd]; (try omega)
  · intro m2
    cases m2 with
    | zero => simp only [app_1_even, Wd, ↓reduceIte, ite_true, ite_false, ne_eq, zero_add,
      add_zero]; (try omega)
    | succ m2 =>
      have he := W_rv_app_1_even_le (m2 + 1) (rv := .R_F 0 (.P_tree (add_c 2 d))) hu2
      have hes := W_safe_app_1_even_pos m2 (rv := .R_F 0 (.P_tree (add_c 2 d))) hu2
      simp only [Wd, ↓reduceIte, ite_true, ite_false, ne_eq, zero_add, add_zero]; (try omega)
  · intro cd m
    simp only [set_c, app_1_odd, Nat.add_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases d <;> simp only [W_rv, W_ra_tree, add_c, set_c, tree_c, W0, Wd] at hd0 hd1 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d <;> simp only [W_safe, W_rv, W_ra_tree, add_c, set_c, tree_c, W0, Wd] at hd0 hd1 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d <;> simp only [S_rv, S_ra_tree, add_c, set_c, tree_c, W0, Wd, stopOnePosBonus,
      evenCeil, not_false_eq_true, not_true_eq_false, ne_eq, zero_add, add_zero,
        Tree.endZero.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
        and_false, false_and, and_true, true_and, or_false, false_or, eq_self, Nat.add_one_ne_zero,
        Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff,
        Nat.reduceSub] at hd0 hd1 hwd ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hcd2 hwd_le hnbr
      cases d <;> simp only [Wd, stopOnePosBonus, BadRoot, BadRV, show rem ≠ 0 by omega, add_c,
        set_c,
        tree_c, not_false_eq_true, not_true_eq_false, ne_eq, Nat.reduceLeDiff, zero_add,
          add_zero, Tree.endZero.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true,
            ite_false, and_false, false_and, and_true, true_and, or_false, false_or, eq_self,
            Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
            Nat.reduceSub] at hd0 hd1 hwd hwd_le hnbr ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem postD0_od_pos (m2 : Nat) {d2 : Tree} (hd2 : WF_d d2) (hpos : tree_c d2 ≥ 1) :
    PostD0 (.od 0 m2 d2) := by
  have hu : WF_u (.od 2 m2 (sub_c 1 d2)) := ⟨by omega, WF_d_set_c _ hd2⟩
  have hwd2 := Wd_ge_9 d2
  have hsub_le : Wd (sub_c 1 d2) ≤ Wd d2 := by
    cases d2 <;> simp only [sub_c, set_c, tree_c, Wd] at hpos ⊢
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  have hw_rv : W_rv (.R_D (.P_tree (.od 2 m2 (sub_c 1 d2)))) ≤ Wd (.od 0 m2 d2) + 4 := by
    simp only [W_rv, W0_lin, W0, Wd, reduceCtorEq, ↓reduceIte, ite_true, ite_false, zero_add,
      add_zero]; (try omega)
  have hws_rv : W_safe (.R_D (.P_tree (.od 2 m2 (sub_c 1 d2)))) = W_rv (.R_D (.P_tree (.od 2 m2
    (sub_c 1 d2)))) := rfl
  refine ⟨.R_D (.P_tree (.od 2 m2 (sub_c 1 d2))), sweep_d0_od_pos m2 hpos, hu, ?_, ?_, ?_, ?_⟩
  · simp [NotBadRD]
  · intro _; exact ⟨hw_rv, by omega⟩
  · intro m
    cases m with
    | zero => simp only [app_1_even, ↓reduceIte, ite_true, ite_false, zero_add,
      add_zero]; (try omega)
    | succ m =>
      have he := W_rv_app_1_even_le (m + 1) (rv := .R_D (.P_tree (.od 2 m2 (sub_c 1 d2)))) hu
      have hes := W_safe_app_1_even_pos m (rv := .R_D (.P_tree (.od 2 m2 (sub_c 1 d2)))) hu
      omega
  · intro cd m
    simp only [set_c]
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [app_1_odd, W_rv, mk_stop, sub_c, set_c, tree_c, W0_lin, W0, Wd] at hsub_le ⊢
        omega
      | succ M =>
        simp [app_1_odd, W_rv, mk_sh, W0_lin, W0, Wd] at hsub_le ⊢
        omega
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [app_1_odd, W_safe, W_rv, mk_stop, sub_c, set_c, tree_c, W0_lin, W0, Wd] at hsub_le ⊢
        omega
      | succ M =>
        simp only [app_1_odd, W_safe, W_rv, mk_sh, W0_lin, W0, Wd] at hsub_le ⊢
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp only [app_1_odd, S_rv, mk_stop, sub_c, set_c, tree_c, S_tree, Wd, stopOnePosBonus,
          evenCeil] at hsub_le hwd2 ⊢
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | succ M =>
        simp [app_1_odd, S_rv, mk_sh, S_tree, W0, Wd, stopOnePosBonus, evenCeil] at hsub_le hwd2 ⊢
        omega
    · intro rem hrem _ hwd_le _
      have hlin : Wd (.od cd m2 d2) = 2 * cd + Wd (.od 0 m2 d2) := by simp only [Wd]; (try omega)
      simp only [stopOnePosBonus] at hwd_le
      exact not_badRV_of_W_safe_le rem (m + 2 * cd) hu (by simp) hrem (by omega)

/-! ### 11. `od` Prefix Combinators & Master Mutual Induction via `Nat.strongRecOn` -/

theorem sweep_od_partial (k m : Nat) {d : Tree} (hd : WF_d d) (hk : k + 1 ≤ tree_c d) :
    SweepRV ((([0, 1] : List (Fin 2)) ^ k) +>
      ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d)))
      (.R_A (m + 2 * k + 1) (.P_od (sub_c (k + 1) d))) := by
  induction k with
  | zero =>
    have h0 := sweep_P_od_pos (d := d) (by omega)
    have hwf0 : WF_rv (.R_F 1 (.P_od (sub_c 1 d))) := WF_d_set_c _ hd
    have h1 := sweepRV_app_1_odd m hwf0 h0
    simpa [list_pow_zero, ListBlank.append_nil, app_1_odd, evalP, Nat.add_assoc] using h1
  | succ k ih =>
    have hprev := ih (by omega)
    have hpos : tree_c (sub_c (k + 1) d) ≥ 1 := by
      unfold sub_c; rw [tree_c_set_c]; (try omega)
    have h0 := sweep_P_od_pos (d := sub_c (k + 1) d) hpos
    have hwf0 : WF_rv (.R_F 1 (.P_od (sub_c 1 (sub_c (k + 1) d)))) :=
      WF_d_set_c _ (WF_d_set_c _ hd)
    have hstep := sweepRV_01_RA (m + 2 * k + 1) hwf0 hprev h0
    have hsub : sub_c 1 (sub_c (k + 1) d) = sub_c (k + 1 + 1) d := by
      cases d <;> simp only [sub_c, set_c, tree_c, Tree.endZero.injEq, Tree.endStop.injEq,
        Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq, Tree.stop.injEq, and_true,
        true_and, Tree.od.injEq, Tree.sh.injEq] ; all_goals (try omega)
    rw [hsub] at hstep
    rw [ListBlank.append_pow_succ]
    simpa [ListBlank.append_cons, ListBlank.append_nil, app_1_odd, bump_ra,
      show m + 2 * k + 1 + 1 + 1 = m + 2 * (k + 1) + 1 by omega] using hstep

theorem sweep_od_prefix (m : Nat) {d : Tree} {rv0 : RVal} (hd : WF_d d) (hwf0 : WF_rv rv0)
    (h0 : SweepRV ((0 : Fin 2) >> evalT (set_c 0 d)) rv0) :
    SweepRV ((([0, 1] : List (Fin 2)) ^ tree_c d) +>
      ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d)))
      (app_1_odd (m + 2 * tree_c d) rv0) := by
  cases hcd : tree_c d with
  | zero =>
    have hd0 : set_c 0 d = d := by
      cases d <;> simp only [set_c, tree_c, Tree.endZero.injEq,
      Tree.endStop.injEq, Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq,
      Tree.stop.injEq, and_true, true_and, Tree.od.injEq,
      Tree.sh.injEq] at hcd ⊢ ; all_goals (try omega)
    rw [hd0] at h0
    have h1 := sweepRV_app_1_odd m hwf0 h0
    simpa [list_pow_zero, ListBlank.append_nil, evalP] using h1
  | succ k =>
    have hpart := sweep_od_partial k m hd (by omega)
    have hsub0 : sub_c (k + 1) d = set_c 0 d := by
      cases d <;> simp only [sub_c, set_c, tree_c, Tree.endZero.injEq, Tree.endStop.injEq,
        Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq, Tree.stop.injEq, and_true,
        true_and, Tree.od.injEq, Tree.sh.injEq] at hcd ⊢ ; all_goals (try omega)
    rw [hsub0] at hpart
    have hstep := sweepRV_01_RA (m + 2 * k + 1) hwf0 hpart h0
    rw [bump_ra_app_1_odd, show m + 2 * k + 1 + 1 = m + 2 * (k + 1) by omega] at hstep
    rw [ListBlank.append_pow_succ]
    simpa [ListBlank.append_cons, ListBlank.append_nil] using hstep

theorem odd_S_of_app_1_odd_pos (M m : Nat) {rv0 : RVal} (hwf0 : WF_rv rv0) :
    S_rv (app_1_odd M (app_1_odd (m + 1) rv0)) ≤
      max 24 (evenCeil (W_rv (app_1_odd (m + 1) rv0) + 7)) := by
  cases rv0 with
  | R_D p =>
    cases p with
    | P_od d => cases hwf0
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, S_ra_tree, W_rv, mk_sh, W0_lin, W0,
        evenCeil, Tree.endStop.injEq, and_false, false_and, ne_eq, reduceCtorEq, ↓reduceIte,
          ite_true, ite_false, and_true, true_and, or_false, false_or, not_false_eq_true,
          not_true_eq_false, eq_self, Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff,
          Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub] at hwf0 hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | R_F m0 p =>
    cases p with
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, W_rv, W_ra_tree, mk_sh, S_tree, W0,
        evenCeil] at hwf0 hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    | P_od d =>
      have hd := Wd_ge_9 d
      cases d <;> simp only [WF_rv, app_1_odd, S_rv, W_rv, W_ra_od, S_tree, Wd, stopOnePosBonus,
        evenCeil] at hwf0 hd ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | R_A m0 p =>
    cases p with
    | P_od d =>
      cases d with
      | stop cd d2 =>
        have h2 := Wd_ge_9 d2
        simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil] at hwf0 h2 ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | od cd m2 d2 =>
        have h2 := Wd_ge_9 d2
        simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil] at hwf0 h2 ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | sh cd m2 u2 =>
        have h2 := W0_ge_11 u2
        simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil] at hwf0 h2 ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      | _ =>
        simp only [WF_rv, app_1_odd, S_rv, S_ra_od, W_rv, set_c, tree_c, Wd, evenCeil,
          Tree.endOne.injEq] at hwf0 ⊢
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs at * )
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    | P_tree u =>
      have hw := W0_ge_11 u
      cases u <;> simp only [WF_rv, WF_u, app_1_odd, S_rv, S_ra_tree, W_rv, mk_sh, W0_lin, W0,
        evenCeil] at hwf0 hw ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem app_1_odd_pos_ne_RF0 (m : Nat) (rv0 : RVal) (p : Payload) :
    app_1_odd (m + 1) rv0 ≠ .R_F 0 p := by
  cases rv0 <;> simp [app_1_odd]

theorem postRV_of_RA_direct (m : Nat) {p : Payload} {rv0 : RVal}
    (hwf0 : WF_rv rv0)
    (hsw0 : SweepRV (evalP p) rv0)
    (hw_b : W_rv (app_1_odd (m + 1) rv0) ≤ W_rv (.R_A m p) + 2)
    (hws_b : W_safe (app_1_odd (m + 1) rv0) ≤ W_safe (.R_A m p) + 2)
    (hs_b : S_rv (app_1_odd (m + 1) rv0) ≤ S_rv (.R_A m p) - 2)
    (hbad_b : ∀ rem, rem ≥ 1 → S_rv (.R_A m p) ≤ 20 + 2 * (rem + 1) →
      ¬ BadRV (rem + 1) (.R_A m p) → ¬ BadRV rem (app_1_odd (m + 1) rv0)) :
    PostRV (.R_A m p) (app_1_odd (m + 1) rv0) := by
  have h1 : ∀ r,
    SweepRV r (.R_A m p) → SweepRV ((0 : Fin 2) >> (1 : Fin 2) >> r) (app_1_odd (m + 1) rv0) := by
    intro r hr
    rw [← bump_ra_app_1_odd]
    exact sweepRV_01_RA m hwf0 hr hsw0
  refine ⟨h1, WF_rv_app_1_odd (m + 1) hwf0, notBadRD_app_1_odd (m + 1) rv0,
    app_1_odd_pos_ne_RF0 m rv0, hw_b, hws_b, hs_b, ?_,
    fun _ => goodRV_of_odd (m + 1) (by intro h; (try omega)), ?_⟩
  · intro rem hs hnb
    cases rem with
    | zero => cases rv0 <;> simp [app_1_odd, BadRV]
    | succ r => exact hbad_b (r + 1) (by omega) hs hnb
  · intro _ M
    have how := (odd_of_app_1_odd_pos M m hwf0).1
    have hows := odd_wsafe_of_app_1_odd_pos M m hwf0
    have hos := odd_S_of_app_1_odd_pos M m hwf0
    refine ⟨by omega, by omega, ?_⟩
    exact le_trans hos (max_le (le_max_left _ _) (le_trans (evenCeil_mono (by omega))
      (le_max_right _ _)))

theorem postRV_of_RA_good (m : Nat) {p : Payload} {rv0 : RVal}
    (hwf0 : WF_rv rv0)
    (hsw0 : SweepRV (evalP p) rv0)
    (hnb0 : m = 0 → NotBadRD rv0)
    (hw2 : W_rv (app_1_odd m rv0) ≤ W_rv (.R_A m p))
    (hs2 : S_rv (app_1_odd m rv0) ≤ S_rv (.R_A m p) - 2)
    (hbad : ∀ rem, rem ≥ 1 → S_rv (.R_A m p) ≤ 20 + 2 * (rem + 1) →
      ¬ BadRV rem (app_1_odd (m + 1) rv0)) :
    PostRV (.R_A m p) (bump_ra (app_1_odd m rv0)) := by
  have hwf2 := WF_rv_app_1_odd m hwf0
  have hnd2 := app_1_odd_ne_RD m rv0
  have hnb2 := notBad_of_odd m hnb0
  obtain ⟨hnb_b, hw_b, hs_b, hodd_b⟩ := bump_ra_bounds hwf2 hnd2 hnb2
  have hws_b := W_safe_bump_ra_odd m hwf0 hnb0
  have hws_ge : W_rv (.R_A m p) ≤ W_safe (.R_A m p) := W_safe_ge_W_rv
  refine ⟨fun r h1 => sweepRV_01_RA m hwf0 h1 hsw0,
    WF_rv_bump_ra hwf2 hnd2, hnb_b,
    fun p' => by rw [bump_ra_app_1_odd]; exact app_1_odd_pos_ne_RF0 m rv0 p',
    by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro rem hs _
    rw [bump_ra_app_1_odd]
    cases rem with
    | zero => cases rv0 <;> simp [app_1_odd, BadRV]
    | succ r => exact hbad (r + 1) (by omega) hs
  · intro _; rw [bump_ra_app_1_odd]; exact goodRV_of_odd (m + 1) (by intro h; (try omega))
  · intro _ M
    obtain ⟨how, hos⟩ := hodd_b M
    have hows : W_safe (app_1_odd M (bump_ra (app_1_odd m rv0))) ≤ 2 * M + 4 + W_rv (.R_A m p) := by
      have h1 := odd_wsafe_of_app_1_odd_pos M m hwf0
      have h2 : W_rv (app_1_odd (m + 1) rv0) ≤ W_rv (app_1_odd m rv0) + 2 := by
        rw [← bump_ra_app_1_odd]; exact hw_b
      rw [bump_ra_app_1_odd]
      omega
    refine ⟨by omega, hows, ?_⟩
    exact le_trans hos (max_le (le_max_left _ _) (le_trans (evenCeil_mono (by omega))
      (le_max_right _ _)))

theorem postD0_od_0_endStop0 : PostD0 (.od 0 0 (.endStop 0)) := by
  have h0 := sweep_d0_endStop
  have h1 := sweepRV_01_RF0 (by simp [WF_u]) h0
  have hev : ((0 : Fin 2) >> evalT (.od 0 0 (.endStop 0))) =
      ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> evalT (.endStop 0))) := by
    simp [evalT_od, list_pow_zero, ListBlank.append_nil]
  have hmk : mk_stop 1 (sub_c 1 (.endZero 2)) = .stop 1 (.endZero 1) := rfl
  rw [hmk] at h1
  rw [← hev] at h1
  have hu_st : WF_rv (.R_D (.P_tree (.stop 1 (.endZero 1)))) := by simp [WF_rv, WF_u, WF_d]
  refine ⟨.R_D (.P_tree (.stop 1 (.endZero 1))), h1, hu_st, ?_, ?_, ?_, ?_⟩
  · simp [NotBadRD]
  · intro _; simp [W_safe, W_rv, W0_lin, W0, Wd]
  · intro m2
    cases m2 <;> simp only [app_1_even, W_safe, W_rv, W_ra_tree, W0_lin, W0, Wd,
      Tree.endStop.injEq, reduceCtorEq, ↓reduceIte, ite_true, ite_false, Nat.add_one_ne_zero,
      Nat.succ_ne_zero, Nat.reduceEqDiff, zero_add, add_zero,
      Nat.succ_eq_add_one] ; all_goals (try omega)
  · intro cd m
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, W_rv, mk_stop, sub_c, tree_c, W0_lin, W0, Wd]
      | succ M =>
        simp only [set_c, app_1_odd, W_rv, mk_sh, W0_lin, W0, Wd]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, W_safe, W_rv, mk_stop, sub_c, tree_c, W0_lin, W0, Wd]
      | succ M =>
        simp only [set_c, app_1_odd, W_safe, W_rv, mk_sh, W0_lin, W0, Wd]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · cases hM : m + 2 * cd with
      | zero =>
        have : m = 0 ∧ cd = 0 := by omega
        rcases this with ⟨rfl, rfl⟩
        simp [set_c, app_1_odd, S_rv, mk_stop, sub_c, tree_c, S_tree, Wd, stopOnePosBonus, evenCeil]
      | succ M =>
        simp only [set_c, app_1_odd, S_rv, mk_sh, S_tree, W0, Wd, stopOnePosBonus, evenCeil]
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
    · intro rem hrem _ hwd_le _
      simp only [set_c, Wd, stopOnePosBonus, ↓reduceIte, ite_true, ite_false] at hwd_le
      exact not_badRV_of_W_safe_le rem (m + 2 * cd) hu_st (by simp) hrem
        (by simp only [W_safe, W_rv, W0_lin, W0, Wd, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
          Nat.reduceEqDiff, Nat.reduceLeDiff, zero_add, add_zero]; (try omega))

theorem postRV_RA_leaves (m : Nat) (w : Tree) (hw : WF_u w)
    (hleaf : match w with
      | .endZero _ | .endStop _ | .endOne _ | .oneEnd _ | .stopOne _ => True
      | _ => False) :
    ∃ rvn, PostRV (.R_A m (.P_tree w)) rvn := by
  cases w with
  | stop _ _ | od _ _ _ | sh _ _ _ => cases hleaf
  | endZero c =>
    have hc : c ≥ 1 := hw
    refine ⟨_, postRV_of_RA_direct m
      (by simp only [WF_rv, WF_u]; (try omega)) (sweep_u_endZero c hc) ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, S_rv, S_ra_tree, mk_sh, S_tree, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp only [S_rv, S_ra_tree, BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh,
        BadRoot] at hs hnb ⊢
      (try split_ifs at *); all_goals (try simp [BadRoot])
  | endStop c =>
    have hc : c ≥ 1 := hw
    refine ⟨_, postRV_of_RA_direct m
      (by simp only [WF_rv, WF_u]; (try omega)) (sweep_u_endStop c hc) ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, S_rv, S_ra_tree, mk_sh, S_tree, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp only [S_rv, S_ra_tree, BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh,
        BadRoot] at hs hnb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | endOne c =>
    have hc : c ≥ 2 := hw
    refine ⟨_, postRV_of_RA_direct m
      (by simp only [WF_rv, WF_u]; (try omega)) (sweep_u_endOne c hc) ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, S_rv, S_ra_tree, mk_sh, S_tree, W0, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp only [S_rv, S_ra_tree, W0, evenCeil, BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh,
        BadRoot] at hs hnb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | oneEnd c =>
    have hc : c ≥ 2 := hw
    refine ⟨_, postRV_of_RA_direct m
      (by simp only [WF_rv, WF_u]; (try omega)) (sweep_u_oneEnd c hc) ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, mk_sh, W0_lin, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, S_rv, S_ra_tree, mk_sh, S_tree, W0, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp [S_rv, S_ra_tree, W0, evenCeil, BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh,
        BadRoot] at hs hnb ⊢
      (try split_ifs at *); all_goals (try simp [BadRoot])
  | stopOne c =>
    have hc : c ≥ 1 := hw
    refine ⟨_, postRV_of_RA_direct m
      (by simp only [WF_rv, WF_u, WF_d, and_true,
        true_and]; (try omega)) (sweep_u_stopOne c hc) ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, mk_sh, W0_lin, W0, Wd, and_true, true_and]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, mk_sh, W0_lin, W0, Wd]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, S_rv, S_ra_tree, mk_sh, S_tree, W0, Wd, evenCeil]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp [BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh, BadRoot]

theorem postRV_RA_od_pos (m : Nat) {d : Tree} (hd : WF_d d) (hpos : tree_c d ≥ 1) :
    ∃ rvn, PostRV (.R_A m (.P_od d)) rvn := by
  refine ⟨_,
    postRV_of_RA_direct m (rv0 :=
    .R_F 1 (.P_od (sub_c 1 d))) (WF_d_set_c _ hd) (sweep_P_od_pos hpos) ?_ ?_ ?_ ?_⟩
  · cases d <;> simp only [app_1_odd, W_rv, W_ra_od, sub_c, set_c, tree_c, Wd] at hpos ⊢
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · cases d <;> simp only [app_1_odd, W_safe, W_rv, W_ra_od, sub_c, set_c, tree_c, Wd] at hpos ⊢
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · have h9 := Wd_ge_9 (set_c 0 d)
    cases d <;> simp only [app_1_odd, S_rv, S_ra_od, sub_c, set_c, tree_c, Wd,
      evenCeil] at hpos h9 ⊢
    all_goals (try omega)
  · intro rem hrem hs hnb
    cases d <;> simp [S_rv, S_ra_od, BadRV, show rem ≠ 0 by omega, app_1_odd, sub_c, set_c,
      tree_c] at hpos hs hnb ⊢
    all_goals (try split_ifs at * )
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs at * )
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)

theorem postRV_RA_od_base0 (m : Nat) (d : Tree) (hd : WF_d d) (hc0 : tree_c d = 0)
    (hbase : match d with
      | .od _ _ _ | .sh _ _ _ => False
      | _ => True) :
    ∃ rvn, PostRV (.R_A m (.P_od d)) rvn := by
  cases d with
  | od _ _ _ | sh _ _ _ => cases hbase
  | endZero c =>
    simp only [tree_c] at hc0; subst hc0
    refine ⟨_, postRV_of_RA_direct m (by simp [WF_rv, WF_u]) sweep_d0_endZero ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, W_ra_od, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, W_ra_od, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp [app_1_odd, S_rv, S_ra_tree, S_ra_od]
    · intro rem hrem _ _; simp [app_1_odd, BadRV, show rem ≠ 0 by omega]
  | endStop c =>
    simp only [tree_c] at hc0; subst hc0
    refine ⟨_, postRV_of_RA_direct m (by simp [WF_rv, WF_u]) sweep_d0_endStop ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, W_ra_od, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, W_ra_od, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp [app_1_odd, S_rv, S_ra_tree, S_ra_od]
    · intro rem hrem _ _; simp [app_1_odd, BadRV, show rem ≠ 0 by omega]
  | endOne c =>
    simp only [tree_c] at hc0; subst hc0
    refine ⟨_, postRV_of_RA_direct m (by simp [WF_rv, WF_u]) sweep_d0_endOne ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_od, mk_sh, W0_lin, W0, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_od, mk_sh, W0_lin, W0, reduceCtorEq, ↓reduceIte,
        ite_true, ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp only [app_1_odd, S_rv, S_ra_od, mk_sh, S_tree, W0, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp only [S_rv, S_ra_od, BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh, BadRoot] at hs hnb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | oneEnd c =>
    simp only [tree_c] at hc0; subst hc0
    refine ⟨_, postRV_of_RA_direct m (by simp [WF_rv, WF_u]) sweep_d0_oneEnd ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_od, mk_sh, W0_lin, W0, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_od, mk_sh, W0_lin, W0, reduceCtorEq, ↓reduceIte,
        ite_true, ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · simp [app_1_odd, S_rv, S_ra_od, mk_sh, S_tree, W0]
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs)
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      simp only [S_rv, S_ra_od, BadRV, show rem ≠ 0 by omega, app_1_odd, mk_sh, BadRoot, and_false,
        false_and, and_true, true_and, or_false, false_or, not_false_eq_true, not_true_eq_false,
        Nat.reduceEqDiff, Nat.reduceLeDiff, zero_add, add_zero] at hs hnb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  | stopOne c =>
    simp only [tree_c] at hc0; subst hc0
    refine ⟨_, postRV_of_RA_direct m (by simp [WF_rv, WF_u]) sweep_d0_stopOne ?_ ?_ ?_ ?_⟩
    · simp only [app_1_odd, W_rv, W_ra_tree, W_ra_od, W0, reduceCtorEq, ↓reduceIte, ite_true,
        ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp only [app_1_odd, W_safe, W_rv, W_ra_tree, W_ra_od, W0, reduceCtorEq, ↓reduceIte,
        ite_true, ite_false, and_false, false_and, and_true, true_and, Nat.add_one_ne_zero,
        Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, eq_self]
      (try omega)
    · simp [app_1_odd, S_rv, S_ra_tree, S_ra_od, W0, evenCeil]; (try omega)
    · intro rem hrem hs hnb
      simp [S_rv, S_ra_od, BadRV, show rem ≠ 0 by omega, app_1_odd] at hs hnb ⊢; (try omega)
  | stop c d2 =>
    simp only [tree_c] at hc0; subst hc0
    rcases hd with ⟨hd0, hd1, hd2⟩
    have hu2 : WF_u (add_c 2 d2) := by
      cases d2 <;> simp [WF_d, WF_u, add_c, set_c, tree_c] at hd2 ⊢ <;> tauto
    have h9 := Wd_ge_9 d2
    refine ⟨_,
      postRV_of_RA_direct m (rv0 :=
      .R_F 0 (.P_tree (add_c 2 d2))) hu2 (sweep_d0_stop_any d2) ?_ ?_ ?_ ?_⟩
    · cases d2 <;> simp only [app_1_odd, W_rv, W_ra_tree, W_ra_od, add_c, set_c, tree_c, W0,
      Wd] at hd0 hd1 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d2 <;> simp only [app_1_odd, W_safe, W_rv, W_ra_tree, W_ra_od, add_c, set_c, tree_c, W0,
      Wd] at hd0 hd1 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d2 <;> simp only [app_1_odd, S_rv, S_ra_tree, S_ra_od, add_c, set_c, tree_c, W0, Wd,
      evenCeil] at hd0 hd1 h9 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · intro rem hrem hs hnb
      cases d2 <;> simp only [S_rv, S_ra_od, BadRV, show rem ≠ 0 by omega, app_1_odd, add_c, set_c,
        tree_c, Wd, evenCeil, and_false, false_and, not_false_eq_true, not_true_eq_false, ne_eq,
          zero_add, add_zero, Tree.endZero.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte,
            ite_true, ite_false, and_true, true_and, or_false, false_or, eq_self,
            Nat.add_one_ne_zero, Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
            Nat.reduceLeDiff, Nat.reduceSub] at hd0 hd1 h9 hs hnb ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)

theorem postU_od_lt_cd (c m : Nat) {d : Tree} (hc : c ≥ 2) (hd : WF_d d) (hlt : c + 1 ≤ tree_c d) :
    PostU (.od c m d) := by
  have hpart := sweep_od_partial c m hd hlt
  have hev : ((([0, 1] : List (Fin 2)) ^ c) +>
      ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d))) =
      evalT (.od c m d) := by
    simp [evalT_od]
  rw [hev] at hpart
  have hwf_rv : WF_rv (.R_A (m + 2 * c + 1) (.P_od (sub_c (c + 1) d))) := WF_d_set_c _ hd
  have h9 := Wd_ge_9 d
  have hws_le : W_safe (.R_A (m + 2 * c + 1) (.P_od (sub_c (c + 1) d))) ≤ W0 (.od c m d) + 2 := by
    cases d <;> simp only [W_safe, W_rv, W_ra_od, W0, Wd, sub_c, set_c, tree_c] at hlt ⊢
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  refine ⟨.R_A (m + 2 * c + 1) (.P_od (sub_c (c + 1) d)), hpart, hwf_rv, ?_, by simp, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro _; simp [NotBadRD]
  · cases d <;> simp only [W_rv, W_ra_od, W0, Wd, sub_c, set_c, tree_c] at hlt ⊢
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
      stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
    all_goals (try split_ifs)
    all_goals (try dsimp only [W0, Wd] at *)
    all_goals (try split_ifs)
    all_goals (try exact not_false)
    all_goals (try omega)
  · simpa [isLeaf] using hws_le
  · intro M _
    have hsub9 := Wd_ge_9 (sub_c (c + 1) d)
    refine ⟨?_, ?_, ?_⟩
    · cases d <;> simp only [app_1_odd, W_rv, W0, Wd, sub_c, set_c, tree_c] at hlt ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d <;> simp only [app_1_odd, W_safe, W_rv, W0, Wd, sub_c, set_c, tree_c] at hlt ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
    · cases d <;> simp only [app_1_odd, S_rv, S_tree, W0, Wd, sub_c, set_c, tree_c, stopOnePosBonus,
      evenCeil] at hlt h9 hsub9 ⊢
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
        stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
      all_goals (try split_ifs at * )
      all_goals (try dsimp only [W0, Wd] at *)
      all_goals (try split_ifs)
      all_goals (try exact not_false)
      all_goals (try omega)
  · intro c' M hc' _ hw0 _
    simp only [isLeaf] at hc'
    exact not_badRV_of_W_safe_le c' M hwf_rv (by simp) hc' (by omega)
  · intro hr
    exfalso
    rcases Wd_ge_2c_9 d with rfl | hge
    · simp [tree_c] at hlt; (try omega)
    · have hgt : Wd d ≥ 2 * tree_c d + 10 := by
        cases d with
        | endZero c | endStop c | endOne c | oneEnd c | stopOne c =>
          simp only [Wd, tree_c] at hlt ⊢
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | stop c d2 => have := Wd_ge_9 d2; simp only [Wd, tree_c]; (try omega)
        | od c m2 d2 => have := Wd_ge_9 d2; simp only [Wd, tree_c]; (try omega)
        | sh c m2 u2 => have := W0_ge_11 u2; simp only [Wd, tree_c]; (try omega)
      have hrc := hr.1
      simp [WF_r_core] at hrc; (try omega)

set_option maxHeartbeats 8000000 in
-- Large case-splitting `simp`/`omega` proof over non-`R_A` `RVal` cases requires extra heartbeats.
theorem postRV_step_nonRA {rv : RVal} (hwf : WF_rv rv) (hnotRA : ∀ m p, rv ≠ .R_A m p) :
    ∃ rvn, PostRV rv rvn := by
  cases rv with
  | R_A m p => exact absurd rfl (hnotRA m p)
  | R_D p =>
    cases p with
    | P_od d => cases hwf
    | P_tree t =>
      have ht : WF_u t := hwf
      have hc := tree_c_pos_of_WF_u ht
      refine ⟨.R_D (.P_tree (add_c 1 t)), fun r h => sweepRV_01_RD ht h, WF_u_add_c 1 ht,
        ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [NotBadRD, ne_eq, RVal.R_D.injEq, Payload.P_tree.injEq]
        refine ⟨?_, ?_⟩
        · intro he
          have hct : tree_c (add_c 1 t) = 1 := by rw [he]; rfl
          unfold add_c at hct; rw [tree_c_set_c] at hct; (try omega)
        · intro he
          cases t <;> simp [WF_u, add_c, set_c, tree_c] at ht he ; all_goals (try omega)
      · simp only [W_rv]; rw [W0_lin_add_c_one ht]
      · cases t <;> simp only [WF_u, W_safe, W_rv, W0_lin, W0, add_c, set_c, tree_c,
        Tree.endStop.injEq, ne_eq, Nat.reduceLeDiff] at ht ⊢
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree, W_ra_od,
          stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
        all_goals (try split_ifs)
        all_goals (try dsimp only [W0, Wd] at *)
        all_goals (try split_ifs)
        all_goals (try exact not_false)
        all_goals (try omega)
      · simp only [S_rv]; rw [S_tree_add_c_one ht]
      · intro rem _ hbad
        cases rem with
        | zero => simpa [BadRV] using hbad
        | succ r =>
          have hadd : add_c (r + 1) (add_c 1 t) = add_c (r + 1 + 1) t := by
            cases t <;> simp only [add_c, set_c, tree_c, Tree.endZero.injEq, Tree.endStop.injEq,
              Tree.endOne.injEq, Tree.oneEnd.injEq, Tree.stopOne.injEq, Tree.stop.injEq, and_true,
              true_and, Tree.od.injEq, Tree.sh.injEq, ne_eq] ; all_goals (try omega)
          simpa [BadRV, hadd] using hbad
      · intro hg; cases t <;> simp [GoodRV, add_c, set_c] at hg ⊢
      · intro hg M
        have hw := W0_ge_11 t
        cases M with
        | zero =>
          cases t <;> simp only [WF_u, GoodRV, app_1_odd, add_c, sub_c, set_c, tree_c, mk_stop,
            W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd, stopOnePosBonus, evenCeil] at ht hg hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        | succ M =>
          cases t <;> simp only [WF_u, GoodRV, app_1_odd, add_c, set_c, tree_c, mk_sh,
            W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd, evenCeil] at ht hg hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
  | R_F m p =>
    cases m with
    | zero =>
      cases p with
      | P_od d => cases hwf
      | P_tree u =>
        have hu : WF_u u := hwf
        have hc := tree_c_pos_of_WF_u hu
        have hmk_wf : WF_u (mk_stop 1 (sub_c 1 u)) :=
          WF_u_mk_stop 1 (by omega) (WF_d_set_c _ (WF_d_of_WF_u hu))
        refine ⟨.R_D (.P_tree (mk_stop 1 (sub_c 1 u))), fun r h => sweepRV_01_RF0 hu h, hmk_wf,
          ?_, by simp, W_rv_RF0_spec hu, ?_, ?_, ?_, ?_, ?_⟩
        · unfold mk_stop; split_ifs <;> simp [NotBadRD]
        · have hw := W0_ge_11 u
          have hsub := Wd_sub_c_one_le hu
          cases u <;> simp only [WF_u, W_safe, W_rv, mk_stop, sub_c, set_c, tree_c, W0_lin, W0,
            Wd, Tree.endZero.injEq, Tree.endStop.injEq, Tree.endOne.injEq, ↓reduceIte, ite_true,
              ite_false, not_false_eq_true, not_true_eq_false, ne_eq, eq_self, Nat.reduceEqDiff,
              Nat.reduceLeDiff, Nat.succ_eq_add_one, reduceCtorEq, and_false, false_and, and_true,
                true_and, or_false, false_or, Nat.add_one_ne_zero, Nat.succ_ne_zero,
                Nat.add_eq_zero_iff, Nat.reduceSub] at hu hw hsub ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · simp only [S_rv]; (try omega)
        · intro rem _ hbad
          cases rem with
          | zero => simpa [BadRV] using hbad
          | succ r =>
            have hadd : add_c (r + 1) (mk_stop 1 (sub_c 1 u)) = mk_stop (r + 1 + 1) (sub_c 1 u) :=
              by
              unfold mk_stop; split_ifs <;> simp only [add_c, set_c, tree_c, Tree.endStop.injEq,
                Tree.stopOne.injEq, Tree.stop.injEq, and_true, true_and,
                ne_eq] ; all_goals (try omega)
            simpa [BadRV, hadd] using hbad
        · intro hg
          have hsub0 : sub_c 1 u ≠ .endZero 0 := by
            intro he
            have hu1 : u = .endZero 1 := by
              cases u <;> simp only [sub_c, set_c, tree_c, Tree.endZero.injEq, reduceCtorEq,
                ne_eq] at hc he ⊢ ; all_goals (try omega)
            subst hu1; exact hg
          unfold mk_stop; simp [hsub0]; split_ifs <;> simp [GoodRV]
        · intro hg M
          have hnez : u ≠ .endZero 1 := by intro he; subst he; exact hg
          have hw := W0_ge_11 u
          have hsub := Wd_sub_c_one_le hu
          cases M with
          | zero =>
            cases u <;> simp only [WF_u, app_1_odd, mk_stop, sub_c, set_c, tree_c,
              W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd, stopOnePosBonus,
                evenCeil, Tree.endZero.injEq, Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq,
                  ↓reduceIte, ite_true, ite_false, and_false, false_and, not_false_eq_true,
                  not_true_eq_false, ne_eq, eq_self, Nat.reduceEqDiff, Nat.reduceLeDiff, zero_add,
                  add_zero] at hu hnez hw hsub ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
          | succ M =>
            cases u <;> simp only [WF_u, app_1_odd, mk_stop, mk_sh, sub_c, set_c, tree_c,
              W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd, evenCeil, Tree.endZero.injEq,
                Tree.endStop.injEq, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte, ite_true,
                ite_false, not_false_eq_true, not_true_eq_false, ne_eq, eq_self, Nat.reduceEqDiff,
                Nat.reduceLeDiff, zero_add, add_zero, Nat.succ_eq_add_one] at hu hnez hw hsub ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
    | succ m =>
      cases p with
      | P_tree u =>
        have hu : WF_u u := hwf
        refine ⟨.R_D (.P_tree (mk_sh 2 m u)), fun r h => sweepRV_01_RF_tree m h,
          WF_u_mk_sh 2 m (by omega) hu, ?_, by simp, W_rv_RF_pos_tree_spec m hu, ?_, ?_, ?_, ?_, ?_⟩
        · unfold mk_sh; split_ifs <;> simp [NotBadRD]
        · have hw := W0_ge_11 u
          cases u <;> simp only [WF_u, W_safe, W_rv, mk_sh, W0_lin, W0, and_false, false_and,
            not_false_eq_true, not_true_eq_false, ne_eq, reduceCtorEq, ↓reduceIte, ite_true,
              ite_false, and_true, true_and, or_false, false_or, eq_self, Nat.add_one_ne_zero,
              Nat.succ_ne_zero, Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff,
              Nat.reduceSub] at hu hw ⊢
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs at * )
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · simp only [S_rv]; (try omega)
        · intro rem _ hbad
          cases rem with
          | zero => simpa [BadRV] using hbad
          | succ r =>
            have hadd : add_c (r + 1) (mk_sh 2 m u) = mk_sh (r + 1 + 1 + 1) m u := by
              unfold mk_sh; split_ifs <;> simp only [add_c, set_c, tree_c, Tree.oneEnd.injEq,
                Tree.sh.injEq, and_true, true_and, ne_eq] ; all_goals (try omega)
            simpa [BadRV, hadd] using hbad
        · intro _; unfold mk_sh; split_ifs <;> simp [GoodRV]
        · intro _ M
          have hw := W0_ge_11 u
          cases M with
          | zero =>
            cases u <;> simp only [WF_u, app_1_odd, mk_stop, mk_sh, sub_c, set_c, tree_c,
              W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd, stopOnePosBonus, evenCeil] at hu hw ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
          | succ M =>
            cases u <;> simp only [WF_u, app_1_odd, mk_sh, S_rv, W_safe, W_rv, S_tree, W0_lin, W0,
              evenCeil] at hu hw ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
      | P_od d =>
        have hd : WF_d d := hwf
        have hd9 := Wd_ge_9 d
        refine ⟨.R_D (.P_tree (.od 2 m d)), fun r h => sweepRV_01_RF_od m h,
          ⟨by omega, hd⟩, by simp [NotBadRD], by simp, ?_, ?_,
          by simp only [S_rv]; (try omega), ?_, fun _ => by simp [GoodRV], ?_⟩
        · cases d <;> simp only [W_rv, W0_lin, W0, Wd, Tree.endOne.injEq, reduceCtorEq, ↓reduceIte,
          ite_true, ite_false, not_false_eq_true, not_true_eq_false, ne_eq]
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · cases d <;> simp only [W_safe, W_rv, W0_lin, W0, Wd, Tree.endOne.injEq, reduceCtorEq,
          ↓reduceIte, ite_true, ite_false, not_false_eq_true, not_true_eq_false, ne_eq]
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
            W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
          all_goals (try split_ifs)
          all_goals (try dsimp only [W0, Wd] at *)
          all_goals (try split_ifs)
          all_goals (try exact not_false)
          all_goals (try omega)
        · intro rem _ hbad
          cases rem with
          | zero => simpa [BadRV] using hbad
          | succ r =>
            simpa [BadRV, add_c, set_c, tree_c,
              show 2 + (r + 1) = r + 1 + 1 + 1 by omega] using hbad
        · intro _ M
          cases M with
          | zero =>
            cases d <;> simp only [app_1_odd, mk_stop, sub_c, set_c, tree_c,
              W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd, stopOnePosBonus, evenCeil,
                Tree.endOne.injEq, not_false_eq_true, not_true_eq_false, ne_eq, Nat.reduceLeDiff,
                zero_add, add_zero] at hd9 ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)
          | succ M =>
            cases d <;> simp only [app_1_odd, mk_sh, W_safe, W_rv, S_rv, S_tree, W0_lin, W0, Wd,
              evenCeil, Tree.endOne.injEq, and_false, false_and, not_false_eq_true,
                not_true_eq_false, ne_eq, Nat.reduceLeDiff] at hd9 ⊢
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs at * )
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)

abbrev MasterStmt (n : Nat) : Prop :=
  (∀ u, WF_u u → M_u u = n → PostU u) ∧
  (∀ d0, WF_d d0 → tree_c d0 = 0 → M_d0 d0 = n → PostD0 d0) ∧
  (∀ rv, WF_rv rv → M_rv rv = n → ∃ rvn, PostRV rv rvn)

theorem master_branch_U (n : Nat) (ih : ∀ m, m < n → MasterStmt m) :
    ∀ u, WF_u u → M_u u = n → PostU u := by
      intro u hu hmu
      cases u with
      | endZero c => exact postU_endZero c hu
      | endStop c => exact postU_endStop c hu
      | endOne c => exact postU_endOne c hu
      | oneEnd c => exact postU_oneEnd c hu
      | stopOne c => exact postU_stopOne c hu
      | stop c d => exact postU_stop c d hu
      | sh c m u2 =>
        rcases hu with ⟨hc, hnot1, hu2⟩
        have hmu_eq : W0 (.sh c m u2) + 3 = n := by simpa [M_u] using hmu
        have hlt_u2 : M_u u2 < n := by
          have hw2 := W0_ge_11 u2
          cases u2 <;> simp only [M_u, W0] at hmu_eq ⊢ ; all_goals (try omega)
        obtain ⟨rv2, hsw2, hwf2, hnb2, _, hw2, _, hodd2, hbad2,
          _⟩ := (ih (M_u u2) hlt_u2).1 u2 hu2 rfl
        have hsw_init := sweepRV_app_1_odd m hwf2 hsw2
        have hwf_init := WF_rv_app_1_odd m hwf2
        have hgood_init : GoodRV (app_1_odd m rv2) := by
          apply goodRV_of_odd
          intro hm0
          exact (hnb2 (fun he => hnot1 ⟨hm0, he⟩)).1
        obtain ⟨how_init, hows_init, hos_init⟩ := hodd2 m hnot1
        have ih_step : ∀ rv', WF_rv rv' → W_rv rv' ≤ W0 (.sh c m u2) → ∃ rvn, PostRV rv' rvn := by
          intro rv' hwf' hw'
          exact (ih (M_rv rv') (by simp only [M_rv]; (try omega))).2.2 rv' hwf' rfl
        have hbudget : W_rv (app_1_odd m rv2) + 2 * (c - 1) ≤ W0 (.sh c m u2) := by
          simp only [W0]; (try omega)
        obtain ⟨rvf, hswf, hwff, hnbf, hnff, _, hwf_w, hwf_ws, hwf_s, hbad_f, hodd_f⟩ :=
          iter_app_01_pos (c - 1) (W0 (.sh c m u2)) ih_step hsw_init hwf_init hgood_init hbudget
        have hc_eq : c - 1 + 1 = c := by omega
        rw [hc_eq] at hswf hwf_w hwf_ws hwf_s hbad_f
        have hws_sh : W_safe rvf ≤ W0 (.sh c m u2) + 2 := by
          simp only [W0] at hows_init hwf_ws ⊢; (try omega)
        refine ⟨rvf, ?_, hwff, fun _ => hnbf, hnff, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [evalT_sh] using hswf
        · simp only [W0] at hbudget hwf_w ⊢; (try omega)
        · simpa [isLeaf] using hws_sh
        · intro M _
          obtain ⟨how_f, hows_f, hos_f⟩ := hodd_f M
          refine ⟨by omega, by omega, ?_⟩
          exact le_trans hos_f (max_le (le_max_left _ _) (le_trans (evenCeil_mono (by omega))
            (le_max_right _ _)))
        · intro c' M hc' _ hw0 _
          simp only [isLeaf] at hc'
          exact not_badRV_of_W_safe_le c' M hwff hnff hc' (by omega)
        · intro hr
          rcases hr with ⟨⟨_, hsh_ge⟩, hnbr⟩
          have hec_le : evenCeil (W0 u2 + 9) ≤ 2 * c + 20 := by
            unfold evenCeil; (try omega)
          have hbad_init : ¬ BadRV c (app_1_odd m rv2) :=
            hbad2 c m (by
            all_goals (try split_ifs)
            all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
              W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
            all_goals (try split_ifs)
            all_goals (try dsimp only [W0, Wd] at *)
            all_goals (try split_ifs)
            all_goals (try exact not_false)
            all_goals (try omega)) hnot1 hsh_ge hnbr
          exact S_rv_RD_of_le_20 hwff (by omega) (hbad_f (by omega) hbad_init)
      | od c m d =>
        rcases hu with ⟨hc, hd⟩
        by_cases hlt_c : c + 1 ≤ tree_c d
        · exact postU_od_lt_cd c m hc hd hlt_c
        · have hge_c : c ≥ tree_c d := by omega
          have hmu_eq : W0 (.od c m d) + 3 = n := by simpa [M_u] using hmu
          set d0 := set_c 0 d
          have hd0_wf : WF_d d0 := WF_d_set_c 0 hd
          have hd0_c : tree_c d0 = 0 := tree_c_set_c 0 d
          have hlt_d0 : M_d0 d0 < n := by
            cases d <;> simp only [d0, set_c, M_d0, W0, Wd] at hmu_eq ⊢ ; all_goals (try omega)
          obtain ⟨rv0, hsw0, hwf0, hnb0, _, _, hodd0⟩ :=
            (ih (M_d0 d0) hlt_d0).2.1 d0 hd0_wf hd0_c rfl
          have hpref := sweep_od_prefix m hd hwf0 hsw0
          have hdf : set_c (tree_c d) d0 = d := by
            cases d <;> simp [d0, set_c, tree_c]
          obtain ⟨how_init, hows_init, hos_init, hbad_init0⟩ := hodd0 (tree_c d) m
          simp only [hdf] at how_init hows_init hos_init hbad_init0
          have hgood_init : GoodRV (app_1_odd (m + 2 * tree_c d) rv0) :=
            goodRV_of_odd _ (fun _ => hnb0.1)
          have hwf_init := WF_rv_app_1_odd (m + 2 * tree_c d) hwf0
          by_cases heq_c : c = tree_c d
          · subst heq_c
            have hev_eq : ((([0, 1] : List (Fin 2)) ^ tree_c d) +>
                ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d))) =
                evalT (.od (tree_c d) m d) := by
              simp [evalT_od]
            rw [hev_eq] at hpref
            have hnf_eq : ∀ p', app_1_odd (m + 2 * tree_c d) rv0 ≠ .R_F 0 p' := by
              intro p'
              have hm_pos : m + 2 * tree_c d = (m + 2 * tree_c d - 1) + 1 := by omega
              rw [hm_pos]
              exact app_1_odd_pos_ne_RF0 _ rv0 p'
            have hws_eq : W_safe (app_1_odd (m + 2 * tree_c d) rv0) ≤ W0 (.od (tree_c d) m d) + 2
              := by
              simp only [W0]; (try omega)
            refine ⟨app_1_odd (m + 2 * tree_c d) rv0, hpref, hwf_init,
              fun _ => notBadRD_app_1_odd _ _, hnf_eq, by simp only [W0]; (try omega),
              by simpa [isLeaf] using hws_eq, ?_, ?_, ?_⟩
            · intro M _
              have hm_pos : m + 2 * tree_c d = (m + 2 * tree_c d - 1) + 1 := by omega
              have how_f := (odd_of_app_1_odd_pos M (m + 2 * tree_c d - 1) hwf0).1
              have hows_f := odd_wsafe_of_app_1_odd_pos M (m + 2 * tree_c d - 1) hwf0
              have hos_f := odd_S_of_app_1_odd_pos M (m + 2 * tree_c d - 1) hwf0
              rw [← hm_pos] at how_f hows_f hos_f
              refine ⟨by simp only [W0]; (try omega), by simp only [W0]; (try omega), ?_⟩
              have hmon :=
                evenCeil_mono (show W_rv (app_1_odd (m + 2 * tree_c d) rv0) + 7 ≤ W0 (.od (tree_c
                d) m d) + 9 by simp only [W0]; (try omega))
              exact le_trans hos_f (max_le (le_max_left _ _) (le_trans hmon (le_max_right _ _)))
            · intro c' M hc' _ hw0 _
              simp only [isLeaf] at hc'
              exact not_badRV_of_W_safe_le c' M hwf_init hnf_eq hc' (by omega)
            · intro hr
              exfalso
              rcases Wd_ge_2c_9 d with rfl | hge
              · simp [tree_c] at hc
              · have hgt : Wd d ≥ 2 * tree_c d + 10 := by
                  cases d with
                  | endZero c | endStop c | endOne c | oneEnd c | stopOne c =>
                    simp only [Wd, tree_c] at hc ⊢
                    all_goals (try split_ifs)
                    all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od,
                      W_ra_tree, W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
                    all_goals (try split_ifs)
                    all_goals (try dsimp only [W0, Wd] at *)
                    all_goals (try split_ifs)
                    all_goals (try exact not_false)
                    all_goals (try omega)
                  | stop c d2 => have := Wd_ge_9 d2; simp only [Wd, tree_c]; (try omega)
                  | od c m2 d2 => have := Wd_ge_9 d2; simp only [Wd, tree_c]; (try omega)
                  | sh c m2 u2 => have := W0_ge_11 u2; simp only [Wd, tree_c]; (try omega)
                have hrc := hr.1
                simp [WF_r_core] at hrc; (try omega)
          · have hgt : c > tree_c d := by omega
            have ih_step : ∀ rv', WF_rv rv' → W_rv rv' ≤ W0 (.od c m d) → ∃ rvn,
              PostRV rv' rvn := by
              intro rv' hwf' hw'
              exact (ih (M_rv rv') (by simp only [M_rv]; (try omega))).2.2 rv' hwf' rfl
            set k := c - tree_c d - 1
            have hk_eq : k + 1 = c - tree_c d := by omega
            have hbudget : W_rv (app_1_odd (m + 2 * tree_c d) rv0) + 2 * k ≤ W0 (.od c m d) := by
              simp only [W0]; (try omega)
            obtain ⟨rvf, hswf, hwff, hnbf, hnff, _, hwf_w, hwf_ws, hwf_s, hbad_f, hodd_f⟩ :=
              iter_app_01_pos k (W0 (.od c m d)) ih_step hpref hwf_init hgood_init hbudget
            rw [hk_eq] at hswf hwf_w hwf_ws hwf_s hbad_f
            have heval_eq : ((([0, 1] : List (Fin 2)) ^ (c - tree_c d)) +>
                ((([0, 1] : List (Fin 2)) ^ tree_c d) +>
                  ((([1, 1] : List (Fin 2)) ^ m) +> ((1 : Fin 2) >> (0 : Fin 2) >> evalT d)))) =
                evalT (.od c m d) := by
              rw [← ListBlank.append_pow_add, show c - tree_c d + tree_c d = c by omega]
              rfl
            rw [heval_eq] at hswf
            have hws_od : W_safe rvf ≤ W0 (.od c m d) + 2 := by
              simp only [W0] at hows_init hwf_ws ⊢; (try omega)
            refine ⟨rvf, hswf, hwff, fun _ => hnbf, hnff, by omega,
              by simpa [isLeaf] using hws_od, ?_, ?_, ?_⟩
            · intro M _
              obtain ⟨how_f, hows_f, hos_f⟩ := hodd_f M
              refine ⟨by omega, by omega, ?_⟩
              have hmon :=
                evenCeil_mono (show W_rv (app_1_odd (m + 2 * tree_c d) rv0) + 2 * k + 9 ≤ W0 (.od
                c m d) + 9 by omega)
              exact le_trans hos_f (max_le (le_max_left _ _) (le_trans hmon (le_max_right _ _)))
            · intro c' M hc' _ hw0 _
              simp only [isLeaf] at hc'
              exact not_badRV_of_W_safe_le c' M hwff hnff hc' (by omega)
            · intro hr
              rcases hr with ⟨⟨_, hc_ez, hod_ge⟩, hnbr⟩
              have hec_le : evenCeil (Wd d + 11 + stopOnePosBonus d - 2 * tree_c d) ≤ 2 * (c -
                tree_c d) + 20 := by
                unfold evenCeil; (try omega)
              have hcsum : tree_c d + (c - tree_c d) = c := by omega
              have hbad_st : ¬ BadRV (c - tree_c d) (app_1_odd (m + 2 * tree_c d) rv0) :=
                hbad_init0 (c - tree_c d) (by omega) (by omega) (by omega) (by rwa [hcsum])
              have hs_le : S_rv rvf ≤ 20 := by
                all_goals (try split_ifs at hc_ez hos_init )
                all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                  W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
                all_goals (try split_ifs at hc_ez hos_init )
                all_goals (try dsimp only [W0, Wd] at *)
                all_goals (try split_ifs)
                all_goals (try exact not_false)
                all_goals (try omega)
              have hs_init_le : S_rv (app_1_odd (m + 2 * tree_c d) rv0) ≤ 20 + 2 * (c - tree_c d)
                := by
                all_goals (try split_ifs at hc_ez hos_init )
                all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                  W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
                all_goals (try split_ifs at hc_ez hos_init )
                all_goals (try dsimp only [W0, Wd] at *)
                all_goals (try split_ifs)
                all_goals (try exact not_false)
                all_goals (try omega)
              exact S_rv_RD_of_le_20 hwff hs_le (hbad_f hs_init_le hbad_st)
theorem master_branch_D0 (n : Nat) (ih : ∀ m, m < n → MasterStmt m) :
    ∀ d0, WF_d d0 → tree_c d0 = 0 → M_d0 d0 = n → PostD0 d0 := by
      intro d0 hd0 hc0 hmd0
      cases d0 with
      | endZero c => simp only [tree_c] at hc0; subst hc0; exact postD0_endZero
      | endStop c => simp only [tree_c] at hc0; subst hc0; exact postD0_endStop
      | endOne c => simp only [tree_c] at hc0; subst hc0; exact postD0_endOne
      | oneEnd c => simp only [tree_c] at hc0; subst hc0; exact postD0_oneEnd
      | stopOne c => simp only [tree_c] at hc0; subst hc0; exact postD0_stopOne
      | stop c d2 => simp only [tree_c] at hc0; subst hc0; exact postD0_stop hd0
      | sh c m2 u2 =>
        simp only [tree_c] at hc0; subst hc0
        rcases hd0 with ⟨hnot1, hu2⟩
        have hmd0_eq : Wd (.sh 0 m2 u2) + 7 = n := by simpa [M_d0] using hmd0
        have hlt_u2 : M_u u2 < n := by
          cases u2 <;> simp only [M_u, Wd, W0] at hmd0_eq ⊢ ; all_goals (try omega)
        obtain ⟨rv2, hsw2, hwf2, hnb2, _, hw2, hws2, _, _, _⟩ := (ih (M_u u2) hlt_u2).1 u2 hu2 rfl
        have hsw_ev := sweepRV_app_1_even m2 hwf2 hsw2
        have hwf_ev := WF_rv_app_1_even m2 hwf2
        have hw_ev_le : W_rv (app_1_even m2 rv2) ≤ Wd (.sh 0 m2 u2) + 2 := by
          have he := W_rv_app_1_even_le m2 hwf2
          simp only [Wd]; (try omega)
        have hws_ev_le : W_safe (app_1_even m2 rv2) ≤ Wd (.sh 0 m2 u2) + 2 := by
          cases m2 with
          | zero =>
              simp only [app_1_even, Wd] at hws2 ⊢
              all_goals (try split_ifs at hws2 )
              all_goals (try dsimp only [W0_lin, W0, Wd, S_tree, S_ra_tree, S_ra_od, W_ra_tree,
                W_ra_od, stopOnePosBonus, isLeaf, evenCeil, tree_c, set_c] at *)
              all_goals (try split_ifs at hws2 )
              all_goals (try dsimp only [W0, Wd] at *)
              all_goals (try split_ifs)
              all_goals (try exact not_false)
              all_goals (try omega)
          | succ m2' =>
            have hes := W_safe_app_1_even_pos m2' hwf2
            simp only [Wd]; (try omega)
        have hlt_ev : M_rv (app_1_even m2 rv2) < n := by simp only [M_rv]; (try omega)
        obtain ⟨rvn, hstep, hwfn, hnbn, hnfn, hwn, hwsn, _, _, _, hodd_n⟩ :=
          (ih (M_rv (app_1_even m2 rv2)) hlt_ev).2.2 (app_1_even m2 rv2) hwf_ev rfl
        have hsw_fin : SweepRV ((0 : Fin 2) >> evalT (.sh 0 m2 u2)) rvn := by
          have h1 := hstep _ hsw_ev
          have heq : ((0 : Fin 2) >> evalT (.sh 0 m2 u2)) =
              ((0 : Fin 2) >> (1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ m2) +> evalT u2)) := by
            simp only [evalT_sh, list_pow_zero, ListBlank.append_nil]
            have hsw := swap_1_11_pow m2 (evalT u2)
            simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
            rw [hsw]
          rw [heq]; exact h1
        have hw20 := W0_ge_11 u2
        have hcu2 := tree_c_pos_of_WF_u hu2
        refine ⟨rvn, hsw_fin, hwfn, hnbn, fun _ => ⟨by omega, by omega⟩, ?_, ?_⟩
        · intro m
          cases m with
          | zero => simp only [app_1_even, ↓reduceIte, ite_true, ite_false, ne_eq, zero_add,
            add_zero]; (try omega)
          | succ m =>
            have he := W_rv_app_1_even_le (m + 1) hwfn
            have hes := W_safe_app_1_even_pos m hwfn
            omega
        · intro cd m
          have hnez : set_c cd (.sh 0 m2 u2) ≠ .endZero 1 := by simp [set_c]
          have hlin : Wd (set_c cd (.sh 0 m2 u2)) = 2 * cd + Wd (.sh 0 m2 u2) := by
            simp only [set_c, Wd]; (try omega)
          have hbonus0 : stopOnePosBonus (set_c cd (.sh 0 m2 u2)) = 0 := rfl
          simp only [hnez, ↓reduceIte, hlin, hbonus0, Nat.add_zero,
            show 2 * cd + Wd (.sh 0 m2 u2) + 11 - 2 * cd = Wd (.sh 0 m2 u2) + 11 by omega]
          have hbad_sh : ∀ rem, rem ≥ 1 → cd + rem ≥ 2 →
              2 * cd + Wd (.sh 0 m2 u2) ≤ 2 * (cd + rem) + 9 →
              ¬ BadRoot (.od (cd + rem) m (set_c cd (.sh 0 m2 u2))) →
              ¬ BadRV rem (app_1_odd (m + 2 * cd) rvn) := by
            intro rem hrem _ hwd_le _
            exact not_badRV_of_W_safe_le rem (m + 2 * cd) hwfn hnfn hrem (by omega)
          cases m2 with
          | zero =>
            have hw_ev0 : W_rv (app_1_even 0 rv2) ≤ Wd (.sh 0 0 u2) := by
              simp only [app_1_even, Wd, ↓reduceIte, ite_true, ite_false, ne_eq, eq_self,
                Nat.reduceEqDiff, zero_add, add_zero]; (try omega)
            have hwn0 : W_rv rvn ≤ Wd (.sh 0 0 u2) + 2 := by omega
            have how := W_rv_app_1_odd_le_4 (m + 2 * cd) hwfn
            have hows := W_safe_app_1_odd_le_4 (m + 2 * cd) hwfn hnfn hnbn.2
            have hos := S_rv_app_1_odd_le (m + 2 * cd) hwfn
            have hge24 : evenCeil (Wd (.sh 0 0 u2) + 11) ≥ 24 := by
              unfold evenCeil; simp only [Wd]; (try omega)
            have hmon := evenCeil_mono (show W_rv rvn + 9 ≤ Wd (.sh 0 0 u2) + 11 by omega)
            exact ⟨by omega, by omega, by omega, hbad_sh⟩
          | succ m2' =>
            have hg_ev : GoodRV (app_1_even (m2' + 1) rv2) := by
              cases rv2 <;> simp [app_1_even, GoodRV]
            obtain ⟨how, hows, hos⟩ := hodd_n hg_ev (m + 2 * cd)
            have hge24 : evenCeil (Wd (.sh 0 (m2' + 1) u2) + 11) ≥ 24 := by
              unfold evenCeil; simp only [Wd]; (try omega)
            have hmon :=
              evenCeil_mono (show W_rv (app_1_even (m2' + 1) rv2) + 9 ≤ Wd (.sh 0 (m2' + 1) u2) +
              11 by omega)
            exact ⟨by omega, by omega, by omega, hbad_sh⟩
      | od c m2 d2 =>
        simp only [tree_c] at hc0; subst hc0
        by_cases hes0 : m2 = 0 ∧ d2 = .endStop 0
        · rcases hes0 with ⟨rfl, rfl⟩; exact postD0_od_0_endStop0
        · by_cases hpos : tree_c d2 ≥ 1
          · exact postD0_od_pos m2 hd0 hpos
          · have hc2 : tree_c d2 = 0 := by omega
            have hmd0_eq : Wd (.od 0 m2 d2) + 7 = n := by simpa [M_d0] using hmd0
            have hlt_d2 : M_d0 d2 < n := by
              cases d2 <;> simp only [M_d0, Wd] at hmd0_eq ⊢ ; all_goals (try omega)
            obtain ⟨rv2, hsw2, hwf2, hnb2, hw2_not_es, hw2_ev, _⟩ :=
              (ih (M_d0 d2) hlt_d2).2.1 d2 hd0 hc2 rfl
            have hsw_ev := sweepRV_app_1_even m2 hwf2 hsw2
            have hwf_ev := WF_rv_app_1_even m2 hwf2
            have hw_ev_le : W_rv (app_1_even m2 rv2) ≤ Wd (.od 0 m2 d2) + 2 := by
              have := (hw2_ev m2).1; simp only [Wd]; (try omega)
            have hws_ev_le : W_safe (app_1_even m2 rv2) ≤ Wd (.od 0 m2 d2) + 2 := by
              have := (hw2_ev m2).2; simp only [Wd]; (try omega)
            have hlt_ev : M_rv (app_1_even m2 rv2) < n := by simp only [M_rv]; (try omega)
            obtain ⟨rvn, hstep, hwfn, hnbn, hnfn, hwn, hwsn, _, _, _, hodd_n⟩ :=
              (ih (M_rv (app_1_even m2 rv2)) hlt_ev).2.2 (app_1_even m2 rv2) hwf_ev rfl
            have hsw_fin : SweepRV ((0 : Fin 2) >> evalT (.od 0 m2 d2)) rvn := by
              have h1 := hstep _ hsw_ev
              have heq : ((0 : Fin 2) >> evalT (.od 0 m2 d2)) =
                  ((0 : Fin 2) >> (1 : Fin 2) >> ((([1,
                    1] : List (Fin 2)) ^ m2) +> ((0 : Fin 2) >> evalT d2))) := by
                simp only [evalT_od, list_pow_zero, ListBlank.append_nil]
                have hsw := swap_1_11_pow m2 ((0 : Fin 2) >> evalT d2)
                simp only [ListBlank.append_cons, ListBlank.append_nil] at hsw
                rw [hsw]
              rw [heq]; exact h1
            have hd9 := Wd_ge_9 d2
            refine ⟨rvn, hsw_fin, hwfn, hnbn, fun _ => ⟨by omega, by omega⟩, ?_, ?_⟩
            · intro m
              cases m with
              | zero => simp only [app_1_even, ↓reduceIte, ite_true, ite_false, ne_eq, zero_add,
                add_zero]; (try omega)
              | succ m =>
                have he := W_rv_app_1_even_le (m + 1) hwfn
                have hes := W_safe_app_1_even_pos m hwfn
                omega
            · intro cd m
              have hnez : set_c cd (.od 0 m2 d2) ≠ .endZero 1 := by simp [set_c]
              have hlin : Wd (set_c cd (.od 0 m2 d2)) = 2 * cd + Wd (.od 0 m2 d2) := by
                simp only [set_c, Wd]; (try omega)
              have hbonus0 : stopOnePosBonus (set_c cd (.od 0 m2 d2)) = 0 := rfl
              simp only [hnez, ↓reduceIte, hlin, hbonus0, Nat.add_zero,
                show 2 * cd + Wd (.od 0 m2 d2) + 11 - 2 * cd = Wd (.od 0 m2 d2) + 11 by omega]
              have hge24 : evenCeil (Wd (.od 0 m2 d2) + 11) ≥ 24 := by
                unfold evenCeil; simp only [Wd]; (try omega)
              have hbad_od : ∀ rem, rem ≥ 1 → cd + rem ≥ 2 →
                  2 * cd + Wd (.od 0 m2 d2) ≤ 2 * (cd + rem) + 9 →
                  ¬ BadRoot (.od (cd + rem) m (set_c cd (.od 0 m2 d2))) →
                  ¬ BadRV rem (app_1_odd (m + 2 * cd) rvn) := by
                intro rem hrem _ hwd_le _
                exact not_badRV_of_W_safe_le rem (m + 2 * cd) hwfn hnfn hrem (by omega)
              cases m2 with
              | zero =>
                have hes : d2 ≠ .endStop 0 := fun he => hes0 ⟨rfl, he⟩
                have hw_ev0 : W_rv (app_1_even 0 rv2) ≤ Wd (.od 0 0 d2) := by
                  have := (hw2_not_es hes).1; simp only [app_1_even, Wd, ↓reduceIte, ite_true,
                    ite_false, ne_eq, eq_self, Nat.reduceEqDiff, zero_add, add_zero]; (try omega)
                have hwn0 : W_rv rvn ≤ Wd (.od 0 0 d2) + 2 := by omega
                have how := W_rv_app_1_odd_le_4 (m + 2 * cd) hwfn
                have hows := W_safe_app_1_odd_le_4 (m + 2 * cd) hwfn hnfn hnbn.2
                have hos := S_rv_app_1_odd_le (m + 2 * cd) hwfn
                have hmon := evenCeil_mono (show W_rv rvn + 9 ≤ Wd (.od 0 0 d2) + 11 by omega)
                exact ⟨by omega, by omega, by omega, hbad_od⟩
              | succ m2' =>
                have hg_ev : GoodRV (app_1_even (m2' + 1) rv2) := by
                  cases rv2 <;> simp [app_1_even, GoodRV]
                obtain ⟨how, hows, hos⟩ := hodd_n hg_ev (m + 2 * cd)
                have hmon :=
                  evenCeil_mono (show W_rv (app_1_even (m2' + 1) rv2) + 9 ≤ Wd (.od 0 (m2' + 1)
                  d2) + 11 by omega)
                exact ⟨by omega, by omega, by omega, hbad_od⟩
theorem master_branch_RV (n : Nat) (ih : ∀ m, m < n → MasterStmt m) :
    ∀ rv, WF_rv rv → M_rv rv = n → ∃ rvn, PostRV rv rvn := by
      intro rv hwf hmrv
      cases rv with
      | R_D p => exact postRV_step_nonRA hwf (by simp)
      | R_F m p => exact postRV_step_nonRA hwf (by simp)
      | R_A m p =>
        cases p with
        | P_tree w =>
          have hw : WF_u w := hwf
          cases w with
          | endZero c => exact postRV_RA_leaves m (.endZero c) hw trivial
          | endStop c => exact postRV_RA_leaves m (.endStop c) hw trivial
          | endOne c => exact postRV_RA_leaves m (.endOne c) hw trivial
          | oneEnd c => exact postRV_RA_leaves m (.oneEnd c) hw trivial
          | stopOne c => exact postRV_RA_leaves m (.stopOne c) hw trivial
          | stop c d =>
            obtain ⟨rv0, hsw0, hwf0, hnb0, _, _, _, hodd0, hbad0, _⟩ := postU_stop c d hw
            obtain ⟨how0, _, hos0⟩ := hodd0 m (by simp)
            have hw9 := Wd_ge_9 d
            have hwc : c ≥ 1 := hw.1
            refine ⟨_, postRV_of_RA_good m hwf0 hsw0 (fun _ => hnb0 (by simp)) ?_ ?_ ?_⟩
            · simpa [W_rv, W_ra_tree] using how0
            · conv_rhs => dsimp only [S_rv, S_ra_tree]
              have hge24 : evenCeil (W0 (.stop c d) + 9) ≥ 24 := by
                unfold evenCeil; simp only [W0]; (try omega)
              omega
            · intro rem hrem hs
              have hge := evenCeil_ge (W0 (.stop c d) + 9)
              simp only [S_rv, S_ra_tree] at hs
              exact hbad0 rem (m + 1) (by simp only [isLeaf, reduceCtorEq, ↓reduceIte, ite_true,
                ite_false, Bool.false_eq_true, ne_eq]; (try omega)) (by simp) (by omega) (by
                simp [BadRoot])
          | od c m2 d2 =>
            have hlt : M_u (.od c m2 d2) < n := by
              simp only [M_u, M_rv, W_rv, W_ra_tree, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
                Bool.false_eq_true, ne_eq] at hmrv ⊢; (try omega)
            obtain ⟨rv0, hsw0, hwf0, hnb0, _, _, _, hodd0, hbad0, _⟩ :=
              (ih (M_u (.od c m2 d2)) hlt).1 (.od c m2 d2) hw rfl
            obtain ⟨how0, _, hos0⟩ := hodd0 m (by simp)
            have hw9 := Wd_ge_9 d2
            have hwc : c ≥ 2 := hw.1
            refine ⟨_, postRV_of_RA_good m hwf0 hsw0 (fun _ => hnb0 (by simp)) ?_ ?_ ?_⟩
            · simpa [W_rv, W_ra_tree] using how0
            · conv_rhs => dsimp only [S_rv, S_ra_tree]
              have hge24 : evenCeil (W0 (.od c m2 d2) + 9) ≥ 24 := by
                unfold evenCeil; simp only [W0]; (try omega)
              omega
            · intro rem hrem hs
              have hge := evenCeil_ge (W0 (.od c m2 d2) + 9)
              simp only [S_rv, S_ra_tree] at hs
              exact hbad0 rem (m + 1) (by simp only [isLeaf, reduceCtorEq, ↓reduceIte, ite_true,
                ite_false, Bool.false_eq_true, ne_eq]; (try omega)) (by simp) (by omega) (by
                simp [BadRoot])
          | sh c m2 u2 =>
            have hlt : M_u (.sh c m2 u2) < n := by
              simp only [M_u, M_rv, W_rv, W_ra_tree, reduceCtorEq, ↓reduceIte, ite_true, ite_false,
                Bool.false_eq_true, ne_eq] at hmrv ⊢; (try omega)
            obtain ⟨rv0, hsw0, hwf0, hnb0, _, _, _, hodd0, hbad0, _⟩ :=
              (ih (M_u (.sh c m2 u2)) hlt).1 (.sh c m2 u2) hw rfl
            obtain ⟨how0, _, hos0⟩ := hodd0 m (by simp)
            have hw11 := W0_ge_11 u2
            have hwc : c ≥ 2 := hw.1
            refine ⟨_, postRV_of_RA_good m hwf0 hsw0 (fun _ => hnb0 (by simp)) ?_ ?_ ?_⟩
            · simpa [W_rv, W_ra_tree] using how0
            · conv_rhs => dsimp only [S_rv, S_ra_tree]
              have hge24 : evenCeil (W0 (.sh c m2 u2) + 9) ≥ 24 := by
                unfold evenCeil; simp only [W0]; (try omega)
              omega
            · intro rem hrem hs
              have hge := evenCeil_ge (W0 (.sh c m2 u2) + 9)
              simp only [S_rv, S_ra_tree] at hs
              exact hbad0 rem (m + 1) (by simp only [isLeaf, reduceCtorEq, ↓reduceIte, ite_true,
                ite_false, Bool.false_eq_true, ne_eq]; (try omega)) (by simp) (by omega) (by
                simp [BadRoot])
        | P_od d =>
          have hd : WF_d d := hwf
          by_cases hpos : tree_c d ≥ 1
          · exact postRV_RA_od_pos m hd hpos
          · have hc0 : tree_c d = 0 := by omega
            cases d with
            | endZero c => exact postRV_RA_od_base0 m (.endZero c) hd hc0 trivial
            | endStop c => exact postRV_RA_od_base0 m (.endStop c) hd hc0 trivial
            | endOne c => exact postRV_RA_od_base0 m (.endOne c) hd hc0 trivial
            | oneEnd c => exact postRV_RA_od_base0 m (.oneEnd c) hd hc0 trivial
            | stopOne c => exact postRV_RA_od_base0 m (.stopOne c) hd hc0 trivial
            | stop c d2 => exact postRV_RA_od_base0 m (.stop c d2) hd hc0 trivial
            | od cd m2 d2 =>
              have hcd0 : cd = 0 := by simpa [tree_c] using hc0
              subst hcd0
              have hlt : M_d0 (.od 0 m2 d2) < n := by
                simp only [M_d0, M_rv, W_rv, W_ra_od] at hmrv ⊢; (try omega)
              obtain ⟨rv0, hsw0, hwf0, hnb0, _, _, hodd0⟩ :=
                (ih (M_d0 (.od 0 m2 d2)) hlt).2.1 (.od 0 m2 d2) hd rfl rfl
              obtain ⟨how0, _, hos0, _⟩ := hodd0 0 m
              simp only [set_c, stopOnePosBonus, Nat.mul_zero, Nat.add_zero,
                Nat.sub_zero] at how0 hos0
              have hd9 := Wd_ge_9 d2
              refine ⟨_, postRV_of_RA_good m hwf0 hsw0 (fun _ => hnb0) ?_ ?_ ?_⟩
              · simpa [W_rv, W_ra_od] using how0
              · conv_rhs => dsimp only [S_rv, S_ra_od, tree_c, set_c, Nat.mul_zero, Nat.zero_add]
                have hnez : Tree.od 0 m2 d2 ≠ .endZero 1 := by simp
                simp only [hnez, ↓reduceIte] at hos0
                have hge24 : evenCeil (Wd (.od 0 m2 d2) + 11) ≥ 24 := by
                  unfold evenCeil; simp only [Wd]; (try omega)
                omega
              · intro rem hrem hs
                obtain ⟨_, _, _, hbad0⟩ := hodd0 0 (m + 1)
                have hge := evenCeil_ge (Wd (.od 0 m2 d2) + 11)
                simp only [S_rv, S_ra_od, tree_c, set_c, Nat.mul_zero, Nat.zero_add] at hs
                simpa [set_c] using hbad0 rem hrem (by omega)
                  (by simp only [set_c, stopOnePosBonus]; (try omega)) (by simp [set_c, BadRoot])
            | sh cd m2 u2 =>
              have hcd0 : cd = 0 := by simpa [tree_c] using hc0
              subst hcd0
              have hlt : M_d0 (.sh 0 m2 u2) < n := by
                simp only [M_d0, M_rv, W_rv, W_ra_od] at hmrv ⊢; (try omega)
              obtain ⟨rv0, hsw0, hwf0, hnb0, _, _, hodd0⟩ :=
                (ih (M_d0 (.sh 0 m2 u2)) hlt).2.1 (.sh 0 m2 u2) hd rfl rfl
              obtain ⟨how0, _, hos0, _⟩ := hodd0 0 m
              simp only [set_c, stopOnePosBonus, Nat.mul_zero, Nat.add_zero,
                Nat.sub_zero] at how0 hos0
              have hu11 := W0_ge_11 u2
              have hcu2 := tree_c_pos_of_WF_u hd.2
              refine ⟨_, postRV_of_RA_good m hwf0 hsw0 (fun _ => hnb0) ?_ ?_ ?_⟩
              · simpa [W_rv, W_ra_od] using how0
              · conv_rhs => dsimp only [S_rv, S_ra_od, tree_c, set_c, Nat.mul_zero, Nat.zero_add]
                have hnez : Tree.sh 0 m2 u2 ≠ .endZero 1 := by simp
                simp only [hnez, ↓reduceIte] at hos0
                have hge24 : evenCeil (Wd (.sh 0 m2 u2) + 11) ≥ 24 := by
                  unfold evenCeil; simp only [Wd]; (try omega)
                omega
              · intro rem hrem hs
                obtain ⟨_, _, _, hbad0⟩ := hodd0 0 (m + 1)
                have hge := evenCeil_ge (Wd (.sh 0 m2 u2) + 11)
                simp only [S_rv, S_ra_od, tree_c, set_c, Nat.mul_zero, Nat.zero_add] at hs
                simpa [set_c] using hbad0 rem hrem (by omega)
                  (by simp only [set_c, stopOnePosBonus]; (try omega)) (by simp [set_c, BadRoot])

theorem master_ind (n : Nat) : MasterStmt n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    exact ⟨master_branch_U n ih, master_branch_D0 n ih, master_branch_RV n ih⟩

def EraInv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ t : Tree, WF_r t ∧ cfg = eraCfg (evalT t)

theorem era_inv_zero : EraInv (eraCfg ([(0 : Fin 2), 1] +> default)) := by
  refine ⟨.endZero 1, ⟨by simp [WF_r_core, WF_u], by simp [BadRoot]⟩, ?_⟩
  simp [evalT, tree_c, evalCore, list_pow_one]

theorem era_inv_step : ∀ c, EraInv c → ∃ c', (c [sweep_tm]⊢⁺ c') ∧ EraInv c' := by
  rintro _ ⟨t, hrt, rfl⟩
  obtain ⟨rv, hsw, _, _, _, _, _, _, _, hr_step⟩ := (master_ind (M_u t)).1 t hrt.1.1 rfl
  obtain ⟨tn, rfl, hrtn⟩ := hr_step hrt
  simp only [SweepRV] at hsw
  have hstep := era_step hsw
  rw [cons_zero_tailT (tree_c_pos_of_WF_u hrtn.1.1)] at hstep
  exact ⟨eraCfg (evalT tn), hstep, ⟨tn, hrtn, rfl⟩⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  IsNotHalt.of_reachesPlus_invariant init_to_era0 era_inv_zero era_inv_step

-- END GOAL STATEMENT


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA
