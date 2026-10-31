/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RE_1LC1RF_---0LD_0LE1LB_1LF1LD_1RD0RA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RE_1LC1RF_---0LD_0LE1LB_1LF1LD_1RD0RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1LC1RF_HHH0LD_0LE1LB_1LF1LD_1RD0RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RE_1LC1RF_---0LD_0LE1LB_1LF1LD_1RD0RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 0, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Donor machine #311 (`1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC`, `suspect_07`). -/
@[reducible] def holdout_0311_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

-- ============================================================================
-- Section 6: Target Theorem Statement
-- ============================================================================

open Counter

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

@[simp] lemma append_nil (l : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> l = l := rfl
@[simp] lemma append_cons (a : Fin 2) (as : List (Fin 2)) (l : ListBlank (Fin 2)) :
    (a :: as) +> l = a >> (as +> l) := rfl

def cfg_modeC (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (0 : Fin 2) >> l) {{2}}> r)

def cfg_modeE1 (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> r))

def cfg_modeE0_first (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> default))

def cfg_modeE0_loop (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))

def cfg_b101_mid (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))

def cfg_e0f_mid (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))

def cfg_e0l_mid (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)))

def cfg_transA_mid (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))

def cfg_transB_mid (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) {{1}}> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))

lemma init_reaches_modeC :
    (init []) [holdout_0311_tm]⊢⁺ cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default) default := by
  refine run_local_plus_eq (n := 9) (s1 := ⟨[(0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2)], 0, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], ([] : List (Fin 2)), 2, .right⟩) default default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]; rfl
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_nil (l : ListBlank (Fin 2)) :
    (cfg_modeC l default) [holdout_0311_tm]⊢⁺
      cfg_modeE0_first l := by
  refine run_local_plus_eq (n := 5) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2, .right⟩) (s2 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_modeC ((1 : Fin 2) >> (0 : Fin 2) >> l) r := by
  refine run_local_plus_eq (n := 1) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], ([] : List (Fin 2)), 2, .right⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01_b10101 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l)) r := by
  refine run_local_plus_eq (n := 6) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], ([] : List (Fin 2)), 2, .right⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b11 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((1 : Fin 2) >> (1 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l r := by
  refine run_local_plus_eq (n := 2) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01_b000 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_modeE0_loop l r := by
  refine run_local_plus_eq (n := 13) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2, .right⟩) (s2 := ⟨[(0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01_b101_nil_1 (l : ListBlank (Fin 2)) :
    (cfg_modeC ((1 : Fin 2) >> (0 : Fin 2) >> l) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) [holdout_0311_tm]⊢⁺
      cfg_b101_mid l := by
  refine run_local_plus_eq (n := 33) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2, .right⟩) (s2 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01_b101_nil_2 (l : ListBlank (Fin 2)) :
    (cfg_b101_mid l) [holdout_0311_tm]⊢⁺
      cfg_modeE1 ((1 : Fin 2) >> (0 : Fin 2) >> l) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) := by
  refine run_local_plus_eq (n := 32) (s1 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01_b1011101 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 16) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE1_base (r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> default) r) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r))) := by
  refine run_local_plus_eq (n := 24) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE1_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((1 : Fin 2) >> (0 : Fin 2) >> l) r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 5) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01_b101_nil (l : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) :=
  stepPlus_stepPlus_stepPlus (step_modeC_b01 l _)
    (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_1 l)
      (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_2 l) (step_modeE1_b10 l _)))

lemma step_modeE1_b011_10_base (r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default)) r) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))) := by
  refine run_local_plus_eq (n := 33) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE1_b011_10_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l)) r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 14) (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_first_base :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> default)) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) := by
  refine run_local_plus_eq (n := 24) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_first_b10 (l : ListBlank (Fin 2)) :
    (cfg_modeE0_first ((1 : Fin 2) >> (0 : Fin 2) >> l)) [holdout_0311_tm]⊢⁺
      cfg_modeE0_loop l default := by
  refine run_local_plus_eq (n := 5) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_first_b011_10_base_1 :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) [holdout_0311_tm]⊢⁺
      cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> default) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
  refine run_local_plus_eq (n := 35) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) default default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_first_b011_10_base :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)))) :=
  stepPlus_stepPlus_stepPlus step_modeE0_first_b011_10_base_1 (step_modeE1_base _)

lemma step_modeE0_first_b011_10_b10_1 (l : ListBlank (Fin 2)) :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))) [holdout_0311_tm]⊢⁺
      cfg_e0f_mid l := by
  refine run_local_plus_eq (n := 20) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_first_b011_10_b10_2 (l : ListBlank (Fin 2)) :
    (cfg_e0f_mid l) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
  refine run_local_plus_eq (n := 20) (s1 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_first_b011_10_b10 (l : ListBlank (Fin 2)) :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) :=
  stepPlus_stepPlus_stepPlus (step_modeE0_first_b011_10_b10_1 l) (step_modeE0_first_b011_10_b10_2 l)

lemma step_modeE0_loop_base (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((0 : Fin 2) >> (1 : Fin 2) >> default) r) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))
        ((0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 26) (s1 := ⟨[(0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_loop_b10_base (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default)) r) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r))))) := by
  refine run_local_plus_eq (n := 24) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_loop_b10_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l)) r) [holdout_0311_tm]⊢⁺
      cfg_modeE0_loop l ((1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  refine run_local_plus_eq (n := 5) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_loop_b10_b011_10_base_1 (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> default) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  refine run_local_plus_eq (n := 35) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_loop_b10_b011_10_base (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) r) [holdout_0311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)))) :=
  stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_base_1 r) (step_modeE1_base _)

lemma step_modeE0_loop_b10_b011_10_b10_1 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))) r) [holdout_0311_tm]⊢⁺
      cfg_e0l_mid l r := by
  refine run_local_plus_eq (n := 20) (s1 := ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_loop_b10_b011_10_b10_2 (l r : ListBlank (Fin 2)) :
    (cfg_e0l_mid l r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  refine run_local_plus_eq (n := 20) (s1 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeE0_loop_b10_b011_10_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))) r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) :=
  stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_b10_1 l r) (step_modeE0_loop_b10_b011_10_b10_2 l r)

lemma step_modeE0_loop_b011_10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r)))) := by
  refine run_local_plus_eq (n := 27) (s1 := ⟨[(0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop, cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01110_b10_b101_nil_1 (l : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) [holdout_0311_tm]⊢⁺
      cfg_transA_mid l := by
  refine run_local_plus_eq (n := 40)
    (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩)
    l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_transA_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_transA_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01110_b10_b101_nil_2 (l : ListBlank (Fin 2)) :
    (cfg_transA_mid l) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
  refine run_local_plus_eq (n := 40)
    (s1 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩)
    l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE1, cfg_transA_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, cfg_transA_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01110_b10_b101_nil (l : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) :=
  stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b101_nil_1 l) (step_modeC_b01110_b10_b101_nil_2 l)

lemma step_modeC_b01110_b10_b0000101_1 (l r : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_transB_mid l r := by
  refine run_local_plus_eq (n := 23)
    (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩)
    l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, cfg_transB_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, cfg_transB_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01110_b10_b0000101_2 (l r : ListBlank (Fin 2)) :
    (cfg_transB_mid l r) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r)))) := by
  refine run_local_plus_eq (n := 23)
    (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩)
    l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE1, cfg_transB_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, cfg_transB_mid, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

lemma step_modeC_b01110_b10_b0000101 (l r : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [holdout_0311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r)))) :=
  stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b0000101_1 l r) (step_modeC_b01110_b10_b0000101_2 l r)

-- ============================================================================
-- Parametric Left-Tape Encoding and Invariant
-- ============================================================================

def prepend10 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, l => l
  | k + 1, l => (1 : Fin 2) >> (0 : Fin 2) >> prepend10 k l

def encL_tail : List ℕ → ListBlank (Fin 2)
  | [] => (0 : Fin 2) >> (1 : Fin 2) >> default
  | k :: ks =>
    (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      prepend10 k (encL_tail ks)

def encL (k₀ : ℕ) (ks : List ℕ) : ListBlank (Fin 2) :=
  prepend10 k₀ (encL_tail ks)

@[simp] lemma encL_zero_nil : encL 0 [] = (0 : Fin 2) >> (1 : Fin 2) >> default := rfl
@[simp] lemma encL_succ (k : ℕ) (ks : List ℕ) :
    encL (k + 1) ks = (1 : Fin 2) >> (0 : Fin 2) >> encL k ks := rfl
@[simp] lemma encL_zero_cons (k : ℕ) (ks : List ℕ) :
    encL 0 (k :: ks) =
      (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encL k ks := rfl

def prepend01 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | k + 1, r => (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k r

lemma prepend01_add (a b : ℕ) (r : ListBlank (Fin 2)) :
    prepend01 (a + b) r = prepend01 a (prepend01 b r) := by
  induction a with
  | zero => simp [prepend01]
  | succ a ih => simp only [Nat.succ_add, prepend01, ih]

def prepend11_01 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | d + 1, r => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d r

lemma prepend11_01_add (a b : ℕ) (r : ListBlank (Fin 2)) :
    prepend11_01 (a + b) r = prepend11_01 a (prepend11_01 b r) := by
  induction a with
  | zero => simp [prepend11_01]
  | succ a ih => simp only [Nat.succ_add, prepend11_01, ih]

-- ============================================================================
-- Macro Transitions (Mode C / E1 / E0_loop)
-- ============================================================================

lemma modeC_prepend01_star : ∀ (n k₀ : ℕ) (ks : List ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeC (encL k₀ ks) (prepend01 n r)) [holdout_0311_tm]⊢*
      cfg_modeC (encL (k₀ + n) ks) r
  | 0, k₀, ks, r => ⟨0, by simp [prepend01]⟩
  | n + 1, k₀, ks, r => by
    have h1 : (cfg_modeC (encL k₀ ks) ((0 : Fin 2) >> (1 : Fin 2) >> prepend01 n r)) [holdout_0311_tm]⊢⁺
        cfg_modeC (encL (k₀ + 1) ks) (prepend01 n r) := step_modeC_b01 (encL k₀ ks) (prepend01 n r)
    have h2 := modeC_prepend01_star n (k₀ + 1) ks r
    have heq : k₀ + 1 + n = k₀ + (n + 1) := by omega
    rw [heq] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

lemma e0_loop_drain_pairs : ∀ (d rem : ℕ) (xs : List ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeE0_loop (encL (rem + 2 * d) xs) r) [holdout_0311_tm]⊢*
      cfg_modeE0_loop (encL rem xs) (prepend11_01 d r)
  | 0, rem, xs, r => ⟨0, by simp [prepend11_01]⟩
  | d + 1, rem, xs, r => by
    have heq : rem + 2 * (d + 1) = ((rem + 2 * d) + 1) + 1 := by omega
    rw [heq]
    have h1 : (cfg_modeE0_loop (encL (((rem + 2 * d) + 1) + 1) xs) r) [holdout_0311_tm]⊢⁺
        cfg_modeE0_loop (encL (rem + 2 * d) xs) (prepend11_01 1 r) :=
      step_modeE0_loop_b10_b10 (encL (rem + 2 * d) xs) r
    have h2 := e0_loop_drain_pairs d rem xs (prepend11_01 1 r)
    rw [← prepend11_01_add] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

lemma modeE1_drain_k0 : ∀ (k₀ : ℕ) (ks : List ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeE1 (encL k₀ ks) r) [holdout_0311_tm]⊢*
      cfg_modeE1 (encL 0 ks) (prepend01 k₀ r)
  | 0, ks, r => ⟨0, rfl⟩
  | k₀ + 1, ks, r => by
    have h1 : (cfg_modeE1 (encL (k₀ + 1) ks) r) [holdout_0311_tm]⊢⁺
        cfg_modeE1 (encL k₀ ks) (prepend01 1 r) := step_modeE1_b10 (encL k₀ ks) r
    have h2 := modeE1_drain_k0 k₀ ks (prepend01 1 r)
    rw [← prepend01_add] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

lemma modeE1_to_modeC : ∀ (ks : List ℕ) (k₀ : ℕ) (r : ListBlank (Fin 2)),
    ValidKS ks →
    let b := bump_enc k₀ ks
    (cfg_modeE1 (encL k₀ ks) r) [holdout_0311_tm]⊢⁺ cfg_modeC (encL b.1 b.2) r
  | [], k₀, r, _ => by
    dsimp [bump_enc]
    have h1 := modeE1_drain_k0 k₀ [] r
    have h2 : (cfg_modeE1 (encL 0 []) (prepend01 k₀ r)) [holdout_0311_tm]⊢⁺
        cfg_modeC (encL 0 []) (prepend01 3 (prepend01 k₀ r)) := step_modeE1_base (prepend01 k₀ r)
    rw [← prepend01_add, Nat.add_comm 3 k₀] at h2
    have h3 := modeC_prepend01_star (k₀ + 3) 0 [] r
    rw [Nat.zero_add] at h3
    exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)
  | [k₁], k₀, r, _ => by
    dsimp [bump_enc, add_last]
    have h1 := modeE1_drain_k0 k₀ [k₁] r
    cases k₁ with
    | zero =>
      have h2 := step_modeE1_b011_10_base (prepend01 k₀ r)
      have h3 := step_modeC_b01 (encL 0 []) ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r))
      have h4 := step_modeC_b01 (encL 1 []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r)
      have h5 : (cfg_modeC (encL 2 []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r))
          [holdout_0311_tm]⊢⁺ cfg_modeC (encL 0 [3]) (prepend01 k₀ r) :=
        step_modeC_b01_b10101 (encL 2 []) (prepend01 k₀ r)
      have h6 := modeC_prepend01_star k₀ 0 [3] r
      rw [Nat.zero_add] at h6
      exact stepStar_stepPlus_stepPlus h1
        (stepPlus_stepPlus_stepPlus h2
          (stepPlus_stepPlus_stepPlus h3
            (stepPlus_stepPlus_stepPlus h4
              (stepPlus_stepStar_stepPlus h5 h6))))
    | succ k₁' =>
      have h2 : (cfg_modeE1 (encL 0 [k₁' + 1]) (prepend01 k₀ r)) [holdout_0311_tm]⊢⁺
          cfg_modeE1 (encL k₁' []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) :=
        step_modeE1_b011_10_b10 (encL k₁' []) (prepend01 k₀ r)
      have h3 := modeE1_to_modeC [] k₁' ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) trivial
      dsimp [bump_enc] at h3
      have h4 : (cfg_modeC (encL (k₁' + 3) []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r))
          [holdout_0311_tm]⊢⁺ cfg_modeC (encL 0 [k₁' + 4]) (prepend01 k₀ r) :=
        step_modeC_b01_b10101 (encL (k₁' + 3) []) (prepend01 k₀ r)
      have h5 := modeC_prepend01_star k₀ 0 [k₁' + 4] r
      rw [Nat.zero_add] at h5
      have heq : k₁' + 1 + 3 = k₁' + 4 := by omega
      rw [heq]
      exact stepStar_stepPlus_stepPlus h1
        (stepPlus_stepPlus_stepPlus h2
          (stepPlus_stepPlus_stepPlus h3
            (stepPlus_stepStar_stepPlus h4 h5)))
  | k₁ :: k₂ :: ks'', k₀, r, ⟨hk1, hval'⟩ => by
    dsimp [bump_enc, add_last]
    cases k₁ with
    | zero => omega
    | succ k₁' =>
      have h1 := modeE1_drain_k0 k₀ ((k₁' + 1) :: k₂ :: ks'') r
      have h2 : (cfg_modeE1 (encL 0 ((k₁' + 1) :: k₂ :: ks'')) (prepend01 k₀ r)) [holdout_0311_tm]⊢⁺
          cfg_modeE1 (encL k₁' (k₂ :: ks'')) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) :=
        step_modeE1_b011_10_b10 (encL k₁' (k₂ :: ks'')) (prepend01 k₀ r)
      have h3 := modeE1_to_modeC (k₂ :: ks'') k₁' ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) hval'
      dsimp [bump_enc] at h3
      have h4 : (cfg_modeC (encL k₁' (add_last (k₂ :: ks'') 3)) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r))
          [holdout_0311_tm]⊢⁺ cfg_modeC (encL 0 ((k₁' + 1) :: add_last (k₂ :: ks'') 3)) (prepend01 k₀ r) :=
        step_modeC_b01_b10101 (encL k₁' (add_last (k₂ :: ks'') 3)) (prepend01 k₀ r)
      have h5 := modeC_prepend01_star k₀ 0 ((k₁' + 1) :: add_last (k₂ :: ks'') 3) r
      rw [Nat.zero_add] at h5
      exact stepStar_stepPlus_stepPlus h1
        (stepPlus_stepPlus_stepPlus h2
          (stepPlus_stepPlus_stepPlus h3
            (stepPlus_stepStar_stepPlus h4 h5)))

lemma modeC_consume_11_01_nil : ∀ (n k₀ : ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeC (encL k₀ []) (prepend11_01 n r)) [holdout_0311_tm]⊢*
      cfg_modeC (encL (k₀ + 4 * n) []) r
  | 0, k₀, r => ⟨0, by simp [prepend11_01]⟩
  | n + 1, k₀, r => by
    have h1 := step_modeC_b11 (encL k₀ []) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r)
    have h2 := modeE1_to_modeC [] k₀ ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r) trivial
    dsimp [bump_enc] at h2
    have h3 : (cfg_modeC (encL (k₀ + 3) []) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r))
        [holdout_0311_tm]⊢⁺ cfg_modeC (encL (k₀ + 4) []) (prepend11_01 n r) :=
      step_modeC_b01 (encL (k₀ + 3) []) (prepend11_01 n r)
    have h4 := modeC_consume_11_01_nil n (k₀ + 4) r
    have heq : k₀ + 4 + 4 * n = k₀ + 4 * (n + 1) := by omega
    rw [heq] at h4
    exact stepPlus_stepStar (stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 (stepPlus_stepStar_stepPlus h3 h4)))

lemma modeC_consume_11_01_nonempty : ∀ (n k₀ : ℕ) (ks : List ℕ) (r : ListBlank (Fin 2)),
    ks ≠ [] → ValidKS ks →
    (cfg_modeC (encL k₀ ks) (prepend11_01 n r)) [holdout_0311_tm]⊢*
      cfg_modeC (encL (k₀ + n) (add_last ks (3 * n))) r
  | 0, k₀, ks, r, _, _ => ⟨0, by simp [prepend11_01, add_last_zero]⟩
  | n + 1, k₀, ks, r, hne, hval => by
    have h1 := step_modeC_b11 (encL k₀ ks) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r)
    have h2 := modeE1_to_modeC ks k₀ ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r) hval
    rw [bump_enc_nonempty k₀ hne] at h2
    have h3 : (cfg_modeC (encL k₀ (add_last ks 3)) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r))
        [holdout_0311_tm]⊢⁺ cfg_modeC (encL (k₀ + 1) (add_last ks 3)) (prepend11_01 n r) :=
      step_modeC_b01 (encL k₀ (add_last ks 3)) (prepend11_01 n r)
    have h4 := modeC_consume_11_01_nonempty n (k₀ + 1) (add_last ks 3) r
      (add_last_ne_nil ks 3 hne) (ValidKS_add_last ks 3 hval)
    rw [add_last_add] at h4
    have heq1 : k₀ + 1 + n = k₀ + (n + 1) := by omega
    have heq2 : 3 + 3 * n = 3 * (n + 1) := by omega
    rw [heq1, heq2] at h4
    exact stepPlus_stepStar (stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 (stepPlus_stepStar_stepPlus h3 h4)))

lemma unwrap_11_01_1011101_step (m₀ : ℕ) (ms : List ℕ) (R : ListBlank (Fin 2))
    (h_valid : ValidKS ms) :
    let p := bump_enc_twice m₀ ms
    (cfg_modeC (encL m₀ ms)
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R))
      [holdout_0311_tm]⊢⁺
      cfg_modeC (encL 0 ((p.1 + 1) :: p.2)) R := by
  dsimp [bump_enc_twice]
  set p1 := bump_enc m₀ ms
  set p2 := bump_enc p1.1 p1.2
  have h1 := step_modeC_b11 (encL m₀ ms)
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
  have h2 := modeE1_to_modeC ms m₀
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) h_valid
  have h3 := step_modeC_b01_b1011101 (encL p1.1 p1.2) R
  have h4 := modeE1_to_modeC p1.2 p1.1
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
    (ValidKS_bump_enc m₀ ms h_valid)
  have h5 : (cfg_modeC (encL p2.1 p2.2) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R))
      [holdout_0311_tm]⊢⁺ cfg_modeC (encL 0 ((p2.1 + 1) :: p2.2)) R :=
    step_modeC_b01_b10101 (encL p2.1 p2.2) R
  exact stepPlus_stepPlus_stepPlus h1
    (stepPlus_stepPlus_stepPlus h2
      (stepPlus_stepPlus_stepPlus h3
        (stepPlus_stepPlus_stepPlus h4 h5)))

-- ============================================================================
-- Master Lemma 1: e0_loop_leave1_goodks
-- ============================================================================

lemma e0_loop_leave1_goodks :
    ∀ (n : ℕ) (x₀ : ℕ) (xs : List ℕ) (S : ℕ) (R : ListBlank (Fin 2)),
    xs.length = n →
    S ≥ 36 →
    (xs = [] → 2 * S ≤ 35 * x₀) →
    (xs ≠ [] → x₀ ≥ 2 ∧ 2 * S ≤ 35 * (x₀ + 3)) →
    GoodKS (2 * S + 63 * (x₀ + 3)) xs →
    ∃ m₀ ms,
      ((cfg_modeE0_loop (encL x₀ xs) R) [holdout_0311_tm]⊢⁺
        cfg_modeC (encL m₀ ms) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)) ∧
      ValidKS ms ∧
      (ms = [] → m₀ ≥ 7) ∧
      (let p := bump_enc_twice m₀ ms; GoodKS S ((p.1 + 1) :: p.2)) ∧
      ((xs = [] → x₀ ≥ 10) → S = 81 →
        let p1 := bump_enc m₀ ms; GoodKS 81 ((p1.1 + 1) :: p1.2))
  | 0, x₀, xs, S, R, hlen, hS, h_nil, h_cons, h_gks => by
    cases xs with
    | cons _ _ => simp at hlen
    | nil =>
      have hx0 : 2 * S ≤ 35 * x₀ := h_nil rfl
      have hx0_ge : x₀ ≥ 3 := by omega
      set d := x₀ / 2
      set rem := x₀ % 2
      have h_div : rem + 2 * d = x₀ := by omega
      have h_rem : rem = 0 ∨ rem = 1 := by omega
      rcases h_rem with h_even | h_odd
      · -- Case 2: xs = [], x₀ = 2 * d (d ≥ 2)
        have hd : d ≥ 2 := by omega
        refine ⟨d, [3 * d - 3], ?_, trivial, by simp, ?_, ?_⟩
        · have hd_split : x₀ = 0 + 2 * d := by omega
          rw [hd_split]
          have h1 := e0_loop_drain_pairs d 0 [] R
          have h2 : (cfg_modeE0_loop (encL 0 []) (prepend11_01 d R)) [holdout_0311_tm]⊢⁺
              cfg_modeC (encL 0 [0]) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d R) :=
            step_modeE0_loop_base (prepend11_01 d R)
          have h3 : (cfg_modeC (encL 0 [0]) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d R)) [holdout_0311_tm]⊢⁺
              cfg_modeC (encL 1 [0]) (prepend11_01 d R) :=
            step_modeC_b01 (encL 0 [0]) (prepend11_01 d R)
          have hd_eq : d = (d - 1) + 1 := by omega
          have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) := by
            conv_lhs => rw [hd_eq]
            rw [prepend11_01_add]; rfl
          have h4 := modeC_consume_11_01_nonempty (d - 1) 1 [0]
            ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) (by simp) trivial
          simp only [add_last, Nat.zero_add] at h4
          have heq1 : 1 + (d - 1) = d := by omega
          have heq2 : 3 * (d - 1) = 3 * d - 3 := by omega
          rw [← h_p11, heq1, heq2] at h4
          exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 (stepPlus_stepStar_stepPlus h3 h4))
        · simp only [bump_enc_twice, bump_enc, add_last, GoodKS]
          refine ⟨by omega, ?_, trivial⟩
          omega
        · intro hx10 hS81
          have hx10' : x₀ ≥ 10 := hx10 rfl
          have hd5 : d ≥ 5 := by omega
          simp only [bump_enc, add_last, GoodKS]
          refine ⟨by omega, ?_, trivial⟩
          omega
      · -- Case 1: xs = [], x₀ = 2 * d + 1 (d ≥ 1)
        have hd : d ≥ 1 := by omega
        refine ⟨4 * d + 3, [], ?_, trivial, fun _ => by omega, ?_, ?_⟩
        · have hd_split : x₀ = 1 + 2 * d := by omega
          rw [hd_split]
          have h1 := e0_loop_drain_pairs d 1 [] R
          have h2 : (cfg_modeE0_loop (encL 1 []) (prepend11_01 d R)) [holdout_0311_tm]⊢⁺
              cfg_modeC (encL 0 []) (prepend01 3 (prepend11_01 (d + 1) R)) :=
            step_modeE0_loop_b10_base (prepend11_01 d R)
          have h3 := modeC_prepend01_star 3 0 [] (prepend11_01 (d + 1) R)
          rw [Nat.zero_add] at h3
          have h_p11 : prepend11_01 (d + 1) R = prepend11_01 d ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) := by
            rw [prepend11_01_add]; rfl
          have h4 := modeC_consume_11_01_nil d 3 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
          have heq : 3 + 4 * d = 4 * d + 3 := by omega
          rw [← h_p11, heq] at h4
          exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))
        · simp only [bump_enc_twice, bump_enc, GoodKS]
          exact ⟨by omega, trivial⟩
        · intro _ _
          simp only [bump_enc, GoodKS]
          exact ⟨by omega, trivial⟩
  | n' + 1, x₀, xs, S, R, hlen, hS, h_nil, h_cons, h_gks => by
    cases xs with
    | nil => simp at hlen
    | cons x₁ xs_rest =>
      have hlen' : xs_rest.length = n' := by simp at hlen; exact hlen
      have ⟨hx0_ge, hx0_bound⟩ := h_cons (by simp)
      have ⟨h_x1_bound, h_gks_rest⟩ := h_gks
      have hx1_ge : x₁ ≥ 1 := by omega
      have h_valid_xs : ValidKS (x₁ :: xs_rest) :=
        GoodKS_valid (x₁ :: xs_rest) (2 * S + 63 * (x₀ + 3)) (by omega) h_gks
      have h_valid_rest : ValidKS xs_rest :=
        GoodKS_valid xs_rest (2 * S + 63 * (x₀ + 3) + 63 * (x₁ + 2)) (by omega) h_gks_rest
      set d := x₀ / 2
      set rem := x₀ % 2
      have hd : d ≥ 1 := by omega
      have h_rem : rem = 0 ∨ rem = 1 := by omega
      rcases h_rem with h_even | h_odd
      · -- Case 3: xs = x₁ :: xs_rest, x₀ = 2 * d (d ≥ 1)
        have hd_split : x₀ = 0 + 2 * d := by omega
        set b := bump_enc x₁ xs_rest
        cases h_rest : xs_rest with
        | nil =>
          -- Subcase 3a: xs_rest = []
          have hb : b = (x₁ + 3, []) := by simp [b, h_rest, bump_enc]
          refine ⟨x₁ + 4 * d + 3, [], ?_, trivial, fun _ => by omega, ?_, ?_⟩
          · rw [hd_split]
            have h1 := e0_loop_drain_pairs d 0 [x₁] R
            have h2 : (cfg_modeE0_loop (encL 0 [x₁]) (prepend11_01 d R)) [holdout_0311_tm]⊢⁺
                cfg_modeE1 (encL x₁ []) (prepend01 4 (prepend11_01 d R)) :=
              step_modeE0_loop_b011_10 (encL x₁ []) (prepend11_01 d R)
            have h3 := modeE1_to_modeC [] x₁ (prepend01 4 (prepend11_01 d R)) trivial
            dsimp only [bump_enc] at h3
            have h4 := modeC_prepend01_star 4 (x₁ + 3) [] (prepend11_01 d R)
            have hd_eq : d = (d - 1) + 1 := by omega
            have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) := by
              conv_lhs => rw [hd_eq]
              rw [prepend11_01_add]; rfl
            have h5 := modeC_consume_11_01_nil (d - 1) (x₁ + 3 + 4)
              ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
            have heq : x₁ + 3 + 4 + 4 * (d - 1) = x₁ + 4 * d + 3 := by omega
            rw [← h_p11, heq] at h5
            exact stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5)))
          · simp only [bump_enc_twice, bump_enc, GoodKS]
            exact ⟨by omega, trivial⟩
          · intro _ _
            simp only [bump_enc, GoodKS]
            exact ⟨by omega, trivial⟩
        | cons x₂ rest' =>
          -- Subcase 3b: xs_rest = x₂ :: rest'
          have hne_rest : (x₂ :: rest') ≠ [] := by simp
          rw [h_rest] at h_gks_rest h_valid_rest
          refine ⟨x₁ + d + 3, add_last (x₂ :: rest') (3 * d), ?_,
            ValidKS_add_last (x₂ :: rest') (3 * d) h_valid_rest,
            fun h_emp => absurd h_emp (add_last_ne_nil (x₂ :: rest') (3 * d) hne_rest),
            ?_, ?_⟩
          · rw [hd_split]
            have h1 := e0_loop_drain_pairs d 0 (x₁ :: x₂ :: rest') R
            have h2 : (cfg_modeE0_loop (encL 0 (x₁ :: x₂ :: rest')) (prepend11_01 d R)) [holdout_0311_tm]⊢⁺
                cfg_modeE1 (encL x₁ (x₂ :: rest')) (prepend01 4 (prepend11_01 d R)) :=
              step_modeE0_loop_b011_10 (encL x₁ (x₂ :: rest')) (prepend11_01 d R)
            have h3 := modeE1_to_modeC (x₂ :: rest') x₁ (prepend01 4 (prepend11_01 d R)) h_valid_rest
            rw [bump_enc_nonempty x₁ hne_rest] at h3
            dsimp only at h3
            have h4 := modeC_prepend01_star 4 x₁ (add_last (x₂ :: rest') 3) (prepend11_01 d R)
            have hd_eq : d = (d - 1) + 1 := by omega
            have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) := by
              conv_lhs => rw [hd_eq]
              rw [prepend11_01_add]; rfl
            have h5 := modeC_consume_11_01_nonempty (d - 1) (x₁ + 4) (add_last (x₂ :: rest') 3)
              ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
              (add_last_ne_nil (x₂ :: rest') 3 hne_rest)
              (ValidKS_add_last (x₂ :: rest') 3 h_valid_rest)
            rw [add_last_add] at h5
            have heq1 : x₁ + 4 + (d - 1) = x₁ + d + 3 := by omega
            have heq2 : 3 + 3 * (d - 1) = 3 * d := by omega
            rw [← h_p11, heq1, heq2] at h5
            exact stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5)))
          · rw [bump_enc_twice_nonempty (x₁ + d + 3) (add_last_ne_nil (x₂ :: rest') (3 * d) hne_rest), add_last_add]
            simp only [GoodKS]
            refine ⟨by omega, ?_⟩
            apply GoodKS_add_last
            exact GoodKS_mono (x₂ :: rest') _ _ (by omega) h_gks_rest
          · intro _ hS81
            subst hS81
            rw [bump_enc_nonempty (x₁ + d + 3) (add_last_ne_nil (x₂ :: rest') (3 * d) hne_rest), add_last_add]
            simp only [GoodKS]
            refine ⟨by omega, ?_⟩
            apply GoodKS_add_last
            exact GoodKS_mono (x₂ :: rest') _ _ (by omega) h_gks_rest
      · -- Case 4: xs = x₁ :: xs_rest, x₀ = 2 * d + 1 (d ≥ 1)
        have hd_split : x₀ = 1 + 2 * d := by omega
        set S_sub := S + 63 * (d + 2)
        have hS_sub : S_sub ≥ 36 := by omega
        have h_eq_2S : 2 * S + 63 * (x₀ + 3) = 2 * S_sub := by omega
        have hx1_ge10 : x₁ ≥ 10 := by omega
        set sub := bump_enc (x₁ - 1) xs_rest
        have h_sub_len : sub.2.length = n' := by
          cases xs_rest with
          | nil => simp [sub, bump_enc] at hlen' ⊢; exact hlen'
          | cons _ _ => simp [sub, bump_enc, add_last_length, hlen']
        have h_sub_nil : sub.2 = [] → 2 * S_sub ≤ 35 * sub.1 := by
          cases xs_rest with
          | nil => intro _; simp [sub, bump_enc]; omega
          | cons y ys =>
            intro h_emp
            exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
        have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * S_sub ≤ 35 * (sub.1 + 3) := by
          cases xs_rest with
          | nil => intro h_ne; simp [sub, bump_enc] at h_ne
          | cons y ys =>
            intro _; simp [sub, bump_enc]; omega
        have h_sub_gks : GoodKS (2 * S_sub + 63 * (sub.1 + 3)) sub.2 := by
          cases xs_rest with
          | nil => simp [sub, bump_enc, GoodKS]
          | cons y ys =>
            simp only [sub, bump_enc]
            have heq_s : 2 * S_sub + 63 * (x₁ - 1 + 3) = 2 * S + 63 * (x₀ + 3) + 63 * (x₁ + 2) := by omega
            rw [heq_s]
            exact GoodKS_add_last (y :: ys) _ 3 h_gks_rest
        set R_tail := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d R
        rcases e0_loop_leave1_goodks n' sub.1 sub.2 S_sub R_tail h_sub_len hS_sub h_sub_nil h_sub_cons h_sub_gks
          with ⟨y₀, ys, h_step_sub, h_val_ys, h_ys_emp, h_gks_sub, _⟩
        set py := bump_enc_twice y₀ ys
        set ks_mid := (py.1 + 1) :: py.2
        have hne_mid : ks_mid ≠ [] := by simp [ks_mid]
        have hval_mid : ValidKS ks_mid := GoodKS_succ_valid S_sub py.1 py.2 h_gks_sub
        refine ⟨d - 1, add_last ks_mid (3 * (d - 1)), ?_,
          ValidKS_add_last ks_mid (3 * (d - 1)) hval_mid,
          fun h_emp => absurd h_emp (add_last_ne_nil ks_mid (3 * (d - 1)) hne_mid),
          ?_, ?_⟩
        · rw [hd_split]
          have h1 := e0_loop_drain_pairs d 1 (x₁ :: xs_rest) R
          have hx1_eq : x₁ = (x₁ - 1) + 1 := by omega
          have h2 : (cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) (prepend11_01 d R)) [holdout_0311_tm]⊢⁺
              cfg_modeE1 (encL (x₁ - 1) xs_rest)
                ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) := by
            rw [show encL 1 (x₁ :: xs_rest) = encL 1 (((x₁ - 1) + 1) :: xs_rest) by rw [← hx1_eq]]
            exact step_modeE0_loop_b10_b011_10_b10 (encL (x₁ - 1) xs_rest) (prepend11_01 d R)
          have h3 := modeE1_to_modeC xs_rest (x₁ - 1)
            ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) h_valid_rest
          have h4 : (cfg_modeC (encL sub.1 sub.2)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail))
              [holdout_0311_tm]⊢⁺ cfg_modeE0_loop (encL sub.1 sub.2) R_tail :=
            step_modeC_b01_b000 (encL sub.1 sub.2) R_tail
          have h5 := unwrap_11_01_1011101_step y₀ ys (prepend11_01 d R) h_val_ys
          have hd_eq : d = (d - 1) + 1 := by omega
          have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) := by
            conv_lhs => rw [hd_eq]
            rw [prepend11_01_add]; rfl
          have h6 := modeC_consume_11_01_nonempty (d - 1) 0 ks_mid
            ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) hne_mid hval_mid
          rw [← h_p11, Nat.zero_add] at h6
          exact stepStar_stepPlus_stepPlus h1
            (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepPlus_stepPlus h3
                (stepPlus_stepPlus_stepPlus h4
                  (stepPlus_stepPlus_stepPlus h_step_sub
                    (stepPlus_stepStar_stepPlus h5 h6)))))
        · rw [bump_enc_twice_nonempty (d - 1) (add_last_ne_nil ks_mid (3 * (d - 1)) hne_mid), add_last_add]
          dsimp only
          have hd1 : d - 1 + 1 = d := by omega
          rw [hd1]
          simp only [GoodKS]
          refine ⟨by omega, ?_⟩
          exact GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 6) h_gks_sub
        · intro _ hS81
          subst hS81
          rw [bump_enc_nonempty (d - 1) (add_last_ne_nil ks_mid (3 * (d - 1)) hne_mid), add_last_add]
          dsimp only
          have hd1 : d - 1 + 1 = d := by omega
          rw [hd1]
          simp only [GoodKS]
          refine ⟨by omega, ?_⟩
          exact GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 3) h_gks_sub

-- ============================================================================
-- Master Lemma 2a: k₀ ≥ 1 Transition (step_k0_pos)
-- ============================================================================

lemma step_k0_pos (k₀ : ℕ) (ks : List ℕ) (hk0 : k₀ ≥ 1) (h_inv : InvNil k₀ ks) :
    ∃ k₀' ks',
      ((cfg_modeC (encL k₀ ks) default) [holdout_0311_tm]⊢⁺ cfg_modeC (encL k₀' ks') default) ∧
      InvNil k₀' ks' := by
  set x₀ := k₀ - 1
  have hk0_eq : k₀ = x₀ + 1 := by omega
  have h_to_e0 : (cfg_modeC (encL k₀ ks) default) [holdout_0311_tm]⊢⁺ cfg_modeE0_loop (encL x₀ ks) default := by
    rw [hk0_eq]
    exact stepPlus_stepPlus_stepPlus (step_modeC_nil (encL (x₀ + 1) ks)) (step_modeE0_first_b10 (encL x₀ ks))
  set d := x₀ / 2
  set rem := x₀ % 2
  have h_rem : rem = 0 ∨ rem = 1 := by omega
  rcases h_inv with ⟨ rfl, hk5 ⟩ | ⟨ hne, h_gks ⟩
  · -- ks = [], k₀ ≥ 5 (so x₀ ≥ 4)
    rcases h_rem with h_even | h_odd
    · -- Branch 2: ks = [], x₀ = 2 * d (d ≥ 2)
      have hd : d ≥ 2 := by omega
      have hx_split : x₀ = 0 + 2 * d := by omega
      refine ⟨d + 1, [3 * d], ?_, Or.inr ⟨by simp, ?_⟩⟩
      · rw [hx_split] at h_to_e0
        have h1 := e0_loop_drain_pairs d 0 [] default
        have h2 := step_modeE0_loop_base (prepend11_01 d default)
        have h3 := step_modeC_b01 (encL 0 [0]) (prepend11_01 d default)
        have h4 := modeC_consume_11_01_nonempty d 1 [0] default (by simp) trivial
        simp only [add_last, Nat.zero_add] at h4
        have heq : 1 + d = d + 1 := by omega
        rw [heq] at h4
        exact stepPlus_stepPlus_stepPlus h_to_e0
          (stepStar_stepPlus_stepPlus h1
            (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepStar_stepPlus h3 h4)))
      · have hd1_ne : d + 1 ≠ 1 := by omega
        simp only [hd1_ne, ite_false, GoodKS]
        exact ⟨by omega, trivial⟩
    · -- Branch 1: ks = [], x₀ = 2 * d + 1 (d ≥ 2)
      have hd : d ≥ 2 := by omega
      have hx_split : x₀ = 1 + 2 * d := by omega
      refine ⟨4 * d + 7, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
      · rw [hx_split] at h_to_e0
        have h1 := e0_loop_drain_pairs d 1 [] default
        have h2 : (cfg_modeE0_loop (encL 1 []) (prepend11_01 d default)) [holdout_0311_tm]⊢⁺
            cfg_modeC (encL 0 []) (prepend01 3 (prepend11_01 (d + 1) default)) :=
          step_modeE0_loop_b10_base (prepend11_01 d default)
        have h3 := modeC_prepend01_star 3 0 [] (prepend11_01 (d + 1) default)
        rw [Nat.zero_add] at h3
        have h4 := modeC_consume_11_01_nil (d + 1) 3 default
        have heq : 3 + 4 * (d + 1) = 4 * d + 7 := by omega
        rw [heq] at h4
        exact stepPlus_stepPlus_stepPlus h_to_e0
          (stepStar_stepPlus_stepPlus h1
            (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4)))
  · -- ks = k₁ :: ks_rest
    cases ks with
    | nil => contradiction
    | cons k₁ ks_rest =>
      set S_in := if k₀ = 1 then 81 else 36 * (k₀ + 2)
      have hS_in_ge : S_in ≥ 81 := by
        dsimp [S_in]; split_ifs <;> omega
      have ⟨hk1_bound, h_gks_rest⟩ := h_gks
      have hk1_ge : k₁ ≥ 1 := by omega
      have h_valid_rest : ValidKS ks_rest :=
        GoodKS_valid ks_rest (S_in + 63 * (k₁ + 2)) (by omega) h_gks_rest
      rcases h_rem with h_even | h_odd
      · -- Branch 3: ks = k₁ :: ks_rest, x₀ = 2 * d (d ≥ 0, k₀ = 2 * d + 1)
        have hx_split : x₀ = 0 + 2 * d := by omega
        cases ks_rest with
        | nil =>
          refine ⟨k₁ + 4 * d + 7, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
          rw [hx_split] at h_to_e0
          have h1 := e0_loop_drain_pairs d 0 [k₁] default
          have h2 : (cfg_modeE0_loop (encL 0 [k₁]) (prepend11_01 d default)) [holdout_0311_tm]⊢⁺
              cfg_modeE1 (encL k₁ []) (prepend01 4 (prepend11_01 d default)) :=
            step_modeE0_loop_b011_10 (encL k₁ []) (prepend11_01 d default)
          have h3 := modeE1_to_modeC [] k₁ (prepend01 4 (prepend11_01 d default)) trivial
          dsimp [bump_enc] at h3
          have h4 := modeC_prepend01_star 4 (k₁ + 3) [] (prepend11_01 d default)
          have h5 := modeC_consume_11_01_nil d (k₁ + 3 + 4) default
          have heq : k₁ + 3 + 4 + 4 * d = k₁ + 4 * d + 7 := by omega
          rw [heq] at h5
          exact stepPlus_stepPlus_stepPlus h_to_e0
            (stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5))))
        | cons k₂ rest' =>
          have hne_rest : (k₂ :: rest') ≠ [] := by simp
          refine ⟨k₁ + d + 4, add_last (k₂ :: rest') (3 * d + 3), ?_,
            Or.inr ⟨add_last_ne_nil (k₂ :: rest') (3 * d + 3) hne_rest, ?_⟩⟩
          · rw [hx_split] at h_to_e0
            have h1 := e0_loop_drain_pairs d 0 (k₁ :: k₂ :: rest') default
            have h2 : (cfg_modeE0_loop (encL 0 (k₁ :: k₂ :: rest')) (prepend11_01 d default)) [holdout_0311_tm]⊢⁺
                cfg_modeE1 (encL k₁ (k₂ :: rest')) (prepend01 4 (prepend11_01 d default)) :=
              step_modeE0_loop_b011_10 (encL k₁ (k₂ :: rest')) (prepend11_01 d default)
            have h3 := modeE1_to_modeC (k₂ :: rest') k₁ (prepend01 4 (prepend11_01 d default)) h_valid_rest
            rw [bump_enc_nonempty k₁ hne_rest] at h3
            have h4 := modeC_prepend01_star 4 k₁ (add_last (k₂ :: rest') 3) (prepend11_01 d default)
            have h5 := modeC_consume_11_01_nonempty d (k₁ + 4) (add_last (k₂ :: rest') 3) default
              (add_last_ne_nil (k₂ :: rest') 3 hne_rest)
              (ValidKS_add_last (k₂ :: rest') 3 h_valid_rest)
            rw [add_last_add] at h5
            have heq1 : k₁ + 4 + d = k₁ + d + 4 := by omega
            have heq2 : 3 + 3 * d = 3 * d + 3 := by omega
            rw [heq1, heq2] at h5
            exact stepPlus_stepPlus_stepPlus h_to_e0
              (stepStar_stepPlus_stepPlus h1
                (stepPlus_stepPlus_stepPlus h2
                  (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5))))
          · have h_ne1 : k₁ + d + 4 ≠ 1 := by omega
            simp only [h_ne1, ite_false]
            apply GoodKS_add_last
            apply GoodKS_mono (k₂ :: rest') _ (S_in + 63 * (k₁ + 2)) ?_ h_gks_rest
            dsimp [S_in]; split_ifs <;> omega
      · -- Branch 4: ks = k₁ :: ks_rest, x₀ = 2 * d + 1 (d ≥ 0, k₀ = 2 * d + 2 ≥ 2)
        have hx_split : x₀ = 1 + 2 * d := by omega
        have hk0_ne1 : k₀ ≠ 1 := by omega
        have hS_in_eq : S_in = 72 * (d + 2) := by
          dsimp [S_in]; rw [if_neg hk0_ne1]; omega
        set S_sub := 36 * (d + 2)
        have hS_sub : S_sub ≥ 36 := by omega
        have hk1_ge3 : k₁ ≥ 3 := by omega
        set sub := bump_enc (k₁ - 1) ks_rest
        have h_sub_nil : sub.2 = [] → 2 * S_sub ≤ 35 * sub.1 := by
          cases ks_rest with
          | nil => intro _; simp [sub, bump_enc]; omega
          | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
        have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * S_sub ≤ 35 * (sub.1 + 3) := by
          cases ks_rest with
          | nil => intro h_ne; simp [sub, bump_enc] at h_ne
          | cons y ys => intro _; simp [sub, bump_enc]; omega
        have h_sub_gks : GoodKS (2 * S_sub + 63 * (sub.1 + 3)) sub.2 := by
          cases ks_rest with
          | nil => simp [sub, bump_enc, GoodKS]
          | cons y ys =>
            simp only [sub, bump_enc]
            have heq_s : 2 * S_sub + 63 * (k₁ - 1 + 3) = S_in + 63 * (k₁ + 2) := by omega
            rw [heq_s]
            exact GoodKS_add_last (y :: ys) _ 3 h_gks_rest
        set R_tail := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d default
        rcases e0_loop_leave1_goodks sub.2.length sub.1 sub.2 S_sub R_tail rfl hS_sub h_sub_nil h_sub_cons h_sub_gks
          with ⟨y₀, ys, h_step_sub, h_val_ys, _, h_gks_sub, _⟩
        set py := bump_enc_twice y₀ ys
        set ks_mid := (py.1 + 1) :: py.2
        have hne_mid : ks_mid ≠ [] := by simp [ks_mid]
        have hval_mid : ValidKS ks_mid := GoodKS_succ_valid S_sub py.1 py.2 h_gks_sub
        refine ⟨d, add_last ks_mid (3 * d), ?_,
          Or.inr ⟨add_last_ne_nil ks_mid (3 * d) hne_mid, ?_⟩⟩
        · rw [hx_split] at h_to_e0
          have h1 := e0_loop_drain_pairs d 1 (k₁ :: ks_rest) default
          have hk1_eq : k₁ = (k₁ - 1) + 1 := by omega
          have h2 : (cfg_modeE0_loop (encL 1 (k₁ :: ks_rest)) (prepend11_01 d default)) [holdout_0311_tm]⊢⁺
              cfg_modeE1 (encL (k₁ - 1) ks_rest)
                ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) := by
            rw [show encL 1 (k₁ :: ks_rest) = encL 1 (((k₁ - 1) + 1) :: ks_rest) by rw [← hk1_eq]]
            exact step_modeE0_loop_b10_b011_10_b10 (encL (k₁ - 1) ks_rest) (prepend11_01 d default)
          have h3 := modeE1_to_modeC ks_rest (k₁ - 1)
            ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) h_valid_rest
          have h4 : (cfg_modeC (encL sub.1 sub.2)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail))
              [holdout_0311_tm]⊢⁺ cfg_modeE0_loop (encL sub.1 sub.2) R_tail :=
            step_modeC_b01_b000 (encL sub.1 sub.2) R_tail
          have h5 := unwrap_11_01_1011101_step y₀ ys (prepend11_01 d default) h_val_ys
          have h6 := modeC_consume_11_01_nonempty d 0 ks_mid default hne_mid hval_mid
          rw [Nat.zero_add] at h6
          exact stepPlus_stepPlus_stepPlus h_to_e0
            (stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepPlus_stepPlus h3
                  (stepPlus_stepPlus_stepPlus h4
                    (stepPlus_stepPlus_stepPlus h_step_sub
                      (stepPlus_stepStar_stepPlus h5 h6))))))
        · apply GoodKS_add_last
          apply GoodKS_mono ks_mid _ S_sub ?_ h_gks_sub
          split_ifs <;> omega

-- ============================================================================
-- Master Lemma 2b: Drain at R = 01 >> 01 >> default (Cases 0a & 0b of k₀ = 0)
-- ============================================================================

lemma e0_loop_drain_plus2 (w₀ : ℕ) (ws : List ℕ) (S_w : ℕ)
    (h_empty : ws = [] → w₀ ≥ 4)
    (h_sw : 36 ≤ S_w + 54 * (w₀ / 2))
    (h_gks : GoodKS (S_w + 63 * (w₀ + 3)) ws) :
    ∃ k₀' ks',
      ((cfg_modeE0_loop (encL w₀ ws) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
        [holdout_0311_tm]⊢⁺ cfg_modeC (encL k₀' ks') default) ∧
      InvNil k₀' ks' := by
  set R0 := (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
  have hR0 : R0 = prepend01 2 default := rfl
  set d := w₀ / 2
  set rem := w₀ % 2
  have h_rem : rem = 0 ∨ rem = 1 := by omega
  cases ws with
  | nil =>
    have hw4 : w₀ ≥ 4 := h_empty rfl
    rcases h_rem with h_even | h_odd
    · -- Case 2: ws = [], w₀ = 2 * d (d ≥ 2)
      have hd : d ≥ 2 := by omega
      have hw_split : w₀ = 0 + 2 * d := by omega
      refine ⟨d + 3, [3 * d], ?_, Or.inr ⟨by simp, ?_⟩⟩
      · rw [hw_split]
        have h1 := e0_loop_drain_pairs d 0 [] R0
        have h2 := step_modeE0_loop_base (prepend11_01 d R0)
        have h3 := step_modeC_b01 (encL 0 [0]) (prepend11_01 d R0)
        have h4 := modeC_consume_11_01_nonempty d 1 [0] R0 (by simp) trivial
        simp only [add_last, Nat.zero_add] at h4
        rw [hR0] at h4
        have h5 := modeC_prepend01_star 2 (1 + d) [3 * d] default
        have heq : 1 + d + 2 = d + 3 := by omega
        rw [heq] at h5
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5)))
      · have hd3_ne : d + 3 ≠ 1 := by omega
        simp only [hd3_ne, ite_false, GoodKS]
        exact ⟨by omega, trivial⟩
    · -- Case 1: ws = [], w₀ = 2 * d + 1 (d ≥ 1)
      have hd : d ≥ 1 := by omega
      have hw_split : w₀ = 1 + 2 * d := by omega
      refine ⟨4 * d + 9, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
      · rw [hw_split]
        have h1 := e0_loop_drain_pairs d 1 [] R0
        have h2 : (cfg_modeE0_loop (encL 1 []) (prepend11_01 d R0)) [holdout_0311_tm]⊢⁺
            cfg_modeC (encL 0 []) (prepend01 3 (prepend11_01 (d + 1) R0)) :=
          step_modeE0_loop_b10_base (prepend11_01 d R0)
        have h3 := modeC_prepend01_star 3 0 [] (prepend11_01 (d + 1) R0)
        rw [Nat.zero_add] at h3
        have h4 := modeC_consume_11_01_nil (d + 1) 3 R0
        rw [hR0] at h4
        have h5 := modeC_prepend01_star 2 (3 + 4 * (d + 1)) [] default
        have heq : 3 + 4 * (d + 1) + 2 = 4 * d + 9 := by omega
        rw [heq] at h5
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5)))
  | cons w₁ ws_rest =>
    have ⟨hw1_bound, h_gks_rest⟩ := h_gks
    have hw1_ge : w₁ ≥ 4 := by omega
    have h_valid_rest : ValidKS ws_rest :=
      GoodKS_valid ws_rest (S_w + 63 * (w₀ + 3) + 63 * (w₁ + 2)) (by omega) h_gks_rest
    rcases h_rem with h_even | h_odd
    · -- Case 3: ws = w₁ :: ws_rest, w₀ = 2 * d (d ≥ 0)
      have hw_split : w₀ = 0 + 2 * d := by omega
      cases ws_rest with
      | nil =>
        refine ⟨w₁ + 4 * d + 9, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
        rw [hw_split]
        have h1 := e0_loop_drain_pairs d 0 [w₁] R0
        have h2 : (cfg_modeE0_loop (encL 0 [w₁]) (prepend11_01 d R0)) [holdout_0311_tm]⊢⁺
            cfg_modeE1 (encL w₁ []) (prepend01 4 (prepend11_01 d R0)) :=
          step_modeE0_loop_b011_10 (encL w₁ []) (prepend11_01 d R0)
        have h3 := modeE1_to_modeC [] w₁ (prepend01 4 (prepend11_01 d R0)) trivial
        dsimp [bump_enc] at h3
        have h4 := modeC_prepend01_star 4 (w₁ + 3) [] (prepend11_01 d R0)
        have h5 := modeC_consume_11_01_nil d (w₁ + 3 + 4) R0
        rw [hR0] at h5
        have h6 := modeC_prepend01_star 2 (w₁ + 3 + 4 + 4 * d) [] default
        have heq : w₁ + 3 + 4 + 4 * d + 2 = w₁ + 4 * d + 9 := by omega
        rw [heq] at h6
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 (stepStar_trans h5 h6))))
      | cons w₂ rest' =>
        have hne_rest : (w₂ :: rest') ≠ [] := by simp
        refine ⟨w₁ + d + 6, add_last (w₂ :: rest') (3 * d + 3), ?_,
          Or.inr ⟨add_last_ne_nil (w₂ :: rest') (3 * d + 3) hne_rest, ?_⟩⟩
        · rw [hw_split]
          have h1 := e0_loop_drain_pairs d 0 (w₁ :: w₂ :: rest') R0
          have h2 : (cfg_modeE0_loop (encL 0 (w₁ :: w₂ :: rest')) (prepend11_01 d R0)) [holdout_0311_tm]⊢⁺
              cfg_modeE1 (encL w₁ (w₂ :: rest')) (prepend01 4 (prepend11_01 d R0)) :=
            step_modeE0_loop_b011_10 (encL w₁ (w₂ :: rest')) (prepend11_01 d R0)
          have h3 := modeE1_to_modeC (w₂ :: rest') w₁ (prepend01 4 (prepend11_01 d R0)) h_valid_rest
          rw [bump_enc_nonempty w₁ hne_rest] at h3
          have h4 := modeC_prepend01_star 4 w₁ (add_last (w₂ :: rest') 3) (prepend11_01 d R0)
          have h5 := modeC_consume_11_01_nonempty d (w₁ + 4) (add_last (w₂ :: rest') 3) R0
            (add_last_ne_nil (w₂ :: rest') 3 hne_rest)
            (ValidKS_add_last (w₂ :: rest') 3 h_valid_rest)
          have heq1 : w₁ + 4 + d + 2 = w₁ + d + 6 := by omega
          have heq2 : 3 + 3 * d = 3 * d + 3 := by omega
          rw [add_last_add, heq2, hR0] at h5
          have h6 := modeC_prepend01_star 2 (w₁ + 4 + d) (add_last (w₂ :: rest') (3 * d + 3)) default
          rw [heq1] at h6
          exact stepStar_stepPlus_stepPlus h1
            (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 (stepStar_trans h5 h6))))
        · have h_ne1 : w₁ + d + 6 ≠ 1 := by omega
          simp only [h_ne1, ite_false]
          apply GoodKS_add_last
          exact GoodKS_mono (w₂ :: rest') _ _ (by omega) h_gks_rest
    · -- Case 4: ws = w₁ :: ws_rest, w₀ = 2 * d + 1 (d ≥ 0)
      have hw_split : w₀ = 1 + 2 * d := by omega
      set S_sub := 36 * (d + 4)
      have hS_sub : S_sub ≥ 36 := by omega
      have h_2S_le : 2 * S_sub ≤ S_w + 63 * (w₀ + 3) := by omega
      set sub := bump_enc (w₁ - 1) ws_rest
      have h_sub_nil : sub.2 = [] → 2 * S_sub ≤ 35 * sub.1 := by
        cases ws_rest with
        | nil => intro _; simp [sub, bump_enc]; omega
        | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
      have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * S_sub ≤ 35 * (sub.1 + 3) := by
        cases ws_rest with
        | nil => intro h_ne; simp [sub, bump_enc] at h_ne
        | cons y ys => intro _; simp [sub, bump_enc]; omega
      have h_sub_gks : GoodKS (2 * S_sub + 63 * (sub.1 + 3)) sub.2 := by
        cases ws_rest with
        | nil => simp [sub, bump_enc, GoodKS]
        | cons y ys =>
          simp only [sub, bump_enc]
          apply GoodKS_add_last
          exact GoodKS_mono (y :: ys) _ _ (by omega) h_gks_rest
      set R_tail := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d R0
      rcases e0_loop_leave1_goodks sub.2.length sub.1 sub.2 S_sub R_tail rfl hS_sub h_sub_nil h_sub_cons h_sub_gks
        with ⟨y₀, ys, h_step_sub, h_val_ys, _, h_gks_sub, _⟩
      set py := bump_enc_twice y₀ ys
      set ks_mid := (py.1 + 1) :: py.2
      have hne_mid : ks_mid ≠ [] := by simp [ks_mid]
      have hval_mid : ValidKS ks_mid := GoodKS_succ_valid S_sub py.1 py.2 h_gks_sub
      refine ⟨d + 2, add_last ks_mid (3 * d), ?_,
        Or.inr ⟨add_last_ne_nil ks_mid (3 * d) hne_mid, ?_⟩⟩
      · rw [hw_split]
        have h1 := e0_loop_drain_pairs d 1 (w₁ :: ws_rest) R0
        have hw1_eq : w₁ = (w₁ - 1) + 1 := by omega
        have h2 : (cfg_modeE0_loop (encL 1 (w₁ :: ws_rest)) (prepend11_01 d R0)) [holdout_0311_tm]⊢⁺
            cfg_modeE1 (encL (w₁ - 1) ws_rest)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) := by
          rw [show encL 1 (w₁ :: ws_rest) = encL 1 (((w₁ - 1) + 1) :: ws_rest) by rw [← hw1_eq]]
          exact step_modeE0_loop_b10_b011_10_b10 (encL (w₁ - 1) ws_rest) (prepend11_01 d R0)
        have h3 := modeE1_to_modeC ws_rest (w₁ - 1)
          ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) h_valid_rest
        have h4 : (cfg_modeC (encL sub.1 sub.2)
            ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail))
            [holdout_0311_tm]⊢⁺ cfg_modeE0_loop (encL sub.1 sub.2) R_tail :=
          step_modeC_b01_b000 (encL sub.1 sub.2) R_tail
        have h5 := unwrap_11_01_1011101_step y₀ ys (prepend11_01 d R0) h_val_ys
        have h6 := modeC_consume_11_01_nonempty d 0 ks_mid R0 hne_mid hval_mid
        rw [Nat.zero_add, hR0] at h6
        have h7 := modeC_prepend01_star 2 d (add_last ks_mid (3 * d)) default
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepPlus_stepPlus h3
              (stepPlus_stepPlus_stepPlus h4
                (stepPlus_stepPlus_stepPlus h_step_sub
                  (stepPlus_stepStar_stepPlus h5 (stepStar_trans h6 h7))))))
      · have hd2_ne : d + 2 ≠ 1 := by omega
        simp only [hd2_ne, ite_false]
        exact GoodKS_add_last ks_mid S_sub (3 * d) h_gks_sub

-- ============================================================================
-- k₀ = 0 Transition (Cases 0a, 0b, 0c)
-- ============================================================================

lemma step_b01_b101_nil_to_e0_loop (p₀ : ℕ) (ps : List ℕ) (h_val : ValidKS ps) :
    let w := bump_enc p₀ ps
    (cfg_modeC (encL p₀ ps) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
      [holdout_0311_tm]⊢⁺
      cfg_modeE0_loop (encL w.1 w.2) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) := by
  dsimp
  set w := bump_enc p₀ ps
  have h1 := step_modeC_b01_b101_nil (encL p₀ ps)
  have h2 := modeE1_to_modeC ps p₀
    ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default)))
    h_val
  have h3 := step_modeC_b01_b000 (encL w.1 w.2) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)
  exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 h3)

lemma step_k0_zero (ks : List ℕ) (h_inv : InvNil 0 ks) :
    ∃ k₀' ks',
      ((cfg_modeC (encL 0 ks) default) [holdout_0311_tm]⊢⁺ cfg_modeC (encL k₀' ks') default) ∧
      InvNil k₀' ks' := by
  rcases h_inv with ⟨ _, hk5 ⟩ | ⟨ hne, h_gks ⟩
  · omega
  · simp only [ Nat.reduceEqDiff, ite_false ] at h_gks
    cases ks with
    | nil => contradiction
    | cons k₁ ks_rest =>
      have ⟨hk1_bound, h_gks_rest⟩ := h_gks
      have hk1_ge : k₁ ≥ 1 := by omega
      have h_valid_rest : ValidKS ks_rest :=
        GoodKS_valid ks_rest (72 + 63 * (k₁ + 2)) (by omega) h_gks_rest
      set sub := bump_enc (k₁ - 1) ks_rest
      have h_to_sub : (cfg_modeC (encL 0 (k₁ :: ks_rest)) default) [holdout_0311_tm]⊢⁺
          cfg_modeE0_loop (encL sub.1 sub.2) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) := by
        have hk1_eq : k₁ = (k₁ - 1) + 1 := by omega
        have h1 := step_modeC_nil (encL 0 (k₁ :: ks_rest))
        have h2 : (cfg_modeE0_first (encL 0 (k₁ :: ks_rest))) [holdout_0311_tm]⊢⁺
            cfg_modeE1 (encL (k₁ - 1) ks_rest)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
          rw [show encL 0 (k₁ :: ks_rest) = encL 0 (((k₁ - 1) + 1) :: ks_rest) by rw [← hk1_eq]]
          exact step_modeE0_first_b011_10_b10 (encL (k₁ - 1) ks_rest)
        have h3 := modeE1_to_modeC ks_rest (k₁ - 1)
          ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
          h_valid_rest
        have h4 := step_modeC_b01_b000 (encL sub.1 sub.2) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)
        exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 (stepPlus_stepPlus_stepPlus h3 h4))
      -- Split on ks_rest = [] ∨ k₁ ≥ 3 (Case 0a), k₁ = 1 ∧ ks_rest ≠ [] (Case 0b), k₁ = 2 ∧ ks_rest ≠ [] (Case 0c)
      by_cases h_0a : ks_rest = [] ∨ k₁ ≥ 3
      · -- Case 0a: leave1(sub.1, sub.2) with S = 36
        have h_sub_nil : sub.2 = [] → 2 * 36 ≤ 35 * sub.1 := by
          cases ks_rest with
          | nil => intro _; simp [sub, bump_enc]; omega
          | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
        have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * 36 ≤ 35 * (sub.1 + 3) := by
          cases ks_rest with
          | nil => intro h_ne; simp [sub, bump_enc] at h_ne
          | cons y ys =>
            rcases h_0a with h_emp | hk3
            · simp at h_emp
            · intro _; simp [sub, bump_enc]; omega
        have h_sub_gks : GoodKS (2 * 36 + 63 * (sub.1 + 3)) sub.2 := by
          cases ks_rest with
          | nil => simp [sub, bump_enc, GoodKS]
          | cons y ys =>
            simp only [sub, bump_enc]
            have heq_s : 2 * 36 + 63 * (k₁ - 1 + 3) = 72 + 63 * (k₁ + 2) := by omega
            rw [heq_s]
            exact GoodKS_add_last (y :: ys) _ 3 h_gks_rest
        rcases e0_loop_leave1_goodks sub.2.length sub.1 sub.2 36 ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)
          rfl (by omega) h_sub_nil h_sub_cons h_sub_gks
          with ⟨m₀, ms, h_step_l1, h_val_ms, h_ms_emp, h_gks_w, _⟩
        set p1 := bump_enc m₀ ms
        set w := bump_enc_twice m₀ ms
        have hw_eq : w = bump_enc p1.1 p1.2 := rfl
        have h_c11 : (cfg_modeC (encL m₀ ms)
            ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
            [holdout_0311_tm]⊢⁺
            cfg_modeC (encL p1.1 p1.2) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) :=
          stepPlus_stepPlus_stepPlus
            (step_modeC_b11 (encL m₀ ms) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
            (modeE1_to_modeC ms m₀ ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) h_val_ms)
        have h_to_w := step_b01_b101_nil_to_e0_loop p1.1 p1.2 (ValidKS_bump_enc m₀ ms h_val_ms)
        have h_w_empty : w.2 = [] → w.1 ≥ 4 := by
          cases ms with
          | nil =>
            intro _; dsimp only [w, bump_enc_twice, bump_enc]; omega
          | cons u us =>
            intro h_emp
            dsimp only [w] at h_emp
            rw [bump_enc_twice_nonempty m₀ (by simp)] at h_emp
            exact absurd h_emp (add_last_ne_nil (u :: us) 6 (by simp))
        have h_gks_ws : GoodKS (36 + 63 * (w.1 + 3)) w.2 := by
          have h2 := h_gks_w.2
          have heq : 36 + 63 * (w.1 + 1 + 2) = 36 + 63 * (w.1 + 3) := by omega
          rw [heq] at h2; exact h2
        rcases e0_loop_drain_plus2 w.1 w.2 36 h_w_empty (by omega) h_gks_ws with ⟨k₀', ks', h_drain, h_inv'⟩
        exact ⟨k₀', ks',
          stepPlus_stepPlus_stepPlus h_to_sub
            (stepPlus_stepPlus_stepPlus h_step_l1
              (stepPlus_stepPlus_stepPlus h_c11
                (stepPlus_stepPlus_stepPlus h_to_w h_drain))),
          h_inv'⟩
      · -- Not Case 0a: ks_rest ≠ [] and k₁ < 3 (so k₁ = 1 or k₁ = 2)
        push Not at h_0a
        rcases h_0a with ⟨hne_rest, hk1_lt3⟩
        cases ks_rest with
        | nil => contradiction
        | cons k₂ ks_tail =>
          have hk1_cases : k₁ = 1 ∨ k₁ = 2 := by omega
          rcases hk1_cases with rfl | rfl
          · -- Case 0b: k₁ = 1, ks_rest = k₂ :: ks_tail
            have h_sub_eq : sub = (0, add_last (k₂ :: ks_tail) 3) := rfl
            have h_gks_sub : GoodKS 261 (add_last (k₂ :: ks_tail) 3) :=
              GoodKS_add_last (k₂ :: ks_tail) 261 3 h_gks_rest
            cases h_al : add_last (k₂ :: ks_tail) 3 with
            | nil => exact absurd h_al (add_last_ne_nil (k₂ :: ks_tail) 3 (by simp))
            | cons x₁ xs_rest =>
              rw [h_al] at h_gks_sub
              have ⟨hx1_bound, h_gks_xs⟩ := h_gks_sub
              have hx1_ge6 : x₁ ≥ 6 := by omega
              have h_val_xs : ValidKS xs_rest :=
                GoodKS_valid xs_rest (261 + 63 * (x₁ + 2)) (by omega) h_gks_xs
              set xb := bump_enc x₁ xs_rest
              set p1 : ℕ × List ℕ := (xb.1 + 3, xb.2)
              set w := bump_enc p1.1 p1.2
              have h_step_0b : (cfg_modeE0_loop (encL 0 (x₁ :: xs_rest)) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
                  [holdout_0311_tm]⊢⁺
                  cfg_modeC (encL p1.1 p1.2) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) := by
                have h1 : (cfg_modeE0_loop (encL 0 (x₁ :: xs_rest)) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
                    [holdout_0311_tm]⊢⁺
                    cfg_modeE1 (encL x₁ xs_rest) (prepend01 3 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) :=
                  step_modeE0_loop_b011_10 (encL x₁ xs_rest) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)
                have h2 := modeE1_to_modeC xs_rest x₁
                  (prepend01 3 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) h_val_xs
                have h3 := modeC_prepend01_star 3 xb.1 xb.2 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)
                exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)
              have h_val_p1 : ValidKS p1.2 := ValidKS_bump_enc x₁ xs_rest h_val_xs
              have h_to_w := step_b01_b101_nil_to_e0_loop p1.1 p1.2 h_val_p1
              have hw1_ge9 : w.1 ≥ 9 := by
                cases xs_rest with
                | nil => dsimp only [w, p1, xb, bump_enc]; omega
                | cons y ys =>
                  have hw_cons : w = (x₁ + 3, add_last (y :: ys) 6) := by
                    change bump_enc (x₁ + 3) (add_last (y :: ys) 3) = _
                    rw [bump_enc_nonempty (x₁ + 3) (add_last_ne_nil (y :: ys) 3 (by simp)), add_last_add]
                  rw [hw_cons]; dsimp only; omega
              have h_w_empty : w.2 = [] → w.1 ≥ 4 := fun _ => by omega
              have h_sw9 : 36 ≤ 9 + 54 * (w.1 / 2) := by omega
              have h_gks_ws : GoodKS (9 + 63 * (w.1 + 3)) w.2 := by
                cases xs_rest with
                | nil => simp [w, p1, xb, bump_enc, GoodKS]
                | cons y ys =>
                  have hw_cons : w = (x₁ + 3, add_last (y :: ys) 6) := by
                    change bump_enc (x₁ + 3) (add_last (y :: ys) 3) = _
                    rw [bump_enc_nonempty (x₁ + 3) (add_last_ne_nil (y :: ys) 3 (by simp)), add_last_add]
                  rw [hw_cons]
                  dsimp only
                  have heq : 9 + 63 * (x₁ + 3 + 3) = 261 + 63 * (x₁ + 2) := by omega
                  rw [heq]
                  exact GoodKS_add_last (y :: ys) _ 6 h_gks_xs
              rcases e0_loop_drain_plus2 w.1 w.2 9 h_w_empty h_sw9 h_gks_ws with ⟨k₀', ks', h_drain, h_inv'⟩
              have h_to_sub' : (cfg_modeC (encL 0 (1 :: k₂ :: ks_tail)) default) [holdout_0311_tm]⊢⁺
                  cfg_modeE0_loop (encL 0 (x₁ :: xs_rest)) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) := by
                simpa [h_sub_eq, h_al] using h_to_sub
              exact ⟨k₀', ks',
                stepPlus_stepPlus_stepPlus h_to_sub'
                  (stepPlus_stepPlus_stepPlus h_step_0b
                    (stepPlus_stepPlus_stepPlus h_to_w h_drain)),
                h_inv'⟩
          · -- Case 0c: k₁ = 2, ks_rest = k₂ :: ks_tail
            have h_sub_eq : sub = (1, add_last (k₂ :: ks_tail) 3) := rfl
            have h_gks_sub : GoodKS 324 (add_last (k₂ :: ks_tail) 3) :=
              GoodKS_add_last (k₂ :: ks_tail) 324 3 h_gks_rest
            cases h_al : add_last (k₂ :: ks_tail) 3 with
            | nil => exact absurd h_al (add_last_ne_nil (k₂ :: ks_tail) 3 (by simp))
            | cons x₁ xs_rest =>
              rw [h_al] at h_gks_sub
              have ⟨hx1_bound, h_gks_xs⟩ := h_gks_sub
              have hx1_ge8 : x₁ ≥ 8 := by omega
              have h_val_xs : ValidKS xs_rest :=
                GoodKS_valid xs_rest (324 + 63 * (x₁ + 2)) (by omega) h_gks_xs
              set sub2 := bump_enc (x₁ - 1) xs_rest
              set R_101 := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
              set R_1011101_101 := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R_101
              -- Step 1 of Case 0c
              have h_step1 : (cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) R_101) [holdout_0311_tm]⊢⁺
                  cfg_modeE0_loop (encL sub2.1 sub2.2) R_1011101_101 := by
                have hx1_eq : x₁ = (x₁ - 1) + 1 := by omega
                have h1 : (cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) R_101) [holdout_0311_tm]⊢⁺
                    cfg_modeE1 (encL (x₁ - 1) xs_rest)
                      ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_1011101_101) := by
                  rw [show encL 1 (x₁ :: xs_rest) = encL 1 (((x₁ - 1) + 1) :: xs_rest) by rw [← hx1_eq]]
                  exact step_modeE0_loop_b10_b011_10_b10 (encL (x₁ - 1) xs_rest) R_101
                have h2 := modeE1_to_modeC xs_rest (x₁ - 1)
                  ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_1011101_101) h_val_xs
                have h3 := step_modeC_b01_b000 (encL sub2.1 sub2.2) R_1011101_101
                exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 h3)
              -- Step 2 of Case 0c: leave1(sub2.1, sub2.2) at S = 162
              have h_sub2_nil : sub2.2 = [] → 2 * 162 ≤ 35 * sub2.1 := by
                cases xs_rest with
                | nil => intro _; simp [sub2, bump_enc]; omega
                | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
              have h_sub2_cons : sub2.2 ≠ [] → sub2.1 ≥ 2 ∧ 2 * 162 ≤ 35 * (sub2.1 + 3) := by
                cases xs_rest with
                | nil => intro h_ne; simp [sub2, bump_enc] at h_ne
                | cons y ys => intro _; simp [sub2, bump_enc]; omega
              have h_sub2_gks : GoodKS (2 * 162 + 63 * (sub2.1 + 3)) sub2.2 := by
                cases xs_rest with
                | nil => simp [sub2, bump_enc, GoodKS]
                | cons y ys =>
                  simp only [sub2, bump_enc]
                  have heq_s : 2 * 162 + 63 * (x₁ - 1 + 3) = 324 + 63 * (x₁ + 2) := by omega
                  rw [heq_s]
                  exact GoodKS_add_last (y :: ys) _ 3 h_gks_xs
              rcases e0_loop_leave1_goodks sub2.2.length sub2.1 sub2.2 162 R_1011101_101
                rfl (by omega) h_sub2_nil h_sub2_cons h_sub2_gks
                with ⟨y₀, ys, h_step_l2, h_val_ys, h_ys_emp, h_gks_z, _⟩
              have h_unwrap2 := unwrap_11_01_1011101_step y₀ ys R_101 h_val_ys
              set pz := bump_enc_twice y₀ ys
              set z₁ := pz.1 + 1
              set zs := pz.2
              have ⟨hz1_bound, h_gks_zs⟩ := h_gks_z
              have hz1_ge3 : z₁ ≥ 3 := by omega
              have h_zs_emp_z1 : zs = [] → z₁ ≥ 14 := by
                cases ys with
                | nil =>
                  have hy7 : y₀ ≥ 7 := h_ys_emp rfl
                  intro _; dsimp only [z₁, pz, bump_enc_twice, bump_enc]; omega
                | cons u us =>
                  intro h_emp
                  dsimp only [zs, pz] at h_emp
                  rw [bump_enc_twice_nonempty y₀ (by simp)] at h_emp
                  exact absurd h_emp (add_last_ne_nil (u :: us) 6 (by simp))
              have h_val_zs : ValidKS zs :=
                GoodKS_valid zs (162 + 63 * (z₁ + 2)) (by omega) h_gks_zs
              -- Step 3 & 4 of Case 0c: Transition A + Transition B
              set zb := bump_enc (z₁ - 1) zs
              set w := bump_enc zb.1 zb.2
              set R_0000101 := (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
              set R_101_01_01 := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))
              have h_step34 : (cfg_modeC (encL 0 (z₁ :: zs)) R_101) [holdout_0311_tm]⊢⁺
                  cfg_modeE0_loop (encL w.1 w.2) R_101_01_01 := by
                have hz1_eq : z₁ = (z₁ - 1) + 1 := by omega
                have hA : (cfg_modeC (encL 0 (z₁ :: zs)) R_101) [holdout_0311_tm]⊢⁺
                    cfg_modeE1 (encL (z₁ - 1) zs)
                      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R_0000101) := by
                  rw [show encL 0 (z₁ :: zs) = encL 0 (((z₁ - 1) + 1) :: zs) by rw [← hz1_eq]]
                  exact step_modeC_b01110_b10_b101_nil (encL (z₁ - 1) zs)
                have hA2 := modeE1_to_modeC zs (z₁ - 1)
                  ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R_0000101) h_val_zs
                have hA3 : (cfg_modeC (encL zb.1 zb.2)
                    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R_0000101))
                    [holdout_0311_tm]⊢⁺ cfg_modeC (encL 0 ((zb.1 + 1) :: zb.2)) R_0000101 :=
                  step_modeC_b01_b10101 (encL zb.1 zb.2) R_0000101
                have hB : (cfg_modeC (encL 0 ((zb.1 + 1) :: zb.2)) R_0000101) [holdout_0311_tm]⊢⁺
                    cfg_modeE1 (encL zb.1 zb.2)
                      ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_101_01_01) :=
                  step_modeC_b01110_b10_b0000101 (encL zb.1 zb.2) default
                have hB2 := modeE1_to_modeC zb.2 zb.1
                  ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_101_01_01)
                  (ValidKS_bump_enc (z₁ - 1) zs h_val_zs)
                have hB3 := step_modeC_b01_b000 (encL w.1 w.2) R_101_01_01
                exact stepPlus_stepPlus_stepPlus hA
                  (stepPlus_stepPlus_stepPlus hA2
                    (stepPlus_stepPlus_stepPlus hA3
                      (stepPlus_stepPlus_stepPlus hB
                        (stepPlus_stepPlus_stepPlus hB2 hB3))))
              -- Step 5 of Case 0c: leave1(w.1, w.2) at S = 81
              have hw_def : w = bump_enc_twice (z₁ - 1) zs := rfl
              have h_w_nil : w.2 = [] → 2 * 81 ≤ 35 * w.1 := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hz14 : z₁ ≥ 14 := h_zs_emp_z1 h_zs
                  have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; intro _; dsimp only; omega
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]; intro h_emp
                  exact absurd h_emp (add_last_ne_nil (y :: ys') 6 (by simp))
              have h_w_ge10 : w.2 = [] → w.1 ≥ 10 := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hz14 : z₁ ≥ 14 := h_zs_emp_z1 h_zs
                  have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; intro _; dsimp only; omega
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]; intro h_emp
                  exact absurd h_emp (add_last_ne_nil (y :: ys') 6 (by simp))
              have h_w_cons : w.2 ≠ [] → w.1 ≥ 2 ∧ 2 * 81 ≤ 35 * (w.1 + 3) := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; intro h_ne; exact absurd rfl h_ne
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]; intro _; dsimp only; omega
              have h_w_gks : GoodKS (2 * 81 + 63 * (w.1 + 3)) w.2 := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; trivial
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]
                  dsimp only
                  have heq_s : 2 * 81 + 63 * (z₁ - 1 + 3) = 162 + 63 * (z₁ + 2) := by omega
                  rw [heq_s]
                  have h_gks_zs' : GoodKS (162 + 63 * (z₁ + 2)) (y :: ys') := by
                    rw [← h_zs]; exact h_gks_zs
                  exact GoodKS_add_last (y :: ys') _ 6 h_gks_zs'
              rcases e0_loop_leave1_goodks w.2.length w.1 w.2 81 R_101_01_01
                rfl (by omega) h_w_nil h_w_cons h_w_gks
                with ⟨m₀, ms, h_step_l5, h_val_ms, _, _, h_gks_81_fn⟩
              have h_gks_b1 := h_gks_81_fn h_w_ge10 rfl
              set b1 := bump_enc m₀ ms
              -- Step 6 of Case 0c: 4 final steps to cfg_modeC (encL 1 ((b1.1 + 1) :: b1.2)) default
              have h_step6 : (cfg_modeC (encL m₀ ms)
                  ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01))
                  [holdout_0311_tm]⊢⁺
                  cfg_modeC (encL 1 ((b1.1 + 1) :: b1.2)) default := by
                have h1 := step_modeC_b11 (encL m₀ ms) ((0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01)
                have h2 := modeE1_to_modeC ms m₀ ((0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01) h_val_ms
                have h3 : (cfg_modeC (encL b1.1 b1.2) ((0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01))
                    [holdout_0311_tm]⊢⁺
                    cfg_modeC (encL 0 ((b1.1 + 1) :: b1.2)) ((0 : Fin 2) >> (1 : Fin 2) >> default) :=
                  step_modeC_b01_b10101 (encL b1.1 b1.2) ((0 : Fin 2) >> (1 : Fin 2) >> default)
                have h4 : (cfg_modeC (encL 0 ((b1.1 + 1) :: b1.2)) ((0 : Fin 2) >> (1 : Fin 2) >> default))
                    [holdout_0311_tm]⊢⁺
                    cfg_modeC (encL 1 ((b1.1 + 1) :: b1.2)) default :=
                  step_modeC_b01 (encL 0 ((b1.1 + 1) :: b1.2)) default
                exact stepPlus_stepPlus_stepPlus h1
                  (stepPlus_stepPlus_stepPlus h2
                    (stepPlus_stepPlus_stepPlus h3 h4))
              have h_to_sub' : (cfg_modeC (encL 0 (2 :: k₂ :: ks_tail)) default) [holdout_0311_tm]⊢⁺
                  cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) R_101 := by
                simpa [h_sub_eq, h_al] using h_to_sub
              exact ⟨1, (b1.1 + 1) :: b1.2,
                stepPlus_stepPlus_stepPlus h_to_sub'
                  (stepPlus_stepPlus_stepPlus h_step1
                    (stepPlus_stepPlus_stepPlus h_step_l2
                      (stepPlus_stepPlus_stepPlus h_unwrap2
                        (stepPlus_stepPlus_stepPlus h_step34
                          (stepPlus_stepPlus_stepPlus h_step_l5 h_step6))))),
                Or.inr ⟨by simp, by simpa [InvNil] using h_gks_b1⟩⟩

-- ============================================================================
-- Top-Level Invariant and Non-Halting Theorem
-- ============================================================================

def Inv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ k₀ ks, c = cfg_modeC (encL k₀ ks) default ∧ InvNil k₀ ks


lemma inv_step (c : Cfg (Fin 2) (Fin 6)) (h : Inv c) :
    ∃ c', (c [holdout_0311_tm]⊢⁺ c') ∧ Inv c' := by
  rcases h with ⟨k₀, ks, rfl, h_inv⟩
  cases k₀ with
  | zero =>
    rcases step_k0_zero ks h_inv with ⟨k₀', ks', h_step, h_inv'⟩
    exact ⟨cfg_modeC (encL k₀' ks') default, h_step, ⟨k₀', ks', rfl, h_inv'⟩⟩
  | succ k₀' =>
    rcases step_k0_pos (k₀' + 1) ks (by omega) h_inv with ⟨k₀'', ks'', h_step, h_inv'⟩
    exact ⟨cfg_modeC (encL k₀'' ks'') default, h_step, ⟨k₀'', ks'', rfl, h_inv'⟩⟩


-- ============================================================================
-- E1 Group 63 Conjugation Transport (`tableIso_311_128`) & Non-Halting Proof
-- ============================================================================

def σ_EFDBAC : Fin 6 → Fin 6
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 2

theorem tableIso_311_128 : ∀ (q : Fin 6) (a : Fin 2),
    target_tm (σ_EFDBAC q) a = (holdout_0311_tm q a).map (conjOut σ_EFDBAC true)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 3, 0 => rfl
  | 3, 1 => rfl
  | 4, 0 => rfl
  | 4, 1 => rfl
  | 5, 0 => rfl
  | 5, 1 => rfl

lemma init_reaches_conj_inv_128 :
    (init []) [target_tm]⊢⁺ conjCfg σ_EFDBAC true (cfg_modeC (encL 7 []) default) := by
  refine run_local_plus_eq (tm := target_tm) (n := 177)
    (s1 := ⟨[(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 0, .right⟩)
    (s2 := ⟨[(0 : Fin 2), (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 3, .left⟩)
    default default rfl ?_ ?_
  · simp only [cfg_of, init, Tape.mk₁, List.head?, Option.getD, List.tail, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]; rfl
  · simp only [cfg_of, cfg_modeC, conjCfg, mirrorTape, σ_EFDBAC, encL, encL_tail, prepend10, append_cons, append_nil, zero_cons_default, default_head, default_tail, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Option.map]; rfl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  does_not_halt_of_conj_invariant tableIso_311_128 Inv
    ⟨cfg_modeC (encL 7 []) default, stepPlus_stepStar init_reaches_conj_inv_128,
      ⟨7, [], rfl, Or.inl ⟨rfl, by omega⟩⟩⟩
    inv_step

end BusyBeaver.M_1RB0RE_1LC1RF_HHH0LD_0LE1LB_1LF1LD_1RD0RA
