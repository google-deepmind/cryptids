/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

@[simp] theorem isVarA_tm : BusyBeaver.SymRunEngine.isVarA target_tm = true := rfl

namespace Solution

open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

def A : Fin 6 := 4
def B : Fin 6 := 3
def C : Fin 6 := 0
def D : Fin 6 := 2
def E : Fin 6 := 5

@[simp] theorem init_nil :
    (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = ⟨some C, ⟨0, default, default⟩⟩ := rfl

macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
    default_tail, enc1_nil, encM_nil, encM_cons_zero, encM_cons_run,
    encLeft_cons_head, cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
    encM_cons_run_head, cons_one_encM_cons_run_tail, multiStep_zero]
  try rfl))

macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head, cons_one_encLeft_tail,
    encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head, cons_one_encM_cons_run_tail]
  apply step_stepStar_stepPlus (by rfl)
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move, pow_succ_list,
    pow_zero_list, cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default,
    default_head, default_tail, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
    cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head,
    cons_one_encM_cons_run_tail]))

macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

theorem step_BB_nil (R : List MItem) :
    (cfgBB target_tm [] R) [target_tm]⊢⁺ cfgCB target_tm [] (bumpM R) := by
  unfold cfgBB cfgCB; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  execute 1

theorem step_BB_zero (L1 R : List MItem) :
    (cfgBB target_tm (.zero :: L1) R) [target_tm]⊢⁺ cfgCB target_tm L1 (bumpM R) := by
  unfold cfgBB cfgCB; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  execute 1

theorem step_BB_run0 (L1 R : List MItem) :
    (cfgBB target_tm (.run 0 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm L1 (.run 0 :: R) := by
  unfold cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  execute 8

theorem step_BB_run1 (L1 R : List MItem) :
    (cfgBB target_tm (.run 1 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm L1 (.run 0 :: bumpM R) := by
  unfold cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

theorem step_BB_run2 (L1 R : List MItem) :
    (cfgBB target_tm (.run 2 :: L1) R) [target_tm]⊢⁺ cfgDL target_tm L1 (.run 0 :: .run 0 :: bumpM
        R) := by
  unfold cfgBB cfgDL; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 5

theorem step_BB_run3 (L1 R : List MItem) :
    (cfgBB target_tm (.run 3 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm (.run 0 :: .zero :: .zero ::
        L1) (bumpM R) := by
  unfold cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  execute 9

theorem step_BB_run_ge4 (d : ℕ) (L1 R : List MItem) :
    (cfgBB target_tm (.run (d + 4) :: L1) R) [target_tm]⊢⁺ cfgBB target_tm (.run 0 :: .zero ::
        .run d :: L1) (bumpM R) := by
  unfold cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  execute 9

theorem cyc_R_A (k : ℕ) (V s : ListBlank (Fin 2)) :
    (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target_tm]⊢*
    ⟨some A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V), s⟩⟩ := by
  induction k generalizing V with
  | zero => finish
  | succ k ih =>
    have h1 :
        (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ (k + 1)) +> s⟩⟩ : Cfg (Fin 2) (Fin
            6))
          [target_tm]⊢⁺
        ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ := by
      execute 3
    have h2 := ih ((0 : Fin 2) >> V)
    have h12 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_eq :
        (([0] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> V) =
        (([0] : List (Fin 2)) ^ (k + 1)) +> V := by
      rw [zeros_append_cons_zero k V]
      simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]
    rwa [h_eq] at h12

theorem exit_R_A (W R1 : List MItem) :
    (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM W, (0 : Fin 2) >> encM R1⟩⟩ :
        Cfg (Fin 2) (Fin 6))
      [target_tm]⊢⁺
    cfgCB target_tm (.run 0 :: .run 0 :: W) R1 := by
  unfold cfgCB; dsimp only [isVarA_tm, ite_true, ite_false]
  execute 13


theorem step_DL_run0 (L1 R : List MItem) :
    (cfgDL target_tm (.run 0 :: L1) R) [target_tm]⊢⁺ cfgBB target_tm L1 (bumpM R) := by
  unfold cfgDL cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  execute 1

theorem step_DL_run1 (L1 R : List MItem) :
    (cfgDL target_tm (.run 1 :: L1) R) [target_tm]⊢⁺ cfgDL target_tm L1 (.run 0 :: bumpM R) := by
  unfold cfgDL; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

theorem step_DL_run2 (d0 : ℕ) (L1 R1 : List MItem) :
    (cfgDL target_tm (.run 2 :: L1) (.run d0 :: R1)) [target_tm]⊢⁺
      cfgCB target_tm (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1 := by
  unfold cfgDL; dsimp only [isVarA_tm, ite_true, ite_false]
  have h1 :
      ((encM (.run 2 :: L1)) <{{D}} (encM (.run d0 :: R1)))
        [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM L1,
        (([1] : List (Fin 2)) ^ (d0 + 1)) +> ((0 : Fin 2) >> encM R1)⟩⟩ := by
    execute 6
  have h2 := cyc_R_A (d0 + 1) ((0 : Fin 2) >> (0 : Fin 2) >> encM L1) ((0 : Fin 2) >> encM R1)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h_z1 := zeros_append_cons_zero (d0 + 1) ((0 : Fin 2) >> encM L1)
  have h_z2 := zeros_append_cons_zero (d0 + 1) (encM L1)
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  exact stepPlus_trans h12 (exit_R_A (List.replicate (d0 + 1) .zero ++ L1) R1)

theorem step_CB_nil (L : List MItem) :
    (cfgCB target_tm L []) [target_tm]⊢⁺ cfgDL target_tm (bumpM L) [.run 0] := by
  unfold cfgCB cfgDL; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  execute 2

theorem step_CB_zero (L R1 : List MItem) :
    (cfgCB target_tm L (.zero :: R1)) [target_tm]⊢⁺ cfgDL target_tm (bumpM L) (bumpM R1) := by
  unfold cfgCB cfgDL; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM L, ← encM_bumpM R1]
  execute 2

theorem step_CB_run0_nil (L : List MItem) :
    (cfgCB target_tm L [.run 0]) [target_tm]⊢⁺ cfgBB target_tm (.run 0 :: bumpM L) [] := by
  unfold cfgCB cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

theorem step_CB_run0_zero (L R2 : List MItem) :
    (cfgCB target_tm L (.run 0 :: .zero :: R2)) [target_tm]⊢⁺ cfgBB target_tm (.run 0 :: bumpM L)
        R2 := by
  unfold cfgCB cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

theorem step_CB_run0_run0 (L R2 : List MItem) :
    (cfgCB target_tm L (.run 0 :: .run 0 :: R2)) [target_tm]⊢⁺ cfgBB target_tm (.run 0 :: .zero ::
        bumpM L) R2 := by
  unfold cfgCB cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run, encM_cons_zero]
  rw [← encM_bumpM]
  execute 6

theorem step_CB_run0_run_pos (d2 : ℕ) (L R2 : List MItem) :
    (cfgCB target_tm L (.run 0 :: .run (d2 + 1) :: R2)) [target_tm]⊢⁺
      cfgCB target_tm (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2 := by
  unfold cfgCB; dsimp only [isVarA_tm, ite_true, ite_false]
  have h1 :
      (⟨some C, ⟨0, encM L, encM (.run 0 :: .run (d2 + 1) :: R2)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target_tm]⊢⁺
      ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> encM (bumpM L),
        (([1] : List (Fin 2)) ^ (d2 + 1)) +> ((0 : Fin 2) >> encM R2)⟩⟩ := by
    rw [← encM_bumpM L]
    execute 5
  have h2 := cyc_R_A (d2 + 1) ((0 : Fin 2) >> encM (bumpM L)) ((0 : Fin 2) >> encM R2)
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h_z1 := zeros_append_cons_zero (d2 + 1) (encM (bumpM L))
  have h_z2 :
      ((([0] : List (Fin 2)) ^ (d2 + 1)) +> encM (bumpM L)) =
      (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ d2) +> encM (bumpM L)) := by
    simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  exact stepPlus_trans h12 (exit_R_A (List.replicate d2 .zero ++ bumpM L) R2)

theorem step_CB_run1 (L R1 : List MItem) :
    (cfgCB target_tm L (.run 1 :: R1)) [target_tm]⊢⁺ cfgCB target_tm (.run 0 :: bumpM L) R1 := by
  unfold cfgCB; dsimp only [isVarA_tm, ite_true, ite_false]
  simp only [encM_cons_run]
  rw [← encM_bumpM]
  execute 3

theorem step_CB_run2 (L R1 : List MItem) :
    (cfgCB target_tm L (.run 2 :: R1)) [target_tm]⊢⁺ cfgBB target_tm (bumpM L) (.run 0 :: .zero ::
        R1) := by
  unfold cfgCB cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  execute 5

theorem step_CB_run_ge3 (d : ℕ) (L R1 : List MItem) :
    (cfgCB target_tm L (.run (d + 3) :: R1)) [target_tm]⊢⁺ cfgBB target_tm (bumpM L) (.run 0 ::
        .run d :: R1) := by
  unfold cfgCB cfgBB; dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  execute 5


theorem init_to_CB : (init []) [target_tm]⊢⁺ cfgCB target_tm [] [.run 1, .run 0] := by
  rw [init_nil]
  unfold cfgCB; dsimp only [isVarA_tm, ite_true, ite_false]
  execute 18

theorem step_DL_zero_halt (L1 R1 : List MItem) :
    (cfgDL target_tm (.zero :: L1) (.run 0 :: R1)) [target_tm]⊢⁺
    ⟨some E, ⟨1, (1 : Fin 2) >> encM L1, (0 : Fin 2) >> encM R1⟩⟩ := by
  unfold cfgDL; dsimp only [isVarA_tm, ite_true, ite_false]
  execute 1


instance : HasSymRunRules target_tm where
  step_BB_nil := step_BB_nil
  step_BB_zero := step_BB_zero
  step_BB_run0 := step_BB_run0
  step_BB_run1 := step_BB_run1
  step_BB_run2 := step_BB_run2
  step_BB_run3 := step_BB_run3
  step_BB_run_ge4 := step_BB_run_ge4
  step_DL_run0 := step_DL_run0
  step_DL_run1 := step_DL_run1
  step_DL_run2 := step_DL_run2
  step_CB_nil := step_CB_nil
  step_CB_zero := step_CB_zero
  step_CB_run0_nil := step_CB_run0_nil
  step_CB_run0_zero := step_CB_run0_zero
  step_CB_run0_run0 := step_CB_run0_run0
  step_CB_run0_run_pos := step_CB_run0_run_pos
  step_CB_run1 := step_CB_run1
  step_CB_run2 := step_CB_run2
  step_CB_run_ge3 := step_CB_run_ge3

def initSymCyc3 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1),
      .repB1 46, .item (.run 0)], [.item (.run 79), .item (.run 0), .item (.run 1), .item .zero,
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk4096 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run
      0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .rep12
      69932, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item
      (.run 1), .repB1 349284, .item (.run 0)], [.item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1)])

def symChk8192 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .rep12 293731192, .item (.run 2), .repB1 1468655224, .item (.run 0)],
      [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 6), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1), .item .zero
      , .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk12288 : SymMode × List SymTok × List SymTok :=
  (.CB, [], [.item (.run 1), .repB1 7401584263016, .item (.run 1), .item (.run 1), .item (.run 0)
      , .item (.run 1), .rep2 1, .item (.run 0), .item (.run 1), .item .zero, .item (.run
      7401584264101), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      2), .item (.run 3), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero, .item (.run
      0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1)])

def symChk16384 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 0), .item (.run 1), .rep2 5828399623694162, .item (.run 1), .item (.run 0),
      .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0)
      , .item (.run 1), .item (.run 2), .repB1 11656799247386921, .item (.run 0)], [.item (.run 0)
      , .item (.run 11656799247388309), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 2), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 3), .item (.run 3), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 5), .item (.run 3), .item (.run 1), .item (.run 1)])

def symChk20480 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .rep12 9179181364734787724, .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1 45895906823673936877, .item
      (.run 0)], [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1)])

def symChk24576 : SymMode × List SymTok × List SymTok :=
  (.DL, [.repB1 192751300452273201788429, .item (.run 0)], [.item (.run 0), .item (.run 0), .item
      (.run 1), .item (.run 1), .rep12 38550260090454640358104, .item (.run 0), .item (.run 2),
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 0), .item (.run 1), .item .zero, .item (.run 0), .item (.run 1)
      , .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item .zero
      , .item (.run 3), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item .zero, .item (.run 1)])

def symChk28672 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .rep12 161901426063024309850221340, .item (.run 2)
      , .repB1 809507130315121549251104250, .item (.run 0)], [.item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run
      5), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1)])

def symChk32768 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .repB1
      3399726966787864888523559563277, .item (.run 0)], [.item (.run 0), .item (.run 1), .item
      (.run 1), .rep12 679945393357572977704711913207, .item (.run 0), .item (.run 1), .item (.run
      0), .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 4), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run 1),
      .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk36864 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 2), .repB1 8566800475893506045311193103085396, .item (.run 0)], [.item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .rep2
      4283400237946753022655596551544268, .item (.run 0), .item (.run 1), .item .zero, .item (.run
      8566800475893506045311193103088524), .item (.run 1), .item (.run 2), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 1),
      .item (.run 1)])

def symChk40960 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 1), .repB1 59964023182123780301115281865963814445, .item (.run 0)], [.item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .rep12 11992804636424756060223056373192763585, .item (.run 0), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 2), .item
      (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 2), .item (.run 3), .item (.run 1), .item (.run 7), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1)])

def symChk45056 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .rep12
      28331309434081290173749125880312046958998, .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 0), .item .zero, .item (.run 1), .repB1
      141656547170406450868745629401560234791159, .item (.run 0)], [.item (.run 1), .item (.run 0)
      , .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3), .item (.run 0), .item (.run
      1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item .zero
      , .item (.run 7), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk49152 : SymMode × List SymTok × List SymTok :=
  (.BB, [.item (.run 0), .item (.run 1), .rep2 1, .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 1), .repB1 535429780494748407225024473657428158523986309, .item (.run 0)],
      [.item (.run 0), .item (.run 1), .item (.run 2), .item (.run
      535429780494748407225024473657428158523990526), .item (.run 1), .item (.run 1), .item (.run
      0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
      .zero, .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1)])

def symChk53248 : SymMode × List SymTok × List SymTok :=
  (.CB, [], [.item (.run 1), .repB1 1873892351078590533629325742230370269117066257558, .item (.run
      0), .item (.run 2), .item (.run 0), .item (.run 1), .item (.run 1), .rep12
      374778470215718106725865148446074053823413252433, .item (.run 0), .item (.run 1), .item
      (.run 0), .item (.run 1), .item .zero, .item (.run 1), .item (.run 6), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 5), .item (.run 1), .item (.run 6), .item
      (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk57344 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .rep2
      996031434861122243531684763682732439419162283857463, .item (.run 1), .item (.run 0), .item
      .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item
      .zero, .item (.run 1), .repB1 1992062869722244487063369527365464878838324567709997, .item
      (.run 0)], [.item (.run 1992062869722244487063369527365464878838324567714920), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk61440 : SymMode × List SymTok × List SymTok :=
  (.DL, [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 0), .item (.run 1), .rep12 661776688146251534887371767366373046443244305364132822,
      .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)
      , .repB1 3308883440731257674436858836831865232216221526820658827, .item (.run 0)], [.item
      (.run 4), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
      .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0)
      , .item (.run 1), .item (.run 2), .item (.run 1), .item (.run 2), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 2), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk65536 : SymMode × List SymTok × List SymTok :=
  (.DL, [.rep12 659540004931999983852102031802319817808504446014405329671, .item (.run 1), .item
      (.run 0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1
      3297700024659999919260510159011599089042522230072026642750, .item (.run 0)], [.item (.run 0)
      , .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
      (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 2), .item (.run 4), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item .zero, .item (.run 1), .item (.run 3), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk69632 : SymMode × List SymTok × List SymTok :=
  (.CB, [.item (.run 0), .item (.run 0), .item .zero, .item (.run 1), .item (.run 1), .item (.run
      0), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1), .repB1
      2629243525178812812679392664523750958759518709707280000200843, .item (.run 0)], [.item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .rep2
      1314621762589406406339696332261875479379759354853640000103353, .item (.run 0), .item (.run
      1), .item (.run 2), .item (.run
      2629243525178812812679392664523750958759518709707280000206708), .item (.run 1), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item
      (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .item (.run 3),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1)])

def symChk70511 : SymMode × List SymTok × List SymTok :=
  (.HALT, [.item .zero, .item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run
      1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 2), .rep12
      2077426982857333580388655932463210634081595029892171852015193, .item (.run 2), .repB1
      10387134914286667901943279662316053170407975149460859260070043, .item (.run 0)], [.item
      (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
      .item (.run 1), .item .zero, .item (.run 3), .item (.run 1), .item (.run 1), .item (.run 1)
      , .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1),
      .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run
      1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 1), .item
      (.run 1), .item (.run 1), .item (.run 1)])


set_option maxRecDepth 200000 in
theorem test_elem_rfl :
    runElemFast 1 1 11 4 (.CB, [], [.run 1, .run 0]) = (initSymCyc3.1, encSymL initSymCyc3.2.1,
        encSymR initSymCyc3.2.2) := by decide +kernel

set_option maxRecDepth 200000 in
theorem sym_chk1 : stepSym4096 initSymCyc3 = symChk4096 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk2 : stepSym4096 symChk4096 = symChk8192 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk3 : stepSym4096 symChk8192 = symChk12288 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk4 : stepSym4096 symChk12288 = symChk16384 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk5 : stepSym4096 symChk16384 = symChk20480 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk6 : stepSym4096 symChk20480 = symChk24576 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk7 : stepSym4096 symChk24576 = symChk28672 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk8 : stepSym4096 symChk28672 = symChk32768 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk9 : stepSym4096 symChk32768 = symChk36864 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk10 : stepSym4096 symChk36864 = symChk40960 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk11 : stepSym4096 symChk40960 = symChk45056 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk12 : stepSym4096 symChk45056 = symChk49152 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk13 : stepSym4096 symChk49152 = symChk53248 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk14 : stepSym4096 symChk53248 = symChk57344 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk15 : stepSym4096 symChk57344 = symChk61440 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk16 : stepSym4096 symChk61440 = symChk65536 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk17 : stepSym4096 symChk65536 = symChk69632 := by decide +kernel
set_option maxRecDepth 200000 in
theorem sym_chk18 : iterStep stepSym 15 (iterStep stepSym16 6 (iterStep stepSym256 3 symChk69632))
    = symChk70511 := by decide +kernel



end Solution

public section

open Solution BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine in
theorem is_halt : IsHalt target := by
  have h0 : (init []) [target_tm]⊢* ((evalM target_tm) (.CB, [], [.run 1, .run 0])) :=
    stepPlus_stepStar init_to_CB
  have h1 : ((evalM target_tm) (.CB, [], [.run 1, .run 0])) [target_tm]⊢* ((evalSym target_tm)
      initSymCyc3) := by
    have h := runElemFast_sound (target_tm := target_tm) 1 1 11 4 (.CB, [], [.run 1, .run 0])
    rw [test_elem_rfl] at h
    exact h
  have hc1 : ((evalSym target_tm) initSymCyc3) [target_tm]⊢* ((evalSym target_tm) symChk4096) :=
      by rw [← sym_chk1]; exact stepSym4096_sound initSymCyc3
  have hc2 : ((evalSym target_tm) symChk4096) [target_tm]⊢* ((evalSym target_tm) symChk8192) := by
      rw [← sym_chk2]; exact stepSym4096_sound symChk4096
  have hc3 : ((evalSym target_tm) symChk8192) [target_tm]⊢* ((evalSym target_tm) symChk12288) :=
      by rw [← sym_chk3]; exact stepSym4096_sound symChk8192
  have hc4 : ((evalSym target_tm) symChk12288) [target_tm]⊢* ((evalSym target_tm) symChk16384) :=
      by rw [← sym_chk4]; exact stepSym4096_sound symChk12288
  have hc5 : ((evalSym target_tm) symChk16384) [target_tm]⊢* ((evalSym target_tm) symChk20480) :=
      by rw [← sym_chk5]; exact stepSym4096_sound symChk16384
  have hc6 : ((evalSym target_tm) symChk20480) [target_tm]⊢* ((evalSym target_tm) symChk24576) :=
      by rw [← sym_chk6]; exact stepSym4096_sound symChk20480
  have hc7 : ((evalSym target_tm) symChk24576) [target_tm]⊢* ((evalSym target_tm) symChk28672) :=
      by rw [← sym_chk7]; exact stepSym4096_sound symChk24576
  have hc8 : ((evalSym target_tm) symChk28672) [target_tm]⊢* ((evalSym target_tm) symChk32768) :=
      by rw [← sym_chk8]; exact stepSym4096_sound symChk28672
  have hc9 : ((evalSym target_tm) symChk32768) [target_tm]⊢* ((evalSym target_tm) symChk36864) :=
      by rw [← sym_chk9]; exact stepSym4096_sound symChk32768
  have hc10 : ((evalSym target_tm) symChk36864) [target_tm]⊢* ((evalSym target_tm) symChk40960) :=
      by rw [← sym_chk10]; exact stepSym4096_sound symChk36864
  have hc11 : ((evalSym target_tm) symChk40960) [target_tm]⊢* ((evalSym target_tm) symChk45056) :=
      by rw [← sym_chk11]; exact stepSym4096_sound symChk40960
  have hc12 : ((evalSym target_tm) symChk45056) [target_tm]⊢* ((evalSym target_tm) symChk49152) :=
      by rw [← sym_chk12]; exact stepSym4096_sound symChk45056
  have hc13 : ((evalSym target_tm) symChk49152) [target_tm]⊢* ((evalSym target_tm) symChk53248) :=
      by rw [← sym_chk13]; exact stepSym4096_sound symChk49152
  have hc14 : ((evalSym target_tm) symChk53248) [target_tm]⊢* ((evalSym target_tm) symChk57344) :=
      by rw [← sym_chk14]; exact stepSym4096_sound symChk53248
  have hc15 : ((evalSym target_tm) symChk57344) [target_tm]⊢* ((evalSym target_tm) symChk61440) :=
      by rw [← sym_chk15]; exact stepSym4096_sound symChk57344
  have hc16 : ((evalSym target_tm) symChk61440) [target_tm]⊢* ((evalSym target_tm) symChk65536) :=
      by rw [← sym_chk16]; exact stepSym4096_sound symChk61440
  have hc17 : ((evalSym target_tm) symChk65536) [target_tm]⊢* ((evalSym target_tm) symChk69632) :=
      by rw [← sym_chk17]; exact stepSym4096_sound symChk65536
  have hc18 : ((evalSym target_tm) symChk69632) [target_tm]⊢* ((evalSym target_tm) symChk70511) :=
      by
    rw [← sym_chk18]
    exact stepStar_trans (iterStep_sound stepSym256 (evalSym target_tm)
        (stepSym256_sound (target_tm := target_tm)) 3
        symChk69632)
      (stepStar_trans (iterStep_sound stepSym16 (evalSym target_tm)
        (stepSym16_sound (target_tm := target_tm)) 6 _)
        (iterStep_sound stepSym (evalSym target_tm)
        (stepSym_sound (target_tm := target_tm)) 15 _))
  have h_to_halt_sym : (init []) [target_tm]⊢* ((evalSym target_tm) symChk70511) :=
    stepStar_trans h0 (stepStar_trans h1 (stepStar_trans hc1 (stepStar_trans hc2
      (stepStar_trans hc3 (stepStar_trans hc4 (stepStar_trans hc5 (stepStar_trans hc6
      (stepStar_trans hc7 (stepStar_trans hc8 (stepStar_trans hc9 (stepStar_trans hc10
      (stepStar_trans hc11 (stepStar_trans hc12 (stepStar_trans hc13 (stepStar_trans hc14
      (stepStar_trans hc15 (stepStar_trans hc16 (stepStar_trans hc17 hc18))))))))))))))))))
  have h_final := step_DL_zero_halt
    (encSymL symChk70511.2.1.tail)
    (encSymR symChk70511.2.2.tail)
  exact ⟨_, stepStar_trans h_to_halt_sym (stepPlus_stepStar h_final), rfl⟩

end

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
